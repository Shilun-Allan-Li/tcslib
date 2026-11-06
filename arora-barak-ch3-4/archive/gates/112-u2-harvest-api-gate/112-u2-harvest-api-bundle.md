## ===== campaign/gates/112-u2-harvest-api/pack.md =====

# External audit pack: the U2 harvest API, `Build/UniversalParts` (PR #221, an API gate)

## Why this PR

F6 (`space_universal`, `SpaceComplexity/Hierarchy`, [AB09, Exercise 4.1]) composes its route
from pieces of the self-universal machine U2-E/U2-U (`TuringMachine/UniversalK`): header scans
with a ruler, the startup-to-loop seam, the forwarding loop's lockstep readings, and the
suffix-ruler layout. Those pieces were privates of `UniversalK`, and rule 11 forbids citing
another file's privates. This PR publishes them. It follows gate 20 (the H1 harvest) and gate 73
(U2's API).

**The user's rulings (2026-11-06):**
- the rows go in a **new `Build/` module**, not in place in `UniversalK`;
- the harvest comes before RO-1's `UniversalK` edits;
- **RS-1**: the restart identity is published here.

The plan is `campaign/items/roadmap3/PLAN.md`, §F6 (c), and the design note is
`evidence/probes/DESIGN.md`.

**The PR:** #221 on `lean/u2-harvest-api`, head `51843dd2` (full hash in the bundle header). It
consists of `065e1e80` (the new module and its facade entry), `db12c154` (`UniversalK` cites it
and the 26 harvested privates are deleted), and merges of the campaign, the last after #218 and
#219. Diff:
- `Build/UniversalParts.lean`: +976 (new);
- `UniversalK.lean`: +44 −790, from 2,873 to 2,127 lines;
- the `TuringMachine` facade: +6.

## What changed (verify)

**`Build/UniversalParts`** (namespace `Turing`; the forwarding-loop rows under
`Turing.StepBlock`; private prefix `up_`). It imports `Build/StepBlockForward`,
`Build/InputDevice`, `Build/Rewind` and `Mathlib.Algebra.Group.Action.Defs` (for `smul_eq_mul`),
none of which reaches `UniversalK`. It has 22 public rows:

| Group | Rows | Source private |
|---|---|---|
| restart identity (RS-1) | `MultiTapeTM.initCfg_eq_mapState` | `uk_init_mapState` |
| forwarding loop at its start | `StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`; `embedEmitCfg_forwardLoop_init` | `uk_encode_init_tapes`, `uk_encode_init_fields`, `uk_encode_halt`, `uk_embed_init` |
| lockstep readings | `StepBlock.forwardLoop_forward`, `_live`, `_converse` | `uk_loop_forward`, `uk_loop_live`, `uk_loop_converse` |
| seam | `startupLoopTM` (def), `_initCfg`, `_live_of_le`, `_runFrom` | `uk_loopTM`, `uk_loop_init`, `uk_loop_pre_live`, `uk_loop_run` |
| seam space | `startupLoopTM_spaceUsed_le`, **generalized** to any seam endpoint (the hypotheses of `startupLoopTM_runFrom`) | `uk_loop_space` (fixed native endpoint) |
| header scan | `headerScanTM`, `headerScanCfg` (defs; `simps` field equations), `headerScanTM_run`, `headerRulerTM`, `headerRulerTM_run` | `uk_scanTM`, `uk_scanCfg`, `uk_scan_run`, `uk_headerTM`, `uk_header_run` |
| ruler | `headerScanCfg_ruler`, **generalized** from a blank tape to a ruler prefix `true^m` (`m = 0` is the old statement), so two scans compose | `uk_scan_ruler` |
| suffix-ruler layout | `suffixRulerCfg` (def; `simps` field equations), `rulerHostCfg_fields`, `suffixRulerCfg_embed` | `uk_suffixCfg`, `uk_ruler_fields`, `uk_embed_suffix` |

Moved with them, renamed: `up_scan_zero`, `up_scan_step`, `up_scan_pair`, `up_scan_header`. A
private corollary `up_scan_ruler_blank` restates the `m = 0` case, derived from the general form.
After renaming, 23 of the 26 moved declarations are textually identical. The three that differ
are the two generalizations and `headerRulerTM_run`, which cites `up_scan_ruler_blank`.

**`UniversalK`:**
- `exists_selfUniversalK` and `universalK` keep **byte-identical statements**; only their bodies
  are re-pointed.
- The private `uk_suffixStartupTM`/`_run` are re-pointed.
- Three definitional reads of the now-foreign `suffixRulerCfg` are fixed through its field
  equations: in `uk_suffixStartup_run`'s final step, in a `rfl` for its state in `universalK`'s
  body, and in `universalK`'s live-prefix step. The seal found the second and third.

## Known deviations (for the audit)

- **Size:** `UniversalParts` has 976 lines, above the 600-line target and below 1,000 (campaign
  lint INFO). Its four groups cite one another.
- **RS-1's home:** the restart identity is a `MultiTapeTM` fact published in a `Build/` module
  rather than `TuringMachine/Finite`. That is the user's ruling, which avoids a replay of most of
  the tree. RS-1's other sites re-point to it in the dedup window.
- **`headerRulerTM_run`** still needs a blank ruler tape. F6's second header composes
  `headerScanTM_run`, `headerScanCfg_ruler` and `rewindTM_run_ofCfg` instead.

## Brief for the auditor

1. **The API:** are the rows correctly stated and placed? Are both generalizations right, and do
   they reduce to the old statements? Is anything missing that F6's route needs? The consumer
   probe below composes the route.
2. **Rule 10 / rule 11:**
   - Does `UniversalParts` read other files' definitions only through published equations?
   - Does `UniversalK` now read `UniversalParts`' definitions only through their equations?
   - Is nothing private cited across files?
3. **The move:** is it faithful, with no statement or behaviour change beyond the two
   generalizations? Are `UniversalK`'s public statements unchanged?
4. **Public text:** docstrings, attributions and sketches.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`, `UniversalK` at the head against the campaign `7027dead`):
  - 12 → 12 public, with no statement change;
  - the only body changes are the two authorized ones, `exists_selfUniversalK` and `universalK`;
  - 67 → 41 private: 26 removed, as listed above, and 2 changed (`uk_suffixStartupTM`,
    `uk_suffixStartup_run`).
- **Rule 10** (`evidence/probes/Seal*.lean.txt`, `.out`):
  - `UniversalParts` is sealed with the 16 other-file definitions it reads made irreducible
    (`SealParts`). The body elaborates; the 16 controls fail sealed (16 errors, all on the
    control lines at the end) and close unsealed (`SealParts0`, 0 errors).
  - `UniversalK` is sealed with the 5 moved definitions irreducible (`SealUK`). The body
    elaborates; the 5 controls fail sealed and close unsealed (`SealUK0`).
- **Axioms** (`evidence/probes/Ax.*`): all 22 rows, their 10 generated field equations,
  `universalK` and `exists_selfUniversalK` (28 prints) use only the standard three or fewer. No
  `sorryAx`.
- **Consumer probe** (`evidence/probes/Probe.lean.txt`, `probe.out`, exit 0):
  - two header scans compose to `true^(ℓ₁ + ℓ₂)`;
  - the startup runs under the ruler host on the first header's suffix (`rulerHostCfg_fields`),
    within `B + ℓ₁ + 2` cells;
  - the final seam is closed with `startupLoopTM_runFrom` and `startupLoopTM_spaceUsed_le`
    through `suffixRulerCfg_embed`;
  - F6's layout is `pairEncode (bits s) (pairEncode α x)`.

  Only F6's own leaves are `sorry`, in `route_space`.
- **Screen** (`evidence/screen/`; `UniversalK`, `StepBlockForward`, `InputDevice`, `Rewind`,
  `SelfUniversal`, and at the head `UniversalParts`): the base has 134 declarations and 23 pairs,
  the head 137 and 23. 5 pairs are new and 5 gone, and the new ones are the gone ones renamed,
  moved with their declarations (`pairdiff.txt`). No new copy.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `TuringMachine` gives 0 FAIL, 72 WARN, over 92 files at the base and 93
    at the head; `UniversalParts` adds only INFO lines (its size).
  - The policy linter gives 1 finding at both, `UniversalK`'s size (2,873 → 2,127 lines, still
    above 1,000).
- **Replay** (`evidence/merged-tree/`): `replay-lhv2` at `51843dd2` covers the downstream closure
  (7 modules: `UniversalParts`, `UniversalK`, `SelfUniversal`, `Hierarchy`, `UniversalTlogT` and
  both facades), chained from the campaign snapshot after #218 and #219. **7 modules, 0 failed.**
  The static check finds 0 mismatches. The 2 `sorry` warnings are `Hierarchy`'s F6 and E-PAD.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/112-u2-harvest-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `u2-harvest-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/112-u2-harvest-api/STATUS.md =====

# Gate 112 (#221, the U2 harvest API)

- 2026-11-06: #221 opened (RS-1 ruled: publish in UniversalParts); `replay-lhv2` (7/0, after #218/#219); freeze, lint, screen at the head; probes (seals, axioms, consumer); pack written; staged.

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

## ===== campaign/items/roadmap3/PLAN.md =====

# Three roadmap tracks: F6, book-form Theorem 3.1, Ladner (planning note)

**Status:** read-only planning (sub-agent, 2026-11-06). No tracked file was edited, and Lean was not run.
**Base:** campaign `complexity/arora-barak-ch3-4` at `508781aa` (Lean as at #209/#191/#207's merges).
Line numbers are at this base unless marked otherwise. **The user's ruling** (HANDOFF §3 item 4, 2026-11-06)
is to run all three in parallel. The ruling's own text sets each track's order: F6 is the U2 harvest and
then the fill; the other two tracks are statement phases.

Gate numbers below are placeholders. The next free number is 108 (the last used is 107-rp1-dedup).

---

## Track 1 — F6: `Complexity.space_universal`

### (a) Current state

- **The target.** `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:150–161`, sorried; in H's delivery
  (`deliver/fill-b6-hierarchy-in`) it is at `:147–158`, byte-preserved. The statement is frozen by RD-3
  (gate 05, PASS 0/0/4) and the B6-hosts gate (13, PASS 0/0/5, which strengthened it to `C · s`).
  `∃ SU, ∀ α, ∃ C, 0 < C ∧ ∀ s x output t, (code.decode α).toFinTM.ComputesInTime x output t →
  spaceUsed … t ≤ s → ∃ t', SU.ComputesInTime (pairEncode (bits s) (pairEncode α x)) output t' ∧
  SU.spaceUsed … t' ≤ C * s`, over the one-tape scheme `TimeHierarchy.code`.
  - No consumer: `space_hierarchy` uses `U₀`. The B6 fill plan places F6 "last".
  - F6 is the last of the 26 headlines (status `campaign/status/2026-11-05-headlines/README.md:15`).
- **Same file, other work.** H's fill was delivered on 2026-11-06 (REPORT `campaign/fills/b6/reports/hierarchy-REPORT.md`):
  - `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` are proved;
  - `SPACE_linear_ne_NP` ends in escalation **E-PAD** (REPORT:510–560): an exact padded-language
    linear-space decider is missing;
  - the delivery changes only `Hierarchy.lean` (+2,295 lines), and its imports gain `SelfUniversal`,
    `Build/WindowRun`, `SpaceComplexity/WindowClock` and `ClassNP/PClosure` (delivery `:11–14`).
  - **Consequence:** after H lands, `Hierarchy` reaches `UniversalK` through `SelfUniversal`
    (`SelfUniversal.lean:8`).
- **The route** (`campaign/fills/b6/drafts/F6-retriage.md`) is U2-E's (`Turing.universalK`,
  `UniversalK.lean:2764`, proved), with two changes: a second header, and a space ledger in place of the
  time bound. Every piece already exists as a **private** of `UniversalK`. Rule 11 forbids citing them,
  and re-deriving them is a duplication finding.
  - Megafill C's Q-U2 says to "publish when `space_universal` is briefed".
  - U2's fill review F7(ii)–(iv) (`campaign/fills/u2s/reviews/universal/REVIEW.md:216`) and its REPORT
    (`universal-REPORT.md:294`) list the promotion candidates.
- **Published hosts F6 also needs** (all proved):
  - `exists_selfStartupTMK` (`UniversalK:1425`, with a space bound `B`) and
    `StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward:481`, with visited-set clauses);
  - `exists_rulerHostTM` (`Build/InputDevice:1226`, a space ledger of the bank plus `ℓ + 2`),
    `pairEncode_drop` (`InputDevice:198`), `pairEncode_pairEncode_length`/`_drop`, and `rewindTM_run_ofCfg`
    (`Build/Rewind:112`);
  - `seamCompTM_step` (`Build/InterpreterStartup:64`), `seamCompTM_spaceUsed_le_add` (`Build/Seam:461`),
    and `vhostSilentTM_runFrom`/`_spaceUsed_le` (`Build/VirtualInput:469/489`);
  - `CodeTM.one_le_spaceUsed` and `length_bits_le_self` (`Encoding`), and `spaceUsed_le_mul_succ` (`Finite`).

### (b) Still to decide or design (the records' open points)

- **D-F6-1, harvest or a private re-derivation** (retriage "Decisions"). The ruling of 2026-10-27,
  "F6 after U2's harvest API PR", already implies harvest first; I recommend confirming it.
- **D-F6-2, the harvest's home** (retriage: "`UniversalK`, or a new `Build/` module if `Hierarchy` should not
  import all of `UniversalK`"). Once H lands, `Hierarchy` imports `UniversalK` transitively, so in-place
  publication costs no import.
  - *Recommended:* publish the scan, seam and suffix-layout rows **in place in `UniversalK`**, whose
    downstream at the tip is 3 modules, plus `Hierarchy` after H.
  - Move the lockstep corollaries beside H2-F in `Build/StepBlockForward` (review F7(ii); downstream 4).
  - Put the `rulerHostCfg` field reader beside `rulerHostCfg` in `Build/InputDevice` (downstream 13).
- **D-F6-3, the startup's input** (retriage's "one open design point"). `exists_selfStartupTMK` reads its
  code at the start of the native input, but in `SU`'s input the code is the second header. The options:
  - (i) the retriage's: a buffered copy of `pairEncode α []`, run through `vhostSilentTM`, at `O(|α|)` cells.
    This needs a new copy leaf, and a full-suffix copy would break `C · s`.
  - (ii) **New, recommended for the route probe:** run the startup under the **ruler host** on the suffix
    `z.drop (2|bits s| + 2) = pairEncode α x`. This is exactly the startup's native input; the ruler is
    the first header's scan, and costs `2|bits s| + 4 ≤ 2s + 4` cells. No copy and no new leaf are needed;
    the ruler is then extended by the second scan.
  - (iii) a startup variant with an input offset: a new host, statement-gated. Not recommended.
- **D-F6-4, the order in `Hierarchy.lean`.** The rule is one fill per file (Q-D3). Three items edit this
  file: H's landing (first, now), F6's fill, and the E-PAD continuation of `SPACE_linear_ne_NP`. The
  record has no ruling on F6 against E-PAD.
- **D-F6-5, RS-1** (`uk_init_mapState`, ledger RS-1: a public row in `TuringMachine/Finite`, with 5 sites in
  4 files). It is not needed by F6. Publishing it in `Finite` means a replay of most of the tree, so
  *recommended:* keep it out of the harvest and leave it to the dedup window.
- The agent: Codex (retriage, step 3). The estimate is 800–1,500 lines (megafill D, T4); with the harvest,
  roughly 500–1,000 (ESTIMATE).

### (c) Next deliverable: the U2 harvest API PR (branch e.g. `lean/u2-harvest-api`; an API gate)

| Public row (proposed name) | Source private (`UniversalK.lean`) | Home | Change |
|---|---|---|---|
| `Turing.headerScanTM (i : Fin k)` + `headerScanCfg` with field equations (or `simps`) | `uk_scanTM :2161`, `uk_scanCfg :2170` | `UniversalK` | visibility; definitions land with their lemmas (policy §1) |
| `Turing.headerScanTM_run` | `uk_scan_run :2370`, already stated "from any input position `1 + p` with `z.drop p = pairEncode u v`" | `UniversalK` | none; `uk_scan_zero/step/pair/header :2180–2310` stay private |
| `Turing.headerScanCfg_ruler` | `uk_scan_ruler :2397` | `UniversalK` | **generalize** from a blank tape to an existing ruler prefix `true^m` before the head, so that two scans give `true^(ℓ₁+ℓ₂)`; `m = 0` is the current statement |
| `Turing.headerRulerTM` + `_run` (scan, then rewind) | `uk_headerTM :2414`, `uk_header_run :2424` | `UniversalK` | visibility (optional; `universalK`'s consumer) |
| `Turing.startupLoopTM` + `_initCfg`, `_live_of_le`, `_runFrom` | `uk_loopTM :1807`, `uk_loop_init :1827`, `uk_loop_pre_live :1834`, `uk_loop_run :1850` | `UniversalK` | visibility |
| `Turing.startupLoopTM_spaceUsed_le` | `uk_loop_space :1954` | `UniversalK` | **generalize**: today it fixes the native startup's endpoint (`hrun` at input position 1, with no ruler). Restate it, like `uk_loop_run`, for any seam endpoint `d` with `d.mapState (fun _ => entry) = embedEmitCfg σ … c`, so that it serves the `k + 1` suffix layout |
| `StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`; `embedEmitCfg_forwardLoop_init` | `uk_encode_init_tapes :1697`, `uk_encode_init_fields :1736`, `uk_encode_halt :1752`, `uk_embed_init :1766` | `Build/StepBlockForward` (the `_halt` lemma is needed by the converse below) | visibility |
| `StepBlock.forwardLoop_forward`, `_live`, `_converse` | `uk_loop_forward :1871`, `uk_loop_live :1896`, `uk_loop_converse :1918` | `Build/StepBlockForward`, beside H2-F | visibility; generic in `M`, `L` and `cost` |
| `Turing.suffixRulerCfg` + field equations; `suffixRulerCfg_embed` | `uk_suffixCfg :2504` (generic in `z`, `ℓ`), `uk_embed_suffix :2672` | `UniversalK` | visibility |
| `Turing.rulerHostCfg_fields` | `uk_ruler_fields :2651` | `Build/InputDevice`, beside `rulerHostCfg` | visibility |

- **Unchanged.** `universalK` and `exists_selfUniversalK` are re-pointed to the public rows, with their
  statements byte-identical. `uk_suffixStartupTM`/`_run` (`:2496/2520`) stay private: they are U2-E's own
  native-startup composition. All names are proposals, to be name-searched on every ref (WORKFLOW §3).
- **Gate pack outline**, after gate 73 (U2's API) and gate 20 (the H1 harvest precedent):
  - why: rule 11, and harvest before the second consumer is briefed;
  - a "what changed" table of row ← private, with each generalization argued;
  - the freeze: every public statement unchanged, with only bodies re-pointed;
  - rule 10, the sealed copies with controls;
  - axioms: every new row on the standard three;
  - a **consumer probe**: F6's route composed from the published rows (two scans, the startup under the
    ruler host, the ruler host around H2-F, the space ledger), with only F6's own leaves sorried;
  - the v3 screen (pairs moved or gone, none new), names on every ref, and lint check 8;
  - the replay: the downstream of `UniversalK`, `StepBlockForward` and `InputDevice`, chained from the
    campaign snapshot. If H has merged, `Hierarchy` is included.
- **Then F6's brief** (Codex), issued on H's merged tree. It authorizes the import union; the expected
  set is none beyond H's nine, to be confirmed by the import probe. The pre-ship has the route probe
  for D-F6-3 (ii), the seal controls, the screen base and the base sorry set.

### (d) Overlaps

- **`lean/dedup-ro1`** (parked, `7c940a8a`): the user ruled to re-point **every** site. RO-1's list names
  `UniversalK`'s fixed-machine statements, and `UniversalK:2291` lies inside `uk_scan_pair`, a harvested
  private. This is a textual conflict, so one goes first; *recommended:* the harvest first, then RO-1
  re-points the published row. RO-1 also touches `TwoTapes` (`tt_round`, ledger +1 from #211).
- **H's landing:** the same downstream (`Hierarchy`). Whichever merges second takes a merged-tree replay.
- **#211** (`TwoTapes` only) and **#212–#216**: no file overlap. NatBits (after #208) moves
  `length_bits_le_self` to `TuringMachine/NatBits` with its name kept, and its 340-module replay
  includes `UniversalK`, so it needs a merged-tree replay with the harvest.

---

## Track 2 — book-form Theorem 3.1 (the `f log f` time hierarchy)

### (a) Current state, and what "book-form" means in the records

- **The received theorem.** `Complexity.time_hierarchy` (`TimeHierarchy/Diagonal.lean:518`, proved) says
  that if `TimeConstructible g` and `∀ A, ∃ N, ∀ n ≥ N, A * (f n + n + 1)^2 ≤ g n`, then
  `DTIME f ⊂ DTIME (g + 1)`. `_of_pos` (`:531`) gives `DTIME g`. Its divergences are recorded at `:67–98`:
  - a **quadratic overhead**, owing to the one-work-tape normal form;
  - `DTIME(n) ⊊ DTIME(n^1.5)` is not derivable (`:84–88`);
  - "the sharper `f log f` form is planned … not available until those exist" (`:79–83`).
  - The facade `TimeHierarchy.lean:13–17` says "quadratic overhead in place of the book's `f log f`".
- **"Book-form"** is defined in plan §2.1 (CH34-Q3, "strengthen", 2026-10-08): Theorem 3.1 at the book's
  `f log f = o(g)`, via Hennie–Stearns plus the two-tape universal. "Until that lands, the received form
  is documented as delivered strength, never as Thm 3.1 verbatim." The U2 design §3.2 specifies
  `time_hierarchy_book : n ≤ f n ∧ f log f = o(g)`, and the G5 plan (lines 3–5) refers to it as
  "book-form Theorem 3.1".
- **Diagonal Part 1 has landed** (#100, gate 24, PASS 0/0/2): `DiagSimulator` (`:212`) with `.mono`,
  `.diagLang_not_mem_DTIME`, `.time_hierarchy` and `_of_pos` (`:226–310`); `SelfSimulator` (`:341`);
  `.toDiagSimulator` (`:364`); and the `f²` instance `oneTapeSelfSimulator`/`sqDiagSimulator` (`:429/465`).
- **Part 2 is the book form**, which the 2026-10-14 authorization places at the end of `Diagonal.lean`
  (Hydroxyi's file). It is drafted and proved in the U2 probe, `campaign/items/u2/probes/U2DiagParam.lean.txt`:
  - `:275–330`: `logOverhead`, `logDiagOverhead`, `le_logDiagOverhead`, `logOverhead_add_le`,
    `time_hierarchy_log`, `logDiagOverhead_le_book` and `time_hierarchy_book`;
  - `:681–742`: `log_mul_two_pow`, `logOverhead_mul_le`, `code₂` and `twoTapeSelfSimulator`.
- **Inputs.**
  - `two_work_tapes_run`/`_binary`: at the base, `Robustness/TwoTapes.lean:64/78`, sorried at `:70`. On
    #211's head (`e7e78aaf`) they are at `:2428/2452` with **no `sorry`**.
  - `exists_selfUniversalK` (`UniversalK:2052`) and `universalK` (`:2764`) are **proved** (no `sorry` in
    `UniversalK`).
  - `exists_effectiveMachineCode2` (`Codes2Tape:253`) and `exists_code2TM` (`:345`) are proved.
  - `Turing.universal_TlogT` (`UniversalTlogT.lean:57`) is proved from `two_work_tapes_run`.
- **A correction to the brief's framing.** The book-form chain does **not** go through `universal_TlogT`.
  Per U2 design Q1 (ruled as recommended), the simulator is the self-application U2-U at `k = 2`
  (`exists_selfUniversalK 2`), not the code-first U2-E plus `preTM`. Both depend on the same single
  admission, `two_work_tapes_run`. **The real prerequisite is therefore #211**, whose gate 102 round 2 is
  **HOLD 0/0/2** (`gates/102-g5-landing-fill/findings-r2.md`): the zero-time sweep in `Loop` and
  `Advice`, and NZ-1's four members. A round 3 is due.

### (b) To decide or design

- **Already ruled** (2026-10-14, "all as recommended"):
  - Q7: state both forms, with the book form under `∀ n, n ≤ f n` rather than `TimeConstructible f`;
  - Q8: the home is the end of `Diagonal.lean`, with Hydroxyi's file authorized;
  - Q10: the illustration `DTIME(n+1) ⊊ DTIME((n+1)²)` is **dropped**;
  - Q4: no U2-V;
  - the facade sentence is fixed in this PR (gate 24's ruling 4).
- **Carried.** Gate 24 asks for compiled sanity checks in this PR (`resolutions.md:58–62`):
  `¬ Nonempty (DiagSimulator (fun _ _ => 0))`, `¬ Nonempty (SelfSimulator (fun _ => 0))`, no
  `SelfSimulator` with a constant `decode`, and the `rfl` projections of `mono`/`toDiagSimulator`.
- **Re-route the probe's simulator.** The probe built `twoTapeSelfSimulator.W` from U2-V
  (`exists_selfVerdictTMK`), which was never landed. It must use
  `Classical.choose (exists_selfUniversalK 2 code₂.toK)`: the forward clause's `C*(t+1)` is at most
  `C*(t + |pairEncode α w| + 1)`, bridged by `EffectiveMachineCode2.toK_toFinTM`. This is a small
  re-proof; the design (§2.2) says U2-U implies the one-bit form.
- **The definitions rule** (policy §1, 2026-10-16) postdates the design. `logOverhead`, `logDiagOverhead`
  and `code₂` each need an `_eq` lemma, and `twoTapeSelfSimulator` needs projection lemmas (`_W`, `_decode`,
  `rfl`) like `sqDiagSimulator_W`.
- **Statement shape.** *Recommended:* write the headline hypotheses expanded, as `time_hierarchy` does,
  and keep `logDiagOverhead` only in the generic layer.
- **Open for the user:**
  - **T31-1, timing.** (A) Land after #211 merges, so the gate audits an admission-free result
    (*recommended*: its only admission would otherwise be `two_work_tapes_run`, and the replay chains
    from the merged snapshot). (B) Land now, with `sorryAx` through `two_work_tapes_run` until #211 merges.
  - **T31-2, `_of_pos`.** Add `time_hierarchy_book_of_pos`, `DTIME f ⊂ DTIME g` for positive `g` (the
    book's literal class)? *Recommended: yes*, mirroring `time_hierarchy_of_pos`. This is a new
    statement, beside Q7.
  - **T31-3, Theorem 1.9's literal code quantifier** (Q11) stays relaxed. `DTIME(n) ⊊ DTIME(n^1.5)` (Q10)
    stays in the backlog: it needs a time-constructibility witness for `n·⌊√n⌋`.

### (c) Next deliverable: the Part 2 PR plus a statement gate

**Edits to `TimeHierarchy/Diagonal.lean`.** New declarations in namespace `Complexity.TimeHierarchy`:
- `logOverhead`, `logOverhead_eq`, `logDiagOverhead`, `logDiagOverhead_eq`, `le_logDiagOverhead`,
  `logOverhead_add_le` and `logOverhead_mul_le` (with `log_mul_two_pow`, private unless Mathlib has it);
- `logDiagOverhead_le_book`;
- `code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2` and `code₂_eq`;
- `twoTapeSelfSimulator : SelfSimulator logOverhead`, with its `_W` and `_decode` projections.

The public statements, in namespace `Complexity`, beside `time_hierarchy`:

```lean
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hf : ∀ n, n ≤ f n) (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g          -- T31-2
```

- Proofs:
  - `time_hierarchy_log`: `(twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy le_logDiagOverhead hg hfg`;
  - `time_hierarchy_book`: from `time_hierarchy_log` with `logDiagOverhead_le_book` at `12 · A`;
  - `twoTapeSelfSimulator.normalForm`: `two_work_tapes_binary`, `exists_code2TM`, `MachineCode2.decode_encode`
    and `logOverhead_mul_le`.
- Existing declarations stay verbatim. Imports gain `TuringMachine.UniversalK`,
  `TuringMachine.Robustness.TwoTapes` (`Codes2Tape` comes through `UniversalK`) and `Mathlib.Data.Nat.Log`
  if it is not already reached.
- **The import graph** has no cycle: neither closure contains `Diagonal` (`UniversalK` has 57 modules,
  `TwoTapes` 24). `Diagonal`'s downstream is 13 modules, which inherit the two.
- **Docstrings:**
  - rewrite `Diagonal`'s "Divergences" section (`:67–98`) and its main results;
  - rewrite the facade `TimeHierarchy.lean:13–17`, "quadratic overhead in place of the book's `f log f`",
    to name `time_hierarchy_book`;
  - add no campaign labels (WORKFLOW §2).
- **The gate pack outline** follows gate 92 and gate 24:
  1. the statements against [AB09, Thm 3.1, pp. 69–70], including:
     - `f log f = o(g)` read as "for every `A`, eventually";
     - `hf : n ≤ f n` in place of `TimeConstructible f`;
     - `DTIME (g + 1)` together with `_of_pos`;
     - `Nat.log 2` and the case `f n ≤ 1`;
  2. the self-simulator's two clauses, and the absorption arithmetic;
  3. axioms: the standard three if after #211, else `sorryAx` only through `two_work_tapes_run`;
  4. rule 10, sealing `DTIME`, `TimeConstructible`, the `SelfSimulator`/`DiagSimulator` fields,
     `EffectiveCodeK.toFinTM`, `ComputesInTime` and the new definitions;
  5. the freeze: every existing public declaration of `Diagonal`, including `diagLang`'s body and
     `diag_cost_le`, is byte-identical;
  6. gate 24's carried sanity checks, as `example`s in an evidence probe;
  7. the screen against `oneTapeSelfSimulator` (an expected idiom pair; disclose it), names, and lint check 8;
  8. the replay: `Diagonal`'s downstream from the campaign snapshot;
  9. FYI to Hydroxyi, since the file is theirs.

### (d) Overlaps

- **#211:** the dependency, per T31-1.
- **The F6 harvest:** both touch `UniversalK`'s closure but not the same file. `UniversalK` gains rows and
  loses nothing public, so whichever merges second takes a merged-tree replay.
- **H's landing:** `Hierarchy` imports `Diagonal`, so its closure grows by `TwoTapes`; this is a replay
  consideration only.
- **RO-1 (parked):** it touches `TwoTapes`, not `Diagonal`. **#208, #212–#216:** none.

---

## Track 3 — Ladner's theorem ([AB09, Theorem 3.3]; P3.4)

### (a) Current state

- **Nothing is stated.** There is no `Ladner.lean` and no `SAT_H` (`git grep` finds only the records).
  The plan is `campaign/design/plans/AroraBarakChapters3-4Plan.md`:
  - §1:41: "Thm 3.3 Ladner, its Claim, and Ex 3.6(a)(b) — Missing — core-late (P3.4)";
  - §3:235: the home is `Diagonalization/Ladner.lean`;
  - §4:259: "`SAT_H`; Ex 3.6(a) (`H` in polynomial time); the Claim; Ex 3.6(b); Thm 3.3 — ~6";
  - §6:994: summit 4, "Ladner's `H` in polynomial time";
  - §7:1028: CH34-Q6, core-late.
- The backlog entry is `campaign/backlog.md:3756–3767`. It consumes the closed SAT surface and the
  `polyTimeComputable` layer, is independent of P3.3, and **was on hold** (user, 2026-10-09). It is now
  started (2026-11-06).
- **Existing surface, by exact name:**
  - `Complexity.SAT` (`ClassNP/SAT.lean:115`; the total decoder, so **every malformed string is in SAT**);
  - `SAT_mem_NP` (`:954`) and `SAT_NPComplete` (`CookLevin/Hardness.lean:8765`);
  - `P` (`ClassP/P.lean:57`, `⋃ c, DTIME (n^c + 1)`) and `NP` (`ClassNP/NP.lean:82`);
  - `PolyTimeComputable` (`ClassNP/PolyTime.lean:69`) and `.comp` (`:149`);
  - `PolyTimeReducible`, with scoped `≤ₚ` (`ClassNP/Reductions.lean:55/58`);
  - `NPHard`, `NPComplete` (`:124/128`), `mem_P_of_polyTimeReducible` (`:98`), `P_eq_NP_of_NPHard_mem_P`
    (`:136`) and `NPComplete.mem_P_iff` (`:146`);
  - `preimage_mem_P`, `inter_mem_P` and `preimage_mem_NP` (`ClassNP/PClosure.lean:71/91/215`);
  - `DTIME` (`ClassP/DTIME.lean:88`) and `TimeConstructible` (`ClassP/TimeConstructible.lean:74`);
  - the FP toolkit `polyTimeComputable_iterate`/`_guardLoop` (`ClassP/BinaryArith/Iterate.lean:160/190`);
  - **the uniform scheme** `Complexity.expCode : UniformMachineCode` (`Diagonalization/EXPCOM.lean:178`).
    Its jointly polynomial bounded-acceptance simulator is defined at `:105–125` and proved at `:156`.
  - `MachineCode.decode_encode_pad` (`Encoding.lean:656`, "every machine has infinitely many codes").
- **The precedent for "`H` polynomial-time":**
  `PolyTimeComputable (fun z => Nat.bits (lovaszPrime z.length))` (`ClassP/BinaryArith/PrimeFind.lean:443`).

### (b) To design (the statement phase's decisions; recommendations in italics)

- **LD-1, the enumeration `M_i`.**
  - The per-code constants of `Turing.universal`/`timed_universal` (an arbitrary `canonizerTime`) would
    make `H` non-polynomial.
  - *Use `M_i := (expCode.decode (Nat.bits i)).toFinTM`*: `expCode`'s simulator is uniform in the code.
  - Every machine has infinitely many indices: `encode M ++ true^(m+1)` ends in `true`, so it is a
    `Nat.bits i`. This is a fill lemma.
- **LD-2, the simulation predicate and the budget.**
  - *Use the acceptance reading: "for all `x` with `|x| ≤ log n`,
    `M_i.ComputesInTime x [true] (i * |x|^i) ↔ x ∈ SAT_H`"*. It matches the simulator's interface
    (`simulator_accepts`/`_rejects`) and `EXPCOM`'s "outputs 1" reading.
  - **A false-statement trap:** the book's literal "outputs `SAT_H(x)`" with the budget `i·|x|^i` gives a
    budget of 0 at `x = []`. No machine halts in 0 steps (`not_computesInTime_zero`), so `H(n) = log log n`
    for every `n`, and the Claim fails.
  - Under the acceptance reading `[] ∉ SAT_H`, so both sides are false and the trap disappears. The
    alternative is the budget `i·(|x|+1)^i`. The gate must check the edge cases `x = []`, `i = 0`, and
    `n < 16`, where `log log n ≤ 1`.
- **LD-3, the pad.** *The book's literal `ψ ++ false :: List.replicate (|ψ|^(H |ψ|)) true`, which splits
  uniquely at its last `false`.* The alternative is `pairEncode ψ (true^…)`, which would align with E-PAD's
  interface (REPORT:518) and the `pairFstD`/`pairSndD` FP lemmas; it is a declared deviation if chosen.
- **LD-4, logarithms.** *`Nat.log 2 (Nat.log 2 n)` and `Nat.log 2 n` (floors)*, as `Diagonal` uses `Nat.log 2`.
- **LD-5, the definition of `H`.** *Use strong recursion on `n` through a parametric
  `padSAT (h : ℕ → ℕ) : Language Bool`.*
  - Membership of strings of length `≤ log n < n` needs `h` only below `n`.
  - `ladnerH n := if ∃ i < log log n, Good i n then Nat.find … else log log n` (noncomputable, classical).
  - **Reading lemmas are proved at skeleton time** (workflow §2's allowed unfolding lemmas, flagged in
    the pack): `ladnerH_eq`, `padSAT_congr` (agreement below a length), `mem_padSAT_iff`, and
    `ladnerH_le` (`≤ log log n`).
- **LD-6, Ex 3.6(b)'s statement.** *General in `h`:* `PolyTimeComputable (bits ∘ h ∘ length)`, `h → ∞`,
  `NPHard (padSAT h) → SAT ∈ P`. `NPHard` is strictly stronger than the book's `NPComplete` hypothesis;
  this is a declared strengthening. The book's form is the alternative.
- **LD-7, the shape of Theorem 3.3.** *Both*:
  - `ladner : P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L` (the book's statement);
  - the witness form `SAT_H_intermediate : P ≠ NP → SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H`.
- **LD-8, source check (attribution, policy §2).** The plan's "Ex 3.6(a)(b)" collides with the library's
  "Example 3.6(1)–(3)" (the oracle claims, `ClassOracle/SATOracle.lean:15`). Before drafting docstrings,
  pin Theorem 3.3's Claim and Exercise 3.6's two parts against the book (pp. 71–72 and the chapter's
  exercises). My reading is that (a) is "`H` is polynomial-time computable" and (b) is "for polynomial-time
  `H → ∞`, `SAT_H` `NP`-complete ⇒ `SAT ∈ P`"; this is unverified.
- **LD-9, hosts** (workflow §2: a sketch names its hosts; an unregistered host is not ready). The sketch
  of Ex 3.6(a) needs two things:
  - (i) an FP-level call of `expCode.simulator` with a **poly-bounded** budget, since the simulator is
    polynomial in the *value* `t` and `t` is given in binary;
  - (ii) brute-force `SAT` on strings of length `≤ log n` in time `poly(n)`.
  - Survey both before the gate. If either is missing, it is a host statement item of this phase, like
    E-PAD. Candidates are `NP_subset_EXP` (`ClassNP/EXP.lean:2488`), `EXPCOM`'s internal calls and the FP
    toolkit.
- **LD-10, homes.**
  - *New `Diagonalization/Ladner.lean`*, namespace `Complexity` (auxiliaries under `Complexity.Ladner`
    or private).
  - Imports: `ClassNP.Reductions`, `ClassNP.PClosure`, `CookLevin.Hardness` (`SAT_NPComplete`; the
    statements do not need it, but the fill does), `Diagonalization.EXPCOM` (`expCode`) and
    `Mathlib.Data.Nat.Log`.
  - The facade `Diagonalization.lean` gains the import and a Contents line. Its docstring already carries
    one campaign label, "decision CH34-Q8" (`:22`), which belongs to the deferred docstring cleanup.

### (c) Next deliverable: the statement file and its gate

`Diagonalization/Ladner.lean`. Definitions with proved readings, then **six sorried statements** (the
plan's count is about 6):

```lean
def padSAT (h : ℕ → ℕ) : Language Bool :=
  {y | ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true}   -- LD-3
noncomputable def ladnerMachine (i : ℕ) : FinTM Bool := (expCode.decode (Nat.bits i)).toFinTM -- LD-1
noncomputable def ladnerH : ℕ → ℕ := …        -- LD-5; proved: ladnerH_eq, ladnerH_le, padSAT_congr
noncomputable def SAT_H : Language Bool := padSAT ladnerH          -- + SAT_H_eq (rfl)

theorem ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))  -- Ex 3.6(a)
theorem SAT_H_mem_NP : SAT_H ∈ NP
theorem ladnerH_bounded_of_mem_P : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C               -- Claim (1)
theorem ladnerH_unbounded_of_not_mem_P : SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n -- Claim (2)
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P        -- Ex 3.6(b), LD-6
theorem SAT_H_intermediate (h : P ≠ NP) : SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H -- Thm 3.3
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L                      -- Thm 3.3
```

Six statements are sorried. `ladner` is proved in one line from `SAT_H_intermediate`. An optional seventh
obligation is `SAT_reducible_padSAT_of_bounded` (`h` bounded and
polynomial-time ⇒ `SAT ≤ₚ padSAT h`), which `SAT_H_intermediate`'s sketch needs.

**The sketches name their obligations:**
- Ex 3.6(a): memoized `H` below `log n`, the bounded-acceptance calls (LD-9 (i)), brute-force SAT
  (LD-9 (ii)), and the arithmetic `i·(log n)^i ≤ n^{O(1)}` for `i < log log n`.
- Claim (1): a code of an `expCode` normal form of the `P`-decider, with an index above its time degree.
- Claim (2): each `M_i` fails at some `x_i`, otherwise `SAT_H ∈ P` via the uniform simulator; so `H(n) ≠ i`
  once `log n ≥ |x_i|`.
- Ex 3.6(b): the reduction's output shrinks `ψ` to `|ψ'| ≤ |ψ|^{1/2}` once `h > 2i`; recurse.
- Theorem 3.3: `SAT_NPComplete`, `NPComplete.mem_P_iff`, Claim (1) together with the bounded pad
  reduction, Claim (2) together with Ex 3.6(b).

**The gate pack outline** follows ch4-p43 (a statement-program phase) and gate 26:
1. the inventory, and the definitions verbatim;
2. the deviations declared: the LD-2 acceptance reading, the LD-1 uniform enumeration, `NPHard` for
   (b), and the total `SAT` decoder;
3. the brief:
   - faithfulness to [AB09, Thm 3.3 and proof];
   - the recursion's well-definedness;
   - the truth of each statement (the Claim's directions; argue (b) constructively);
   - the edge cases of LD-2;
   - non-vacuity checks (`padSAT` nonempty; `ladnerH_le`; `SAT_H ≠ ∅`);
   - the skeleton-time proofs, which are part of the audited surface;
4. hosts (LD-9) against the `machine-library-design.md` §14 registry;
5. axioms: `sorryAx` only in the six sorried statements (and through them in `ladner`), and the readings
   standard;
6. rule 10, the seal for the proved readings;
7. the freeze: no existing statement changes, and the facade wiring;
8. names, screen and lint check 8;
9. the elaboration and the replay: the new module, the facade and the root;
10. the open questions LD-1 to LD-8, for the user after the findings.

**The route note first.** Before the file, write a short design note at `campaign/items/ladner/LADNER-design.md`
with the LD-* decisions and a probe that elaborates the definitions and readings. Have the user rule the
LD-* decisions, then draft.

### (d) Overlaps

- **None blocking.** No open PR touches `Diagonalization/`, `ClassNP/{SAT,Reductions,PClosure}` or `EXPCOM`.
- **`lean/dedup-ro1`** touches `ClassNP/SAT.lean` (`satRed_one`, privates only), so Ladner's citations are
  unaffected.
- **NatBits** keeps the names of the `Nat.bits` lemmas.
- **E-PAD** (H's escalation) also designs padding. If its host lands as a general padding/validation row,
  Ladner may cite it (LD-3's `pairEncode` option). Coordinate the shape before either gate.

---

## (e) Rulings needed from the user

1. **D-F6-2, the harvest's homes:** in place in `UniversalK`, with the corollaries in `StepBlockForward`
   and `InputDevice`? *Recommended: yes.* D-F6-1 (harvest first) is to be confirmed.
2. **D-F6-3, F6's startup route:** the ruler host on the first header's suffix (new, *recommended*) or the
   retriage's buffered copy? This can be decided after the harvest's consumer probe.
3. **D-F6-4, the order in `Hierarchy.lean`:** after H's landing, F6's fill or E-PAD's continuation of
   `SPACE_linear_ne_NP` first? One fill per file.
4. **RO-1 against the harvest:** both edit `UniversalK` (`:2291` is inside a harvested private). *The harvest
   first.* RO-1's two parked questions (ledger RO-1) still stand.
5. **T31-1:** land the book-form PR after #211 merges, admission-free (*recommended*), or now with `sorryAx`?
   **T31-2:** add `time_hierarchy_book_of_pos`?
6. **Ladner's LD-1 to LD-7** (the enumeration, the acceptance reading and budget, the pad form, the
   recursion, (b)'s generality and `NPHard`, Theorem 3.3's shape), and **LD-8**, the source check of
   Exercise 3.6 against the book.
7. **The agents:** Codex for F6 (the retriage). The book-form PR is the maintainer's (about 150–220 lines;
   U2 design §6 item 7). Ladner's fill comes later and needs an agent.


## (f) The user's rulings (2026-11-06)

1. **D-F6-2:** the harvested rows go in a new `Build/` module, not in place in `UniversalK`. D-F6-1: the harvest comes first, before RO-1's `UniversalK` edits (option "RO-1 first" not taken).
2. **D-F6-3:** open; decide after the harvest's consumer probe.
3. **D-F6-4:** E-PAD's continuation of `SPACE_linear_ne_NP` first, then F6's fill.
4. **T31-1/T31-2:** after #211 merges, admission-free, with `time_hierarchy_book_of_pos`.
5. **Ladner:** LD-1 to LD-7 as recommended; LD-8 is the maintainer's source check before docstrings.

**LD-8 (the maintainer, 2026-11-06).** The book's text of Exercise 3.6 could not be fetched from this
session (network policy). Course notes (Princeton COS 522 hw6, Cornell CS 6810 lec. 3/4) confirm the
book's own pointer: "the definition of `H` implies an `O(n³)`-time recursive algorithm that computes
`H(n)` from `n` (see Exercise 3.6)". So `ladnerH_polyTime` is Exercise 3.6's first part. The second
part's wording is unpinned. Until it is pinned against the book, docstrings cite
[AB09, Theorem 3.3 and its proof] for the Claim and for `H → ∞`, and give no exercise part letter
beyond the `O(n³)` computation.

**E-PAD (the user, 2026-11-06):** the API fill publishes a **general** `mem_SPACE_pad` (any space
bound, a polynomial unary pad) in a **new `SpaceComplexity/Padding`** module. It is meant for later
reuse by Ladner's padding. `Hierarchy.lean` may import it, and the maintainer closes
`SPACE_linear_ne_NP` (`sph_linear_ne_NP_of_padding space_hierarchy <E-PAD>`) in a small PR with its
own gate, not through a fill. The fill is dispatched by pasted prompt (WORKFLOW §5).

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
  `Randomized/BPTIMEThreshold`'s `BPDecidesInTimeWith.one_le`; #217 re-points all five. **+1 (gate 108,
  minor 1):** `Randomized/ExpectedTime`'s `notHaltedProb_haltRun_zero` (the probability form);
  re-pointed in #217. Census: 8 sites (6 nondeterministic in 5 files, 2 deterministic).

**The search** (by kind, at `1dd510aa`): `rw`/`simp`/`change … at` forms with `runFrom_zero`,
`runWith_nil`, `initCfg`, `Cfg.init` or `init_state`; zero-case scans (`by_contra`,
`Nat.pos_of_ne_zero`, `eq_zero_or_pos`, `| zero`) near initial-configuration terms; `[] rfl` and
`[] (by …)` instantiations of halting hypotheses; literal time-0 `runFrom`/`ComputesInTime`/`HaltsWithin`;
`show`/`change`; and, after gate 108, probability and expected-time forms and `simp` closures without `at`. **Not members**, each a different fact: first-halt helpers from an arbitrary `cfg`
(`Loop:219`, `Catalog:6463`, `SAT:3797`, `Hardness:6176`); runs from non-initial configurations
ending in a state mismatch (`Hardness`, `NDCodeSimulator`, `NDNormalForm`, `StepBlockLoop`,
`Contract/Basic`, `Contract/Seam`, `NTimeDiagonalizer`); composite runs at positive times
(`UniversalK`, `NTimeHierarchy`, `Composition`, `Inclusions`); positive liveness facts
(`state = some q₀`); and other models (NARM's `narun`, `Yap`'s `badLang`, the oracle machines).
**Retired: #217 merged 2026-11-06 (`eb8cbf60`).**

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
**Partly published (the user, 2026-11-06):** the U2 harvest publishes it as `Turing.MultiTapeTM.initCfg_eq_mapState` in `Build/UniversalParts` (both of `UniversalK`'s uses now cite it). The other sites re-point to it in the dedup window, without a move to `Finite`.

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

**Widened (gate 105, 2026-11-06):** 181 containing declarations in 40 files (8 excluded as machine comparisons; scope `campaign/items/dedup/as1-SCOPE.md`); **the user ruled: all in #214.** That makes six members. None is a copy: the screen with `LogspaceUniformWalk` added gives
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
**+6 (gate 109, minor 1):** `SpaceComplexity/Hierarchy` (H's landing, #218): six `Cfg.ext` conversions over `Cfg.mapState` in four privates; re-pointed in #218 (`1a782c36`).

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
`mem_iff_reach` (probe only); all re-pointed (`f200144b`, `3d0f6ceb`). **Retired: #216 merged 2026-11-06 (`e4e7a419`).**

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

## ===== campaign/gates/112-u2-harvest-api/evidence/freeze/declfreeze-UniversalK.txt =====

public before/after: 12 12 private before/after: 67 41
public added: []
public removed: []
authorized body change: Turing.exists_selfUniversalK
authorized body change: Turing.universalK
private removed: ['Turing.uk_embed_init', 'Turing.uk_embed_suffix', 'Turing.uk_encode_halt', 'Turing.uk_encode_init_fields', 'Turing.uk_encode_init_tapes', 'Turing.uk_headerTM', 'Turing.uk_header_run', 'Turing.uk_init_mapState', 'Turing.uk_loopTM', 'Turing.uk_loop_converse', 'Turing.uk_loop_forward', 'Turing.uk_loop_init', 'Turing.uk_loop_live', 'Turing.uk_loop_pre_live', 'Turing.uk_loop_run', 'Turing.uk_loop_space', 'Turing.uk_ruler_fields', 'Turing.uk_scanCfg', 'Turing.uk_scanTM', 'Turing.uk_scan_header', 'Turing.uk_scan_pair', 'Turing.uk_scan_ruler', 'Turing.uk_scan_run', 'Turing.uk_scan_step', 'Turing.uk_scan_zero', 'Turing.uk_suffixCfg']
private added: []
private changed: ['Turing.uk_suffixStartupTM', 'Turing.uk_suffixStartup_run']

## ===== campaign/gates/112-u2-harvest-api/evidence/lint/campaign-TuringMachine-base.txt =====

WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  9 public def(s) without a lemma beside them (check 8): catalogTrace, inputMoveAction, mealyRun, scanCarry, scanFold, scanKeep, scanMap, scanShift, tapeAction
WARN  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1 public def(s) without a lemma beside them (check 8): roundStop
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            1 public def(s) without a lemma beside them (check 8): Contract.liftSymbols
WARN  TCSlib/Complexity/TuringMachine/Build/Convention.lean               4 public def(s) without a lemma beside them (check 8): solveSplit, solveSplitWith, splitAtLastTrue, unaryTokenSplit
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2 public def(s) without a lemma beside them (check 8): counterLoopDecExit, counterLoopRedirect
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1 public def(s) without a lemma beside them (check 8): Cfg.select
WARN  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            1 public def(s) without a lemma beside them (check 8): SafeRun
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1 public def(s) without a lemma beside them (check 8): RulerAt
WARN  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2 public def(s) without a lemma beside them (check 8): callEntry, callExit
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              11 public def(s) without a lemma beside them (check 8): FinNDTM.clockHost, aI, bootCfg, capPush, clockTr, emitTo, hostTM, runCfg, sI, tapeAfter, yI
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           1 public def(s) without a lemma beside them (check 8): ClockReady
WARN  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            6 public def(s) without a lemma beside them (check 8): AgreeShift, coinBranchAct, coinBranchAct, coinBranchCfg, coinBranchCfg, mapOutputCfg
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   3 public def(s) without a lemma beside them (check 8): GuessRunPhase.State, guessRunPhases, guessRunRed
WARN  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               1 public def(s) without a lemma beside them (check 8): answerAction
WARN  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              4 public def(s) without a lemma beside them (check 8): TableAt, TableWF, recordTemplate, tableFields
WARN  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                6 public def(s) without a lemma beside them (check 8): SeekPh, SkipPh, afterTag, recordFinTM, roundFinTM, succFieldCfg
WARN  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 4 public def(s) without a lemma beside them (check 8): captureAction, captureCfg, emitAction, emitCfg
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15398 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            2 public def(s) without a lemma beside them (check 8): zoneRowHi, zoneRowLo
WARN  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     5 public def(s) without a lemma beside them (check 8): codeScan, codeSkipTable2, codeSkipWork, oneTapeFormat, workPair
WARN  TCSlib/Complexity/TuringMachine/CodeParser.lean                     5 public def(s) without a lemma beside them (check 8): codeFallback, codeSkipAction, codeSkipFin, codeSkipPair, codeSkipState
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  3 public def(s) without a lemma beside them (check 8): MachineFormat.toFinTM, codeSkipTableK, oneTapeMachineFormat
WARN  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     1 public def(s) without a lemma beside them (check 8): Code2TM.toFinTM
WARN  TCSlib/Complexity/TuringMachine/CounterProg.lean                    5 public def(s) without a lemma beside them (check 8): act, ctl, init, toTM, tr
WARN  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               1 public def(s) without a lemma beside them (check 8): shiftInput
WARN  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 5 public def(s) without a lemma beside them (check 8): LinE.val, MOp.exec, bitsOps, linOps, tmplInstr
WARN  TCSlib/Complexity/TuringMachine/Encoding.lean                       2 public def(s) without a lemma beside them (check 8): CodeTM.serialize, actionBits
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodes.lean                        1 public def(s) without a lemma beside them (check 8): CodeNDTM.serialize
WARN  TCSlib/Complexity/TuringMachine/Oracle.lean                         4 public def(s) without a lemma beside them (check 8): Action.extend, initCfg, plainEmptyOracle, queryTapeIdx
WARN  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                1 public def(s) without a lemma beside them (check 8): queriesAlong
WARN  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   2 public def(s) without a lemma beside them (check 8): ComputesInTime, DecidesInTime
WARN  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         6 public def(s) without a lemma beside them (check 8): AcceptsWithin, DecidesInTime, FinOracleTM.toFinOracleNDTM, HaltsWithin, OracleNDTM.fixChoice, initCfg
WARN  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       1 public def(s) without a lemma beside them (check 8): NonnegativeHeads
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  7 public def(s) without a lemma beside them (check 8): blankPayload, clockTape, dataCell, laneCfg, obliviousDataInit, obliviousVisit, sourceWrittenPayload
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   5 public def(s) without a lemma beside them (check 8): Oblivious, clockBit, nextThird, oblAction, oblEmbed
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1 public def(s) without a lemma beside them (check 8): setupWrite
WARN  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     4 public def(s) without a lemma beside them (check 8): emitAction, leftAction, rightAction, virtualNextTag
WARN  TCSlib/Complexity/TuringMachine/Sweep.lean                          2 public def(s) without a lemma beside them (check 8): indexedVisit, sweepAct
WARN  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      1 public def(s) without a lemma beside them (check 8): wrT
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 1 public def(s) without a lemma beside them (check 8): universalBlockBound
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           14 public def(s) without a lemma beside them (check 8): universalActionBits, universalAdmin, universalEvalCfg, universalFour, universalInterpreter, universalNextOnes, universalRecordBits, universalRecordIndex, universalRecords, universalSign, universalSimulationCfg, universalSkipDone, universalStartupBound, universalWrite
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2873 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2 public def(s) without a lemma beside them (check 8): EffectiveCodeK.ofSerialize, EffectiveCodeK.toFinTM
WARN  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               3 public def(s) without a lemma beside them (check 8): universalCaptureCfg, universalCapturedCfg, universalInputPos
INFO  TCSlib/Complexity/TuringMachine/BufferWords.lean                    118 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines; 113 public / 392 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines; 24 public / 106 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines; 92 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean         562 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Counter.lean         134 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean           130 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            84 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines; 15 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract.lean                 62 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               252 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines; 59 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines; 32 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean                535 lines; 2 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines; 16 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputLength.lean              571 lines; 1 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputRewind.lean              201 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputWindow.lean              438 lines; 1 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines; 21 public / 183 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              598 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           393 lines; 23 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            379 lines; 24 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines; 56 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines; 13 public / 87 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines; 49 public / 236 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines; 29 public / 100 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Rewind.lean                   223 lines; 3 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines; 9 public / 15 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines; 26 public / 8 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines; 1 public / 35 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines; 64 public / 71 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean         565 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean            511 lines; 5 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines; 9 public / 33 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean             543 lines; 20 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines; 10 public / 25 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WordTests.lean                136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines; 14 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines; 87 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15398 lines; 25 public / 852 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean                 326 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean                 568 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CfgFacts.lean                       119 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceReplay.lean                   153 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceWords.lean                    118 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     595 lines; 47 public / 3 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     487 lines; 44 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines; 12 public / 196 private declarations
INFO  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     355 lines; 11 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines; 19 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  278 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 448 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  535 lines; 42 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines; 55 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         485 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines; 21 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines; 3 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodes.lean                        277 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               661 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               661 lines; 29 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean          194 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines; 42 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                375 lines; 9 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   149 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         408 lines; 25 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines; 3 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines; 4 public / 96 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines; 2 public / 102 private declarations
INFO  TCSlib/Complexity/TuringMachine/SelfUniversal.lean                  159 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines; 62 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  230 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/SymbolLift.lean                     478 lines; 32 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2873 lines; 12 public / 67 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines; 16 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalTlogT.lean                 84 lines; 1 public / 0 private declarations

style_lint: 0 FAIL, 72 WARN over 92 files

## ===== campaign/gates/112-u2-harvest-api/evidence/lint/campaign-TuringMachine-head.txt =====

WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  9 public def(s) without a lemma beside them (check 8): catalogTrace, inputMoveAction, mealyRun, scanCarry, scanFold, scanKeep, scanMap, scanShift, tapeAction
WARN  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1 public def(s) without a lemma beside them (check 8): roundStop
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            1 public def(s) without a lemma beside them (check 8): Contract.liftSymbols
WARN  TCSlib/Complexity/TuringMachine/Build/Convention.lean               4 public def(s) without a lemma beside them (check 8): solveSplit, solveSplitWith, splitAtLastTrue, unaryTokenSplit
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2 public def(s) without a lemma beside them (check 8): counterLoopDecExit, counterLoopRedirect
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1 public def(s) without a lemma beside them (check 8): Cfg.select
WARN  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            1 public def(s) without a lemma beside them (check 8): SafeRun
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1 public def(s) without a lemma beside them (check 8): RulerAt
WARN  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2 public def(s) without a lemma beside them (check 8): callEntry, callExit
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              11 public def(s) without a lemma beside them (check 8): FinNDTM.clockHost, aI, bootCfg, capPush, clockTr, emitTo, hostTM, runCfg, sI, tapeAfter, yI
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           1 public def(s) without a lemma beside them (check 8): ClockReady
WARN  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            6 public def(s) without a lemma beside them (check 8): AgreeShift, coinBranchAct, coinBranchAct, coinBranchCfg, coinBranchCfg, mapOutputCfg
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   3 public def(s) without a lemma beside them (check 8): GuessRunPhase.State, guessRunPhases, guessRunRed
WARN  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               1 public def(s) without a lemma beside them (check 8): answerAction
WARN  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              4 public def(s) without a lemma beside them (check 8): TableAt, TableWF, recordTemplate, tableFields
WARN  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                6 public def(s) without a lemma beside them (check 8): SeekPh, SkipPh, afterTag, recordFinTM, roundFinTM, succFieldCfg
WARN  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 4 public def(s) without a lemma beside them (check 8): captureAction, captureCfg, emitAction, emitCfg
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15398 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            2 public def(s) without a lemma beside them (check 8): zoneRowHi, zoneRowLo
WARN  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     5 public def(s) without a lemma beside them (check 8): codeScan, codeSkipTable2, codeSkipWork, oneTapeFormat, workPair
WARN  TCSlib/Complexity/TuringMachine/CodeParser.lean                     5 public def(s) without a lemma beside them (check 8): codeFallback, codeSkipAction, codeSkipFin, codeSkipPair, codeSkipState
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  3 public def(s) without a lemma beside them (check 8): MachineFormat.toFinTM, codeSkipTableK, oneTapeMachineFormat
WARN  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     1 public def(s) without a lemma beside them (check 8): Code2TM.toFinTM
WARN  TCSlib/Complexity/TuringMachine/CounterProg.lean                    5 public def(s) without a lemma beside them (check 8): act, ctl, init, toTM, tr
WARN  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               1 public def(s) without a lemma beside them (check 8): shiftInput
WARN  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 5 public def(s) without a lemma beside them (check 8): LinE.val, MOp.exec, bitsOps, linOps, tmplInstr
WARN  TCSlib/Complexity/TuringMachine/Encoding.lean                       2 public def(s) without a lemma beside them (check 8): CodeTM.serialize, actionBits
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodes.lean                        1 public def(s) without a lemma beside them (check 8): CodeNDTM.serialize
WARN  TCSlib/Complexity/TuringMachine/Oracle.lean                         4 public def(s) without a lemma beside them (check 8): Action.extend, initCfg, plainEmptyOracle, queryTapeIdx
WARN  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                1 public def(s) without a lemma beside them (check 8): queriesAlong
WARN  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   2 public def(s) without a lemma beside them (check 8): ComputesInTime, DecidesInTime
WARN  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         6 public def(s) without a lemma beside them (check 8): AcceptsWithin, DecidesInTime, FinOracleTM.toFinOracleNDTM, HaltsWithin, OracleNDTM.fixChoice, initCfg
WARN  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       1 public def(s) without a lemma beside them (check 8): NonnegativeHeads
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  7 public def(s) without a lemma beside them (check 8): blankPayload, clockTape, dataCell, laneCfg, obliviousDataInit, obliviousVisit, sourceWrittenPayload
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   5 public def(s) without a lemma beside them (check 8): Oblivious, clockBit, nextThird, oblAction, oblEmbed
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1 public def(s) without a lemma beside them (check 8): setupWrite
WARN  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     4 public def(s) without a lemma beside them (check 8): emitAction, leftAction, rightAction, virtualNextTag
WARN  TCSlib/Complexity/TuringMachine/Sweep.lean                          2 public def(s) without a lemma beside them (check 8): indexedVisit, sweepAct
WARN  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      1 public def(s) without a lemma beside them (check 8): wrT
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 1 public def(s) without a lemma beside them (check 8): universalBlockBound
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           14 public def(s) without a lemma beside them (check 8): universalActionBits, universalAdmin, universalEvalCfg, universalFour, universalInterpreter, universalNextOnes, universalRecordBits, universalRecordIndex, universalRecords, universalSign, universalSimulationCfg, universalSkipDone, universalStartupBound, universalWrite
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2 public def(s) without a lemma beside them (check 8): EffectiveCodeK.ofSerialize, EffectiveCodeK.toFinTM
WARN  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               3 public def(s) without a lemma beside them (check 8): universalCaptureCfg, universalCapturedCfg, universalInputPos
INFO  TCSlib/Complexity/TuringMachine/BufferWords.lean                    118 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines; 113 public / 392 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines; 24 public / 106 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines; 92 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean         562 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Counter.lean         134 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean           130 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            84 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines; 15 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract.lean                 62 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               252 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines; 59 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines; 32 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean                535 lines; 2 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines; 16 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputLength.lean              571 lines; 1 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputRewind.lean              201 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputWindow.lean              438 lines; 1 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines; 21 public / 183 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              598 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           393 lines; 23 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            379 lines; 24 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines; 56 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines; 13 public / 87 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines; 49 public / 236 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines; 29 public / 100 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Rewind.lean                   223 lines; 3 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines; 9 public / 15 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines; 26 public / 8 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines; 1 public / 35 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines; 64 public / 71 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean         565 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean            511 lines; 5 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines; 9 public / 33 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean           976 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean           976 lines; 22 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean             543 lines; 20 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines; 10 public / 25 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WordTests.lean                136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines; 14 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines; 87 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15398 lines; 25 public / 852 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean                 326 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean                 568 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CfgFacts.lean                       119 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceReplay.lean                   153 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceWords.lean                    118 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     595 lines; 47 public / 3 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     487 lines; 44 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines; 12 public / 196 private declarations
INFO  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     355 lines; 11 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines; 19 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  278 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 448 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  535 lines; 42 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines; 55 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         485 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines; 21 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines; 3 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodes.lean                        277 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               661 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               661 lines; 29 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean          194 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines; 42 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                375 lines; 9 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   149 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         408 lines; 25 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines; 3 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines; 4 public / 96 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines; 2 public / 102 private declarations
INFO  TCSlib/Complexity/TuringMachine/SelfUniversal.lean                  159 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines; 62 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  230 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/SymbolLift.lean                     478 lines; 32 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2127 lines; 12 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines; 16 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalTlogT.lean                 84 lines; 1 public / 0 private declarations

style_lint: 0 FAIL, 72 WARN over 93 files

## ===== campaign/gates/112-u2-harvest-api/evidence/lint/policy-base.txt =====


1 findings in 1 files
TCSlib/Complexity/TuringMachine/UniversalK.lean: 2874 lines (> 1000, must split)

## ===== campaign/gates/112-u2-harvest-api/evidence/lint/policy-head.txt =====


1 findings in 2 files
TCSlib/Complexity/TuringMachine/UniversalK.lean: 2128 lines (> 1000, must split)


## ===== campaign/gates/112-u2-harvest-api/evidence/merged-tree/down-lhv2.txt =====

TCSlib/Complexity/TuringMachine/Build/UniversalParts
TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/SelfUniversal
TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity
TCSlib/Complexity/TuringMachine/UniversalTlogT
TCSlib/Complexity/TuringMachine

## ===== campaign/gates/112-u2-harvest-api/evidence/merged-tree/replay-lhv2-static.txt =====

modules 7, mismatches 0, static total 2

## ===== campaign/gates/112-u2-harvest-api/evidence/merged-tree/replay-lhv2.log =====

# replay-lhv2 at 51843dd2: #221, the U2 harvest, on the campaign after #218/#219 (7 modules), fresh .oleans into oleans-lhv2
TCSlib/Complexity/TuringMachine/Build/UniversalParts exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalK exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/SelfUniversal exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Hierarchy exit=0 errors=0 sorry=2
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalTlogT exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine exit=0 errors=0 sorry=0
# modules=7 failed=0

## ===== campaign/gates/112-u2-harvest-api/evidence/merged-tree/replay-lhv2.sh =====

#!/usr/bin/env bash
# Replay lhv2 (#221, the U2 harvest, on the campaign after #218/#219; branch lean/u2-harvest-api, stacked on the campaign after #218, #219 (oleans-lcamp6)): its downstream closure (7 modules),
# fresh .oleans into oleans-lhv2, a copy of oleans-lcamp6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-harvest"
LIST="/home/user/tcslib-scratch/fills/replay/down-lhv2.txt"
LOG="$S/fills/replay/replay-lhv2.log"
PINS="TCSlib/Complexity/TuringMachine.lean:42807f2d086a8834071ad5e6613bc225192caaa6
TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean:dcd5d51988449537f5dfa22bfe9b346d209df669
TCSlib/Complexity/TuringMachine/UniversalK.lean:4c94bbe6651470bfd241f16f77c90d9171c5ecd3"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/u2-harvest-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 7a66896024c86de6399955a399faf501e04ac2f1 HEAD || { echo "precheck: the head must contain the campaign after #218, #219 (oleans-lcamp6); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 7a66896024c86de6399955a399faf501e04ac2f1 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #218, #219 (oleans-lcamp6) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp6.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "7" ] || { echo "precheck: the replay list must have 7 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lhv2" ] && { echo "precheck: $S/oleans-lhv2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp6" ] || { echo "precheck: oleans-lcamp6 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp6" "$S/oleans-lhv2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lhv2 at $(git rev-parse --short HEAD): #221, the U2 harvest, on the campaign after #218/#219 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lhv2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lhv2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/Ax.lean.txt =====

import TCSlib.Complexity.TuringMachine.Build.UniversalParts
import TCSlib.Complexity.TuringMachine.UniversalK
#print axioms Turing.MultiTapeTM.initCfg_eq_mapState
#print axioms Turing.StepBlock.forwardLoopCfg_init_workTapes
#print axioms Turing.StepBlock.forwardLoopCfg_init_fields
#print axioms Turing.StepBlock.forwardLoopCfg_halt_iff
#print axioms Turing.embedEmitCfg_forwardLoop_init
#print axioms Turing.StepBlock.forwardLoop_forward
#print axioms Turing.StepBlock.forwardLoop_live
#print axioms Turing.StepBlock.forwardLoop_converse
#print axioms Turing.startupLoopTM
#print axioms Turing.startupLoopTM_initCfg
#print axioms Turing.startupLoopTM_live_of_le
#print axioms Turing.startupLoopTM_runFrom
#print axioms Turing.startupLoopTM_spaceUsed_le
#print axioms Turing.headerScanTM
#print axioms Turing.headerScanCfg
#print axioms Turing.headerScanCfg_state
#print axioms Turing.headerScanCfg_inputPos
#print axioms Turing.headerScanCfg_workTapes
#print axioms Turing.headerScanCfg_workTapePos
#print axioms Turing.headerScanCfg_output
#print axioms Turing.headerScanTM_run
#print axioms Turing.headerScanCfg_ruler
#print axioms Turing.headerRulerTM
#print axioms Turing.headerRulerTM_run
#print axioms Turing.suffixRulerCfg
#print axioms Turing.suffixRulerCfg_state
#print axioms Turing.suffixRulerCfg_inputPos
#print axioms Turing.suffixRulerCfg_workTapes
#print axioms Turing.suffixRulerCfg_workTapePos
#print axioms Turing.suffixRulerCfg_output
#print axioms Turing.rulerHostCfg_fields
#print axioms Turing.suffixRulerCfg_embed
#print axioms Turing.universalK
#print axioms Turing.exists_selfUniversalK
#check @Turing.headerScanCfg_state
#check @Turing.headerScanCfg_inputPos
#check @Turing.headerScanCfg_workTapes
#check @Turing.headerScanCfg_workTapePos
#check @Turing.headerScanCfg_output
#check @Turing.suffixRulerCfg_state
#check @Turing.suffixRulerCfg_inputPos
#check @Turing.suffixRulerCfg_workTapes
#check @Turing.suffixRulerCfg_workTapePos
#check @Turing.suffixRulerCfg_output

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/Ax.out =====

'Turing.MultiTapeTM.initCfg_eq_mapState' depends on axioms: [propext, Quot.sound]
'Turing.StepBlock.forwardLoopCfg_init_workTapes' depends on axioms: [propext, Quot.sound]
'Turing.StepBlock.forwardLoopCfg_init_fields' depends on axioms: [propext, Quot.sound]
'Turing.StepBlock.forwardLoopCfg_halt_iff' depends on axioms: [propext, Quot.sound]
'Turing.embedEmitCfg_forwardLoop_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.StepBlock.forwardLoop_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.StepBlock.forwardLoop_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.StepBlock.forwardLoop_converse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.startupLoopTM' depends on axioms: [propext, Quot.sound]
'Turing.startupLoopTM_initCfg' depends on axioms: [propext, Quot.sound]
'Turing.startupLoopTM_live_of_le' depends on axioms: [propext, Quot.sound]
'Turing.startupLoopTM_runFrom' depends on axioms: [propext, Quot.sound]
'Turing.startupLoopTM_spaceUsed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.headerScanTM' depends on axioms: [propext]
'Turing.headerScanCfg' does not depend on any axioms
'Turing.headerScanCfg_state' does not depend on any axioms
'Turing.headerScanCfg_inputPos' does not depend on any axioms
'Turing.headerScanCfg_workTapes' does not depend on any axioms
'Turing.headerScanCfg_workTapePos' does not depend on any axioms
'Turing.headerScanCfg_output' does not depend on any axioms
'Turing.headerScanTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.headerScanCfg_ruler' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.headerRulerTM' depends on axioms: [propext]
'Turing.headerRulerTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.suffixRulerCfg' depends on axioms: [propext]
'Turing.suffixRulerCfg_state' depends on axioms: [propext]
'Turing.suffixRulerCfg_inputPos' depends on axioms: [propext]
'Turing.suffixRulerCfg_workTapes' depends on axioms: [propext]
'Turing.suffixRulerCfg_workTapePos' depends on axioms: [propext]
'Turing.suffixRulerCfg_output' depends on axioms: [propext]
'Turing.rulerHostCfg_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.suffixRulerCfg_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universalK' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_selfUniversalK' depends on axioms: [propext, Classical.choice, Quot.sound]
@Turing.headerScanCfg_state : ∀ {k : ℕ} {z : List Bool} (i : Fin k) (d : Turing.Cfg k Bool (Fin 4) z) (q : Fin 4)
  (t : ℕ) (ht : ↑d.inputPos + t < z.length + 2), (Turing.headerScanCfg i d q t ht).state = some q
@Turing.headerScanCfg_inputPos : ∀ {k : ℕ} {z : List Bool} (i : Fin k) (d : Turing.Cfg k Bool (Fin 4) z) (q : Fin 4)
  (t : ℕ) (ht : ↑d.inputPos + t < z.length + 2), (Turing.headerScanCfg i d q t ht).inputPos = ⟨↑d.inputPos + t, ht⟩
@Turing.headerScanCfg_workTapes : ∀ {k : ℕ} {z : List Bool} (i : Fin k) (d : Turing.Cfg k Bool (Fin 4) z) (q : Fin 4)
  (t : ℕ) (ht : ↑d.inputPos + t < z.length + 2) (a : Fin k) (a_1 : ℤ),
  (Turing.headerScanCfg i d q t ht).workTapes a a_1 =
    Function.update d.workTapes i
      (fun a => if d.workTapePos i ≤ a ∧ a < d.workTapePos i + ↑t then some true else d.workTapes i a) a a_1
@Turing.headerScanCfg_workTapePos : ∀ {k : ℕ} {z : List Bool} (i : Fin k) (d : Turing.Cfg k Bool (Fin 4) z) (q : Fin 4)
  (t : ℕ) (ht : ↑d.inputPos + t < z.length + 2) (a : Fin k),
  (Turing.headerScanCfg i d q t ht).workTapePos a = Function.update d.workTapePos i (d.workTapePos i + ↑t) a
@Turing.headerScanCfg_output : ∀ {k : ℕ} {z : List Bool} (i : Fin k) (d : Turing.Cfg k Bool (Fin 4) z) (q : Fin 4)
  (t : ℕ) (ht : ↑d.inputPos + t < z.length + 2), (Turing.headerScanCfg i d q t ht).output = d.output
@Turing.suffixRulerCfg_state : ∀ {k K n : ℕ} {P : Type} (q : P) (M : Turing.MultiTapeTM k Bool (Fin (n + 1)))
  (z : List Bool) (ℓ : ℕ) (hℓ : ℓ + 1 < z.length + 2), (Turing.suffixRulerCfg q M z ℓ hℓ).state = some q
@Turing.suffixRulerCfg_inputPos : ∀ {k K n : ℕ} {P : Type} (q : P) (M : Turing.MultiTapeTM k Bool (Fin (n + 1)))
  (z : List Bool) (ℓ : ℕ) (hℓ : ℓ + 1 < z.length + 2), (Turing.suffixRulerCfg q M z ℓ hℓ).inputPos = ⟨ℓ + 1, hℓ⟩
@Turing.suffixRulerCfg_workTapes : ∀ {k K n : ℕ} {P : Type} (q : P) (M : Turing.MultiTapeTM k Bool (Fin (n + 1)))
  (z : List Bool) (ℓ : ℕ) (hℓ : ℓ + 1 < z.length + 2) (j : Fin (K + (k + 3))) (a : ℤ),
  (Turing.suffixRulerCfg q M z ℓ hℓ).workTapes j a =
    (if ↑j = k then Turing.FinTM.bufferTape (Turing.tableBitsK M.tr)
      else
        if ↑j = k + 1 then fun a => Turing.FinTM.bufferTape (Turing.unaryFin M.q₀) (a - 2)
        else if ↑j = k + 2 then Turing.FinTM.bufferTape (List.replicate ℓ true) else fun x => none)
      a
@Turing.suffixRulerCfg_workTapePos : ∀ {k K n : ℕ} {P : Type} (q : P) (M : Turing.MultiTapeTM k Bool (Fin (n + 1)))
  (z : List Bool) (ℓ : ℕ) (hℓ : ℓ + 1 < z.length + 2) (x : Fin (K + (k + 3))),
  (Turing.suffixRulerCfg q M z ℓ hℓ).workTapePos x = 0
@Turing.suffixRulerCfg_output : ∀ {k K n : ℕ} {P : Type} (q : P) (M : Turing.MultiTapeTM k Bool (Fin (n + 1)))
  (z : List Bool) (ℓ : ℕ) (hℓ : ℓ + 1 < z.length + 2), (Turing.suffixRulerCfg q M z ℓ hℓ).output = []
exit=0 3s

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/DESIGN.md =====

# U2 harvest API (`lean/u2-harvest-api`): design

Base: `origin/complexity/arora-barak-ch3-4` at `205bbdbe` (Lean tree equal to `a28b8c42`, the
`oleans-lcamp2` replay's tree). Source: `TCSlib/Complexity/TuringMachine/UniversalK.lean`
(2,873 lines). Ruling (user, 2026-11-06): the harvested rows go in a **new `Build/` module**;
`UniversalK` imports it; `universalK`'s and `exists_selfUniversalK`'s statements are
byte-identical.

## 1. The module

**`TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean`**, namespace `Turing` (the forwarding
loop's rows under `Turing.StepBlock`, beside H2-F's names), private prefix `up_`.

*Why this name.* The module holds the four groups of parts the `k`-generic universal machines are
assembled from: the header ruler (a scan of a doubled header writing one ruler cell per input cell,
then the rewind), the startup–loop seam with its time and space readings, the forwarding loop's
corollaries at an initial configuration, and the suffix-ruler layout that joins the first three to
the ruler host. `HeaderScan` would name only the first group; the four have one purpose (the
universal machines U2-U, U2-E and next F6's `SU`). The name follows the directory's
noun-phrase style and parallels `Build/InterpreterStartup` ("the pieces of a universal machine's
startup").

*Imports (minimum, computed from header imports).* Three `TCSlib` modules, none in another's
closure, none reaching `UniversalK`, plus one Mathlib module found at elaboration
(`Mathlib.Algebra.Group.Action.Defs`, for `smul_eq_mul` in the `Finset.sum_const` steps;
`UniversalK` had it through `Codes2Tape`/`Clean`):
- `Build.StepBlockForward` — `StepBlock.forwardLoopCfg` and its field equations, `Lockstep`
  (`Contract/Basic`), `summaryCells_eq`, `tableBitsK`, and in its closure `Seam`, `Embed`,
  `Catalog` (`tapeAction`, `inputMoveAction`, `step_of_tapeAction_write`), `Encoding`
  (`pairEncode`, `length_pairEncode`, `unaryFin`), `Simulation` (`FinTM.bufferTape`), `Finite`;
- `Build.InputDevice` — `rulerHostCfg` and its field equations;
- `Build.Rewind` — `rewindTM`, `RewindPhase`, `rewindTM_run_ofCfg`.

`UniversalK` keeps its seven imports and gains `Build.UniversalParts` (no cycle: the new module's
closure is 20 + 19 + 15 modules of the `Build` layer, without `UniversalK`, `UniversalStartup`'s
consumers or `Codes2Tape`). Size: 976 lines (target band 150–600 is exceeded; under 1000;
reported, not split, because the four groups cite one another: the suffix layout's embedding
lemma reads the forwarding rows, the space ledger reads the seam rows).

## 2. The rows (each: final statement, source, what moves with it)

Notation: `σ := Fin.castLEEmb (_ : k + 2 ≤ K + (k + 2))`; `blank₀ := embedEmitCfg σ (fun _ _ =>
none) (fun _ => 0) []`.

### 2a. The restart identity (RS-1) — see §5 Q1
- **`Turing.MultiTapeTM.initCfg_eq_mapState`** ← `uk_init_mapState` (private, :1816). Statement
  unchanged: `B.q₀ = f A.q₀ → B.initCfg x = (A.initCfg x).mapState f` (binary alphabet). Needed by
  `startupLoopTM_initCfg` (new module) **and** by `uk_suffixStartup_run` (stays in `UniversalK`).

### 2b. The forwarding loop at an initial configuration (`Turing.StepBlock`)
- **`StepBlock.forwardLoopCfg_init_workTapes`** ← `uk_encode_init_tapes` (:1697). Unchanged.
- **`StepBlock.forwardLoopCfg_init_fields`** ← `uk_encode_init_fields` (:1736). Unchanged.
- **`StepBlock.forwardLoopCfg_halt_iff`** ← `uk_encode_halt` (:1752). Unchanged (an iff and the
  output equation, as a conjunction).
- **`Turing.embedEmitCfg_forwardLoop_init`** ← `uk_embed_init` (:1766). Unchanged: `blank₀
  (forwardLoopCfg entry M (M.initCfg x))` is the startup's native endpoint layout relabelled at
  `entry`.
- **`StepBlock.forwardLoop_forward`**, **`_live`**, **`_converse`** ← `uk_loop_forward` (:1871),
  `uk_loop_live` (:1896), `uk_loop_converse` (:1918). Unchanged; generic in `M`, `L`, `cost`.

### 2c. The startup–loop seam
- **`Turing.startupLoopTM R exit L entry`** ← `uk_loopTM` (:1807), a machine: `{ seamCompTM R exit
  (embedEmitTM σ L) entry with q₀ := Sum.inl R.q₀ }`. Read through its run lemmas (policy §1).
- **`startupLoopTM_initCfg`** ← `uk_loop_init` (:1827); **`startupLoopTM_live_of_le`** ←
  `uk_loop_pre_live` (:1834); **`startupLoopTM_runFrom`** ← `uk_loop_run` (:1850). Unchanged.
- **`startupLoopTM_spaceUsed_le`** ← `uk_loop_space` (:1954), **generalized** (plan §F6(c)):
  ```
  (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
  (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
  (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
  (hcfg : d.mapState (fun _ => entry) = blank₀ c)
  (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
  (hloop : ∀ i, L.spaceUsedByTape c t i ≤ S) :
  (startupLoopTM R exit L entry).spaceUsed (…initCfg x) (T + 1 + t) ≤ B + (K + (k + 2)) * S
  ```
  i.e. for **any seam endpoint** `d` and loop start `c`, exactly `startupLoopTM_runFrom`'s seam
  hypotheses. *Argument:* the old proof read the fixed endpoint only through `uk_embed_init`
  (its `he : d.mapState (fun _ => entry) = e`) and through `d.state = some exit` (`rfl`); both are
  now hypotheses, and `M` disappears. At `d :=` the native layout and `c := forwardLoopCfg entry M
  (M.initCfg x)`, `hexit` is `rfl` and `hcfg` is `embedEmitCfg_forwardLoop_init`, which is the old
  statement. At `(K, k + 1)` with `d := suffixRulerCfg …` and `c := rulerHostCfg …` it is the
  suffix layout F6 needs.

### 2d. The header scan and the header ruler
- **`Turing.headerScanTM i`** ← `uk_scanTM` (:2161). A machine, read through `headerScanTM_run`.
- **`Turing.headerScanCfg i d q t ht`** ← `uk_scanCfg` (:2170), with
  `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]`:
  `headerScanCfg_state`, `_inputPos`, `_workTapes` (pointwise), `_workTapePos`, `_output`.
- **`headerScanTM_run`** ← `uk_scan_run` (:2370). Unchanged (any input offset `1 + p` with
  `z.drop p = pairEncode u v`, any ruler head): the endpoint `headerScanCfg i d 3 (2|u|+2)`, the
  first-return cut and silence.
- **`headerScanCfg_ruler`** ← `uk_scan_ruler` (:2397), **generalized** to an existing ruler prefix:
  ```
  (m : ℕ) (hpre : ∀ a : ℤ, d.workTapes i (d.workTapePos i - m + a) =
      FinTM.bufferTape (List.replicate m true) a) :
  ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i - m + a) =
      FinTM.bufferTape (List.replicate (m + t) true) a
  ```
  *Argument:* `hpre` says the tape is exactly `true^m` ending just before the head (blank
  elsewhere). The scan marks `[pos, pos + t)` and keeps every other cell, so the tape becomes
  `true^(m + t)` from the same start. At `m = 0`, `hpre` is equivalent to the old `hblank`
  (`bufferTape [] = none`) and the conclusion is the old one up to `Nat.cast_zero`, `sub_zero`,
  `zero_add` (the private corollary `up_scan_ruler_blank` restates it, used by
  `headerRulerTM_run`). Two scans compose: after the first, the head is at `pos + ℓ₁` and
  `(pos + ℓ₁) - ℓ₁ = pos`, so the second scan's `hpre` at `m = ℓ₁` is the first's conclusion,
  giving `true^(ℓ₁ + ℓ₂)` (checked in the probe).
- **`Turing.headerRulerTM i`** + **`headerRulerTM_run`** ← `uk_headerTM` (:2414), `uk_header_run`
  (:2424). Unchanged (scan from a blank ruler tape, then the rewind).
- Moving with them, renamed: `uk_scan_zero/step/pair/header` → private `up_scan_zero`,
  `up_scan_step`, `up_scan_pair`, `up_scan_header`; new private `up_scan_ruler_blank` (the
  `m = 0` corollary, derived, not a copy).

### 2e. The suffix-ruler layout
- **`Turing.suffixRulerCfg q M z ℓ hℓ`** ← `uk_suffixCfg` (:2504), generic in `z`, `ℓ`, with
  `simps` field equations (`suffixRulerCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
  `_output`, no `simp` attribute).
- **`Turing.rulerHostCfg_fields`** ← `uk_ruler_fields` (:2651). Unchanged.
- **`Turing.suffixRulerCfg_embed`** ← `uk_embed_suffix` (:2672). Unchanged.

None of the plan's rows has to sit beside its host's definition: the corollaries of
`forwardLoopCfg` and `rulerHostCfg` read them only through their published `simps` equations
(and `summaryCells_eq`), so they all go in the new module, as the ruling asks.

## 3. Rule-10 cases (a proof unfolding a definition that is now in another file)

Moved code: its own definitions move with it (`headerScanTM`, `headerScanCfg`, `headerRulerTM`,
`startupLoopTM`, `suffixRulerCfg`), so its unfoldings of them stay own-file; it reads no definition
that stays in `UniversalK`; its reading of other files' definitions is unchanged by the move.

`UniversalK`'s remaining proofs are now consumers of the moved definitions:
1. **`uk_suffixStartup_run`, step `final`** unfolds `uk_suffixCfg` five times: `rfl` on `.state`,
   `change c.inputPos.val + ℓ = ℓ + 1` on `.inputPos`, `simp only [… uk_suffixCfg …]` on
   `.workTapes` (both branches), `rfl` on `.workTapePos` and `.output`. **Fix:** rewrite with
   `suffixRulerCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`.
2. `uk_suffixStartupTM` mentions `uk_headerTM` only as a machine argument; `uk_suffixStartup_run`
   reads it through `uk_header_run` only. No unfolding (re-pointed by name).
3. `exists_selfUniversalK`, `universalK`: `uk_loopTM` only as `tm := …` and through the run,
   live and space lemmas; `U.tm` reduces the local structure, not `startupLoopTM`. No unfolding.
4. **`universalK`'s body** (found by the seal probe, missed by reading): `uRun` passed `rfl` for
   `(uk_suffixCfg …).state = some finish`, and `hprefix` closed `(uk_suffixCfg …).state ≠ none`
   by `Option.some_ne_none` through the definition. **Fix:** `suffixRulerCfg_state` in both.
   A body change of `universalK`, statement unchanged.
Verification (done): a seal probe — `UniversalK` with the five moved definitions `[local irreducible]`
(controls: an `rfl` per definition failing sealed, closing unsealed) — and the new module with the
other-file definitions it reads sealed.

## 4. What stays in `UniversalK`

Lines 1–1688 unchanged (`EffectiveCodeK`, the instances, the `ss_*` startup kit,
`exists_selfStartupTMK`) apart from the import and the module docstring; `exists_selfUniversalK`
(body re-pointed); `uk_suffixStartupTM` and `uk_suffixStartup_run` (private, U2-E's own native
startup composition; re-pointed, rule-10 fix 1); `universalK` (body re-pointed). Deleted (moved):
the 26 privates listed above (`uk_init_mapState` included, §5 Q1). Result: 2,873 → 2,127 lines (12 public, 67 → 41 private); the new module 976 lines (22
public, 5 private).

## 5. Open points for the user

- **Q1 (RS-1).** `uk_init_mapState` is needed on both sides of the cut. Two options: (A,
  implemented) publish it in the new module as `Turing.MultiTapeTM.initCfg_eq_mapState`; RS-1 stays
  at five sites, and the ledger's disposition (a row beside `initCfg_with_q₀` in `Finite`) becomes a
  move of a public lemma with its name kept; (B) a private copy in the new module, RS-1 five → six
  sites, a disclosed new copy. The plan's D-F6-5 said "keep RS-1 out of the harvest", written for
  the in-place home, where no copy arose. Switching to (B) is a ten-line change.
- **Q2 (optional).** `headerRulerTM_run` keeps its blank-tape hypothesis (visibility only, per the
  plan). F6's second header (scan from the ruler's end, then rewind over `true^(ℓ₁ + ℓ₂)`) composes
  `headerScanTM_run`, `headerScanCfg_ruler` and `rewindTM_run_ofCfg` itself; a generalized
  `headerRulerTM_run` from a prefix `true^m` was not asked for and is not added.

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/Probe.lean.txt =====

import TCSlib.Complexity.TuringMachine.Build.UniversalParts
import TCSlib.Complexity.TuringMachine.UniversalK

/-! Consumer probe for the U2 harvest (scratch, never committed): F6's route
(`Complexity.space_universal`, plan §F6(b) D-F6-3 (ii)) composed from the public rows of
`Build/UniversalParts`. Only F6's own leaves are `sorry`. -/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace F6Probe

open Turing

/-! ### §1 Two header scans, the ruler extended -/

/-- Two consecutive header scans from a blank ruler tape write the ruler `true^(ℓ₁ + ℓ₂)`, with
the input head just past both headers. -/
theorem two_scans {k : ℕ} {z : List Bool} (i : Fin k) (d : Cfg k Bool (Fin 4) z) (p : ℕ)
    (hp : d.inputPos.val = 1 + p) (hd : d.state = some 0)
    (hblank : ∀ a, d.workTapes i a = none) (u₁ u₂ v : List Bool)
    (hz : z.drop p = pairEncode u₁ (pairEncode u₂ v)) :
    ((headerScanTM i).runFrom d (2 * u₁.length + 2)).state = some 3 ∧
      ((headerScanTM i).runFrom
          (((headerScanTM i).runFrom d (2 * u₁.length + 2)).mapState fun _ => 0)
          (2 * u₂.length + 2)).state = some 3 ∧
      ((headerScanTM i).runFrom
          (((headerScanTM i).runFrom d (2 * u₁.length + 2)).mapState fun _ => 0)
          (2 * u₂.length + 2)).inputPos.val =
        1 + p + (2 * u₁.length + 2) + (2 * u₂.length + 2) ∧
      ∀ a : ℤ, ((headerScanTM i).runFrom
          (((headerScanTM i).runFrom d (2 * u₁.length + 2)).mapState fun _ => 0)
          (2 * u₂.length + 2)).workTapes i (d.workTapePos i + a) =
        FinTM.bufferTape (List.replicate ((2 * u₁.length + 2) + (2 * u₂.length + 2)) true) a := by
  obtain ⟨h1, -, -⟩ := headerScanTM_run i d p hp hd u₁ (pairEncode u₂ v) hz
  rw [h1]
  set ℓ₁ := 2 * u₁.length + 2 with hℓ₁
  have hlen₁ : d.inputPos.val + ℓ₁ < z.length + 2 := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    omega
  -- the second scan's start
  set d₂ := (headerScanCfg i d 3 ℓ₁ hlen₁).mapState (fun _ => (0 : Fin 4)) with hd₂
  have hp₂ : d₂.inputPos.val = 1 + (p + ℓ₁) := by
    rw [hd₂, Cfg.mapState_inputPos, headerScanCfg_inputPos, Fin.val_mk, hp]
    omega
  have hs₂ : d₂.state = some 0 := by
    rw [hd₂, Cfg.mapState_state, headerScanCfg_state, Option.map_some]
  have hz₂ : z.drop (p + ℓ₁) = pairEncode u₂ v := by
    rw [← List.drop_drop, hz, hℓ₁, pairEncode_drop]
  have hlen₂ : d₂.inputPos.val + (2 * u₂.length + 2) < z.length + 2 := by
    have h := congrArg List.length hz₂
    rw [List.length_drop, length_pairEncode] at h
    omega
  have hpos₂ : d₂.workTapePos i = d.workTapePos i + ℓ₁ := by
    rw [hd₂, Cfg.mapState_workTapePos, headerScanCfg_workTapePos, Function.update_self]
  -- the first scan's ruler (`m = 0`), as the second scan's prefix (`m = ℓ₁`)
  have hfirst : ∀ a : ℤ, (headerScanCfg i d 3 ℓ₁ hlen₁).workTapes i (d.workTapePos i + a) =
      FinTM.bufferTape (List.replicate ℓ₁ true) a := by
    intro a
    have h := headerScanCfg_ruler i d 3 ℓ₁ hlen₁ 0 (fun b => by
      rw [hblank, List.replicate_zero, FinTM.bufferTape_eq, List.getElem?_nil, ite_self]) a
    simpa only [Nat.cast_zero, sub_zero, Nat.zero_add] using h
  have hpre₂ : ∀ a : ℤ, d₂.workTapes i (d₂.workTapePos i - (ℓ₁ : ℤ) + a) =
      FinTM.bufferTape (List.replicate ℓ₁ true) a := by
    intro a
    rw [hpos₂, show d.workTapePos i + (ℓ₁ : ℤ) - ℓ₁ + a = d.workTapePos i + a by ring, hd₂,
      Cfg.mapState_workTapes]
    exact hfirst a
  obtain ⟨h2, -, -⟩ := headerScanTM_run i d₂ (p + ℓ₁) hp₂ hs₂ u₂ v hz₂
  rw [h2]
  refine ⟨by rw [headerScanCfg_state], by rw [headerScanCfg_state], ?_, ?_⟩
  · rw [headerScanCfg_inputPos, Fin.val_mk, hp₂]
    omega
  · intro a
    have h := headerScanCfg_ruler i d₂ 3 (2 * u₂.length + 2) hlen₂ ℓ₁ hpre₂ a
    rwa [hpos₂, show d.workTapePos i + (ℓ₁ : ℤ) - ℓ₁ + a = d.workTapePos i + a by ring] at h

/-! ### §2 The startup under the ruler host, on the first header's suffix -/

/-- The startup run under H5's ruler host on the suffix `pairEncode α x` of
`pairEncode u (pairEncode α x)`, with the first header's ruler `true^ℓ₁`: the host ends at the
startup's endpoint presented through `rulerHostCfg` (input head at `ℓ₁ + 1`, the bank holding
the startup's tapes, the ruler last), within `C · (ℓ₁ + 1) · T` steps, and uses the startup's
cells plus `ℓ₁ + 2`. -/
theorem hosted_startup {K k : ℕ} {P : Type} [Fintype P] [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (u y : List Bool) (T B : ℕ)
    (d : Cfg (K + (k + 2)) Bool P y)
    (hrun : R.runFrom (R.initCfg y) T = d) (hB : R.spaceUsed (R.initCfg y) T ≤ B) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : MultiTapeTM (K + (k + 2) + 1) Bool V)
      (inj : P → Bool → V) (C : ℕ), 0 < C ∧
      ∃ (hz : (pairEncode u y).length = (2 * u.length + 2) + y.length) (t' : ℕ) (b' : Bool),
        t' ≤ C * (2 * u.length + 2 + 1) * T ∧
        (H.runFrom (rulerHostCfg (2 * u.length + 2) hz (some (inj R.q₀ false)) (R.initCfg y)
            (FinTM.bufferTape (List.replicate (2 * u.length + 2) true)) 0) t').inputPos.val =
          2 * u.length + 2 + d.inputPos.val ∧
        H.runFrom (rulerHostCfg (2 * u.length + 2) hz (some (inj R.q₀ false)) (R.initCfg y)
            (FinTM.bufferTape (List.replicate (2 * u.length + 2) true)) 0) t' =
          rulerHostCfg (2 * u.length + 2) hz (d.state.map fun q => inj q b') d
            (FinTM.bufferTape (List.replicate (2 * u.length + 2) true)) 0 ∧
        H.spaceUsed (rulerHostCfg (2 * u.length + 2) hz (some (inj R.q₀ false)) (R.initCfg y)
            (FinTM.bufferTape (List.replicate (2 * u.length + 2) true)) 0) t' ≤
          B + (2 * u.length + 2 + 2) := by
  classical
  obtain ⟨V, fV, dV, H, inj, C, hC, hH⟩ := exists_rulerHostTM R
  refine ⟨V, fV, dV, H, inj, C, hC, ?_⟩
  set ℓ := 2 * u.length + 2 with hℓ
  have hz : (pairEncode u y).length = ℓ + y.length := length_pairEncode u y
  have hinit : (R.initCfg y).inputPos.val = 1 := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  have hb : false = true ↔ (R.initCfg y).inputPos.val = 0 := by rw [hinit]; decide
  have hstate : (R.initCfg y).state.map (fun q => inj q false) = some (inj R.q₀ false) := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  obtain ⟨t', -, ht', ⟨b', -, hend⟩, -, -, hbank, hruler⟩ :=
    hH ℓ hz (by omega) (pairEncode_drop u y) (FinTM.bufferTape (List.replicate ℓ true)) 0
      (by intro p _ _; rw [zero_add]) (R.initCfg y) false hb T
  rw [hstate, hrun] at hend
  rw [hstate] at hbank hruler
  refine ⟨hz, t', b', ht', ?_, ?_, ?_⟩
  · rw [hend]
    exact (rulerHostCfg_fields ℓ hz _ d _ 0).1
  · rw [hend]
  · -- the space ledger: the bank's cells are the startup's, the ruler's at most `ℓ + 2`
    rw [MultiTapeTM.spaceUsed_eq_sum, Fin.sum_univ_castSucc]
    have hbankle : ∑ i : Fin (K + (k + 2)), H.spaceUsedByTape
        (rulerHostCfg ℓ hz (some (inj R.q₀ false)) (R.initCfg y)
          (FinTM.bufferTape (List.replicate ℓ true)) 0) t' i.castSucc ≤ B := by
      calc
        _ = ∑ i : Fin (K + (k + 2)), R.spaceUsedByTape (R.initCfg y) T i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card,
            hbank i]
        _ = R.spaceUsed (R.initCfg y) T := (MultiTapeTM.spaceUsed_eq_sum _ _).symm
        _ ≤ B := hB
    have hrulerle : H.spaceUsedByTape
        (rulerHostCfg ℓ hz (some (inj R.q₀ false)) (R.initCfg y)
          (FinTM.bufferTape (List.replicate ℓ true)) 0) t' (Fin.last _) ≤ ℓ + 2 := by
      rw [MultiTapeTM.spaceUsedByTape_eq_card]
      calc
        _ ≤ (Finset.Icc ((0 : ℤ) - 1) (0 + ℓ)).card := Finset.card_le_card hruler
        _ = ℓ + 2 := by rw [Int.card_Icc]; omega
    omega

/-! ### §3 The final seam: the suffix-ruler layout into the ruler host around H2-F -/

/-- From any prefix machine `A` that ends at the suffix-ruler layout with a ruler of length `ℓ`
(F6: `ℓ = ℓ₁ + ℓ₂`, two headers), the seam machine runs the ruler host `H` around the forwarding
loop on the suffix `x`, and its space is `A`'s plus `(K + (k + 3)) · S` for a per-tape bound `S`
of the hosted loop. -/
theorem final_seam {k K n : ℕ} {P Q V : Type} [DecidableEq P]
    (A : MultiTapeTM (K + (k + 3)) Bool P) (finish : P)
    (H : MultiTapeTM (k + 3) Bool V) (inj : Q → Bool → V) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) {z x : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + x.length) (hlen : ℓ + 1 < z.length + 2) (T : ℕ)
    (aRun : A.runFrom (A.initCfg z) T = suffixRulerCfg (K := K) finish M z ℓ hlen)
    (aCut : ∀ u < T, (A.runFrom (A.initCfg z) u).state ≠ some finish)
    (t B S : ℕ) (hB : A.spaceUsed (A.initCfg z) T ≤ B) (hS : 1 ≤ S)
    (hloop : ∀ i, H.spaceUsedByTape
      (rulerHostCfg ℓ hz ((StepBlock.forwardLoopCfg entry M (M.initCfg x)).state.map
        fun q => inj q false) (StepBlock.forwardLoopCfg entry M (M.initCfg x))
        (FinTM.bufferTape (List.replicate ℓ true)) 0) t i ≤ S) :
    (startupLoopTM (k := k + 1) A finish H (inj entry false)).runFrom
        ((startupLoopTM (k := k + 1) A finish H (inj entry false)).initCfg z) (T + 1 + t) =
      (embedEmitCfg (Fin.castLEEmb (by omega : k + 1 + 2 ≤ K + (k + 1 + 2)))
        (fun _ _ => none) (fun _ => 0) []
        (H.runFrom (rulerHostCfg ℓ hz
          ((StepBlock.forwardLoopCfg entry M (M.initCfg x)).state.map fun q => inj q false)
          (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          (FinTM.bufferTape (List.replicate ℓ true)) 0) t)).mapState Sum.inr ∧
    (startupLoopTM (k := k + 1) A finish H (inj entry false)).spaceUsed
        ((startupLoopTM (k := k + 1) A finish H (inj entry false)).initCfg z) (T + 1 + t) ≤
      B + (K + (k + 1 + 2)) * S := by
  have hcfg := (suffixRulerCfg_embed (K := K) finish entry inj M ℓ hz hlen).symm
  have hexit : (suffixRulerCfg (K := K) finish M z ℓ hlen).state = some finish :=
    suffixRulerCfg_state _ _ _ _ _
  exact ⟨startupLoopTM_runFrom (k := k + 1) A finish H (inj entry false) _ _ T aRun hexit
      aCut hcfg t,
    startupLoopTM_spaceUsed_le (k := k + 1) A finish H (inj entry false) _ _ T aRun hexit
      aCut hcfg t B S hB hS hloop⟩

/-! ### §4 The route at F6's layout `pairEncode (bits s) (pairEncode α x)` -/

/-- F6's layout: the two headers' lengths add up to the suffix-ruler layout's `ℓ`, and the
suffix after both is `x`. -/
theorem layout (u α x : List Bool) :
    (pairEncode u (pairEncode α x)).length =
        ((2 * u.length + 2) + (2 * α.length + 2)) + x.length ∧
      (pairEncode u (pairEncode α x)).drop ((2 * u.length + 2) + (2 * α.length + 2)) = x := by
  refine ⟨by rw [length_pairEncode, length_pairEncode]; omega, ?_⟩
  rw [← List.drop_drop, pairEncode_drop, pairEncode_drop]

/-- The route's space ledger at F6's layout, from §3. F6's own leaves are `sorry`: (L1) the
prefix machine (header ruler on `bits s`, the startup under the ruler host (§2), a seek to the
ruler's end, the second scan (§1) and the rewind) and its exact run to the suffix-ruler layout;
(L2) the hosted loop's per-tape bound from H5's and H2-F's visited-set clauses. -/
theorem route_space {k K n : ℕ} {P Q V : Type} [DecidableEq P]
    (A : MultiTapeTM (K + (k + 3)) Bool P) (finish : P)
    (H : MultiTapeTM (k + 3) Bool V) (inj : Q → Bool → V) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (u α x : List Bool) (T t B S : ℕ)
    (hB : A.spaceUsed (A.initCfg (pairEncode u (pairEncode α x))) T ≤ B) (hS : 1 ≤ S) :
    (startupLoopTM (k := k + 1) A finish H (inj entry false)).spaceUsed
        ((startupLoopTM (k := k + 1) A finish H (inj entry false)).initCfg
          (pairEncode u (pairEncode α x))) (T + 1 + t) ≤ B + (K + (k + 1 + 2)) * S := by
  obtain ⟨hz, -⟩ := layout u α x
  have hlen : (2 * u.length + 2) + (2 * α.length + 2) + 1 <
      (pairEncode u (pairEncode α x)).length + 2 := by omega
  -- (L1) F6's prefix machine reaches the suffix-ruler layout at `ℓ = ℓ₁ + ℓ₂`
  have aRun : A.runFrom (A.initCfg (pairEncode u (pairEncode α x))) T =
      suffixRulerCfg (K := K) finish M (pairEncode u (pairEncode α x))
        ((2 * u.length + 2) + (2 * α.length + 2)) hlen := sorry
  have aCut : ∀ v < T,
      (A.runFrom (A.initCfg (pairEncode u (pairEncode α x))) v).state ≠ some finish := sorry
  -- (L2) the hosted loop's per-tape bound
  have hloop : ∀ i, H.spaceUsedByTape
      (rulerHostCfg ((2 * u.length + 2) + (2 * α.length + 2)) hz
        ((StepBlock.forwardLoopCfg entry M (M.initCfg x)).state.map fun q => inj q false)
        (StepBlock.forwardLoopCfg entry M (M.initCfg x))
        (FinTM.bufferTape (List.replicate ((2 * u.length + 2) + (2 * α.length + 2)) true)) 0)
      t i ≤ S := sorry
  exact (final_seam A finish H inj entry M _ hz hlen T aRun aCut t B S hB hS hloop).2

end F6Probe

#print axioms F6Probe.two_scans
#print axioms F6Probe.hosted_startup
#print axioms F6Probe.final_seam
#print axioms F6Probe.layout
#print axioms F6Probe.route_space

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealParts.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.Rewind
import Mathlib.Algebra.Group.Action.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parts of the `k`-generic universal machines

[AB09, §1.4.1 and the proof of Theorem 1.9]: the pieces that the `k`-generic universal machines
of `TuringMachine/UniversalK.lean` (U2) are assembled from, published so that a second consumer
(the space-universal machine `Complexity.space_universal`, [AB09, Exercise 4.1]) composes them
instead of re-deriving them. Harvested from `UniversalK`'s privates (the U2 harvest API, user
ruling of 2026-11-06: a new `Build/` module; plan `campaign/items/roadmap3/PLAN.md`, §F6(c)).

* **The forwarding loop at an initial configuration.** H2-F's encoding
  `Turing.StepBlock.forwardLoopCfg` of a machine's initial configuration (its tapes, fields and
  halting), its embedding at the startup's endpoint, and the three readings of H2-F's lockstep
  used by both universal machines: the forward time bound to the first halt, liveness forever,
  and the converse on outputs.
* **The startup–loop seam.** `Turing.startupLoopTM`: a startup on `K + (k + 2)` tapes followed,
  at its exit, by a loop on the first `k + 2`; its start, its live prefix, its run after the
  seam from any seam endpoint, and its space ledger from any seam endpoint.
* **The header ruler.** `Turing.headerScanTM`: a finite-state scan of one doubled header
  `pairEncode u v`, from any input offset, writing one ruler cell per input cell; from an
  existing ruler prefix `true^m` it extends the ruler to `true^(m + 2|u| + 2)`, so consecutive
  headers give one ruler. `Turing.headerRulerTM`: the scan followed by the rewind.
* **The suffix-ruler layout.** `Turing.suffixRulerCfg`: the simulation bank, then the ruler
  `true^ℓ`, with the input head just past a header of length `ℓ`; it is the embedding of the
  ruler host's initial presentation (`Turing.rulerHostCfg`) of the forwarding loop's start.

## Main definitions

* `Turing.startupLoopTM` — the startup followed by the embedded loop.
* `Turing.headerScanTM`, `Turing.headerScanCfg` — the header scan and its presentation after
  `t` marks (with field equations).
* `Turing.headerRulerTM` — the header scan followed by the work-tape rewind.
* `Turing.suffixRulerCfg` — the suffix-ruler seam layout (with field equations).

## Main results

* `Turing.MultiTapeTM.initCfg_eq_mapState` — the restart identity (ledger RS-1's general form).
* `Turing.StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`,
  `Turing.embedEmitCfg_forwardLoop_init` — the forwarding loop's encoding at the start.
* `Turing.StepBlock.forwardLoop_forward`, `_live`, `_converse` — the lockstep's readings.
* `Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom`, `_spaceUsed_le` — the seam.
* `Turing.headerScanTM_run`, `Turing.headerScanCfg_ruler`, `Turing.headerRulerTM_run` — the
  header ruler.
* `Turing.rulerHostCfg_fields`, `Turing.suffixRulerCfg_embed` — the suffix-ruler layout.

All proved. The generalizations against the private forms are `startupLoopTM_spaceUsed_le` (any
seam endpoint, not only the native startup's) and `headerScanCfg_ruler` (from a ruler prefix
`true^m`, not only a blank tape); every other row is the private statement, renamed.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9 and its proof: the universal machine
  reads the code and simulates `M` step by step on a work-tape copy of its table; Exercise 4.1,
  the space-bounded universal machine.)
-/

namespace Turing

attribute [local irreducible] StepBlock.forwardLoopCfg rulerHostCfg MultiTapeTM.initCfg Cfg.init
  FinTM.bufferTape StepBlock.summaryCells tableBitsK unaryFin embedEmitCfg Cfg.mapState
  pairEncode rewindTM seamCompTM embedEmitTM tapeAction inputMoveAction
attribute [-simp] MultiTapeTM.initCfg Cfg.init

/-! ## The restart identity -/

/-- **The restart identity**: if a machine `B`'s initial state is the image `f A.q₀` of
another machine `A`'s, then `B`'s initial configuration on any input is `A`'s with its state
relabelled by `f`. Ledger RS-1's general form (`campaign/duplication-ledger.md`). [AB09, §1.4.1]
(glue for the universal machine's composed startups). -/
theorem MultiTapeTM.initCfg_eq_mapState {m : ℕ} {P Q : Type}
    (A : MultiTapeTM m Bool P) (B : MultiTapeTM m Bool Q) (f : P → Q)
    (hq : B.q₀ = f A.q₀) (x : List Bool) : B.initCfg x = (A.initCfg x).mapState f := by
  refine Cfg.ext ?_ ?_ (funext fun j => funext fun a => ?_) (funext fun j => ?_) ?_
  all_goals
    simp only [MultiTapeTM.initCfg_eq, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
      Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes, Cfg.init_workTapePos,
      Cfg.init_output, Option.map_some, hq]

/-! ## The forwarding loop at an initial configuration -/

/-- **The forwarding loop's encoding of an initial configuration, its tapes**: H2-F's
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` of a `k`-tape binary machine's
initial configuration has, on its `k + 2` tapes, the table bits `tableBitsK M.tr` as a buffer on
tape `k`, the unary initial state `unaryFin M.q₀` from cell `2` on tape `k + 1` (cells `0` and
`1` blank), and blank mirrored tapes `0, …, k - 1`. This is the layout the universal machines'
startups install. [AB09, §1.4.1, the proof of Theorem 1.9: the work-tape copy of `M`'s table
and its current state]

**Proof sketch.** Split the tape index into a mirrored tape and one of the two
auxiliary tapes. The initial mirrored tapes are blank; the table is unchanged,
and the summary agrees cell by cell, including its blank cell at zero. -/
theorem StepBlock.forwardLoopCfg_init_workTapes {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) (j : Fin (k + 2)) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
      else fun _ => none := by
  have hw : (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      Fin.addCases (motive := fun _ => ℤ → Option Bool) (M.initCfg x).workTapes (fun j =>
        if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
        else StepBlock.summaryCells none (((M.initCfg x).state.map unaryFin).getD [])) j :=
    funext fun a => StepBlock.forwardLoopCfg_workTapes entry M (M.initCfg x) j a
  rw [hw]
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq]
    have h1 : (Fin.castAdd 2 i).val ≠ k := by simp only [Fin.coe_castAdd]; omega
    have h2 : (Fin.castAdd 2 i).val ≠ k + 1 := by simp only [Fin.coe_castAdd]; omega
    rw [if_neg h1, if_neg h2]
    funext p
    rw [Cfg.init_workTapes]
  · rw [Fin.addCases_right, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some,
      Option.getD_some]
    by_cases h : j' = 0
    · subst h
      have h1 : (Fin.natAdd k (0 : Fin 2)).val = k := by simp only [Fin.coe_natAdd]; omega
      rw [if_pos rfl, if_pos h1]
    · have hj : j' = 1 := by omega
      subst hj
      have h1 : (Fin.natAdd k (1 : Fin 2)).val ≠ k := by simp only [Fin.coe_natAdd]; omega
      have h2 : (Fin.natAdd k (1 : Fin 2)).val = k + 1 := by simp only [Fin.coe_natAdd]; omega
      rw [if_neg (by decide), if_neg h1, if_pos h2]
      funext p
      rw [StepBlock.summaryCells_eq]
      by_cases hp : p = 0
      · rw [if_pos hp, hp]
        exact (FinTM.bufferTape_of_neg _ (by omega)).symm
      · rw [if_neg hp]

/-- **The forwarding loop's encoding of an initial configuration, its other fields**: the
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` is at the control `entry`, with
input head at cell `1`, every work head at `0` and an empty output. [AB09, §1.4.1, the proof of
Theorem 1.9] -/
theorem StepBlock.forwardLoopCfg_init_fields {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).state = some entry ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).inputPos.val = 1 ∧
      (∀ j, (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapePos j = 0) ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).output = [] := by
  refine ⟨?_, ?_, fun j => ?_, ?_⟩
  · rw [StepBlock.forwardLoopCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  · rw [StepBlock.forwardLoopCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  · rw [StepBlock.forwardLoopCfg_workTapePos]
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    · rw [Fin.addCases_right]
  · rw [StepBlock.forwardLoopCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output]

/-- **The forwarding loop's encoding halts with its source**: for any configuration `c` of a
`k`-tape binary machine, the encoding `Turing.StepBlock.forwardLoopCfg entry M c` is halted
exactly when `c` is, and its output is `c`'s. Stated as the conjunction of the iff and the output
equation. [AB09, §1.4.1, the proof of Theorem 1.9: the universal machine halts with `M`'s
output] -/
theorem StepBlock.forwardLoopCfg_halt_iff {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    ((StepBlock.forwardLoopCfg entry M c).state = none ↔ c.state = none) ∧
      (StepBlock.forwardLoopCfg entry M c).output = c.output := by
  rw [StepBlock.forwardLoopCfg_state, StepBlock.forwardLoopCfg_output, Option.map_eq_none_iff]
  exact ⟨Iff.rfl, rfl⟩

/-- **The startup's native endpoint is the embedded initial encoding**: embedding the
forwarding loop's encoding of `M`'s initial configuration on `x` in the first `k + 2` of
`K + (k + 2)` tapes (the other tapes blank with their heads at `0`, no prior output) gives the
configuration at the control `exit`, input head `1`, the table on tape `k`, the unary initial
state from cell `2` on tape `k + 1`, every other tape blank, every head at `0` and an empty
output, with its control relabelled to `entry`. This is the endpoint of the startup
`Turing.exists_selfStartupTMK`, hence the seam hypothesis of `Turing.startupLoopTM_runFrom` for
the native layout. [AB09, §1.4.1, the proof of Theorem 1.9]

**Proof sketch.** Use the public reconstruction theorem for the emitting embedding.
The selected tapes and heads are the initial encoding's fields. An unselected
tape has index at least `k + 2`, so both tests in the startup layout are false. -/
theorem embedEmitCfg_forwardLoop_init {k n K : ℕ} {P Q : Type} (exit : P) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
      (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)) =
        (⟨some exit, 1,
          fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
            else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
            else fun _ => none,
          fun _ => 0, []⟩ : Cfg (K + (k + 2)) Bool P x).mapState (fun _ => entry) := by
  apply embedEmitCfg_eq
  · rw [Cfg.mapState_state]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).1
  · apply Fin.ext
    rw [Cfg.mapState_inputPos]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.1
  · rw [List.nil_append, Cfg.mapState_output]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.2
  · intro i
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      exact congrFun (StepBlock.forwardLoopCfg_init_workTapes entry M x i) a
    · rw [Cfg.mapState_workTapePos]
      exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.1 i
  · intro j hj
    have hjge : k + 2 ≤ j.val := by
      by_contra h
      have hlt : j.val < k + 2 := by omega
      apply hj
      refine ⟨⟨j.val, hlt⟩, ?_⟩
      apply Fin.ext
      rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      dsimp only
      rw [if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
    · rw [Cfg.mapState_workTapePos]

/-- **The forwarding loop's forward time bound**: let `L` simulate a `k`-tape binary machine
`M` in macro-step lockstep over H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M`
(the `Turing.Lockstep` of `Turing.StepBlock.exists_forwardLoopTM`), with every live step's cost
at most `D`. If `M` has halted on `x` by time `t`, there is its first halting time `t₀ ≤ t`
(live before `t₀`) such that the simulated time `Σ_{u < t₀} cost` is at most `D · t` and `L`,
started at the encoding of `M`'s initial configuration, is after that many steps at the
encoding of `M`'s configuration at time `t`. [AB09, §1.4.1, the proof of Theorem 1.9: each
step of `M` costs the universal machine a number of steps depending on `M` only]

**Proof sketch.** Choose the first source halt. The lockstep applies up to that
time, and each summand in its simulated time is bounded by the per-step bound.
Absorption identifies the first halted configuration with the given final one. -/
theorem StepBlock.forwardLoop_forward {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → cost c ≤ D) (t : ℕ)
    (hhalt : (M.runFrom (M.initCfg x) t).state = none) :
    ∃ t₀ ≤ t, (∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none) ∧
      (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) ≤ D * t ∧
      L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) =
        StepBlock.forwardLoopCfg entry M (M.runFrom (M.initCfg x) t) := by
  obtain ⟨t₀, hle, hfirst, hsame⟩ := MultiTapeTM.exists_first_halt M (M.initCfg x) hhalt
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
  · calc
      _ ≤ ∑ _u ∈ Finset.range t₀, D := Finset.sum_le_sum fun u hu =>
        hcost _ (hfirst u (Finset.mem_range.mp hu))
      _ = D * t₀ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ D * t := Nat.mul_le_mul_left D hle
  · rw [hlock.runFrom (M.initCfg x) t₀ (by
      simpa only [Set.mem_singleton_iff] using hfirst), hsame]

/-- **The forwarding loop diverges with its source**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` with positive costs at live configurations, if `M`
never halts on `x`, then `L` started at the encoding of `M`'s initial configuration is live at
every time. [AB09, §1.4.1, Theorem 1.9: the universal machine diverges when `M` does]

**Proof sketch.** For a target time `v`, simulate `v + 1` source steps. Every
cost is positive, so their sum exceeds `v`; the lockstep cut gives liveness. -/
theorem StepBlock.forwardLoop_live {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hpos : ∀ c, c.state ≠ none → 0 < cost c)
    (hlive : ∀ u, (M.runFrom (M.initCfg x) u).state ≠ none) (v : ℕ) :
    (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state ≠ none := by
  have hsum : v + 1 ≤ ∑ u ∈ Finset.range (v + 1), cost (M.runFrom (M.initCfg x) u) := by
    calc
      _ = ∑ _u ∈ Finset.range (v + 1), (1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum fun u _ => hpos _ (hlive u)
  have hcut := hlock.cut (M.initCfg x) (v + 1)
    (fun u _ => by simpa only [Set.mem_singleton_iff] using hlive u) v (by omega)
  simpa only [Set.mem_singleton_iff] using hcut

/-- **The forwarding loop's converse**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` whose costs at live configurations lie in `[1, D]`,
if `L` started at the encoding of `M`'s initial configuration on `x` has halted at time `u`,
then `M` has halted on `x` at some time `t`, with the same output as `L` at `u`. So every
completed output of the loop is a completed output of `M`. [AB09, §1.4.1, Theorem 1.9: the
universal machine's output is `M`'s]

**Proof sketch.** If the source never halted, positivity and the lockstep cut
would keep the loop live at the given time. Choose a source halt and apply the
forward lemma. The loop is now halted at both times, so its output agrees at
their maximum; the encoding preserves the source's output. -/
theorem StepBlock.forwardLoop_converse {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → 0 < cost c ∧ cost c ≤ D) (u : ℕ)
    (hhalt : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).state = none) :
    ∃ t, (M.runFrom (M.initCfg x) t).state = none ∧
      (M.runFrom (M.initCfg x) t).output =
        (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).output := by
  classical
  have hex : ∃ t, (M.runFrom (M.initCfg x) t).state = none := by
    by_contra h
    have hsource : ∀ t, (M.runFrom (M.initCfg x) t).state ≠ none :=
      fun t ht => h ⟨t, ht⟩
    exact (StepBlock.forwardLoop_live M L entry cost hlock (fun c hc => (hcost c hc).1)
      hsource u) hhalt
  obtain ⟨t, ht⟩ := hex
  obtain ⟨t₀, _, _, _, hr⟩ :=
    StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t ht
  let v := ∑ i ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) i)
  have hv : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state = none := by
    rw [hr]
    exact (StepBlock.forwardLoopCfg_halt_iff entry M _).1.mpr ht
  refine ⟨t, ht, ?_⟩
  calc
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).output := by
      rw [hr, (StepBlock.forwardLoopCfg_halt_iff entry M _).2]
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) (max u v)).output :=
      (MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_right u v) hv).symm
    _ = _ := MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_left u v) hhalt
/-! ## The startup–loop seam -/

/-- **The startup–loop seam machine**: a startup `R` on `K + (k + 2)` work tapes, followed at
its exit control `exit` by the loop `L` on the first `k + 2` of them, entered at `entry`
(`Turing.seamCompTM` of `R` and the emitting embedding `Turing.embedEmitTM` of `L` along
`Fin.castLEEmb`, the other tapes untouched), started in `R`'s initial control. Read through
`Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom` and `_spaceUsed_le`. [AB09, §1.4.1,
the proof of Theorem 1.9: the universal machine first prepares its work tapes, then simulates]
-/
noncomputable def startupLoopTM {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) :
    MultiTapeTM (K + (k + 2)) Bool (P ⊕ Q) :=
  { seamCompTM R exit
      (embedEmitTM (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))) L) entry with
    q₀ := Sum.inl R.q₀ }

/-- **The seam machine's start**: on every input, `Turing.startupLoopTM R exit L entry` starts
in the startup's initial configuration, its control relabelled by `Sum.inl`. [AB09, §1.4.1] -/
theorem startupLoopTM_initCfg {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) (x : List Bool) :
    (startupLoopTM R exit L entry).initCfg x = (R.initCfg x).mapState Sum.inl := by
  exact MultiTapeTM.initCfg_eq_mapState R (startupLoopTM R exit L entry) Sum.inl rfl x

/-- **The seam machine is live through the startup**: if the startup `R` is live at time `T`
on `x` and does not reach `exit` before `T`, then `Turing.startupLoopTM R exit L entry` is live
on `x` at every time `t ≤ T`. [AB09, §1.4.1] -/
theorem startupLoopTM_live_of_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool} (T : ℕ)
    (hlive : (R.runFrom (R.initCfg x) T).state ≠ none)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    ((startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x) t).state ≠
      none := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_left R exit _ entry hcut t ht, Cfg.mapState_state]
  intro hh
  exact MultiTapeTM.runFrom_state_ne_none_of_le R (R.initCfg x) T hlive t ht
    (Option.map_eq_none_iff.mp hh)

/-- **The seam machine after the seam, from any seam endpoint**: suppose the startup `R`
reaches the configuration `d` on `x` at exactly time `T`, at the control `exit`, and not
earlier, and that `d` with its control replaced by `entry` is the embedding of a loop
configuration `c` in the first `k + 2` tapes (the others blank with their heads at `0`, no
prior output). Then for every `t`, `Turing.startupLoopTM R exit L entry` at time `T + 1 + t` is
the embedding of `L`'s run from `c` for `t` steps, with its control relabelled by `Sum.inr`. The
loop may be the native forwarding loop (`c` its encoding, `d` the startup's native endpoint,
`Turing.embedEmitCfg_forwardLoop_init`) or its suffix host (`c` the ruler host's presentation,
`d` the suffix-ruler layout, `Turing.suffixRulerCfg_embed`). [AB09, §1.4.1] -/
theorem startupLoopTM_runFrom {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c) (t : ℕ) :
    (startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) =
      (embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] (L.runFrom c t)).mapState Sum.inr := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_right R exit _ entry hrun hexit hcut t, hcfg, embedEmitTM_runFrom]

/-- **The seam machine's space ledger, from any seam endpoint**: under the seam hypotheses of
`Turing.startupLoopTM_runFrom` (the startup `R` reaches `d` on `x` at exactly `T`, at `exit`,
not earlier, and `d` relabelled at `entry` is the embedding of the loop configuration `c`), if
the startup uses at most `B` cells by `T` and the loop `L`, run from `c`, uses at most `S ≥ 1`
cells on each of its tapes by `t`, then `Turing.startupLoopTM R exit L entry` uses at most
`B + (K + (k + 2)) · S` cells on `x` by time `T + 1 + t`. [AB09, Exercise 4.1: the universal
machine's space is the simulated machine's up to a factor depending on the code]

*Generalization.* The private form fixed the native endpoint (`d` the startup's layout at input
position `1`, `c` the encoding of `M`'s initial configuration). It read that endpoint only
through its exit control and the embedding identity, now the hypotheses `hexit` and `hcfg`; at
the native endpoint they are `rfl` and `Turing.embedEmitCfg_forwardLoop_init`, which is the old
statement. At `(K, k + 1)`, `d` the suffix-ruler layout and `c` the ruler host's presentation
(`Turing.suffixRulerCfg_embed`) it is the ledger of the suffix layout.

**Proof sketch.** The seam's visited-set theorem bounds each tape by the union
of its startup and loop visits. A selected loop tape has the source loop's
visited set; an unselected tape visits just its initial cell. Count each union
and sum over the host's tapes, using the public space equations. -/
theorem startupLoopTM_spaceUsed_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c)
    (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
    (hloop : ∀ i, L.spaceUsedByTape c t i ≤ S) :
    (startupLoopTM R exit L entry).spaceUsed ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) ≤ B + (K + (k + 2)) * S := by
  classical
  let σ := Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))
  let A := embedEmitTM σ L
  let e := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] c
  have he : d.mapState (fun _ => entry) = e := hcfg
  have hA : ∀ j, A.spaceUsedByTape e t j ≤ S := by
    intro j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [(embedEmitTM_visitedByTapeHead σ L _ _ [] c t i).2]
      exact hloop i
    · rw [(embedEmitTM_visitedByTapeHead_frame σ L _ _ [] c t j hj).2]
      exact hS
  have htape (j : Fin (K + (k + 2))) :
      (startupLoopTM R exit L entry).spaceUsedByTape
          ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ≤
        R.spaceUsedByTape (R.initCfg x) T j + S := by
    rw [MultiTapeTM.spaceUsedByTape_eq_card]
    have hsub := seamCompTM_visitedByTapeHead_ofCfg R exit A entry
      (c₁ := d) (T₂ := t) hrun hexit hcut j
    rw [he] at hsub
    have hown : (startupLoopTM R exit L entry).visitedByTapeHead
        ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ⊆
        (seamCompTM R exit A entry).visitedByTapeHead
          ((R.initCfg x).mapState Sum.inl) (T + 1 + t) j := by
      intro p hp
      rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
      obtain ⟨u, hu, hp⟩ := hp
      refine ⟨u, hu, ?_⟩
      rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀] at hp
      exact hp
    calc
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j ∪ A.visitedByTapeHead e t j).card :=
        Finset.card_le_card (hown.trans hsub)
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j).card +
          (A.visitedByTapeHead e t j).card := Finset.card_union_le _ _
      _ = R.spaceUsedByTape (R.initCfg x) T j + A.spaceUsedByTape e t j := by
        rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      _ ≤ _ := Nat.add_le_add_left (hA j) _
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    _ ≤ ∑ j, (R.spaceUsedByTape (R.initCfg x) T j + S) :=
      Finset.sum_le_sum fun j _ => htape j
    _ = R.spaceUsed (R.initCfg x) T + (K + (k + 2)) * S := by
      rw [Finset.sum_add_distrib, ← MultiTapeTM.spaceUsed_eq_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right hB _

/-! ## The header scan and the header ruler -/

/-- **The header scan**: a finite-state machine on `k` work tapes that reads a doubled header
`pairEncode u v` (the bits of `u`, each written twice, then the separator `false, true`) in
aligned pairs from its input head, writing `true` on tape `i` and moving that head and the input
head right at every step, and stops at its control `3` just past the separator. States `0`, `1`
and `2` read a pair (`1` and `2` remember its first bit); `3` is the exit, where the machine idles.
So it writes one ruler cell per header cell. It is hand-built: no catalog row writes a ruler of a
doubled header's length. Read through `Turing.headerScanTM_run`. [AB09, §1.4.1, the proof of
Theorem 1.9: the universal machine reads the code at the start of its input; the pair encoding
of [AB09, §1.4]] -/
def headerScanTM {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Fin 4) where
  q₀ := 0
  tr := fun q b _ =>
    if q = 3 then inputMoveAction 0 3
    else tapeAction i .pos (some (some true)) .pos
      (if q = 0 then if b = some false then 1 else 2
       else if q = 1 ∧ b = some true then 3 else 0)

/-- **The header scan's presentation after `t` marks**: from a configuration `d`, the
configuration at control `q` with the input head and the head of tape `i` both `t` cells right
of `d`'s, the cells `[pos, pos + t)` of tape `i` (`pos` its head in `d`) set to `true` and every
other cell, tape, head and the output as in `d`. [AB09, §1.4.1] -/
def headerScanCfg {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : Cfg k Bool (Fin 4) z :=
  ⟨some q, ⟨d.inputPos.val + t, ht⟩,
    Function.update d.workTapes i
      (fun a => if d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        then some true else d.workTapes i a),
    Function.update d.workTapePos i (d.workTapePos i + t), d.output⟩

/-! The header scan's presentation's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.headerScanCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  headerScanCfg

/-- Zero scan steps leave the initial live configuration unchanged. -/
private theorem up_scan_zero {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (hd : d.state = some 0) :
    headerScanCfg i d 0 0 (by have := d.inputPos.isLt; omega) = d := by
  apply Cfg.ext
  · exact hd.symm
  · apply Fin.ext; simp only [headerScanCfg, Nat.add_zero]
  · funext j a
    simp only [headerScanCfg, Nat.cast_zero, add_zero]
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]
  · simp only [headerScanCfg, Nat.cast_zero, add_zero, Function.update_eq_self]
  · rfl

/-- One scan step writes and advances both heads, preserving every frame field.

**Proof sketch.** Read the transition with the public writing-action equation. Its
updated cell is exactly the new right endpoint of the already marked interval;
all other cells retain their previous value. -/
private theorem up_scan_step {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 1) (hq : q ≠ 3) (b : Bool)
    (hb : (headerScanCfg i d q t (by omega)).inputSymbol = some b) :
    (headerScanTM i).step (headerScanCfg i d q t (by omega)) =
      headerScanCfg i d
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) (t + 1) (by omega) := by
  have ht' : (headerScanTM i).tr q (headerScanCfg i d q t (by omega)).inputSymbol
      (headerScanCfg i d q t (by omega)).workTapeSymbols = tapeAction i .pos
        (some (some true)) .pos
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) := by
    simp only [headerScanTM, if_neg hq, hb, Option.some.injEq]
  rw [step_of_tapeAction_write _ _ i .pos (some true) .pos rfl ht']
  apply Cfg.ext
  · rfl
  · rw [moveInputPos_pos_of_ne_right _ (by simp only [headerScanCfg]; omega)]
    apply Fin.ext
    simp only [headerScanCfg]
    omega
  · funext j a
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one]
      by_cases ha : a = d.workTapePos i + t
      · subst a
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne ha]
        by_cases ha' : d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        · rw [if_pos ha', if_pos (by omega)]
        · rw [if_neg ha', if_neg (by omega)]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one,
        SignType.pos_eq_one, SignType.coe_one, add_assoc]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · rfl

/-- The scanner consumes one aligned pair, marking both input cells.

**Proof sketch.** The suffix equation gives the two input symbols through `getElem_drop`.
Apply the one-step result twice. The intermediate state stores the first bit,
and the second bit either returns on the separator or resumes the pair scan. -/
private theorem up_scan_pair {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p t : ℕ) (hp : d.inputPos.val = 1 + p)
    (a b : Bool) (rest : List Bool) (hz : z.drop (p + t) = a :: b :: rest) :
    let hlen : d.inputPos.val + (t + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      simp only [List.length_drop, List.length_cons] at h
      omega
    let c := headerScanCfg i d 0 t (by omega)
    (headerScanTM i).runFrom c 2 =
        headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) hlen ∧
      (∀ v < 2, ((headerScanTM i).runFrom c v).state ≠ some 3) := by
  have hlen : p + t + 2 ≤ z.length := by
    have h := congrArg List.length hz
    simp only [List.length_drop, List.length_cons] at h
    omega
  dsimp only
  have ha : z[p + t]'(by omega) = a := by
    have hh : (z.drop (p + t))[0]'(by rw [hz]; simp) = a := by
      simp only [hz, List.getElem_cons_zero]
    simpa only [List.getElem_drop, Nat.add_zero] using hh
  have hb : z[p + t + 1]'(by omega) = b := by
    have hh : (z.drop (p + t))[1]'(by rw [hz]; simp) = b := by
      simp only [hz, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa only [List.getElem_drop] using hh
  let q : Fin 4 := if a = false then 1 else 2
  have h1 : (headerScanTM i).step (headerScanCfg i d 0 t (by omega)) =
      headerScanCfg i d q (t + 1) (by omega) := by
    have read : (headerScanCfg i d 0 t (by omega)).inputSymbol = some a := by
      rw [inputSymbolInner (p + t) (by simp only [headerScanCfg]; omega) (by omega), ha]
    simpa only [if_pos rfl] using up_scan_step i d 0 t (by omega) (by decide) a read
  have h2 : (headerScanTM i).step (headerScanCfg i d q (t + 1) (by omega)) =
      headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) (by omega) := by
    have read : (headerScanCfg i d q (t + 1) (by omega)).inputSymbol = some b := by
      rw [inputSymbolInner (p + t + 1) (by simp only [headerScanCfg]; omega) (by omega), hb]
    have step := up_scan_step i d q (t + 1) (by omega)
      (by dsimp only [q]; split <;> decide) b read
    cases a <;> cases b <;> simpa only [q, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, and_self, and_false, false_and, true_and] using step
  have one (e : Cfg k Bool (Fin 4) z) :
      (headerScanTM i).runFrom e 1 = (headerScanTM i).step e := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  constructor
  · calc
      _ = (headerScanTM i).runFrom
          ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 1) 1 :=
        MultiTapeTM.runFrom_add _ 1 1
      _ = _ := by rw [one, one, h1, h2]
  · intro v hv
    have casesv : v = 0 ∨ v = 1 := by omega
    rcases casesv with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
      change some (0 : Fin 4) ≠ some 3
      decide
    · rw [one, h1]
      change some q ≠ some 3
      cases a <;> decide

/-- The scanner consumes one doubled header from any native input offset.

**Proof sketch.** Induct on the header word. Every doubled bit takes two steps
and returns to the pair-reading state; the separator takes two steps and returns.
The suffix equation is advanced with `drop_drop`, while the exact-time cut is
split before and after each pair. -/
private theorem up_scan_header {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (u v : List Bool) (t : ℕ) (hz : z.drop (p + t) = pairEncode u v) :
    let hlen : d.inputPos.val + (t + (2 * u.length + 2)) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) (2 * u.length + 2) =
        headerScanCfg i d 3 (t + (2 * u.length + 2)) hlen ∧
      (∀ r < 2 * u.length + 2,
        ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) r).state ≠ some 3) := by
  have length_bound : p + t + (2 * u.length + 2) ≤ z.length := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    omega
  dsimp only
  induction u generalizing t with
  | nil =>
    have hz' : z.drop (p + t) = false :: true :: v := by
      simpa only [pairEncode_eq, List.flatMap_nil, List.nil_append,
        List.cons_append] using hz
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, and_self, ↓reduceIte]
      using up_scan_pair i d p t hp false true v hz'
  | cons b u ih =>
    have hz' : z.drop (p + t) = b :: b :: pairEncode u v := by
      simpa only [pairEncode_eq, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hz
    have pair := up_scan_pair i d p t hp b b (pairEncode u v) hz'
    have hpair : (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 2 =
        headerScanCfg i d 0 (t + 2) (by omega) := by
      cases b <;> simpa only [Bool.false_eq_true, Bool.true_eq_false,
        false_and, and_false, ↓reduceIte] using pair.1
    have suffix : z.drop (p + (t + 2)) = pairEncode u v := by
      rw [show p + (t + 2) = (p + t) + 2 by omega, ← List.drop_drop, hz']
      rfl
    have tail := ih (t + 2) suffix (by simp only [List.length_cons] at length_bound; omega)
    have duration : 2 * (b :: u).length + 2 = 2 + (2 * u.length + 2) := by
      simp only [List.length_cons]
      omega
    constructor
    · calc
        _ = (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega))
            (2 + (2 * u.length + 2)) := congrArg _ duration
        _ = headerScanCfg i d 3 (t + 2 + (2 * u.length + 2)) (by omega) := by
          rw [MultiTapeTM.runFrom_add, hpair, tail.1]
        _ = _ := by congr 1; omega
    · intro r hr
      by_cases hsmall : r < 2
      · exact pair.2 r hsmall
      · have hr' : r - 2 < 2 * u.length + 2 := by omega
        rw [show r = 2 + (r - 2) by omega, MultiTapeTM.runFrom_add, hpair]
        exact tail.2 (r - 2) hr'

/-- **The header scan's contract, from any input offset**: let `d` be at control `0` with its
input head at cell `1 + p` of `z`, where `z.drop p = pairEncode u v`. Then
`Turing.headerScanTM i` run from `d` is after exactly `2|u| + 2` steps at
`Turing.headerScanCfg i d 3 (2|u| + 2)` (the header's cells read and the same number of cells
`true` on tape `i` from its head, both heads just past them), it does not reach the control `3`
earlier, and its output is `d`'s throughout. The painted interval overwrites its old contents and
every cell outside it is preserved, so consecutive scans write one ruler for consecutive headers
(`Turing.headerScanCfg_ruler`). [AB09, §1.4.1, the proof of Theorem 1.9; the pair encoding of
[AB09, §1.4]]

**Proof sketch.** Instantiate the header induction at time zero. The endpoint has
the original output; output-prefix monotonicity in both directions gives silence
at every intermediate time. -/
theorem headerScanTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v) :
    let hlen : d.inputPos.val + (2 * u.length + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom d (2 * u.length + 2) =
        headerScanCfg i d 3 (2 * u.length + 2) hlen ∧
      (∀ t < 2 * u.length + 2, ((headerScanTM i).runFrom d t).state ≠ some 3) ∧
      (∀ t ≤ 2 * u.length + 2, ((headerScanTM i).runFrom d t).output = d.output) := by
  have hz' : z.drop (p + 0) = pairEncode u v := by simpa only [Nat.add_zero] using hz
  have h := up_scan_header i d p hp u v 0 hz'
  simp only [Nat.zero_add, up_scan_zero i d hd] at h
  refine ⟨h.1, h.2, ?_⟩
  intro t ht
  have hle := MultiTapeTM.output_prefix (headerScanTM i) d ht
  have hge := MultiTapeTM.output_prefix (headerScanTM i) d (Nat.zero_le t)
  rw [h.1] at hle
  rw [MultiTapeTM.runFrom_zero] at hge
  exact hle.eq_of_length_le hge.length_le

/-- **The header scan extends a ruler**: if tape `i` of `d` holds exactly the ruler `true^m`
ending just before its head (cells `[pos - m, pos)` `true`, every other cell blank, `pos` the
head), then in `Turing.headerScanCfg i d q t` it holds exactly `true^(m + t)` from the same
first cell `pos - m`: as a unary buffer, `bufferTape (true^(m + t))` read from `pos - m`.
[AB09, §1.4.1]

*Generalization.* The private form assumed a blank tape `i` and read the buffer from `pos`; that
is the case `m = 0` (the hypothesis then says the tape is blank, since `bufferTape [] = none`, and
the conclusion is the old one up to `Nat.cast_zero`, `sub_zero` and `zero_add`). For two
consecutive headers of lengths `ℓ₁` and `ℓ₂` the first scan's conclusion (`m = 0`) is the second
scan's hypothesis at `m = ℓ₁`, because the head has moved to `pos + ℓ₁`; the two give
`true^(ℓ₁ + ℓ₂)`.

**Proof sketch.** Read both buffers through their public equation and the scanned tape through
its field equation. A cell in the painted interval is offset `m ≤ a < m + t` from the ruler's
start, hence inside the longer ruler. Any other cell keeps its old value: inside the old ruler
(`0 ≤ a < m`) it is `true` in both rulers, and outside both rulers it is blank. -/
theorem headerScanCfg_ruler {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (m : ℕ)
    (hpre : ∀ a : ℤ, d.workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate m true) a) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate (m + t) true) a := by
  intro a
  have h := hpre a
  simp only [headerScanCfg_workTapes, Function.update_self]
  rw [FinTM.bufferTape_eq] at h ⊢
  by_cases hin : d.workTapePos i ≤ d.workTapePos i - (m : ℤ) + a ∧
      d.workTapePos i - (m : ℤ) + a < d.workTapePos i + t
  · rw [if_pos hin, if_pos (show 0 ≤ a by omega), List.getElem?_replicate,
      if_pos (show a.toNat < m + t by omega)]
  · rw [if_neg hin, h]
    by_cases ha : 0 ≤ a
    · rw [if_pos ha, if_pos ha, List.getElem?_replicate, List.getElem?_replicate]
      by_cases ham : a < m
      · rw [if_pos (show a.toNat < m by omega), if_pos (show a.toNat < m + t by omega)]
      · rw [if_neg (show ¬a.toNat < m by omega), if_neg (show ¬a.toNat < m + t by omega)]
    · rw [if_neg ha, if_neg ha]

/-- On an initially blank ruler tape, the marked interval is the standard unary buffer: the
case `m = 0` of `Turing.headerScanCfg_ruler`. -/
private theorem up_scan_ruler_blank {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (hblank : ∀ a, d.workTapes i a = none) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i + a) =
      FinTM.bufferTape (List.replicate t true) a := by
  intro a
  have h := headerScanCfg_ruler i d q t ht 0 (fun b => by
    rw [hblank, List.replicate_zero, FinTM.bufferTape_eq, List.getElem?_nil, ite_self]) a
  simpa only [Nat.cast_zero, sub_zero, Nat.zero_add] using h

/-- **The header ruler machine**: `Turing.headerScanTM i` followed, at its exit `3`, by the
work-tape rewind `Turing.rewindTM k i` of tape `i` (`Turing.seamCompTM`), started at the scan's
control `0`. It reads one doubled header and leaves the ruler `true^(2|u| + 2)` on tape `i` with
that head back at the ruler's first cell. Read through `Turing.headerRulerTM_run`. [AB09,
§1.4.1] -/
def headerRulerTM {k : ℕ} (i : Fin k) :
    MultiTapeTM k Bool (Fin 4 ⊕ RewindPhase) :=
  { seamCompTM (headerScanTM i) 3 (rewindTM k i) .start with q₀ := Sum.inl 0 }

/-- **The header ruler's contract**: let `d` be at control `0` with its input head at cell
`1 + p` of `z`, where `z.drop p = pairEncode u v`, and tape `i` blank. With `ℓ = 2|u| + 2`,
`Turing.headerRulerTM i` run from `d` (control relabelled by `Sum.inl`) is after exactly
`2ℓ + 3` steps at the rewind's `done`, with the input head `ℓ` cells further, tape `i` holding the
ruler `true^ℓ` from its head's original cell, every head (that of tape `i` included) and every
other tape as in `d`, and `d`'s output; and it does not reach `done` earlier. [AB09, §1.4.1]

**Proof sketch.** The scan writes the unary buffer and ends immediately after it.
Its buffer equation supplies the framed rewind's hypothesis. The public seam
combines their exact runs and first-return cuts; its endpoint resets just the
ruler head, which restores the original vector of heads. -/
theorem headerRulerTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v)
    (hblank : ∀ a, d.workTapes i a = none) :
    let ℓ := 2 * u.length + 2
    let hlen : d.inputPos.val + ℓ < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    let e : Cfg k Bool (Fin 4 ⊕ RewindPhase) z :=
      ⟨some (Sum.inr .done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩
    (headerRulerTM i).runFrom (d.mapState Sum.inl) (2 * ℓ + 3) = e ∧
      (∀ t < 2 * ℓ + 3,
        ((headerRulerTM i).runFrom (d.mapState Sum.inl) t).state ≠ some (Sum.inr .done)) := by
  dsimp only
  let ℓ := 2 * u.length + 2
  have hlen : d.inputPos.val + ℓ < z.length + 2 := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    dsimp only [ℓ]; omega
  let c := headerScanCfg i d 3 ℓ hlen
  obtain ⟨hscan, hcut, _⟩ := headerScanTM_run i d p hp hd u v hz
  have hrewind := rewindTM_run_ofCfg i (List.replicate ℓ true) ℓ
    (by rw [List.length_replicate]) (c.mapState fun _ => RewindPhase.start)
    (by rw [Cfg.mapState_state]; rfl) (by
      intro a _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank a
      simpa only [c, headerScanCfg, Function.update_self, add_sub_cancel_right] using hh)
  let r : Cfg k Bool RewindPhase z :=
    { c.mapState (fun _ => RewindPhase.start) with
      state := some .done
      workTapePos := Function.update (c.mapState (fun _ => RewindPhase.start)).workTapePos i
        ((c.mapState (fun _ => RewindPhase.start)).workTapePos i - ℓ) }
  have endpoint : r.mapState Sum.inr =
      (⟨some (Sum.inr RewindPhase.done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩ : Cfg k Bool (Fin 4 ⊕ RewindPhase) z) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
    · funext j a
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hj : j = i
      · subst j
        have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank (a - d.workTapePos i)
        simpa only [add_sub_cancel, Function.update_self] using hh
      · simp only [c, headerScanCfg, Function.update_of_ne hj]
    · funext j
      rw [Cfg.mapState_workTapePos]
      by_cases hj : j = i
      · subst j
        simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg,
          Function.update_self, add_sub_cancel_right]
      · simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg, Function.update_of_ne hj]
    · rw [Cfg.mapState_output, Cfg.mapState_output]; rfl
  have total : 2 * ℓ + 3 = ℓ + 1 + (ℓ + 2) := by omega
  constructor
  · rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀, total]
    exact (seamCompTM_run_ofCfg (headerScanTM i) 3 (rewindTM k i) .start
      hscan rfl hcut hrewind.1).trans endpoint
  · intro t ht
    rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg (headerScanTM i) 3 (rewindTM k i) .start .done
      hscan rfl hcut hrewind.1 rfl hrewind.2.1 t (by omega)

/-! ## The suffix-ruler layout -/

/-- **The suffix-ruler seam layout**: on `K + (k + 3)` work tapes over the input `z`, the
configuration at control `q` with the input head at cell `ℓ + 1` (just past a header of length
`ℓ`), the table bits `tableBitsK M.tr` on tape `k`, the unary initial state `unaryFin M.q₀` from
cell `2` on tape `k + 1`, the ruler `true^ℓ` on tape `k + 2`, every other tape blank, every head
at `0` and an empty output. It is where a startup and header scans leave the machine before the
ruler host runs the forwarding loop on the suffix `z.drop ℓ` (`Turing.suffixRulerCfg_embed`).
[AB09, §1.4.1, the proof of Theorem 1.9] -/
def suffixRulerCfg {k K n : ℕ} {P : Type} (q : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool) (ℓ : ℕ)
    (hℓ : ℓ + 1 < z.length + 2) : Cfg (K + (k + 3)) Bool P z :=
  ⟨some q, ⟨ℓ + 1, hℓ⟩,
    fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
      else if j.val = k + 2 then FinTM.bufferTape (List.replicate ℓ true)
      else fun _ => none,
    fun _ => 0, []⟩

/-! The suffix-ruler layout's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.suffixRulerCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  suffixRulerCfg

/-- **The ruler host's presentation, its fields**: in `Turing.rulerHostCfg ℓ hz q c rt rp` the
physical input head is at `ℓ` plus `c`'s, the last tape is the ruler `rt` with its head at `rp`,
the first `m` tapes are `c`'s, and the output is `c`'s. [AB09, §1.2, Exercise 4.1: a machine run
on a suffix of its input] -/
theorem rulerHostCfg_fields {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool)
    (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).inputPos.val = ℓ + c.inputPos.val ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapes (Fin.last m) = rt ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapePos (Fin.last m) = rp ∧
      (∀ i : Fin m, (rulerHostCfg ℓ hz q c rt rp).workTapes i.castSucc = c.workTapes i) ∧
      (rulerHostCfg ℓ hz q c rt rp).output = c.output := by
  refine ⟨by rw [rulerHostCfg_inputPos], ?_, ?_, fun i => ?_, rulerHostCfg_output _ _ _ _ _ _⟩
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_last]
  · rw [rulerHostCfg_workTapePos, Fin.lastCases_last]
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc]

/-- **The suffix-ruler layout is the embedded ruler-host start**: let `z` have length
`ℓ + |x|`. Present H2-F's encoding `c` of `M`'s initial configuration on the suffix `x` through
the ruler host's layout `Turing.rulerHostCfg` (control `inj q false` for `c`'s control `q`, the
ruler `true^ℓ` with its head at `0`) and embed it in the first `k + 3` of `K + (k + 3)` tapes (the
others blank with their heads at `0`, no prior output). The result is
`Turing.suffixRulerCfg exit M z ℓ` with its control relabelled to `inj entry false`. So it is the
seam hypothesis of `Turing.startupLoopTM_runFrom` and `Turing.startupLoopTM_spaceUsed_le` at
`(K, k + 1)` for a startup ending at the suffix-ruler layout. [AB09, §1.4.1, the proof of
Theorem 1.9]

**Proof sketch.** Reconstruct the embedding from its public field equations. Its
first bank is the initial forwarding-loop encoding, its last tape is the ruler,
and all unselected tapes are blank. The encoded input head is one, so the
physical head is exactly one cell after the header and its virtual-zero tag is false. -/
theorem suffixRulerCfg_embed {k K n : ℕ} {P Q H : Type} {x z : List Bool}
    (exit : P) (entry : Q) (inj : Q → Bool → H) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (ℓ : ℕ) (hz : z.length = ℓ + x.length) (hlen : ℓ + 1 < z.length + 2) :
    let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
    embedEmitCfg (Fin.castLEEmb (by omega : k + 3 ≤ K + (k + 3)))
      (fun _ _ => none) (fun _ => 0) []
      (rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c
        (FinTM.bufferTape (List.replicate ℓ true)) 0) =
      (suffixRulerCfg (K := K) exit M z ℓ hlen).mapState (fun _ => inj entry false) := by
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  have fields := StepBlock.forwardLoopCfg_init_fields entry M x
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  have host := rulerHostCfg_fields ℓ hz (c.state.map fun q => inj q false) c rt 0
  apply embedEmitCfg_eq
  · rw [rulerHostCfg_state, fields.1, Option.map_some, Cfg.mapState_state]
    rfl
  · apply Fin.ext
    rw [host.1, Cfg.mapState_inputPos]
    change ℓ + c.inputPos.val = ℓ + 1
    rw [fields.2.1]
  · rw [List.nil_append, rulerHostCfg_output, fields.2.2.2, Cfg.mapState_output]
    rfl
  · intro j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_last, Cfg.mapState_workTapes]
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.val_last,
          if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_last, Cfg.mapState_workTapePos]
        rfl
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc, Cfg.mapState_workTapes,
          StepBlock.forwardLoopCfg_init_workTapes]
        have ha : a.val ≠ k + 2 := by omega
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.coe_castSucc, if_neg ha]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_castSucc, Cfg.mapState_workTapePos,
          fields.2.2.1 a]
        rfl
  · intro j hj
    have hjge : k + 3 ≤ j.val := by
      by_contra h
      apply hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      apply Fin.ext; rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      simp only [suffixRulerCfg, if_neg (by omega : j.val ≠ k),
        if_neg (by omega : j.val ≠ k + 1), if_neg (by omega : j.val ≠ k + 2)]
    · rw [Cfg.mapState_workTapePos]
      rfl

/-! ## Seal controls (each closes unsealed and fails sealed) -/
example {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) : (StepBlock.forwardLoopCfg entry M c).output = c.output :=
  rfl
example {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ) (hz : z.length = ℓ + y.length)
    (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool) (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).output = c.output := rfl
example {k : ℕ} {S : Type} (M : MultiTapeTM k Bool S) (x : List Bool) :
    M.initCfg x = Cfg.init M.q₀ x := rfl
example {k : ℕ} {S : Type} (q : S) (x : List Bool) :
    (Cfg.init (k := k) (Symbol := Bool) q x).output = [] := rfl
example : FinTM.bufferTape [true] 0 = some true := rfl
example (w : List Bool) : StepBlock.summaryCells none w 0 = none := rfl
example {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1))) :
    tableBitsK tr = (List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK k).flatMap fun w => actionBitsK (tr q inp w) := rfl
example : unaryFin (0 : Fin 1) = [false] := rfl
example {k m : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin k) (c : Cfg m Bool S x) :
    (embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] c).output = [] ++ c.output := rfl
example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) :
    (c.mapState fun _ => ()).output = c.output := rfl
example : pairEncode [] [] = [false, true] := rfl
example : (rewindTM (Symbol := Bool) 1 0).q₀ = .start := rfl
example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (en : S₂) : (seamCompTM M₁ e M₂ en).q₀ = Sum.inl M₁.q₀ := rfl
example {k m : ℕ} {S : Type} (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    (embedEmitTM ι M).q₀ = M.q₀ := rfl
example : tapeAction (k := 1) (Symbol := Bool) (State := Unit) 0 .pos none .pos () =
    ⟨.pos, fun j => if j = 0 then (none, .pos) else (none, 0), none, some ()⟩ := rfl
example : inputMoveAction (k := 1) (Symbol := Bool) (State := Unit) 0 () =
    ⟨0, fun _ => (none, 0), none, some ()⟩ := rfl

end Turing

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealParts.out =====

Scratch/SealParts.lean:985:2: error: Type mismatch
  rfl
has type
  ?m.27 = ?m.27
but is expected to have type
  (StepBlock.forwardLoopCfg entry M c).output = c.output
Scratch/SealParts.lean:988:55: error: Type mismatch
  rfl
has type
  ?m.23 = ?m.23
but is expected to have type
  (rulerHostCfg ℓ hz q c rt rp).output = c.output
Scratch/SealParts.lean:990:37: error: Type mismatch
  rfl
has type
  ?m.12 = ?m.12
but is expected to have type
  MultiTapeTM.initCfg x = Cfg.init M.q₀ x
Scratch/SealParts.lean:992:60: error: Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  (Cfg.init q x).output = []
Scratch/SealParts.lean:993:51: error: Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  FinTM.bufferTape [true] 0 = some true
Scratch/SealParts.lean:994:68: error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  StepBlock.summaryCells none w 0 = none
Scratch/SealParts.lean:999:68: error: Type mismatch
  rfl
has type
  ?m.43 = ?m.43
but is expected to have type
  tableBitsK tr =
    List.flatMap
      (fun q =>
        List.flatMap (fun inp => List.flatMap (fun w => actionBitsK (tr q inp w)) (workReadsK k))
          [none, some false, some true])
      (List.finRange (n + 1))
Scratch/SealParts.lean:1000:44: error: Type mismatch
  rfl
has type
  ?m.10 = ?m.10
but is expected to have type
  unaryFin 0 = [false]
Scratch/SealParts.lean:1002:84: error: Type mismatch
  rfl
has type
  ?m.31 = ?m.31
but is expected to have type
  (embedEmitCfg ι (fun x x_1 => none) (fun x => 0) [] c).output = [] ++ c.output
Scratch/SealParts.lean:1004:50: error: Type mismatch
  rfl
has type
  ?m.17 = ?m.17
but is expected to have type
  (Cfg.mapState (fun x => ()) c).output = c.output
Scratch/SealParts.lean:1005:46: error: Type mismatch
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  pairEncode [] [] = [false, true]
Scratch/SealParts.lean:1006:57: error: Type mismatch
  rfl
has type
  ?m.12 = ?m.12
but is expected to have type
  (rewindTM 1 0).q₀ = RewindPhase.start
Scratch/SealParts.lean:1008:91: error: Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  (seamCompTM M₁ e M₂ en).q₀ = Sum.inl M₁.q₀
Scratch/SealParts.lean:1010:35: error: Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  (embedEmitTM ι M).q₀ = M.q₀
Scratch/SealParts.lean:1012:81: error: Type mismatch
  rfl
has type
  ?m.30 = ?m.30
but is expected to have type
  tapeAction 0 SignType.pos none SignType.pos () =
    { inputTape := SignType.pos, workTapes := fun j => if j = 0 then (none, SignType.pos) else (none, 0),
      output := none, state := some () }
Scratch/SealParts.lean:1014:46: error: Type mismatch
  rfl
has type
  ?m.22 = ?m.22
but is expected to have type
  inputMoveAction 0 () = { inputTape := 0, workTapes := fun x => (none, 0), output := none, state := some () }
exit=1 4s

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealParts0.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.Rewind
import Mathlib.Algebra.Group.Action.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parts of the `k`-generic universal machines

[AB09, §1.4.1 and the proof of Theorem 1.9]: the pieces that the `k`-generic universal machines
of `TuringMachine/UniversalK.lean` (U2) are assembled from, published so that a second consumer
(the space-universal machine `Complexity.space_universal`, [AB09, Exercise 4.1]) composes them
instead of re-deriving them. Harvested from `UniversalK`'s privates (the U2 harvest API, user
ruling of 2026-11-06: a new `Build/` module; plan `campaign/items/roadmap3/PLAN.md`, §F6(c)).

* **The forwarding loop at an initial configuration.** H2-F's encoding
  `Turing.StepBlock.forwardLoopCfg` of a machine's initial configuration (its tapes, fields and
  halting), its embedding at the startup's endpoint, and the three readings of H2-F's lockstep
  used by both universal machines: the forward time bound to the first halt, liveness forever,
  and the converse on outputs.
* **The startup–loop seam.** `Turing.startupLoopTM`: a startup on `K + (k + 2)` tapes followed,
  at its exit, by a loop on the first `k + 2`; its start, its live prefix, its run after the
  seam from any seam endpoint, and its space ledger from any seam endpoint.
* **The header ruler.** `Turing.headerScanTM`: a finite-state scan of one doubled header
  `pairEncode u v`, from any input offset, writing one ruler cell per input cell; from an
  existing ruler prefix `true^m` it extends the ruler to `true^(m + 2|u| + 2)`, so consecutive
  headers give one ruler. `Turing.headerRulerTM`: the scan followed by the rewind.
* **The suffix-ruler layout.** `Turing.suffixRulerCfg`: the simulation bank, then the ruler
  `true^ℓ`, with the input head just past a header of length `ℓ`; it is the embedding of the
  ruler host's initial presentation (`Turing.rulerHostCfg`) of the forwarding loop's start.

## Main definitions

* `Turing.startupLoopTM` — the startup followed by the embedded loop.
* `Turing.headerScanTM`, `Turing.headerScanCfg` — the header scan and its presentation after
  `t` marks (with field equations).
* `Turing.headerRulerTM` — the header scan followed by the work-tape rewind.
* `Turing.suffixRulerCfg` — the suffix-ruler seam layout (with field equations).

## Main results

* `Turing.MultiTapeTM.initCfg_eq_mapState` — the restart identity (ledger RS-1's general form).
* `Turing.StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`,
  `Turing.embedEmitCfg_forwardLoop_init` — the forwarding loop's encoding at the start.
* `Turing.StepBlock.forwardLoop_forward`, `_live`, `_converse` — the lockstep's readings.
* `Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom`, `_spaceUsed_le` — the seam.
* `Turing.headerScanTM_run`, `Turing.headerScanCfg_ruler`, `Turing.headerRulerTM_run` — the
  header ruler.
* `Turing.rulerHostCfg_fields`, `Turing.suffixRulerCfg_embed` — the suffix-ruler layout.

All proved. The generalizations against the private forms are `startupLoopTM_spaceUsed_le` (any
seam endpoint, not only the native startup's) and `headerScanCfg_ruler` (from a ruler prefix
`true^m`, not only a blank tape); every other row is the private statement, renamed.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9 and its proof: the universal machine
  reads the code and simulates `M` step by step on a work-tape copy of its table; Exercise 4.1,
  the space-bounded universal machine.)
-/

namespace Turing

/-! ## The restart identity -/

/-- **The restart identity**: if a machine `B`'s initial state is the image `f A.q₀` of
another machine `A`'s, then `B`'s initial configuration on any input is `A`'s with its state
relabelled by `f`. Ledger RS-1's general form (`campaign/duplication-ledger.md`). [AB09, §1.4.1]
(glue for the universal machine's composed startups). -/
theorem MultiTapeTM.initCfg_eq_mapState {m : ℕ} {P Q : Type}
    (A : MultiTapeTM m Bool P) (B : MultiTapeTM m Bool Q) (f : P → Q)
    (hq : B.q₀ = f A.q₀) (x : List Bool) : B.initCfg x = (A.initCfg x).mapState f := by
  refine Cfg.ext ?_ ?_ (funext fun j => funext fun a => ?_) (funext fun j => ?_) ?_
  all_goals
    simp only [MultiTapeTM.initCfg_eq, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
      Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes, Cfg.init_workTapePos,
      Cfg.init_output, Option.map_some, hq]

/-! ## The forwarding loop at an initial configuration -/

/-- **The forwarding loop's encoding of an initial configuration, its tapes**: H2-F's
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` of a `k`-tape binary machine's
initial configuration has, on its `k + 2` tapes, the table bits `tableBitsK M.tr` as a buffer on
tape `k`, the unary initial state `unaryFin M.q₀` from cell `2` on tape `k + 1` (cells `0` and
`1` blank), and blank mirrored tapes `0, …, k - 1`. This is the layout the universal machines'
startups install. [AB09, §1.4.1, the proof of Theorem 1.9: the work-tape copy of `M`'s table
and its current state]

**Proof sketch.** Split the tape index into a mirrored tape and one of the two
auxiliary tapes. The initial mirrored tapes are blank; the table is unchanged,
and the summary agrees cell by cell, including its blank cell at zero. -/
theorem StepBlock.forwardLoopCfg_init_workTapes {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) (j : Fin (k + 2)) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
      else fun _ => none := by
  have hw : (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      Fin.addCases (motive := fun _ => ℤ → Option Bool) (M.initCfg x).workTapes (fun j =>
        if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
        else StepBlock.summaryCells none (((M.initCfg x).state.map unaryFin).getD [])) j :=
    funext fun a => StepBlock.forwardLoopCfg_workTapes entry M (M.initCfg x) j a
  rw [hw]
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq]
    have h1 : (Fin.castAdd 2 i).val ≠ k := by simp only [Fin.coe_castAdd]; omega
    have h2 : (Fin.castAdd 2 i).val ≠ k + 1 := by simp only [Fin.coe_castAdd]; omega
    rw [if_neg h1, if_neg h2]
    funext p
    rw [Cfg.init_workTapes]
  · rw [Fin.addCases_right, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some,
      Option.getD_some]
    by_cases h : j' = 0
    · subst h
      have h1 : (Fin.natAdd k (0 : Fin 2)).val = k := by simp only [Fin.coe_natAdd]; omega
      rw [if_pos rfl, if_pos h1]
    · have hj : j' = 1 := by omega
      subst hj
      have h1 : (Fin.natAdd k (1 : Fin 2)).val ≠ k := by simp only [Fin.coe_natAdd]; omega
      have h2 : (Fin.natAdd k (1 : Fin 2)).val = k + 1 := by simp only [Fin.coe_natAdd]; omega
      rw [if_neg (by decide), if_neg h1, if_pos h2]
      funext p
      rw [StepBlock.summaryCells_eq]
      by_cases hp : p = 0
      · rw [if_pos hp, hp]
        exact (FinTM.bufferTape_of_neg _ (by omega)).symm
      · rw [if_neg hp]

/-- **The forwarding loop's encoding of an initial configuration, its other fields**: the
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` is at the control `entry`, with
input head at cell `1`, every work head at `0` and an empty output. [AB09, §1.4.1, the proof of
Theorem 1.9] -/
theorem StepBlock.forwardLoopCfg_init_fields {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).state = some entry ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).inputPos.val = 1 ∧
      (∀ j, (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapePos j = 0) ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).output = [] := by
  refine ⟨?_, ?_, fun j => ?_, ?_⟩
  · rw [StepBlock.forwardLoopCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  · rw [StepBlock.forwardLoopCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  · rw [StepBlock.forwardLoopCfg_workTapePos]
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    · rw [Fin.addCases_right]
  · rw [StepBlock.forwardLoopCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output]

/-- **The forwarding loop's encoding halts with its source**: for any configuration `c` of a
`k`-tape binary machine, the encoding `Turing.StepBlock.forwardLoopCfg entry M c` is halted
exactly when `c` is, and its output is `c`'s. Stated as the conjunction of the iff and the output
equation. [AB09, §1.4.1, the proof of Theorem 1.9: the universal machine halts with `M`'s
output] -/
theorem StepBlock.forwardLoopCfg_halt_iff {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    ((StepBlock.forwardLoopCfg entry M c).state = none ↔ c.state = none) ∧
      (StepBlock.forwardLoopCfg entry M c).output = c.output := by
  rw [StepBlock.forwardLoopCfg_state, StepBlock.forwardLoopCfg_output, Option.map_eq_none_iff]
  exact ⟨Iff.rfl, rfl⟩

/-- **The startup's native endpoint is the embedded initial encoding**: embedding the
forwarding loop's encoding of `M`'s initial configuration on `x` in the first `k + 2` of
`K + (k + 2)` tapes (the other tapes blank with their heads at `0`, no prior output) gives the
configuration at the control `exit`, input head `1`, the table on tape `k`, the unary initial
state from cell `2` on tape `k + 1`, every other tape blank, every head at `0` and an empty
output, with its control relabelled to `entry`. This is the endpoint of the startup
`Turing.exists_selfStartupTMK`, hence the seam hypothesis of `Turing.startupLoopTM_runFrom` for
the native layout. [AB09, §1.4.1, the proof of Theorem 1.9]

**Proof sketch.** Use the public reconstruction theorem for the emitting embedding.
The selected tapes and heads are the initial encoding's fields. An unselected
tape has index at least `k + 2`, so both tests in the startup layout are false. -/
theorem embedEmitCfg_forwardLoop_init {k n K : ℕ} {P Q : Type} (exit : P) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
      (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)) =
        (⟨some exit, 1,
          fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
            else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
            else fun _ => none,
          fun _ => 0, []⟩ : Cfg (K + (k + 2)) Bool P x).mapState (fun _ => entry) := by
  apply embedEmitCfg_eq
  · rw [Cfg.mapState_state]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).1
  · apply Fin.ext
    rw [Cfg.mapState_inputPos]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.1
  · rw [List.nil_append, Cfg.mapState_output]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.2
  · intro i
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      exact congrFun (StepBlock.forwardLoopCfg_init_workTapes entry M x i) a
    · rw [Cfg.mapState_workTapePos]
      exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.1 i
  · intro j hj
    have hjge : k + 2 ≤ j.val := by
      by_contra h
      have hlt : j.val < k + 2 := by omega
      apply hj
      refine ⟨⟨j.val, hlt⟩, ?_⟩
      apply Fin.ext
      rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      dsimp only
      rw [if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
    · rw [Cfg.mapState_workTapePos]

/-- **The forwarding loop's forward time bound**: let `L` simulate a `k`-tape binary machine
`M` in macro-step lockstep over H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M`
(the `Turing.Lockstep` of `Turing.StepBlock.exists_forwardLoopTM`), with every live step's cost
at most `D`. If `M` has halted on `x` by time `t`, there is its first halting time `t₀ ≤ t`
(live before `t₀`) such that the simulated time `Σ_{u < t₀} cost` is at most `D · t` and `L`,
started at the encoding of `M`'s initial configuration, is after that many steps at the
encoding of `M`'s configuration at time `t`. [AB09, §1.4.1, the proof of Theorem 1.9: each
step of `M` costs the universal machine a number of steps depending on `M` only]

**Proof sketch.** Choose the first source halt. The lockstep applies up to that
time, and each summand in its simulated time is bounded by the per-step bound.
Absorption identifies the first halted configuration with the given final one. -/
theorem StepBlock.forwardLoop_forward {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → cost c ≤ D) (t : ℕ)
    (hhalt : (M.runFrom (M.initCfg x) t).state = none) :
    ∃ t₀ ≤ t, (∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none) ∧
      (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) ≤ D * t ∧
      L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) =
        StepBlock.forwardLoopCfg entry M (M.runFrom (M.initCfg x) t) := by
  obtain ⟨t₀, hle, hfirst, hsame⟩ := MultiTapeTM.exists_first_halt M (M.initCfg x) hhalt
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
  · calc
      _ ≤ ∑ _u ∈ Finset.range t₀, D := Finset.sum_le_sum fun u hu =>
        hcost _ (hfirst u (Finset.mem_range.mp hu))
      _ = D * t₀ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ D * t := Nat.mul_le_mul_left D hle
  · rw [hlock.runFrom (M.initCfg x) t₀ (by
      simpa only [Set.mem_singleton_iff] using hfirst), hsame]

/-- **The forwarding loop diverges with its source**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` with positive costs at live configurations, if `M`
never halts on `x`, then `L` started at the encoding of `M`'s initial configuration is live at
every time. [AB09, §1.4.1, Theorem 1.9: the universal machine diverges when `M` does]

**Proof sketch.** For a target time `v`, simulate `v + 1` source steps. Every
cost is positive, so their sum exceeds `v`; the lockstep cut gives liveness. -/
theorem StepBlock.forwardLoop_live {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hpos : ∀ c, c.state ≠ none → 0 < cost c)
    (hlive : ∀ u, (M.runFrom (M.initCfg x) u).state ≠ none) (v : ℕ) :
    (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state ≠ none := by
  have hsum : v + 1 ≤ ∑ u ∈ Finset.range (v + 1), cost (M.runFrom (M.initCfg x) u) := by
    calc
      _ = ∑ _u ∈ Finset.range (v + 1), (1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum fun u _ => hpos _ (hlive u)
  have hcut := hlock.cut (M.initCfg x) (v + 1)
    (fun u _ => by simpa only [Set.mem_singleton_iff] using hlive u) v (by omega)
  simpa only [Set.mem_singleton_iff] using hcut

/-- **The forwarding loop's converse**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` whose costs at live configurations lie in `[1, D]`,
if `L` started at the encoding of `M`'s initial configuration on `x` has halted at time `u`,
then `M` has halted on `x` at some time `t`, with the same output as `L` at `u`. So every
completed output of the loop is a completed output of `M`. [AB09, §1.4.1, Theorem 1.9: the
universal machine's output is `M`'s]

**Proof sketch.** If the source never halted, positivity and the lockstep cut
would keep the loop live at the given time. Choose a source halt and apply the
forward lemma. The loop is now halted at both times, so its output agrees at
their maximum; the encoding preserves the source's output. -/
theorem StepBlock.forwardLoop_converse {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → 0 < cost c ∧ cost c ≤ D) (u : ℕ)
    (hhalt : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).state = none) :
    ∃ t, (M.runFrom (M.initCfg x) t).state = none ∧
      (M.runFrom (M.initCfg x) t).output =
        (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).output := by
  classical
  have hex : ∃ t, (M.runFrom (M.initCfg x) t).state = none := by
    by_contra h
    have hsource : ∀ t, (M.runFrom (M.initCfg x) t).state ≠ none :=
      fun t ht => h ⟨t, ht⟩
    exact (StepBlock.forwardLoop_live M L entry cost hlock (fun c hc => (hcost c hc).1)
      hsource u) hhalt
  obtain ⟨t, ht⟩ := hex
  obtain ⟨t₀, _, _, _, hr⟩ :=
    StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t ht
  let v := ∑ i ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) i)
  have hv : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state = none := by
    rw [hr]
    exact (StepBlock.forwardLoopCfg_halt_iff entry M _).1.mpr ht
  refine ⟨t, ht, ?_⟩
  calc
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).output := by
      rw [hr, (StepBlock.forwardLoopCfg_halt_iff entry M _).2]
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) (max u v)).output :=
      (MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_right u v) hv).symm
    _ = _ := MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_left u v) hhalt
/-! ## The startup–loop seam -/

/-- **The startup–loop seam machine**: a startup `R` on `K + (k + 2)` work tapes, followed at
its exit control `exit` by the loop `L` on the first `k + 2` of them, entered at `entry`
(`Turing.seamCompTM` of `R` and the emitting embedding `Turing.embedEmitTM` of `L` along
`Fin.castLEEmb`, the other tapes untouched), started in `R`'s initial control. Read through
`Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom` and `_spaceUsed_le`. [AB09, §1.4.1,
the proof of Theorem 1.9: the universal machine first prepares its work tapes, then simulates]
-/
noncomputable def startupLoopTM {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) :
    MultiTapeTM (K + (k + 2)) Bool (P ⊕ Q) :=
  { seamCompTM R exit
      (embedEmitTM (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))) L) entry with
    q₀ := Sum.inl R.q₀ }

/-- **The seam machine's start**: on every input, `Turing.startupLoopTM R exit L entry` starts
in the startup's initial configuration, its control relabelled by `Sum.inl`. [AB09, §1.4.1] -/
theorem startupLoopTM_initCfg {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) (x : List Bool) :
    (startupLoopTM R exit L entry).initCfg x = (R.initCfg x).mapState Sum.inl := by
  exact MultiTapeTM.initCfg_eq_mapState R (startupLoopTM R exit L entry) Sum.inl rfl x

/-- **The seam machine is live through the startup**: if the startup `R` is live at time `T`
on `x` and does not reach `exit` before `T`, then `Turing.startupLoopTM R exit L entry` is live
on `x` at every time `t ≤ T`. [AB09, §1.4.1] -/
theorem startupLoopTM_live_of_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool} (T : ℕ)
    (hlive : (R.runFrom (R.initCfg x) T).state ≠ none)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    ((startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x) t).state ≠
      none := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_left R exit _ entry hcut t ht, Cfg.mapState_state]
  intro hh
  exact MultiTapeTM.runFrom_state_ne_none_of_le R (R.initCfg x) T hlive t ht
    (Option.map_eq_none_iff.mp hh)

/-- **The seam machine after the seam, from any seam endpoint**: suppose the startup `R`
reaches the configuration `d` on `x` at exactly time `T`, at the control `exit`, and not
earlier, and that `d` with its control replaced by `entry` is the embedding of a loop
configuration `c` in the first `k + 2` tapes (the others blank with their heads at `0`, no
prior output). Then for every `t`, `Turing.startupLoopTM R exit L entry` at time `T + 1 + t` is
the embedding of `L`'s run from `c` for `t` steps, with its control relabelled by `Sum.inr`. The
loop may be the native forwarding loop (`c` its encoding, `d` the startup's native endpoint,
`Turing.embedEmitCfg_forwardLoop_init`) or its suffix host (`c` the ruler host's presentation,
`d` the suffix-ruler layout, `Turing.suffixRulerCfg_embed`). [AB09, §1.4.1] -/
theorem startupLoopTM_runFrom {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c) (t : ℕ) :
    (startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) =
      (embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] (L.runFrom c t)).mapState Sum.inr := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_right R exit _ entry hrun hexit hcut t, hcfg, embedEmitTM_runFrom]

/-- **The seam machine's space ledger, from any seam endpoint**: under the seam hypotheses of
`Turing.startupLoopTM_runFrom` (the startup `R` reaches `d` on `x` at exactly `T`, at `exit`,
not earlier, and `d` relabelled at `entry` is the embedding of the loop configuration `c`), if
the startup uses at most `B` cells by `T` and the loop `L`, run from `c`, uses at most `S ≥ 1`
cells on each of its tapes by `t`, then `Turing.startupLoopTM R exit L entry` uses at most
`B + (K + (k + 2)) · S` cells on `x` by time `T + 1 + t`. [AB09, Exercise 4.1: the universal
machine's space is the simulated machine's up to a factor depending on the code]

*Generalization.* The private form fixed the native endpoint (`d` the startup's layout at input
position `1`, `c` the encoding of `M`'s initial configuration). It read that endpoint only
through its exit control and the embedding identity, now the hypotheses `hexit` and `hcfg`; at
the native endpoint they are `rfl` and `Turing.embedEmitCfg_forwardLoop_init`, which is the old
statement. At `(K, k + 1)`, `d` the suffix-ruler layout and `c` the ruler host's presentation
(`Turing.suffixRulerCfg_embed`) it is the ledger of the suffix layout.

**Proof sketch.** The seam's visited-set theorem bounds each tape by the union
of its startup and loop visits. A selected loop tape has the source loop's
visited set; an unselected tape visits just its initial cell. Count each union
and sum over the host's tapes, using the public space equations. -/
theorem startupLoopTM_spaceUsed_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c)
    (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
    (hloop : ∀ i, L.spaceUsedByTape c t i ≤ S) :
    (startupLoopTM R exit L entry).spaceUsed ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) ≤ B + (K + (k + 2)) * S := by
  classical
  let σ := Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))
  let A := embedEmitTM σ L
  let e := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] c
  have he : d.mapState (fun _ => entry) = e := hcfg
  have hA : ∀ j, A.spaceUsedByTape e t j ≤ S := by
    intro j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [(embedEmitTM_visitedByTapeHead σ L _ _ [] c t i).2]
      exact hloop i
    · rw [(embedEmitTM_visitedByTapeHead_frame σ L _ _ [] c t j hj).2]
      exact hS
  have htape (j : Fin (K + (k + 2))) :
      (startupLoopTM R exit L entry).spaceUsedByTape
          ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ≤
        R.spaceUsedByTape (R.initCfg x) T j + S := by
    rw [MultiTapeTM.spaceUsedByTape_eq_card]
    have hsub := seamCompTM_visitedByTapeHead_ofCfg R exit A entry
      (c₁ := d) (T₂ := t) hrun hexit hcut j
    rw [he] at hsub
    have hown : (startupLoopTM R exit L entry).visitedByTapeHead
        ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ⊆
        (seamCompTM R exit A entry).visitedByTapeHead
          ((R.initCfg x).mapState Sum.inl) (T + 1 + t) j := by
      intro p hp
      rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
      obtain ⟨u, hu, hp⟩ := hp
      refine ⟨u, hu, ?_⟩
      rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀] at hp
      exact hp
    calc
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j ∪ A.visitedByTapeHead e t j).card :=
        Finset.card_le_card (hown.trans hsub)
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j).card +
          (A.visitedByTapeHead e t j).card := Finset.card_union_le _ _
      _ = R.spaceUsedByTape (R.initCfg x) T j + A.spaceUsedByTape e t j := by
        rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      _ ≤ _ := Nat.add_le_add_left (hA j) _
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    _ ≤ ∑ j, (R.spaceUsedByTape (R.initCfg x) T j + S) :=
      Finset.sum_le_sum fun j _ => htape j
    _ = R.spaceUsed (R.initCfg x) T + (K + (k + 2)) * S := by
      rw [Finset.sum_add_distrib, ← MultiTapeTM.spaceUsed_eq_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right hB _

/-! ## The header scan and the header ruler -/

/-- **The header scan**: a finite-state machine on `k` work tapes that reads a doubled header
`pairEncode u v` (the bits of `u`, each written twice, then the separator `false, true`) in
aligned pairs from its input head, writing `true` on tape `i` and moving that head and the input
head right at every step, and stops at its control `3` just past the separator. States `0`, `1`
and `2` read a pair (`1` and `2` remember its first bit); `3` is the exit, where the machine idles.
So it writes one ruler cell per header cell. It is hand-built: no catalog row writes a ruler of a
doubled header's length. Read through `Turing.headerScanTM_run`. [AB09, §1.4.1, the proof of
Theorem 1.9: the universal machine reads the code at the start of its input; the pair encoding
of [AB09, §1.4]] -/
def headerScanTM {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Fin 4) where
  q₀ := 0
  tr := fun q b _ =>
    if q = 3 then inputMoveAction 0 3
    else tapeAction i .pos (some (some true)) .pos
      (if q = 0 then if b = some false then 1 else 2
       else if q = 1 ∧ b = some true then 3 else 0)

/-- **The header scan's presentation after `t` marks**: from a configuration `d`, the
configuration at control `q` with the input head and the head of tape `i` both `t` cells right
of `d`'s, the cells `[pos, pos + t)` of tape `i` (`pos` its head in `d`) set to `true` and every
other cell, tape, head and the output as in `d`. [AB09, §1.4.1] -/
def headerScanCfg {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : Cfg k Bool (Fin 4) z :=
  ⟨some q, ⟨d.inputPos.val + t, ht⟩,
    Function.update d.workTapes i
      (fun a => if d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        then some true else d.workTapes i a),
    Function.update d.workTapePos i (d.workTapePos i + t), d.output⟩

/-! The header scan's presentation's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.headerScanCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  headerScanCfg

/-- Zero scan steps leave the initial live configuration unchanged. -/
private theorem up_scan_zero {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (hd : d.state = some 0) :
    headerScanCfg i d 0 0 (by have := d.inputPos.isLt; omega) = d := by
  apply Cfg.ext
  · exact hd.symm
  · apply Fin.ext; simp only [headerScanCfg, Nat.add_zero]
  · funext j a
    simp only [headerScanCfg, Nat.cast_zero, add_zero]
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]
  · simp only [headerScanCfg, Nat.cast_zero, add_zero, Function.update_eq_self]
  · rfl

/-- One scan step writes and advances both heads, preserving every frame field.

**Proof sketch.** Read the transition with the public writing-action equation. Its
updated cell is exactly the new right endpoint of the already marked interval;
all other cells retain their previous value. -/
private theorem up_scan_step {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 1) (hq : q ≠ 3) (b : Bool)
    (hb : (headerScanCfg i d q t (by omega)).inputSymbol = some b) :
    (headerScanTM i).step (headerScanCfg i d q t (by omega)) =
      headerScanCfg i d
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) (t + 1) (by omega) := by
  have ht' : (headerScanTM i).tr q (headerScanCfg i d q t (by omega)).inputSymbol
      (headerScanCfg i d q t (by omega)).workTapeSymbols = tapeAction i .pos
        (some (some true)) .pos
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) := by
    simp only [headerScanTM, if_neg hq, hb, Option.some.injEq]
  rw [step_of_tapeAction_write _ _ i .pos (some true) .pos rfl ht']
  apply Cfg.ext
  · rfl
  · rw [moveInputPos_pos_of_ne_right _ (by simp only [headerScanCfg]; omega)]
    apply Fin.ext
    simp only [headerScanCfg]
    omega
  · funext j a
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one]
      by_cases ha : a = d.workTapePos i + t
      · subst a
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne ha]
        by_cases ha' : d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        · rw [if_pos ha', if_pos (by omega)]
        · rw [if_neg ha', if_neg (by omega)]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one,
        SignType.pos_eq_one, SignType.coe_one, add_assoc]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · rfl

/-- The scanner consumes one aligned pair, marking both input cells.

**Proof sketch.** The suffix equation gives the two input symbols through `getElem_drop`.
Apply the one-step result twice. The intermediate state stores the first bit,
and the second bit either returns on the separator or resumes the pair scan. -/
private theorem up_scan_pair {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p t : ℕ) (hp : d.inputPos.val = 1 + p)
    (a b : Bool) (rest : List Bool) (hz : z.drop (p + t) = a :: b :: rest) :
    let hlen : d.inputPos.val + (t + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      simp only [List.length_drop, List.length_cons] at h
      omega
    let c := headerScanCfg i d 0 t (by omega)
    (headerScanTM i).runFrom c 2 =
        headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) hlen ∧
      (∀ v < 2, ((headerScanTM i).runFrom c v).state ≠ some 3) := by
  have hlen : p + t + 2 ≤ z.length := by
    have h := congrArg List.length hz
    simp only [List.length_drop, List.length_cons] at h
    omega
  dsimp only
  have ha : z[p + t]'(by omega) = a := by
    have hh : (z.drop (p + t))[0]'(by rw [hz]; simp) = a := by
      simp only [hz, List.getElem_cons_zero]
    simpa only [List.getElem_drop, Nat.add_zero] using hh
  have hb : z[p + t + 1]'(by omega) = b := by
    have hh : (z.drop (p + t))[1]'(by rw [hz]; simp) = b := by
      simp only [hz, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa only [List.getElem_drop] using hh
  let q : Fin 4 := if a = false then 1 else 2
  have h1 : (headerScanTM i).step (headerScanCfg i d 0 t (by omega)) =
      headerScanCfg i d q (t + 1) (by omega) := by
    have read : (headerScanCfg i d 0 t (by omega)).inputSymbol = some a := by
      rw [inputSymbolInner (p + t) (by simp only [headerScanCfg]; omega) (by omega), ha]
    simpa only [if_pos rfl] using up_scan_step i d 0 t (by omega) (by decide) a read
  have h2 : (headerScanTM i).step (headerScanCfg i d q (t + 1) (by omega)) =
      headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) (by omega) := by
    have read : (headerScanCfg i d q (t + 1) (by omega)).inputSymbol = some b := by
      rw [inputSymbolInner (p + t + 1) (by simp only [headerScanCfg]; omega) (by omega), hb]
    have step := up_scan_step i d q (t + 1) (by omega)
      (by dsimp only [q]; split <;> decide) b read
    cases a <;> cases b <;> simpa only [q, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, and_self, and_false, false_and, true_and] using step
  have one (e : Cfg k Bool (Fin 4) z) :
      (headerScanTM i).runFrom e 1 = (headerScanTM i).step e := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  constructor
  · calc
      _ = (headerScanTM i).runFrom
          ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 1) 1 :=
        MultiTapeTM.runFrom_add _ 1 1
      _ = _ := by rw [one, one, h1, h2]
  · intro v hv
    have casesv : v = 0 ∨ v = 1 := by omega
    rcases casesv with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
      change some (0 : Fin 4) ≠ some 3
      decide
    · rw [one, h1]
      change some q ≠ some 3
      cases a <;> decide

/-- The scanner consumes one doubled header from any native input offset.

**Proof sketch.** Induct on the header word. Every doubled bit takes two steps
and returns to the pair-reading state; the separator takes two steps and returns.
The suffix equation is advanced with `drop_drop`, while the exact-time cut is
split before and after each pair. -/
private theorem up_scan_header {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (u v : List Bool) (t : ℕ) (hz : z.drop (p + t) = pairEncode u v) :
    let hlen : d.inputPos.val + (t + (2 * u.length + 2)) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) (2 * u.length + 2) =
        headerScanCfg i d 3 (t + (2 * u.length + 2)) hlen ∧
      (∀ r < 2 * u.length + 2,
        ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) r).state ≠ some 3) := by
  have length_bound : p + t + (2 * u.length + 2) ≤ z.length := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    omega
  dsimp only
  induction u generalizing t with
  | nil =>
    have hz' : z.drop (p + t) = false :: true :: v := by
      simpa only [pairEncode_eq, List.flatMap_nil, List.nil_append,
        List.cons_append] using hz
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, and_self, ↓reduceIte]
      using up_scan_pair i d p t hp false true v hz'
  | cons b u ih =>
    have hz' : z.drop (p + t) = b :: b :: pairEncode u v := by
      simpa only [pairEncode_eq, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hz
    have pair := up_scan_pair i d p t hp b b (pairEncode u v) hz'
    have hpair : (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 2 =
        headerScanCfg i d 0 (t + 2) (by omega) := by
      cases b <;> simpa only [Bool.false_eq_true, Bool.true_eq_false,
        false_and, and_false, ↓reduceIte] using pair.1
    have suffix : z.drop (p + (t + 2)) = pairEncode u v := by
      rw [show p + (t + 2) = (p + t) + 2 by omega, ← List.drop_drop, hz']
      rfl
    have tail := ih (t + 2) suffix (by simp only [List.length_cons] at length_bound; omega)
    have duration : 2 * (b :: u).length + 2 = 2 + (2 * u.length + 2) := by
      simp only [List.length_cons]
      omega
    constructor
    · calc
        _ = (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega))
            (2 + (2 * u.length + 2)) := congrArg _ duration
        _ = headerScanCfg i d 3 (t + 2 + (2 * u.length + 2)) (by omega) := by
          rw [MultiTapeTM.runFrom_add, hpair, tail.1]
        _ = _ := by congr 1; omega
    · intro r hr
      by_cases hsmall : r < 2
      · exact pair.2 r hsmall
      · have hr' : r - 2 < 2 * u.length + 2 := by omega
        rw [show r = 2 + (r - 2) by omega, MultiTapeTM.runFrom_add, hpair]
        exact tail.2 (r - 2) hr'

/-- **The header scan's contract, from any input offset**: let `d` be at control `0` with its
input head at cell `1 + p` of `z`, where `z.drop p = pairEncode u v`. Then
`Turing.headerScanTM i` run from `d` is after exactly `2|u| + 2` steps at
`Turing.headerScanCfg i d 3 (2|u| + 2)` (the header's cells read and the same number of cells
`true` on tape `i` from its head, both heads just past them), it does not reach the control `3`
earlier, and its output is `d`'s throughout. The painted interval overwrites its old contents and
every cell outside it is preserved, so consecutive scans write one ruler for consecutive headers
(`Turing.headerScanCfg_ruler`). [AB09, §1.4.1, the proof of Theorem 1.9; the pair encoding of
[AB09, §1.4]]

**Proof sketch.** Instantiate the header induction at time zero. The endpoint has
the original output; output-prefix monotonicity in both directions gives silence
at every intermediate time. -/
theorem headerScanTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v) :
    let hlen : d.inputPos.val + (2 * u.length + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom d (2 * u.length + 2) =
        headerScanCfg i d 3 (2 * u.length + 2) hlen ∧
      (∀ t < 2 * u.length + 2, ((headerScanTM i).runFrom d t).state ≠ some 3) ∧
      (∀ t ≤ 2 * u.length + 2, ((headerScanTM i).runFrom d t).output = d.output) := by
  have hz' : z.drop (p + 0) = pairEncode u v := by simpa only [Nat.add_zero] using hz
  have h := up_scan_header i d p hp u v 0 hz'
  simp only [Nat.zero_add, up_scan_zero i d hd] at h
  refine ⟨h.1, h.2, ?_⟩
  intro t ht
  have hle := MultiTapeTM.output_prefix (headerScanTM i) d ht
  have hge := MultiTapeTM.output_prefix (headerScanTM i) d (Nat.zero_le t)
  rw [h.1] at hle
  rw [MultiTapeTM.runFrom_zero] at hge
  exact hle.eq_of_length_le hge.length_le

/-- **The header scan extends a ruler**: if tape `i` of `d` holds exactly the ruler `true^m`
ending just before its head (cells `[pos - m, pos)` `true`, every other cell blank, `pos` the
head), then in `Turing.headerScanCfg i d q t` it holds exactly `true^(m + t)` from the same
first cell `pos - m`: as a unary buffer, `bufferTape (true^(m + t))` read from `pos - m`.
[AB09, §1.4.1]

*Generalization.* The private form assumed a blank tape `i` and read the buffer from `pos`; that
is the case `m = 0` (the hypothesis then says the tape is blank, since `bufferTape [] = none`, and
the conclusion is the old one up to `Nat.cast_zero`, `sub_zero` and `zero_add`). For two
consecutive headers of lengths `ℓ₁` and `ℓ₂` the first scan's conclusion (`m = 0`) is the second
scan's hypothesis at `m = ℓ₁`, because the head has moved to `pos + ℓ₁`; the two give
`true^(ℓ₁ + ℓ₂)`.

**Proof sketch.** Read both buffers through their public equation and the scanned tape through
its field equation. A cell in the painted interval is offset `m ≤ a < m + t` from the ruler's
start, hence inside the longer ruler. Any other cell keeps its old value: inside the old ruler
(`0 ≤ a < m`) it is `true` in both rulers, and outside both rulers it is blank. -/
theorem headerScanCfg_ruler {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (m : ℕ)
    (hpre : ∀ a : ℤ, d.workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate m true) a) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate (m + t) true) a := by
  intro a
  have h := hpre a
  simp only [headerScanCfg_workTapes, Function.update_self]
  rw [FinTM.bufferTape_eq] at h ⊢
  by_cases hin : d.workTapePos i ≤ d.workTapePos i - (m : ℤ) + a ∧
      d.workTapePos i - (m : ℤ) + a < d.workTapePos i + t
  · rw [if_pos hin, if_pos (show 0 ≤ a by omega), List.getElem?_replicate,
      if_pos (show a.toNat < m + t by omega)]
  · rw [if_neg hin, h]
    by_cases ha : 0 ≤ a
    · rw [if_pos ha, if_pos ha, List.getElem?_replicate, List.getElem?_replicate]
      by_cases ham : a < m
      · rw [if_pos (show a.toNat < m by omega), if_pos (show a.toNat < m + t by omega)]
      · rw [if_neg (show ¬a.toNat < m by omega), if_neg (show ¬a.toNat < m + t by omega)]
    · rw [if_neg ha, if_neg ha]

/-- On an initially blank ruler tape, the marked interval is the standard unary buffer: the
case `m = 0` of `Turing.headerScanCfg_ruler`. -/
private theorem up_scan_ruler_blank {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (hblank : ∀ a, d.workTapes i a = none) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i + a) =
      FinTM.bufferTape (List.replicate t true) a := by
  intro a
  have h := headerScanCfg_ruler i d q t ht 0 (fun b => by
    rw [hblank, List.replicate_zero, FinTM.bufferTape_eq, List.getElem?_nil, ite_self]) a
  simpa only [Nat.cast_zero, sub_zero, Nat.zero_add] using h

/-- **The header ruler machine**: `Turing.headerScanTM i` followed, at its exit `3`, by the
work-tape rewind `Turing.rewindTM k i` of tape `i` (`Turing.seamCompTM`), started at the scan's
control `0`. It reads one doubled header and leaves the ruler `true^(2|u| + 2)` on tape `i` with
that head back at the ruler's first cell. Read through `Turing.headerRulerTM_run`. [AB09,
§1.4.1] -/
def headerRulerTM {k : ℕ} (i : Fin k) :
    MultiTapeTM k Bool (Fin 4 ⊕ RewindPhase) :=
  { seamCompTM (headerScanTM i) 3 (rewindTM k i) .start with q₀ := Sum.inl 0 }

/-- **The header ruler's contract**: let `d` be at control `0` with its input head at cell
`1 + p` of `z`, where `z.drop p = pairEncode u v`, and tape `i` blank. With `ℓ = 2|u| + 2`,
`Turing.headerRulerTM i` run from `d` (control relabelled by `Sum.inl`) is after exactly
`2ℓ + 3` steps at the rewind's `done`, with the input head `ℓ` cells further, tape `i` holding the
ruler `true^ℓ` from its head's original cell, every head (that of tape `i` included) and every
other tape as in `d`, and `d`'s output; and it does not reach `done` earlier. [AB09, §1.4.1]

**Proof sketch.** The scan writes the unary buffer and ends immediately after it.
Its buffer equation supplies the framed rewind's hypothesis. The public seam
combines their exact runs and first-return cuts; its endpoint resets just the
ruler head, which restores the original vector of heads. -/
theorem headerRulerTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v)
    (hblank : ∀ a, d.workTapes i a = none) :
    let ℓ := 2 * u.length + 2
    let hlen : d.inputPos.val + ℓ < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    let e : Cfg k Bool (Fin 4 ⊕ RewindPhase) z :=
      ⟨some (Sum.inr .done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩
    (headerRulerTM i).runFrom (d.mapState Sum.inl) (2 * ℓ + 3) = e ∧
      (∀ t < 2 * ℓ + 3,
        ((headerRulerTM i).runFrom (d.mapState Sum.inl) t).state ≠ some (Sum.inr .done)) := by
  dsimp only
  let ℓ := 2 * u.length + 2
  have hlen : d.inputPos.val + ℓ < z.length + 2 := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    dsimp only [ℓ]; omega
  let c := headerScanCfg i d 3 ℓ hlen
  obtain ⟨hscan, hcut, _⟩ := headerScanTM_run i d p hp hd u v hz
  have hrewind := rewindTM_run_ofCfg i (List.replicate ℓ true) ℓ
    (by rw [List.length_replicate]) (c.mapState fun _ => RewindPhase.start)
    (by rw [Cfg.mapState_state]; rfl) (by
      intro a _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank a
      simpa only [c, headerScanCfg, Function.update_self, add_sub_cancel_right] using hh)
  let r : Cfg k Bool RewindPhase z :=
    { c.mapState (fun _ => RewindPhase.start) with
      state := some .done
      workTapePos := Function.update (c.mapState (fun _ => RewindPhase.start)).workTapePos i
        ((c.mapState (fun _ => RewindPhase.start)).workTapePos i - ℓ) }
  have endpoint : r.mapState Sum.inr =
      (⟨some (Sum.inr RewindPhase.done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩ : Cfg k Bool (Fin 4 ⊕ RewindPhase) z) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
    · funext j a
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hj : j = i
      · subst j
        have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank (a - d.workTapePos i)
        simpa only [add_sub_cancel, Function.update_self] using hh
      · simp only [c, headerScanCfg, Function.update_of_ne hj]
    · funext j
      rw [Cfg.mapState_workTapePos]
      by_cases hj : j = i
      · subst j
        simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg,
          Function.update_self, add_sub_cancel_right]
      · simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg, Function.update_of_ne hj]
    · rw [Cfg.mapState_output, Cfg.mapState_output]; rfl
  have total : 2 * ℓ + 3 = ℓ + 1 + (ℓ + 2) := by omega
  constructor
  · rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀, total]
    exact (seamCompTM_run_ofCfg (headerScanTM i) 3 (rewindTM k i) .start
      hscan rfl hcut hrewind.1).trans endpoint
  · intro t ht
    rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg (headerScanTM i) 3 (rewindTM k i) .start .done
      hscan rfl hcut hrewind.1 rfl hrewind.2.1 t (by omega)

/-! ## The suffix-ruler layout -/

/-- **The suffix-ruler seam layout**: on `K + (k + 3)` work tapes over the input `z`, the
configuration at control `q` with the input head at cell `ℓ + 1` (just past a header of length
`ℓ`), the table bits `tableBitsK M.tr` on tape `k`, the unary initial state `unaryFin M.q₀` from
cell `2` on tape `k + 1`, the ruler `true^ℓ` on tape `k + 2`, every other tape blank, every head
at `0` and an empty output. It is where a startup and header scans leave the machine before the
ruler host runs the forwarding loop on the suffix `z.drop ℓ` (`Turing.suffixRulerCfg_embed`).
[AB09, §1.4.1, the proof of Theorem 1.9] -/
def suffixRulerCfg {k K n : ℕ} {P : Type} (q : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool) (ℓ : ℕ)
    (hℓ : ℓ + 1 < z.length + 2) : Cfg (K + (k + 3)) Bool P z :=
  ⟨some q, ⟨ℓ + 1, hℓ⟩,
    fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
      else if j.val = k + 2 then FinTM.bufferTape (List.replicate ℓ true)
      else fun _ => none,
    fun _ => 0, []⟩

/-! The suffix-ruler layout's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.suffixRulerCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  suffixRulerCfg

/-- **The ruler host's presentation, its fields**: in `Turing.rulerHostCfg ℓ hz q c rt rp` the
physical input head is at `ℓ` plus `c`'s, the last tape is the ruler `rt` with its head at `rp`,
the first `m` tapes are `c`'s, and the output is `c`'s. [AB09, §1.2, Exercise 4.1: a machine run
on a suffix of its input] -/
theorem rulerHostCfg_fields {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool)
    (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).inputPos.val = ℓ + c.inputPos.val ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapes (Fin.last m) = rt ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapePos (Fin.last m) = rp ∧
      (∀ i : Fin m, (rulerHostCfg ℓ hz q c rt rp).workTapes i.castSucc = c.workTapes i) ∧
      (rulerHostCfg ℓ hz q c rt rp).output = c.output := by
  refine ⟨by rw [rulerHostCfg_inputPos], ?_, ?_, fun i => ?_, rulerHostCfg_output _ _ _ _ _ _⟩
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_last]
  · rw [rulerHostCfg_workTapePos, Fin.lastCases_last]
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc]

/-- **The suffix-ruler layout is the embedded ruler-host start**: let `z` have length
`ℓ + |x|`. Present H2-F's encoding `c` of `M`'s initial configuration on the suffix `x` through
the ruler host's layout `Turing.rulerHostCfg` (control `inj q false` for `c`'s control `q`, the
ruler `true^ℓ` with its head at `0`) and embed it in the first `k + 3` of `K + (k + 3)` tapes (the
others blank with their heads at `0`, no prior output). The result is
`Turing.suffixRulerCfg exit M z ℓ` with its control relabelled to `inj entry false`. So it is the
seam hypothesis of `Turing.startupLoopTM_runFrom` and `Turing.startupLoopTM_spaceUsed_le` at
`(K, k + 1)` for a startup ending at the suffix-ruler layout. [AB09, §1.4.1, the proof of
Theorem 1.9]

**Proof sketch.** Reconstruct the embedding from its public field equations. Its
first bank is the initial forwarding-loop encoding, its last tape is the ruler,
and all unselected tapes are blank. The encoded input head is one, so the
physical head is exactly one cell after the header and its virtual-zero tag is false. -/
theorem suffixRulerCfg_embed {k K n : ℕ} {P Q H : Type} {x z : List Bool}
    (exit : P) (entry : Q) (inj : Q → Bool → H) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (ℓ : ℕ) (hz : z.length = ℓ + x.length) (hlen : ℓ + 1 < z.length + 2) :
    let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
    embedEmitCfg (Fin.castLEEmb (by omega : k + 3 ≤ K + (k + 3)))
      (fun _ _ => none) (fun _ => 0) []
      (rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c
        (FinTM.bufferTape (List.replicate ℓ true)) 0) =
      (suffixRulerCfg (K := K) exit M z ℓ hlen).mapState (fun _ => inj entry false) := by
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  have fields := StepBlock.forwardLoopCfg_init_fields entry M x
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  have host := rulerHostCfg_fields ℓ hz (c.state.map fun q => inj q false) c rt 0
  apply embedEmitCfg_eq
  · rw [rulerHostCfg_state, fields.1, Option.map_some, Cfg.mapState_state]
    rfl
  · apply Fin.ext
    rw [host.1, Cfg.mapState_inputPos]
    change ℓ + c.inputPos.val = ℓ + 1
    rw [fields.2.1]
  · rw [List.nil_append, rulerHostCfg_output, fields.2.2.2, Cfg.mapState_output]
    rfl
  · intro j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_last, Cfg.mapState_workTapes]
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.val_last,
          if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_last, Cfg.mapState_workTapePos]
        rfl
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc, Cfg.mapState_workTapes,
          StepBlock.forwardLoopCfg_init_workTapes]
        have ha : a.val ≠ k + 2 := by omega
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.coe_castSucc, if_neg ha]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_castSucc, Cfg.mapState_workTapePos,
          fields.2.2.1 a]
        rfl
  · intro j hj
    have hjge : k + 3 ≤ j.val := by
      by_contra h
      apply hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      apply Fin.ext; rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      simp only [suffixRulerCfg, if_neg (by omega : j.val ≠ k),
        if_neg (by omega : j.val ≠ k + 1), if_neg (by omega : j.val ≠ k + 2)]
    · rw [Cfg.mapState_workTapePos]
      rfl

/-! ## Seal controls (each closes unsealed and fails sealed) -/
example {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) : (StepBlock.forwardLoopCfg entry M c).output = c.output :=
  rfl
example {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ) (hz : z.length = ℓ + y.length)
    (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool) (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).output = c.output := rfl
example {k : ℕ} {S : Type} (M : MultiTapeTM k Bool S) (x : List Bool) :
    M.initCfg x = Cfg.init M.q₀ x := rfl
example {k : ℕ} {S : Type} (q : S) (x : List Bool) :
    (Cfg.init (k := k) (Symbol := Bool) q x).output = [] := rfl
example : FinTM.bufferTape [true] 0 = some true := rfl
example (w : List Bool) : StepBlock.summaryCells none w 0 = none := rfl
example {k n : ℕ}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1))) :
    tableBitsK tr = (List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK k).flatMap fun w => actionBitsK (tr q inp w) := rfl
example : unaryFin (0 : Fin 1) = [false] := rfl
example {k m : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin k) (c : Cfg m Bool S x) :
    (embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] c).output = [] ++ c.output := rfl
example {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) :
    (c.mapState fun _ => ()).output = c.output := rfl
example : pairEncode [] [] = [false, true] := rfl
example : (rewindTM (Symbol := Bool) 1 0).q₀ = .start := rfl
example {k : ℕ} {S₁ S₂ : Type} [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (e : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (en : S₂) : (seamCompTM M₁ e M₂ en).q₀ = Sum.inl M₁.q₀ := rfl
example {k m : ℕ} {S : Type} (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    (embedEmitTM ι M).q₀ = M.q₀ := rfl
example : tapeAction (k := 1) (Symbol := Bool) (State := Unit) 0 .pos none .pos () =
    ⟨.pos, fun j => if j = 0 then (none, .pos) else (none, 0), none, some ()⟩ := rfl
example : inputMoveAction (k := 1) (Symbol := Bool) (State := Unit) 0 () =
    ⟨0, fun _ => (none, 0), none, some ()⟩ := rfl

end Turing

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealParts0.out =====

exit=0 4s

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealUK.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.UniversalParts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `k`-generic universal machine (U2)

[AB09, §1.4.1 and Theorem 1.9]: one universal machine for codes of `k`-work-tape binary
machines, for every `k`, with an overhead linear in the simulated time and a constant depending
on the code only. At `k = 2` it is the two-tape universal machine of the time hierarchy at
`f log f` (plan §2.1; the Hennie–Stearns conversion of [AB09, §1.7] lands machines there); at
`k = 1` it is the self-application universal `U₀` of the space hierarchy
(`Turing.exists_selfUniversal`, its `k = 1` corollary) and the code-first evaluator of
`Turing.universal` (the U-1 re-derivation, deferred). Design: `audits/evidence/u2/U2-design.md`;
the user's decisions of 2026-10-14 (`backlog.md` RD-5).

**Status.** Proved: the scheme interface and its two instances, the startup
`Turing.exists_selfStartupTMK`, and both machine contracts. They are built on the step block's
forwarding round loop `Turing.StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward.lean`)
and, for the code-first evaluator, on the ruler host `Turing.exists_rulerHostTM`
(`Build/InputDevice.lean`). The parts both contracts are assembled from (the startup–loop seam
`Turing.startupLoopTM` and its ledgers, the forwarding loop's readings at an initial
configuration, the header ruler `Turing.headerRulerTM` and the suffix-ruler layout
`Turing.suffixRulerCfg`) are public in `Build/UniversalParts.lean`, harvested from this file's
privates for their second consumer (the U2 harvest, user ruling of 2026-11-06).

## Design

* **One construction, generic in `k`.** The step block `Turing.StepBlock.roundTM k` simulates one
  transition of any `k`-tape table held as data at a cost `≤ 50 · (|table| + 1)`, a constant for
  a fixed code; H2-F forwards the emissions. Nothing here is specific to one or two work tapes.
* **The scheme interface** `Turing.EffectiveCodeK k`: a total decoding into `k`-tape machines and
  a canonizer computing the fixed serialization `Turing.serializeK` in arbitrary time. The
  received one-tape scheme and the Z3 two-tape scheme are instances. No uniformity is assumed:
  per-code constants absorb the canonizer's time.
* **Two input layouts.** Self-application (`Turing.exists_selfUniversalK`): on `pairEncode α w`
  the coded machine runs on that same input, through the native device, with no copy and no
  position counter. Code first (`Turing.universalK`): on `pairEncode α x` it runs on `x`,
  through H5's bounded-prefix ruler device, at a constant cost per step for a fixed code.
* **Both directions** in both layouts: forward time (and, for self-application, space) ledgers,
  and the converse that every completed output of the universal machine is one of the coded
  machine's.

## Main definitions

* `Turing.EffectiveCodeK`, `Turing.EffectiveCodeK.toFinTM` — the `k`-tape scheme interface;
  `Turing.EffectiveCodeK.ofSerialize` — its constructor from a scheme with its own serialization.
* `Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK` — the received one- and
  two-tape schemes as `k`-tape schemes.

## Main results

* `Turing.EffectiveMachineCode.toK_toFinTM`, `Turing.EffectiveMachineCode2.toK_toFinTM`,
  `Turing.EffectiveMachineCode.toK_machine`, `Turing.EffectiveMachineCode2.toK_machine` — the
  decoded machines agree, by definition.
* `Turing.exists_selfStartupTMK` — the startup, ending at the step block's seam (proved).
* `Turing.exists_selfUniversalK` — the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (proved).
* `Turing.universalK` — the code-first evaluator with time `C · (t + 1)` and the converse
  (proved).

Their assembly cites `Build/UniversalParts.lean`: `Turing.startupLoopTM_runFrom`,
`_live_of_le` and `_spaceUsed_le`; `Turing.StepBlock.forwardLoop_forward` and `_converse`;
`Turing.embedEmitCfg_forwardLoop_init`; `Turing.headerRulerTM_run`; `Turing.suffixRulerCfg_embed`
and `Turing.MultiTapeTM.initCfg_eq_mapState`. The code-first evaluator's own startup composition
(the startup embedded with one more tape, then the header ruler) stays private here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, machine codes; §1.4.1, Theorem 1.9 and its proof:
  the universal machine simulates one step of `M` in a number of steps depending only on `M`'s
  table; §1.7, the two-tape simulation; Exercise 4.1, the space-bounded universal machine.)
-/

namespace Turing

attribute [local irreducible] startupLoopTM headerScanTM headerScanCfg headerRulerTM suffixRulerCfg

/-! ## The `k`-tape scheme interface -/

/-- **An effective scheme for `k`-work-tape codes** [AB09, §1.4]: a total decoding of every
string `α` into a `k`-work-tape binary machine `machine α` with state space
`Fin (numStates α + 1)`, together with a machine of this development, the canonizer, that
computes from `α` the fixed `k`-record serialization `Turing.serializeK (machine α)` within an
arbitrary time bound `canonizerTime`. As for `Turing.EffectiveMachineCode` (Argument A), the
canonizer targets the fixed, scheme-independent serialization, and its time bound is arbitrary:
fixed-code consumers absorb it into their constants. The received schemes are instances
(`Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK`). -/
structure EffectiveCodeK (k : ℕ) where
  /-- one less than the number of states of the machine a string denotes -/
  numStates : List Bool → ℕ
  /-- the machine a string denotes -/
  machine : (α : List Bool) → MultiTapeTM k Bool (Fin (numStates α + 1))
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serializeK ∘ machine` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => serializeK (machine α)) canonizerTime

/-- The bundled machine a string denotes in a `k`-tape scheme: `k` work tapes, the states
`Fin (numStates α + 1)`, the decoded machine. -/
def EffectiveCodeK.toFinTM {k : ℕ} (E : EffectiveCodeK k) (α : List Bool) : FinTM Bool where
  k := k
  State := Fin (E.numStates α + 1)
  tm := E.machine α

/-- **A `k`-tape scheme from a scheme with its own serialization** (the common constructor of
the two instances below): given a type of coded machines with their state counts and their
`k`-tape machines, a serialization equal to `serializeK` of the machine, a decoding, and a
canonizer computing the serialization of the decoded machine, the `k`-tape scheme with the same
decoding and canonizer. -/
def EffectiveCodeK.ofSerialize {k : ℕ} {Code : Type} (numStates : Code → ℕ)
    (tm : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))) (serialize : Code → List Bool)
    (serialize_eq : ∀ M, serialize M = serializeK (tm M)) (decode : List Bool → Code)
    (canonizer : FinTM Bool) (canonizerTime : ℕ → ℕ)
    (h : canonizer.ComputesFunInTime (fun α => serialize (decode α)) canonizerTime) :
    EffectiveCodeK k where
  numStates α := numStates (decode α)
  machine α := tm (decode α)
  canonizer := canonizer
  canonizerTime := canonizerTime
  canonizer_computes := by
    have e : (fun α => serialize (decode α)) = fun α => serializeK (tm (decode α)) :=
      funext fun α => serialize_eq (decode α)
    exact e ▸ h

/-- **The received one-tape scheme as a `k`-tape scheme** (`k = 1`): the same decoding and the
same canonizer, whose target `CodeTM.serialize` is `serializeK` at one work tape
(`Turing.oneTapeMachineFormat.serialize_eq`). [AB09, §1.4] -/
def EffectiveMachineCode.toK (c : EffectiveMachineCode) : EffectiveCodeK 1 :=
  EffectiveCodeK.ofSerialize CodeTM.numStates CodeTM.tm CodeTM.serialize
    oneTapeMachineFormat.serialize_eq c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- **The Z3 two-tape scheme as a `k`-tape scheme** (`k = 2`): the same decoding and the same
canonizer, whose target `Code2TM.serialize` is `serializeK` at two work tapes
(`Turing.Code2TM.serialize_eq_serializeK`). [AB09, §1.4] -/
def EffectiveMachineCode2.toK (c : EffectiveMachineCode2) : EffectiveCodeK 2 :=
  EffectiveCodeK.ofSerialize Code2TM.numStates Code2TM.tm Code2TM.serialize
    Code2TM.serialize_eq_serializeK c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- The one-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode.toK_toFinTM (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The two-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode2.toK_toFinTM (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The one-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode.toK_machine (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-- The two-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode2.toK_machine (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-! ## U2-S: the startup -/

/-- The canonizer, with the public cleanup machine restarted in its cleaning state. -/
private def ss_cleanCanonizer (F : FinTM Bool) : FinTM Bool where
  k := F.k + F.k
  State := Complexity.LogProg.CleanSt F.State F.k
  tm := { Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ }

/-- The bundled cleanup run is the run from the public cleaning entry. -/
private theorem ss_cleanCanonizer_run (F : FinTM Bool) (α : List Bool) (t : ℕ) :
    (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t =
      (Complexity.LogProg.cleanTM F.tm F.tm.q₀).runFrom
        (Cfg.init (.init F.tm.q₀) α) t := by
  change ({ Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ } :
    MultiTapeTM (F.k + F.k) Bool (Complexity.LogProg.CleanSt F.State F.k)).runFrom _ _ = _
  rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]

/-- Cleanup preserves a completed computation and blanks every work tape.

**Proof sketch.** Bound the original run's visited set on each tape by their finite
maximum. Apply the public cleanup theorem, then use the restart equations. -/
private theorem ss_cleanCanonizer_halts (F : FinTM Bool) (α out : List Bool) (t : ℕ)
    (h : F.ComputesInTime α out t) :
    ∃ u, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).output =
        out ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapePos =
        (fun _ => 0) := by
  classical
  have hc := (FinTM.computesInTime_iff F α out t).mp h
  rw [MultiTapeTM.initCfg_eq] at hc
  let s := Finset.univ.sup fun i : Fin F.k =>
    (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t i).card
  obtain ⟨u, hu, hout, hblank, hpos, _⟩ :=
    Complexity.LogProg.cleanTM_run F.tm F.tm.q₀ F.tm.q₀ α t hc.1 s
      (fun i => Finset.le_sup
        (f := fun j : Fin F.k => (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t j).card)
        (Finset.mem_univ i))
  refine ⟨u, ?_⟩
  simpa only [ss_cleanCanonizer_run] using ⟨hu, hout.trans hc.2, hblank, hpos⟩

/-- A string-dependent time is bounded by a function of string length. -/
private theorem ss_lengthBound (time : List Bool → ℕ) :
    ∃ bound : ℕ → ℕ, ∀ α, time α ≤ bound α.length := by
  classical
  refine ⟨fun n => Finset.univ.sup (fun f : Fin n → Bool => time (List.ofFn f)), ?_⟩
  intro α
  simpa only [List.ofFn_get] using
    (Finset.le_sup (f := fun f : Fin α.length → Bool => time (List.ofFn f))
      (Finset.mem_univ α.get))

/-- A total canonizer remains total after cleanup, at a bound depending only on length;
the same bound leaves every work tape blank and every work head at zero.

**Proof sketch.** Choose each input's cleaned halting time and take a finite maximum
at each input length. Absorbing halting preserves the output and cleanup at the maximum. -/
private theorem ss_cleanCanonizer_computes (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) :
    ∃ bound, (ss_cleanCanonizer F).ComputesFunInTime f bound ∧ ∀ α,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapes = (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapePos = (fun _ => 0) := by
  classical
  have hex := fun α => ss_cleanCanonizer_halts F α (f α) (τ α.length)
    ((FinTM.computesFunInTime_iff F f τ).mp hF α)
  choose time htime using hex
  obtain ⟨bound, hbound⟩ := ss_lengthBound time
  have hfreeze (α : List Bool) :
      (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (bound α.length) =
        (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (time α) := by
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (hbound α)
    calc
      _ = (ss_cleanCanonizer F).tm.runFrom
          ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
            (time α)) extra := by rw [heq, MultiTapeTM.runFrom_add]
      _ = _ := MultiTapeTM.runFrom_of_halt _ (htime α).1
  refine ⟨bound, (FinTM.computesFunInTime_iff _ _ _).mpr ?_, ?_⟩
  · intro α
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hfreeze α]
    exact ⟨(htime α).1, (htime α).2.1⟩
  · intro α
    rw [hfreeze α]
    exact (htime α).2.2

/-- A buffered second-phase configuration halts exactly when its source does. -/
private theorem ss_bufferedHalt_iff (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    (FinTM.bufferedSecondCfg M₁ M₂ c b p tapes heads).state = none ↔ c.state = none := by
  rw [FinTM.bufferedSecondCfg_state]
  simp only [FinTM.bufferedCompTM_State, Option.map_eq_none_iff]

/-- A first halt of the virtual canonizer is a first halt of the prefix canonizer,
after the fixed prefix phase, uniformly over all suffixes.

**Proof sketch.** The exact prefix formula identifies the state after the prefix phase.
Before that phase ends, absorbing halting and its live final state exclude a halt. -/
private theorem ss_prefix_first_halt (F : FinTM Bool) (α : List Bool) (t : ℕ)
    (hhalt : (F.tm.runFrom (F.tm.initCfg α) t).state = none)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg α) u).state ≠ none) (w : List Bool) :
    ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w))
      (3 * α.length + 4 + t)).state = none ∧
    ∀ u < 3 * α.length + 4 + t,
      ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w)) u).state ≠
        none := by
  rw [prefixCanonTM_eq]
  constructor
  · obtain ⟨b, hb⟩ := prefixCanon_run F α w t
    simp only [prefixCanonTM_eq] at hb
    rw [hb, ss_bufferedHalt_iff]
    exact hhalt
  · intro u hu
    by_cases hpre : u < 3 * α.length + 4
    · have hs := prefixCanon_start F α w
      simp only [prefixCanonTM_eq] at hs
      have hstart :
          ((FinTM.bufferedCompTM universalPrefixTM F).tm.runFrom
            ((FinTM.bufferedCompTM universalPrefixTM F).tm.initCfg (pairEncode α w))
            (3 * α.length + 4)).state ≠ none := by
        intro h
        rw [hs, ss_bufferedHalt_iff, MultiTapeTM.initCfg_eq, Cfg.init_state] at h
        exact Option.some_ne_none F.tm.q₀ h
      exact MultiTapeTM.runFrom_state_ne_none_of_le _ _ _ hstart u (by omega)
    · obtain ⟨b, hb⟩ := prefixCanon_run F α w (u - (3 * α.length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * α.length + 4 ≤ u)] at hb
      intro h
      rw [hb, ss_bufferedHalt_iff] at h
      exact hlive (u - (3 * α.length + 4)) (by omega) h

/-- The cleaned canonizer's first halt has the completed output and clean scratch.

**Proof sketch.** The public first-halt theorem identifies its configuration with the
one at the cleaned length bound, including all fields of that configuration. -/
private theorem ss_cleanCanonizer_first_halt (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) (α : List Bool) :
    ∃ t, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧
      ∀ u < t, ((ss_cleanCanonizer F).tm.runFrom
        ((ss_cleanCanonizer F).tm.initCfg α) u).state ≠ none := by
  obtain ⟨bound, hfun, hclean⟩ := ss_cleanCanonizer_computes F f τ hF
  have hc := (FinTM.computesInTime_iff _ _ _ _).mp
    ((FinTM.computesFunInTime_iff _ _ _).mp hfun α)
  obtain ⟨t, _, hbefore, hsame⟩ := MultiTapeTM.exists_first_halt _ _ hc.1
  refine ⟨t, ?_, ?_, ?_, ?_, hbefore⟩
  · rw [hsame]
    exact hc.1
  · rw [hsame]
    exact hc.2
  · rw [hsame]
    exact (hclean α).1
  · rw [hsame]
    exact (hclean α).2

/-- Capturing a fresh run starts with blank host tapes and zero work heads.

**Proof sketch.** Partition host tapes into selected tapes, the capture tape, and the frame.
The selected tapes inherit the blank initial configuration; the empty captured output makes
its tape blank; the frame is blank by construction. Compare all configuration fields. -/
private theorem ss_captureInitial {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
    (ι : Fin m ↪ Fin n) (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) :
    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
      (M.initCfg x)).mapState Sum.inl =
      Cfg.init (Sum.inl M.q₀ : S ⊕ Unit) x := by
  classical
  have hfields (j : Fin n) :
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapes j = (fun _ => none) ∧
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapePos j = 0 := by
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_tape, embedSilentCfg_selected_pos,
        MultiTapeTM.initCfg_eq]
      exact ⟨funext fun z => Cfg.init_workTapes _ _ i z, Cfg.init_workTapePos _ _ i⟩
    · by_cases he : j = cap
      · subst j
        have hh := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x)
        simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
          FinTM.bufferTape_nil, List.length_nil, Nat.cast_zero] using hh
      · exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x) j hj he
  apply Cfg.ext
  · rw [Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq,
      Cfg.init_state, Option.map_some, Cfg.init_state]
  · rw [Cfg.mapState_inputPos, embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq,
      Cfg.init_inputPos, Cfg.init_inputPos]
  · funext j z
    rw [Cfg.mapState_workTapes, Cfg.init_workTapes, (hfields j).1]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, (hfields j).2]
  · rw [Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]

/-- The returning capture host, restarted in the source's initial state. -/
private def ss_captureTM (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n) (cap : Fin n) :
    MultiTapeTM n Bool (F.State ⊕ Unit) :=
  { embedSilentRetTM ι cap F.tm with q₀ := Sum.inl F.tm.q₀ }

/-- The returning capture reaches its anchor exactly at the source's first halt and
is silent throughout. Its final tapes are the public silent embedding's exact tapes.

**Proof sketch.** Identify the blank initial configuration, use the returning embedding's
through-halt contract, and project its output field before and at the return. -/
private theorem ss_capture_run (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) (t : ℕ)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg x) u).state ≠ none)
    (hhalt : (F.tm.runFrom (F.tm.initCfg x) t).state = none) :
    (ss_captureTM F ι cap).runFrom ((ss_captureTM F ι cap).initCfg x) t =
      { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (F.tm.runFrom (F.tm.initCfg x) t) with state := some (Sum.inr ()) } ∧
    (∀ u < t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).state ≠ some (Sum.inr ())) ∧
    (∀ u ≤ t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).output = []) := by
  have hinit : (F.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hr := embedSilentRetTM_run ι cap hcap F.tm (fun _ _ => none) (fun _ => 0)
    [] [] (F.tm.initCfg x) t hinit hlive hhalt
  simp only [MultiTapeTM.initCfg_eq] at hr
  simp only [ss_captureTM, MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀,
    ← ss_captureInitial F.tm ι cap hcap x]
  refine ⟨hr.2.1, hr.2.2, ?_⟩
  intro u hu
  rcases lt_or_eq_of_le hu with hlt | rfl
  · rw [hr.1 u hlt, Cfg.mapState_output, embedSilentCfg_output]
  · simp only [hr.2.1, embedSilentCfg_output]

/-- With the prefix parser's empty left block, index zero is the buffer and every other
index belongs to the constant right block.

**Proof sketch.** Cast the composite index to the public block partition. Its value is either
zero, the buffer index, or one plus an index of the right block; apply the corresponding
published projection equation. -/
private theorem ss_tapeBlocks_zeroLeft {A : Type} (F : FinTM Bool)
    (left : Fin universalPrefixTM.k → A) (buffer right : A)
    (i : Fin (FinTM.bufferedCompTM universalPrefixTM F).k) :
    FinTM.tapeBlocks left buffer (fun _ : Fin F.k => right)
        (Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i) =
      if i.val = 0 then buffer else right := by
  have hp := universalPrefixTM_k
  have hk := FinTM.bufferedCompTM_k universalPrefixTM F
  have hi := i.isLt
  by_cases hz : i.val = 0
  · have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k (0 : Fin 1)) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_zero]
      omega
    rw [he, FinTM.tapeBlocks_buffer, if_pos hz]
  · let j : Fin F.k := ⟨i.val - 1, by omega⟩
    have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd]
      dsimp only [j]
      omega
    rw [he, FinTM.tapeBlocks_right, if_neg hz]

/-- After the canonizer's work tapes have been cleared, the prefix composite keeps only
the original code buffer, whose head is the virtual input position minus one.

**Proof sketch.** Read the exact prefix run through the published composite fields at its own
index type. The empty parser block leaves index zero for the code buffer; the cleaned right
block contributes blank tapes and zero heads. -/
private theorem ss_prefix_return_fields (F : FinTM Bool) (α w : List Bool) (t : ℕ)
    (hblank : (F.tm.runFrom (F.tm.initCfg α) t).workTapes = (fun _ _ => none))
    (hheads : (F.tm.runFrom (F.tm.initCfg α) t).workTapePos = (fun _ => 0)) :
    let c := F.tm.runFrom (F.tm.initCfg α) t
    let G := FinTM.bufferedCompTM universalPrefixTM F
    let d := G.tm.runFrom (G.tm.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
    d.inputPos.val = 2 * α.length + 3 ∧ d.output = c.output ∧
      (∀ i, d.workTapes i = if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      ∀ i, d.workTapePos i = if i.val = 0 then (c.inputPos.val : ℤ) - 1 else 0 := by
  dsimp only
  obtain ⟨b, hb⟩ := prefixCanon_run F α w t
  simp only [prefixCanonTM_eq] at hb
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FinTM.bufferedSecondCfg_inputPos]
  · rw [FinTM.bufferedSecondCfg_output]
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapes_cast, hblank]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapePos_cast, hheads]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i

/-- Capturing the cleaned prefix has a code-dependent first return, silence, and a
uniform space bound. The final configuration is expressed through the prefix run;
its cleaned source data are retained for the layout normalization below.

**Proof sketch.** Select the cleaned canonizer's first halt before quantifying the suffix.
The prefix first-halt lemma and the returning capture contract give the claimed run. -/
private theorem ss_capturedPrefix_run (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t : ℕ,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧ ∀ w : List Bool,
      R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) =
        { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
            (G.tm.runFrom (G.tm.initCfg (pairEncode α w))
              (3 * α.length + 4 + t)) with state := some (Sum.inr ()) } ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, ht, hout, hblank, hheads, hlive⟩ := ss_cleanCanonizer_first_halt F f τ hF α
  refine ⟨t, hout, hblank, hheads, fun w => ?_⟩
  have hp := ss_prefix_first_halt (ss_cleanCanonizer F) α t ht hlive w
  simp only [prefixCanonTM_eq] at hp
  have hr := ss_capture_run
    (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)) ι cap hcap
    (pairEncode α w) (3 * α.length + 4 + t) hp.2 hp.1
  exact ⟨hr.1, hr.2.1, hr.2.2, MultiTapeTM.spaceUsed_le_mul_succ _ _ _⟩

/-- The returned capture has exactly the code buffer, the captured result, and blank scratch.
Its code-buffer head is a code-dependent position between minus one and the code length.

**Proof sketch.** Retain the cleaned source's output and blankness at the first halt chosen
before the suffix. Project the exact captured return through the selected, capture, and frame
equations, and normalize the source fields with the cast-indexed composite equations. The
source input position determines the buffer head independently of the suffix. -/
private theorem ss_capturedPrefix_fields (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t p : ℕ, p ≤ α.length + 1 ∧ ∀ w : List Bool,
      let d := R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
      d.state = some (Sum.inr ()) ∧ d.inputPos.val = 2 * α.length + 3 ∧
      (∀ i, d.workTapes (ι i) =
        if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      (∀ i, d.workTapePos (ι i) = if i.val = 0 then (p : ℤ) - 1 else 0) ∧
      (d.workTapes cap = FinTM.bufferTape (f α) ∧ d.workTapePos cap = (f α).length) ∧
      (∀ j, j ∉ Set.range ι → j ≠ cap →
        d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0) ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, hout, hblank, hheads, hret⟩ := ss_capturedPrefix_run F f τ hF ι cap hcap α
  refine ⟨t, ((ss_cleanCanonizer F).tm.runFrom
    ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.val, ?_, fun w => ?_⟩
  · have h := ((ss_cleanCanonizer F).tm.runFrom
      ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.isLt
    omega
  · obtain ⟨hr, hcut, hsilent, hspace⟩ := hret w
    have hf := ss_prefix_return_fields (ss_cleanCanonizer F) α w t hblank hheads
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcut, hsilent, hspace⟩
    · rw [hr]
    · rw [hr]
      rw [embedSilentCfg_inputPos]
      exact hf.1
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_tape]
      exact hf.2.2.1 i
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_pos]
      exact hf.2.2.2 i
    · rw [hr]
      have hc := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
        [] [] ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.initCfg
            (pairEncode α w)) (3 * α.length + 4 + t))
      simpa only [List.nil_append, hf.2.1, hout] using hc
    · intro j hj hjc
      rw [hr]
      exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0) [] [] _ j hj hjc

/-- The public seam-layout machine redistributes a canonical serialization from its right
blank, at one time chosen before the input and the ambient configuration.

**Proof sketch.** Instantiate the layout contract with the state-count bits, unary initial
state, and transition table. The published serialization and unary-word equations identify
its source word and its two output words. -/
private theorem ss_serialized_layout (n : ℕ) (src tbl sm : Fin n)
    (hst : src ≠ tbl) (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM n Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k m : ℕ} (M : MultiTapeTM k Bool (Fin (m + 1))),
        ∃ T ≤ C * ((serializeK M).length + 1),
          ∀ {z : List Bool} (d : Cfg n Bool Q z),
            d.state = some entry →
            d.workTapes src = FinTM.bufferTape (serializeK M) →
            d.workTapePos src = (serializeK M).length →
            d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
            d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
            (L.runFrom d T).state = some done ∧
            (L.runFrom d T).inputPos = d.inputPos ∧
            (L.runFrom d T).workTapes =
              Function.update (Function.update (Function.update d.workTapes src
                (fun _ => none)) tbl (FinTM.bufferTape (tableBitsK M.tr)))
                sm (fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)) ∧
            (L.runFrom d T).workTapePos =
              Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0)
                sm 0 ∧
            (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
            ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ := exists_seamLayoutTM n src tbl sm hst hss hts
  refine ⟨Q, hQ, hD, L, entry, done, C, ?_⟩
  intro k m M
  have hw := serializeK_eq M
  rw [unaryFin_eq] at hw
  have h := hL m.bits (tableBitsK M.tr) M.q₀.val (serializeK M).length (by rw [← hw])
  rw [← hw] at h
  simpa only [← unaryFin_eq M.q₀] using h

/-- A one-step move of the tested head when its cell is blank. The catalog rows do not
supply this conditional single step; it joins two skips and restores an empty buffer's head.
The action itself is the public one-tape action. -/
private def ss_bufferLeaf (n : ℕ) (i : Fin n) (emptyMove : SignType) :
    MultiTapeTM n Bool Bool where
  q₀ := false
  tr := fun _ _ work =>
    tapeAction i 0 none (if work i = none then emptyMove else 0)
      true

/-- The buffer leaf performs its conditional move in one silent step, with every other
tape and head fixed; its exit is absent before that step.

**Proof sketch.** Apply the public one-step tape-action equation. Before time one there is
only the entry configuration, whose false state is distinct from the true exit. -/
private theorem ss_bufferLeaf_run {n : ℕ} (i : Fin n) (emptyMove : SignType)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false) :
    (ss_bufferLeaf n i emptyMove).runFrom d 1 =
      { d with
        state := some true
        workTapePos := Function.update d.workTapePos i
          (d.workTapePos i + if d.workTapeSymbols i = none then (emptyMove : ℤ) else 0) } ∧
      ∀ u < 1, ((ss_bufferLeaf n i emptyMove).runFrom d u).state ≠ some true := by
  constructor
  · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have h := step_of_tapeAction_move (ss_bufferLeaf n i emptyMove) d i 0
      (if d.workTapeSymbols i = none then emptyMove else 0) hstate rfl
    simpa only [moveInputPos_zero, apply_ite, SignType.coe_zero] using h
  · intro u hu
    have hu0 : u = 0 := by omega
    rw [hu0, MultiTapeTM.runFrom_zero, hstate]
    simp only [ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- The first rightward skip starts at the source's virtual input position minus one.
At the left blank it moves to zero; at a nonnegative position it skips the remaining suffix.

**Proof sketch.** For virtual position zero, use the empty-word instance of the catalog
skip at the left blank. Otherwise, use the dropped suffix and the public buffer equation.
The catalog supplies both the framed endpoint and the first-return cut. -/
private theorem ss_bufferSkip_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    (skipTM n i).runFrom d (v.length + 1) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if p = 0 then 0 else (α.length : ℤ) + 1) } ∧
      ∀ u < v.length + 1, ((skipTM n i).runFrom d u).state ≠ some .done := by
  dsimp only
  have hw : ∀ q : ℤ, 0 ≤ q → q ≤
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) →
      d.workTapes i (d.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then [] else α.drop (p - 1)) q := by
    intro q hq hqv
    rw [hbuf, hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0]
      simp only [Int.zero_sub, add_zero, FinTM.bufferTape_left, FinTM.bufferTape_nil]
    · simp only [if_neg h] at hqv ⊢
      rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos hq,
        if_pos (by omega), List.getElem?_drop]
      congr 1
      omega
  obtain ⟨hr, hc, _⟩ := skipTM_run_ofCfg i _ d hstate hw
  have he : d.workTapePos i +
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) + 1 =
      if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero]
      omega
    · simp only [if_neg h, List.length_drop]
      omega
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- The second part of the rightward positioning pass: step left at a blank, then skip.
It is the existing seam constructor applied to the one-step leaf and the catalog skip. -/
private def ss_bufferAdvance (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (Bool ⊕ SeekPhase) :=
  seamCompTM (ss_bufferLeaf n i .neg) true (skipTM n i) .run

/-- After the first skip, the conditional left step and second skip reach one beyond the
right delimiter of a nonempty word. For the empty word they preserve the virtual position.

**Proof sketch.** Read blankness through the configuration and buffer equations. At position
zero of a nonempty word the leaf stays put and the skip crosses the word; otherwise the leaf
steps left and the empty-word skip steps right again. The public seam theorem supplies the
joined run and its first-return cut, preserving every ambient field. -/
private theorem ss_bufferAdvance_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool Bool z)
    (hstate : d.state = some false) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1) :
    let v := if p = 0 then α else []
    (ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) (v.length + 3) =
      ⟨some (Sum.inr .done), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + 3,
        ((ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  dsimp only
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (-1 : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i .neg d hstate
  change (ss_bufferLeaf n i .neg).runFrom d 1 = a at hr
  let b := a.mapState (fun _ => SeekPhase.run)
  have hba : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  have hbp : b.workTapePos i =
      if p = 0 then (if α = [] then -1 else 0) else (α.length : ℤ) := by
    rw [Cfg.mapState_workTapePos]
    dsimp only [a]
    rw [Function.update_self, Cfg.workTapeSymbols_eq, hbuf, hpos]
    by_cases h : p = 0
    · simp only [if_pos h]
      cases α with
      | nil => simp only [FinTM.bufferTape_nil, ite_true]; omega
      | cons x xs =>
        rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
        simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, List.cons_ne_nil,
          Nat.cast_zero, add_zero]
    · rw [if_neg h]
      have hn : FinTM.bufferTape α ((α.length : ℤ) + 1) = none := by
        rw [show (α.length : ℤ) + 1 = ((α.length + 1 : ℕ) : ℤ) by omega,
          FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
        omega
      rw [hn, if_pos rfl]
      omega
  have hw : ∀ q : ℤ, 0 ≤ q →
      q ≤ ((if p = 0 then α else []).length : ℤ) →
      b.workTapes i (b.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then α else []) q := by
    intro q hq hqv
    rw [hba, hbp]
    by_cases h : p = 0
    · simp only [if_pos h] at hqv ⊢
      by_cases ha : α = []
      · subst α
        simp only [FinTM.bufferTape_nil]
      · rw [if_neg ha, zero_add]
    · simp only [if_neg h, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0, add_zero, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega),
        FinTM.bufferTape_nil]
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  obtain ⟨hs, hscut, _⟩ := skipTM_run_ofCfg i _ b hbstate hw
  have he : b.workTapePos i + ((if p = 0 then α else []).length : ℤ) + 1 =
      if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [hbp]
    by_cases h : p = 0
    · simp only [if_pos h]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero]
        omega
      · simp only [if_neg ha]
        omega
    · simp only [if_neg h, List.length_nil, Nat.cast_zero]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero] at hp ⊢
        omega
      · simp only [if_neg ha, add_zero]
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + ((if p = 0 then α else []).length + 1) =
      (if p = 0 then α else []).length + 3 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, he]
    change Function.update b.workTapePos i _ j = _
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Position the code buffer for the backward catalog row, using three existing phases. -/
private def ss_bufferSeek (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) :=
  seamCompTM (skipTM n i) .done (ss_bufferAdvance n i) (Sum.inl false)

/-- The two skips and their intervening conditional step find the right edge, with a time
that depends only on the code and its chosen virtual position.

**Proof sketch.** The first catalog skip has the dropped-suffix time. The proved advance
then has the whole-word or empty-word time. Compose their framed contracts by the general
seam equations and read the final head update through the state-map field equations. -/
private theorem ss_bufferSeek_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    (ss_bufferSeek n i).runFrom (d.mapState Sum.inl) (v.length + w.length + 5) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + w.length + 5,
        ((ss_bufferSeek n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSkip_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if p = 0 then 0 else (α.length : ℤ) + 1) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferAdvance_run i α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SeekPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length + 1 + 1 +
      ((if p = 0 then α else []).length + 3) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 5 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The backward catalog row restores the first cell of a nonempty buffer and the
original position of an empty buffer, preserving the full surrounding configuration.

**Proof sketch.** For a nonempty word the forward endpoint is one beyond its right blank,
so the catalog precondition is the buffer itself. For an empty word all cells are blank.
The resulting head formula is the catalog's subtraction of the word length and one. -/
private theorem ss_bufferBack_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (skipBackTM n i).runFrom d (α.length + 3) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if α = [] then (p : ℤ) - 1 else 0) } ∧
      ∀ u < α.length + 3, ((skipBackTM n i).runFrom d u).state ≠ some .done := by
  have he : d.workTapePos i - (α.length : ℤ) - 1 =
      if α = [] then (p : ℤ) - 1 else 0 := by
    rw [hpos]
    by_cases ha : α = []
    · subst α
      simp only [ite_true, List.length_nil, Nat.cast_zero, sub_zero]
    · simp only [if_neg ha]
      omega
  obtain ⟨hr, hc, _⟩ := skipBackTM_run_ofCfg i α d hstate (by
    intro q _ _
    rw [hbuf, he]
    by_cases ha : α = []
    · subst α
      simp only [FinTM.bufferTape_nil]
    · rw [if_neg ha, zero_add])
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- Restore the empty word's origin if necessary, then clear through the catalog row.
The parameter is the virtual position chosen for the empty code, fixed for the machine. -/
private def ss_bufferClear (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (Bool ⊕ SweepPhase) :=
  seamCompTM (ss_bufferLeaf n i (if emptyPos = 0 then .pos else 0)) true
    (clearTM n i) .sweep

/-- The final buffer phases erase the code and put its head at zero. The empty code uses
its one fixed virtual position, so the machine does not depend on the input suffix.

**Proof sketch.** A nonempty buffer has a symbol at zero, so the leaf does not move. On an
empty buffer, the fixed position is zero or one and the conditional step restores zero.
The catalog clear then erases the word interval; outside that interval the public buffer
formula is already blank. Compose by the framed seam and its first-return theorem. -/
private theorem ss_bufferClear_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) - 1 else 0) :
    (ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) (2 * α.length + 4) =
      ⟨some (Sum.inr .done), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 2 * α.length + 4,
        ((ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  let mv : SignType := if emptyPos = 0 then .pos else 0
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (mv : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i mv d hstate
  change (ss_bufferLeaf n i mv).runFrom d 1 = a at hr
  have haheads : a.workTapePos = Function.update d.workTapePos i 0 := by
    have hm : d.workTapePos i +
        (if d.workTapeSymbols i = none then (mv : ℤ) else 0) = 0 := by
      rw [Cfg.workTapeSymbols_eq, hbuf, hpos]
      by_cases ha : α = []
      · rw [if_pos ha, hp ha]
        subst α
        simp only [FinTM.bufferTape_nil, ite_true]
        by_cases h : emptyPos = 0
        · simp only [mv, if_pos h, SignType.pos_eq_one, SignType.coe_one, h, Nat.cast_zero]
          omega
        · have h1 : emptyPos = 1 := by omega
          simp only [mv, if_neg h, SignType.coe_zero, h1, Nat.cast_one]
          omega
      · rw [if_neg ha]
        cases α with
        | nil => exact False.elim (ha rfl)
        | cons x xs =>
          rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
          simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, Nat.cast_zero,
            add_zero]
    dsimp only [a]
    rw [hm]
  let b := a.mapState (fun _ => SweepPhase.sweep)
  have hbstate : b.state = some .sweep := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = 0 := by
    rw [Cfg.mapState_workTapePos, haheads, Function.update_self]
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨hs, hscut, _⟩ := clearTM_run_ofCfg i α b hbstate (by
    intro q _ _
    rw [hbbuf, hbpos, zero_add])
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + (2 * α.length + 2) = 2 * α.length + 4 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    by_cases hj : j = i
    · subst j
      simp only [hbpos, zero_add, Function.update_self, true_and]
      by_cases hq : 0 ≤ q ∧ q < (α.length : ℤ)
      · rw [if_pos hq]
      · rw [if_neg hq, hbbuf, FinTM.bufferTape_eq]
        by_cases hq0 : 0 ≤ q
        · rw [if_pos hq0, List.getElem?_eq_none (by omega)]
        · rw [if_neg hq0]
    · simp only [hj, false_and, if_false, Function.update_of_ne hj]
      rw [Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, haheads]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Backward positioning followed by the fixed-origin clear, joined by the public seam. -/
private def ss_bufferFinish (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
  seamCompTM (skipBackTM n i) .done (ss_bufferClear n i emptyPos) (Sum.inl false)

/-- The backward pass and clear erase a buffer from the forward pass's endpoint.

**Proof sketch.** Apply the backward catalog specialization, then the proved fixed-origin
clear. The public seam transports their first-return cuts. Its state-map equations and
idempotence of a head update identify the framed endpoint. -/
private theorem ss_bufferFinish_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) (3 * α.length + 8) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 3 * α.length + 8,
        ((ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  obtain ⟨hr, hc⟩ := ss_bufferBack_run i α p d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if α = [] then (p : ℤ) - 1 else 0) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) - 1 else 0 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferClear_run i emptyPos he α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SweepPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipBackTM n i) .done (ss_bufferClear n i emptyPos)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipBackTM n i) .done
    (ss_bufferClear n i emptyPos) (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : α.length + 3 + 1 + (2 * α.length + 4) = 3 * α.length + 8 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Clear the captured code buffer from any of its possible virtual input positions.
All positioning and erasure phases are joined by existing seam constructors. -/
private def ss_bufferCleanup (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) :=
  seamCompTM (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run)

/-- The complete code-buffer cleanup is uniform in the suffix and ambient configuration.
Its only fixed parameter is the virtual position assigned to the empty code.

**Proof sketch.** The forward sequence positions the head for the backward pass. The
backward and clear sequence restores zero and erases the buffer. Join the two proved
contracts with the general seam theorem; sum their code-dependent times. The inherited
first-return theorem makes the final right-tagged exit fresh until that time. -/
private theorem ss_bufferCleanup_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : p ≤ α.length + 1)
    (hpe : α = [] → p = emptyPos) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    let T := v.length + w.length + 3 * α.length + 14
    (ss_bufferCleanup n i emptyPos).runFrom
      ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) T =
      ⟨some (Sum.inr (Sum.inr (Sum.inr .done))), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < T, ((ss_bufferCleanup n i emptyPos).runFrom
        ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
          Sum.inl) u).state ≠ some (Sum.inr (Sum.inr (Sum.inr .done))) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSeek_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) z :=
    ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
      Function.update d.workTapePos i
        (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩
  let b := a.mapState (fun _ => SeekPhase.run)
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferFinish_run i emptyPos he α p hpe b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SweepPhase)) =
      a.mapState (fun _ => Sum.inl .run) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) (Sum.inr (Sum.inr .done))
    hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length +
      (if p = 0 then α else []).length + 5 + 1 + (3 * α.length + 8) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 3 * α.length + 14 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The native rewind has a separate pre-exit anchor so that the final exit is fresh. -/
private inductive ss_RewindState where
  | enter | scan | stop | done
  deriving DecidableEq, Fintype

/-- A native input-only leaf; its scan is handled by the published rewind contracts. -/
private def ss_inputRewind (n : ℕ) : MultiTapeTM n Bool ss_RewindState where
  q₀ := .enter
  tr := fun q inp _ => match q with
    | .enter => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .stop)
    | .stop => FinTM.controlAction 0 (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- The final rewind anchor is stationary for every further time.

**Proof sketch.** Its own transition is a zero control action. Induction through the public
successor equation preserves the configuration; the control-action equation fixes its fields. -/
private theorem ss_inputRewind_done {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .done) (t : ℕ) :
    (ss_inputRewind n).runFrom d t = d := by
  have hs : (ss_inputRewind n).step d = d := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply d = d
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · rfl
    · rfl
  induction t with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hs]

/-- The native input rewind returns at an exact position-dependent time, with a first exit
and fixed work heads throughout. Its time is independent of the input's suffix.

**Proof sketch.** One left step puts the input head within the word. The public scan equation
then reaches the pre-exit anchor after exactly the old position plus one steps. An earlier
final exit would be stationary and contradict that anchor. The public rewind-head theorem
has the same pre-exit time, since leaving that anchor enters the stationary final exit.
One final stationary step completes the run. -/
private theorem ss_inputRewind_run {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .enter)
    (hp : 0 < d.inputPos.val) :
    (ss_inputRewind n).runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } ∧
      (∀ u < d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).workTapePos = d.workTapePos := by
  let M := ss_inputRewind n
  let c : Cfg n Bool ss_RewindState z :=
    { d with state := some .scan, inputPos := moveInputPos d.inputPos .neg }
  have hstep : M.step d = c := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction .neg (some ss_RewindState.scan)).apply d = c
    rw [FinTM.controlAction_apply]
  have hcp : c.inputPos.val ≤ z.length := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    have := d.inputPos.isLt
    omega
  have hscan := FinTM.rewind_scan M .scan (some .stop)
    (fun inp _ => by cases inp <;> rfl) c rfl hcp
  have ht : 1 + (c.inputPos.val + 1) = d.inputPos.val + 1 := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    omega
  have hstop : M.runFrom d (d.inputPos.val + 1) =
      { d with state := some .stop, inputPos := 1 } := by
    rw [← ht, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step' (cfg := d) (t := 0),
      MultiTapeTM.runFrom_zero, hstep, hscan]
  have hlast : ∀ (a : Cfg n Bool ss_RewindState z), a.state = some .stop →
      M.step a = { a with state := some .done } := by
    intro a ha
    rw [MultiTapeTM.step_of_some ha]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply a = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
  have hcut : ∀ u ≤ d.inputPos.val + 1, (M.runFrom d u).state ≠ some .done := by
    intro u hu hdone
    have hf := ss_inputRewind_done (M.runFrom d u) hdone (d.inputPos.val + 1 - u)
    have hsum : u + (d.inputPos.val + 1 - u) = d.inputPos.val + 1 := by omega
    rw [← MultiTapeTM.runFrom_add, hsum, hstop] at hf
    have heq := congrArg Cfg.state hf
    rw [hdone] at heq
    cases heq
  have hret : M.runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } := by
    rw [show d.inputPos.val + 2 = (d.inputPos.val + 1) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', hstop, hlast _ rfl]
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads M .enter .scan (some .stop)
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have htime : r = d.inputPos.val + 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx : (M.runFrom d (r + 1)).state = some .done := by
        rw [MultiTapeTM.runFrom_succ_eq_step', hrun, hlast _ rfl]
      exact hcut (r + 1) (by omega) hx
    · have hf := ss_inputRewind_done
        ({ d with state := some .done, inputPos := 1 } : Cfg n Bool ss_RewindState z)
        rfl (r - (d.inputPos.val + 2))
      have hsum : d.inputPos.val + 2 + (r - (d.inputPos.val + 2)) = r := by omega
      rw [← hret, ← MultiTapeTM.runFrom_add, hsum, hrun, hret] at hf
      have heq := congrArg Cfg.state hf
      cases heq
  refine ⟨hret, fun u hu => hcut u (by omega), ?_⟩
  intro u hu
  by_cases h : u ≤ d.inputPos.val + 1
  · exact hheads u (by omega)
  · have heq : u = d.inputPos.val + 2 := by omega
    rw [heq, hret]

/-- A live configuration's state map preserves its physical frame, read through the public
field equations rather than through the definition of state renaming.

**Proof sketch.** Configuration extensionality reduces to the five published field equations;
the live-state equation reduces the option map to one constructor. -/
private theorem ss_live_map {n : ℕ} {P Q : Type} {z : List Bool}
    (d : Cfg n Bool P z) (q : P) (hq : d.state = some q) (f : P → Q) :
    d.mapState f = ⟨some (f q), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, hq, Option.map_some]
  · exact Cfg.mapState_inputPos _ _
  · funext i p
    exact Cfg.mapState_workTapes _ _ _ _
  · funext i
    exact Cfg.mapState_workTapePos _ _ _
  · exact Cfg.mapState_output _ _

/-- Selected code and capture cells give a two-update normal form for any field.

**Proof sketch.** At the capture index use its equation. In the selected block, injectivity
identifies index zero; every other selected field has the background value. Outside both
blocks use the framing equation. This single argument applies to tapes and head positions. -/
private theorem ss_block_updates {A : Type} {m n : ℕ} (ι : Fin m ↪ Fin n)
    (cap : Fin n) (zero : Fin m) (hz : zero.val = 0)
    (f : Fin n → A) (base code captured : A)
    (hsel : ∀ j, f (ι j) = if j.val = 0 then code else base)
    (hc : f cap = captured)
    (ho : ∀ j, j ∉ Set.range ι → j ≠ cap → f j = base) :
    f = Function.update (Function.update (fun _ => base) (ι zero) code) cap captured := by
  funext j
  by_cases hj : j = cap
  · subst j
    rw [hc, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hs : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hs
      rw [hsel]
      by_cases hi : i = zero
      · subst i
        rw [hz, if_pos rfl, Function.update_self]
      · have hival : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext (h.trans hz.symm))
        have hislot : ι i ≠ ι zero := fun h => hi (ι.injective h)
        rw [if_neg hival, Function.update_of_ne hislot]
    · have hjz : j ≠ ι zero := by
        intro h
        exact hs ⟨zero, h.symm⟩
      rw [ho j hs hj, Function.update_of_ne hjz]

/-- The source block sits after the simulated tapes, table, and summary. -/
private def ss_sourceSlot (m k : ℕ) : Fin m ↪ Fin ((m + 1) + (k + 2)) where
  toFun i := ⟨k + 2 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change k + 2 + i.val = k + 2 + j.val at hv
    omega

/-- The capture tape is last, beyond the source block. -/
private def ss_captureTape (m k : ℕ) : Fin ((m + 1) + (k + 2)) :=
  ⟨k + 2 + m, by omega⟩

/-- The capture tape is separate, and all first `k + 2` tapes lie outside both blocks.

**Proof sketch.** Every selected index lies between `k + 2` and `k + 2 + m - 1`.
The capture index is `k + 2 + m`, and each reserved index is smaller than `k + 2`. -/
private theorem ss_capture_indices (m k : ℕ) :
    ss_captureTape m k ∉ Set.range (ss_sourceSlot m k) ∧
    ∀ j : Fin ((m + 1) + (k + 2)), j.val < k + 2 →
      j ∉ Set.range (ss_sourceSlot m k) ∧ j ≠ ss_captureTape m k := by
  have hs (i : Fin m) : k + 2 ≤ (ss_sourceSlot m k i).val ∧
      (ss_sourceSlot m k i).val < (ss_captureTape m k).val := by
    change k + 2 ≤ k + 2 + i.val ∧ k + 2 + i.val < k + 2 + m
    omega
  constructor
  · rintro ⟨i, hi⟩
    have := (hs i).2
    rw [hi] at this
    exact (lt_irrefl _ this)
  · intro j hj
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have := (hs i).1
      rw [hi] at this
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = k + 2 + m at hv
      omega

/-- **U2-S, the `k`-generic startup** (the startup of `Turing.exists_selfStartupTM`, generic in
the work-tape count). For a `k`-tape scheme `E` there is a binary machine with `K + (k + 2)` work
tapes and an exit state such that for every code `α` there are a time `T` and a space bound `B`,
**depending on `α` only**, with the following property on every input `pairEncode α w`. At time
`T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before;
* tapes `0, …, k - 1`, the simulated work tapes, blank, and tape `k` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `k + 1` holding the decoded machine's initial state in unary from cell `2` (cells `0`
  and `1` blank), the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam
(`Turing.StepBlock.Rep`) for the decoded machine's initial configuration on the same input, and
its restriction to the first `k + 2` tapes is H2-F's encoding `Turing.StepBlock.forwardLoopCfg` of
that configuration. [AB09, §1.4.1, Theorem 1.9]

**Proof sketch.** As `Turing.exists_selfStartupTM`'s, at `k` mirrored tapes. Extract and
canonize: the prefix parser composed with the scheme's canonizer by buffered composition, its
emissions captured on a scratch tape (the pattern of `Turing.universalCanonTM` and
`Turing.universalCaptureTM`, with `E.canonizer` in place of the one-tape scheme's); it ends after
`3|α| + 4 + E.canonizerTime |α|` steps with `serializeK (E.machine α)` captured and the input
head at `2|α| + 3`. Skip the doubled state count and the separator of
`serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`, copy the unary initial state to
tape `k + 1` at offset `2` and the table to tape `k`; clear the scratch and the buffer. Rewind the
input head to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends
on `α` only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's
halting time bounds its cells).

**Implementation.** The scheme's canonizer runs behind the public cleaner, which blanks its work
tapes and returns its heads, and the capture uses that machine's first halting time `t α`
(`Turing.MultiTapeTM.exists_first_halt`): the capture ends after `3|α| + 4 + t α` steps rather
than at the bound `E.canonizerTime |α|`. The code buffer is cleared by the catalog skip, skip back
and clear around a one-step move that acts only on a blank cell; on the empty code the buffer is
all blank, so the canonizer's final head position on the empty code is a fixed parameter of the
machine, chosen from `E`. The input head is rewound by `Turing.FinTM.rewind_scan` and
`Turing.FinTM.rewind_heads`, in `2|α| + 5` steps. -/
theorem exists_selfStartupTMK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
              else if j.val = k + 1 then
                fun p => FinTM.bufferTape (unaryFin (E.machine α).q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  classical
  let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer E.canonizer)
  let n := (G.k + 1) + (k + 2)
  let ι := ss_sourceSlot G.k k
  let cap := ss_captureTape G.k k
  have hcap : cap ∉ Set.range ι := (ss_capture_indices G.k k).1
  have hm : 0 < G.k := by
    dsimp only [G]
    rw [FinTM.bufferedCompTM_k, universalPrefixTM_k]
    omega
  let zero : Fin G.k := ⟨0, hm⟩
  let code := ι zero
  let tbl : Fin n := ⟨k, by dsimp only [n]; omega⟩
  let sm : Fin n := ⟨k + 1, by dsimp only [n]; omega⟩
  have htbl := (ss_capture_indices G.k k).2 tbl (by dsimp only [tbl]; omega)
  have hsm := (ss_capture_indices G.k k).2 sm (by dsimp only [sm]; omega)
  have hts : tbl ≠ sm := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [tbl, sm] at hv
    omega
  have hct : code ≠ tbl := fun h => htbl.1 ⟨zero, h⟩
  have hcs : code ≠ sm := fun h => hsm.1 ⟨zero, h⟩
  have hcc : code ≠ cap := fun h => hcap ⟨zero, h⟩
  let A := ss_captureTM G ι cap
  have hcapture := fun α => ss_capturedPrefix_fields E.canonizer
    (fun β => serializeK (E.machine β)) E.canonizerTime E.canonizer_computes ι cap hcap α
  dsimp only at hcapture
  choose t p hp hc using hcapture
  have hp0 : p [] ≤ 1 := by simpa only [List.length_nil, zero_add] using hp []
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ :=
    ss_serialized_layout n cap tbl sm htbl.2.symm hsm.2.symm hts
  letI := hQ
  letI := hD
  let J := ss_bufferCleanup n code (p [])
  let jentry : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inl (Sum.inl .run)
  let jexit : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inr (Sum.inr (Sum.inr .done))
  let B := seamCompTM J jexit (ss_inputRewind n) .enter
  let D := seamCompTM L done B (Sum.inl jentry)
  let W := seamCompTM A (Sum.inr ()) D (Sum.inl entry)
  let R := { W with q₀ := Sum.inl A.q₀ }
  let exit : (G.State ⊕ Unit) ⊕ Q ⊕
      (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
        ss_RewindState) := Sum.inr (Sum.inr (Sum.inr .done))
  refine ⟨G.k + 1, _, inferInstance, inferInstance, R, exit, ?_⟩
  intro α
  obtain ⟨l, hl, hlayout⟩ := hL (E.machine α)
  let a := 3 * α.length + 4 + t α
  let v := if p α = 0 then [] else α.drop (p α - 1)
  let w₀ := if p α = 0 then α else []
  let b := v.length + w₀.length + 3 * α.length + 14
  let r := 2 * α.length + 5
  let T := a + 1 + (l + 1 + (b + 1 + r))
  refine ⟨T, n * (T + 1), ?_⟩
  intro w
  let d₀ := A.initCfg (pairEncode α w)
  let d₁ := A.runFrom d₀ a
  obtain ⟨hstate, hip, hsel, hheads, hcapt, hother, hcut, hsil, _⟩ := hc α w
  have hs₁ : d₁.state = some (Sum.inr ()) := hstate
  have ht₁ : d₁.workTapes = Function.update
      (Function.update (fun _ => fun _ => none) code (FinTM.bufferTape α))
      cap (FinTM.bufferTape (serializeK (E.machine α))) :=
    ss_block_updates ι cap zero rfl _ _ _ _ hsel hcapt.1
      (fun j hj hjc => (hother j hj hjc).1)
  have hh₁ : d₁.workTapePos = Function.update
      (Function.update (fun _ => 0) code ((p α : ℤ) - 1))
      cap (serializeK (E.machine α)).length :=
    ss_block_updates ι cap zero rfl _ _ _ _ hheads hcapt.2
      (fun j hj hjc => (hother j hj hjc).2)
  have ho₁ : d₁.output = [] := hsil a le_rfl
  let d₂ := d₁.mapState (fun _ => entry)
  have hd₂ : d₂.state = some entry := by
    rw [Cfg.mapState_state, hs₁, Option.map_some]
  have ht₂ (j : Fin n) : d₂.workTapes j = d₁.workTapes j := by
    funext q
    exact Cfg.mapState_workTapes _ _ _ _
  have hh₂ (j : Fin n) : d₂.workTapePos j = d₁.workTapePos j :=
    Cfg.mapState_workTapePos _ _ _
  obtain ⟨hs₃, hi₃, ht₃, hh₃, ho₃, hcut₃⟩ := hlayout d₂ hd₂
    ((ht₂ cap).trans hcapt.1) ((hh₂ cap).trans hcapt.2)
    ((ht₂ tbl).trans (hother tbl htbl.1 htbl.2).1)
    ((hh₂ tbl).trans (hother tbl htbl.1 htbl.2).2)
    ((ht₂ sm).trans (hother sm hsm.1 hsm.2).1)
    ((hh₂ sm).trans (hother sm hsm.1 hsm.2).2)
  let d₃ := L.runFrom d₂ l
  let c : Cfg n Bool SeekPhase (pairEncode α w) :=
    ⟨some .run, d₃.inputPos, d₃.workTapes, d₃.workTapePos, d₃.output⟩
  have hbuf : c.workTapes code = FinTM.bufferTape α := by
    change d₃.workTapes code = _
    rw [ht₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, ht₂]
    exact (hsel zero).trans (if_pos rfl)
  have hpos : c.workTapePos code = (p α : ℤ) - 1 := by
    change d₃.workTapePos code = _
    rw [hh₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, hh₂]
    exact (hheads zero).trans (if_pos rfl)
  obtain ⟨hj, hjcut⟩ := ss_bufferCleanup_run code (p []) hp0 α (p α) (hp α)
    (fun h => congrArg p h) c rfl hbuf hpos
  have hjstart :
      ((c.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) = d₃.mapState (fun _ => jentry) := by
    rw [ss_live_map c .run rfl,
      ss_live_map _ (Sum.inl .run) rfl, ss_live_map d₃ done hs₃]
  rw [hjstart] at hj hjcut
  let d₄ : Cfg n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)))
      (pairEncode α w) :=
    ⟨some jexit, d₃.inputPos, Function.update d₃.workTapes code (fun _ => none),
      Function.update d₃.workTapePos code 0, d₃.output⟩
  change J.runFrom (d₃.mapState (fun _ => jentry)) b = d₄ at hj
  change ∀ u < b, (J.runFrom (d₃.mapState (fun _ => jentry)) u).state ≠ some jexit at hjcut
  let d₅ := d₄.mapState (fun _ => ss_RewindState.enter)
  have hd₅ : d₅.state = some .enter := by rw [Cfg.mapState_state]; rfl
  have hi₅ : d₅.inputPos.val = 2 * α.length + 3 := by
    rw [Cfg.mapState_inputPos]
    change d₃.inputPos.val = _
    rw [hi₃, Cfg.mapState_inputPos]
    exact hip
  obtain ⟨hrew, hrewcut, _⟩ := ss_inputRewind_run d₅ hd₅ (by omega)
  have htime : d₅.inputPos.val + 2 = r := by dsimp only [r]; omega
  rw [htime] at hrew hrewcut
  have hb := seamCompTM_run_ofCfg J jexit (ss_inputRewind n) .enter hj rfl hjcut hrew
  have hbcut := seamCompTM_firstReturn_ofCfg J jexit (ss_inputRewind n) .enter .done
    hj rfl hjcut hrew rfl hrewcut
  have hbstart : (d₃.mapState (fun _ => jentry)).mapState
      (Sum.inl : _ → _ ⊕ ss_RewindState) = d₃.mapState (fun _ => Sum.inl jentry) := by
    rw [ss_live_map d₃ done hs₃, ss_live_map _ jentry rfl, ss_live_map d₃ done hs₃]
  rw [hbstart] at hb hbcut
  have hd := seamCompTM_run_ofCfg L done B (Sum.inl jentry) rfl hs₃ hcut₃ hb
  have hdcut := seamCompTM_firstReturn_ofCfg L done B (Sum.inl jentry) (Sum.inr .done)
    rfl hs₃ hcut₃ hb (by rw [Cfg.mapState_state]; rfl) hbcut
  have hdstart : (d₁.mapState (fun _ => entry)).mapState
      (Sum.inl : Q → Q ⊕
        (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
          ss_RewindState)) = d₁.mapState (fun _ => Sum.inl entry) := by
    rw [ss_live_map d₁ (Sum.inr ()) hs₁, ss_live_map _ entry rfl,
      ss_live_map d₁ (Sum.inr ()) hs₁]
  rw [hdstart] at hd hdcut
  have hw := seamCompTM_run_ofCfg A (Sum.inr ()) D (Sum.inl entry) rfl hs₁ hcut hd
  have hwcut := seamCompTM_firstReturn_ofCfg A (Sum.inr ()) D (Sum.inl entry)
    (Sum.inr (Sum.inr .done)) rfl hs₁ hcut hd
    (by rw [Cfg.mapState_state, Cfg.mapState_state]; rfl) hdcut
  have hinit : R.initCfg (pairEncode α w) = d₀.mapState Sum.inl := by
    apply Cfg.ext
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_state, Cfg.mapState_state,
        d₀, Option.map_some]
      rfl
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos, Cfg.mapState_inputPos,
        d₀]
    · funext j q
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes, Cfg.mapState_workTapes,
        d₀]
    · funext j
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos,
        Cfg.mapState_workTapePos, d₀]
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, Cfg.mapState_output,
        d₀]
  have htfinal : Function.update d₃.workTapes code (fun _ => none) =
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
        else if j.val = k + 1 then
          fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
        else fun _ => none := by
    funext j q
    rw [ht₃]
    have hdtapes : d₂.workTapes = d₁.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hdtapes, ht₁]
    by_cases hjt : j = tbl
    · subst j
      simp only [tbl, Function.update_of_ne hct.symm, Function.update_of_ne hts,
        Function.update_self, ite_true]
    · have hjtv : j.val ≠ k := fun h => hjt (Fin.ext h)
      by_cases hjs : j = sm
      · subst j
        simp only [sm, Function.update_of_ne hcs.symm, Function.update_self,
          if_neg hjtv, ite_true]
      · have hjsv : j.val ≠ k + 1 := fun h => hjs (Fin.ext h)
        simp only [if_neg hjtv, if_neg hjsv]
        by_cases hjc : j = code
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjc, Function.update_of_ne hjs,
            Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hhfinal : Function.update d₃.workTapePos code 0 = fun _ => 0 := by
    funext j
    rw [hh₃]
    have hdheads : d₂.workTapePos = d₁.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hdheads, hh₁]
    by_cases hjc : j = code
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hjc]
      by_cases hjs : j = sm
      · subst j
        rw [Function.update_self]
      · rw [Function.update_of_ne hjs]
        by_cases hjt : j = tbl
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hofinal : d₃.output = [] := by
    rw [ho₃ l le_rfl, Cfg.mapState_output]
    exact ho₁
  have hfinal : R.runFrom (R.initCfg (pairEncode α w)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
          else if j.val = k + 1 then
            fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
          else fun _ => none,
        fun _ => 0, []⟩ := by
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    rw [hw]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes]
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun htfinal j) q
    · funext j
      simp only [Cfg.mapState_workTapePos]
      rw [Cfg.mapState_workTapePos]
      exact congrFun hhfinal j
    · simp only [Cfg.mapState_output]
      rw [Cfg.mapState_output]
      exact hofinal
  refine ⟨hfinal, ?_, ?_, MultiTapeTM.spaceUsed_le_mul_succ R _ T⟩
  · intro u hu
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    exact hwcut u hu
  · intro u hu
    have hpre := MultiTapeTM.output_prefix R (R.initCfg (pairEncode α w)) hu
    rw [hfinal] at hpre
    exact List.prefix_nil.mp hpre

/-! ## U2-U: the self-application universal machine -/

/-- **U2-U, the self-application universal machine, with time and space ledgers and the
converse** [AB09, Theorem 1.9 and Exercise 4.1, at self-application]. For a `k`-tape scheme `E`
there is a binary machine `U` such that for every code `α` there is a constant `C > 0`
(depending on `α` only) with, for every `w`:
* whenever the machine coded by `α` halts on `pairEncode α w` with `output` within `t` steps,
  `U` halts on the same input with the same `output` within `C · (t + 1)` steps, having visited
  by then at most `C · (s + 1)` cells, `s` the coded machine's cells by time `t`;
* every completed output of `U` on `pairEncode α w` is a completed output of the coded machine
  there (so divergence is preserved).

`C` depends on the code string, as in `Turing.universal` (Argument E): it absorbs the canonizer's
arbitrary time and the table's length. B6's `Turing.exists_selfUniversal` is the case `k = 1`
(forward clause, space only).

**Proof sketch.** Startup, then H2-F. (i) U2-S reaches, after `T_α` steps and within `B_α`
cells, H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg (pairEncode α w))` of
the coded machine `M := E.machine α`, on the block's tapes, the other tapes blank; seam it into
H2-F's machine `L` (R2, R1 on the first `k + 2` tapes). (ii) H2-F's lockstep
(`Turing.Lockstep.runFrom`) runs `M` from its initial configuration through its first halt
`t₀ ≤ t`: `L` is then at the encoding of the halted configuration, halted, with `M`'s output,
after `Σ_{u < t₀} cost ≤ (50 · (|tableBitsK| + 1) + C_L) · t` steps; with the seam's one step,
the time is at most `T_α + 1 + (50 · (|tableBitsK| + 1) + C_L) · t ≤ C · (t + 1)`. (iii) Space:
the mirrored heads visit only `M`'s cells, at most `s`; the auxiliary heads stay in an interval
of length `2 (50 · (|tableBitsK| + 1) + C_L) + 1`; the startup `B_α`; in all `≤ C · (s + 1)`,
and the halted configuration is frozen afterwards. (iv) Converse: by the lockstep's cut
(`Turing.Lockstep.cut`) `L` is live while `M` is, and an encoded live configuration is live, so
`U` halts only at the encoding of a halted configuration of `M`, whose output is `M`'s. -/
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  let U : FinTM Bool :=
    { k := K + (k + 2), State := P ⊕ Q, tm := startupLoopTM R exit L entry }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, B, hRα⟩ := hR α
  let M := E.machine α
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let N := K + (k + 2)
  let C := T + 1 + D + B + N * (2 * D + 1) + N
  have hTC : T + 1 ≤ C := by dsimp only [C]; omega
  have hDC : D ≤ C := by dsimp only [C]; omega
  have hNC : N ≤ C := by dsimp only [C]; omega
  have hBC : B + N * (2 * D + 1) ≤ C := by dsimp only [C]; omega
  refine ⟨C, by omega, ?_⟩
  intro w
  let z := pairEncode α w
  obtain ⟨hrun, hcut, _, hB⟩ := hRα w
  obtain ⟨cost, hlock, hcost, hledger⟩ := hL (x := z) M
  have hUrun := startupLoopTM_runFrom R exit L entry
    (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
    (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) z output t).mp hcomp
    obtain ⟨t₀, ht₀, hfirst, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg z) u)
    have hUhalt : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).state = none := by
      rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, hr,
        StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none]
    have hUout : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).output = output := by
      rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hr,
        StepBlock.forwardLoopCfg_output]
      exact hout
    have htime : T + 1 + v ≤ C * (t + 1) := by
      calc
        _ ≤ C + D * t := Nat.add_le_add hTC hvbound
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    have hUcomp : U.ComputesInTime z output (T + 1 + v) :=
      (FinTM.computesInTime_iff U z output (T + 1 + v)).mpr ⟨hUhalt, hUout⟩
    refine ⟨hUcomp.mono htime, ?_⟩
    let s := M.spaceUsed (M.initCfg z) t
    have hloop : ∀ i, L.spaceUsedByTape
        (StepBlock.forwardLoopCfg entry M (M.initCfg z)) v i ≤ s + (2 * D + 1) := by
      intro i
      by_cases hi : i.val < k
      · let j : Fin k := ⟨i.val, hi⟩
        have hij : Fin.castAdd 2 j = i := Fin.ext rfl
        rw [← hij, MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t₀ j).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).1 j)
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card :=
            Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (M.initCfg z) ht₀ j)
          _ = M.spaceUsedByTape (M.initCfg z) t j :=
            (MultiTapeTM.spaceUsedByTape_eq_card (tm := M) _ t j).symm
          _ ≤ s := MultiTapeTM.spaceUsedByTape_le_spaceUsed (tm := M) _ t j
          _ ≤ _ := by omega
      · rw [MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (Finset.Icc (-(D : ℤ)) (D : ℤ)).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).2 i (by omega))
          _ = 2 * D + 1 := by rw [Int.card_Icc]; omega
          _ ≤ _ := by omega
    have hspace := startupLoopTM_spaceUsed_le R exit L entry
      (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
      (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
      v B (s + (2 * D + 1)) hB (by omega) hloop
    calc
      _ ≤ B + N * (s + (2 * D + 1)) :=
        FinTM.ComputesInTime.spaceUsed_le_of_halt hUcomp hspace _
      _ = N * s + (B + N * (2 * D + 1)) := by ring
      _ ≤ C * s + C := Nat.add_le_add (Nat.mul_le_mul_right s hNC) hBC
      _ = _ := by dsimp only [s, M, EffectiveCodeK.toFinTM]; ring
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le R exit L entry T
      (by rw [hrun]; exact Option.some_ne_none exit) hcut
    have hafter : T + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) hhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hafter
    rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at hhalt
    rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at hout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost v hhalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) z output t).mpr
      ⟨ht, ho.trans hout⟩⟩

/-! ## U2-E: the code-first evaluator -/


/-- The startup embedded with one extra tape, followed by the header ruler preparation. -/
private noncomputable def uk_suffixStartupTM {k K : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P) :
    MultiTapeTM (K + (k + 3)) Bool (P ⊕ (Fin 4 ⊕ RewindPhase)) :=
  { seamCompTM
      ({ embedEmitTM (Fin.castLEEmb (by omega)) R with q₀ := R.q₀ }) exit
      (headerRulerTM ⟨k + 2, by omega⟩) (Sum.inl 0) with q₀ := Sum.inl R.q₀ }

/-- The original startup followed by the header scan and rewind reaches the suffix seam.

**Proof sketch.** Embed the startup in one more tape and reconstruct its initial
and final configurations with the public embedding theorem. At the endpoint,
the tape immediately after the simulation bank is blank. The framed header
contract prepares it, and the public seam composes the two runs and their cuts. -/
private theorem uk_suffixStartup_run {k K n : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (α x : List Bool) (T : ℕ)
    (hrun : R.runFrom (R.initCfg (pairEncode α x)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
          else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
          else fun _ => none,
        fun _ => 0, []⟩)
    (hcut : ∀ t < T, (R.runFrom (R.initCfg (pairEncode α x)) t).state ≠ some exit) :
    let ℓ := 2 * α.length + 2
    let hlen : ℓ + 1 < (pairEncode α x).length + 2 := by rw [length_pairEncode]; omega
    (uk_suffixStartupTM R exit).runFrom ((uk_suffixStartupTM R exit).initCfg (pairEncode α x))
        (T + 1 + (2 * ℓ + 3)) = suffixRulerCfg (Sum.inr (Sum.inr .done)) M
          (pairEncode α x) ℓ hlen ∧
      (∀ t < T + 1 + (2 * ℓ + 3),
        ((uk_suffixStartupTM R exit).runFrom
          ((uk_suffixStartupTM R exit).initCfg (pairEncode α x)) t).state ≠
            some (Sum.inr (Sum.inr .done))) := by
  let z := pairEncode α x
  let ℓ := 2 * α.length + 2
  let σ := Fin.castLEEmb (by omega : K + (k + 2) ≤ K + (k + 3))
  let A := ({ embedEmitTM σ R with q₀ := R.q₀ } : MultiTapeTM (K + (k + 3)) Bool P)
  let i : Fin (K + (k + 3)) := ⟨k + 2, by omega⟩
  let B := headerRulerTM i
  let d : Cfg (K + (k + 3)) Bool P z :=
    ⟨some exit, 1,
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
        else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have initEmbed : embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (R.initCfg z) =
      A.initCfg z := by
    apply embedEmitCfg_eq
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_state]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, List.nil_append]
    · intro j
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
  have aRun : A.runFrom (A.initCfg z) T = d := by
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, z, hrun]
    apply embedEmitCfg_eq
    · rfl
    · rfl
    · rfl
    · intro j; exact ⟨rfl, rfl⟩
    · intro j hj
      have hge : K + (k + 2) ≤ j.val := by
        by_contra h
        apply hj
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext; rfl
      constructor
      · funext a
        simp only [d, if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
      · rfl
  have aCut : ∀ t < T, (A.runFrom (A.initCfg z) t).state ≠ some exit := by
    intro t ht
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, embedEmitCfg_state]
    exact hcut t ht
  let c := d.mapState (fun _ => (0 : Fin 4))
  have cstate : c.state = some 0 := by rw [Cfg.mapState_state]; rfl
  have cpos : c.inputPos.val = 1 + 0 := by rw [Cfg.mapState_inputPos]; rfl
  have cblank : ∀ a, c.workTapes i a = none := by
    intro a
    rw [Cfg.mapState_workTapes]
    simp only [d, i, if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1)]
  obtain ⟨bRun, bCut⟩ := headerRulerTM_run i c 0 cpos cstate α x
    (by rw [List.drop_zero]) cblank
  have cmap : c.mapState Sum.inl = d.mapState (fun _ => (Sum.inl 0 : Fin 4 ⊕ RewindPhase)) := by
    rw [Cfg.mapState_mapState]; rfl
  rw [cmap] at bRun bCut
  have clen : c.inputPos.val + ℓ < z.length + 2 := by
    rw [cpos]
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have plen : ℓ + 1 < z.length + 2 := by
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have final :
      (⟨some (Sum.inr RewindPhase.done),
        ⟨c.inputPos.val + ℓ, clen⟩,
        Function.update c.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - c.workTapePos i)),
        c.workTapePos, c.output⟩ : Cfg (K + (k + 3)) Bool (Fin 4 ⊕ RewindPhase) z).mapState
          Sum.inr =
        suffixRulerCfg (Sum.inr (Sum.inr .done) : P ⊕ (Fin 4 ⊕ RewindPhase)) M z ℓ plen := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, suffixRulerCfg_state]; rfl
    · rw [Cfg.mapState_inputPos, suffixRulerCfg_inputPos]
      apply Fin.ext
      change c.inputPos.val + ℓ = ℓ + 1
      rw [cpos]
      omega
    · funext j a
      rw [Cfg.mapState_workTapes, suffixRulerCfg_workTapes]
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, c, Cfg.mapState_workTapePos, d, sub_zero,
          i, if_neg (by omega : k + 2 ≠ k),
          if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · have hjv : j.val ≠ k + 2 := by intro h; apply hj; exact Fin.ext h
        simp only [Function.update_of_ne hj, c, Cfg.mapState_workTapes, d, if_neg hjv]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, suffixRulerCfg_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, suffixRulerCfg_output]
  have init : (uk_suffixStartupTM R exit).initCfg z = (A.initCfg z).mapState Sum.inl := by
    exact MultiTapeTM.initCfg_eq_mapState A (uk_suffixStartupTM R exit) Sum.inl rfl z
  constructor
  · rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact (seamCompTM_run_ofCfg A exit B (Sum.inl 0) aRun rfl aCut bRun).trans final
  · intro t ht
    rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg A exit B (Sum.inl 0) (Sum.inr .done)
      aRun rfl aCut bRun rfl bCut t ht

/-- **U2-E, the code-first evaluator** [AB09, Theorem 1.9, the evaluator `U(x, α) = M_α(x)`, in
the code-first layout of `Turing.universal`]. For a `k`-tape scheme `E` there is a binary
machine `U` such that for every code `α` there is a constant `C` (depending on `α` only) with,
for every input `x`:
* whenever the machine coded by `α` halts on `x` with `output` within `t` steps, `U` halts on
  `pairEncode α x` with the same `output` within `C · (t + 1)` steps (no term in `|x|`);
* every completed output of `U` on `pairEncode α x` is a completed output of the coded machine
  on `x`.

At `k = 1` and `E := c.toK` this is `Turing.universal c`'s statement (shown in the gate's
probe); re-deriving `Turing.universal` from it is deferred. At `k = 2` it is the core of
Theorem 1.9 at `T log T` with the Hennie–Stearns conversion (design note §4).

**Proof sketch.** (i) *Code-first startup:* scan the doubled code and its separator, writing
one ruler cell per header cell, so the ruler is `true^ℓ` with `ℓ = 2|α| + 2`, the header length
(`Turing.universal_pair_length`); extract and canonize `α` as U2-S does, installing H2-F's
encoding of `M := E.machine α`'s initial configuration on the virtual input `x` (virtual
position `1`, physical head at `ℓ + 1`). (ii) *Ruler host:* run H2-F's machine `L` through H5's
bounded-prefix ruler host (`Turing.exists_rulerHostTM`, `Turing.RulerAt`): a block simulation
of `L` on the suffix input `x`, with at most `C_R · (ℓ + 1)` host steps per step of `L`, the same
bank and output, and exit cut. Composing with H2-F's lockstep, each step of `M` costs at most
`C_R (ℓ + 1)(50 · (|tableBitsK| + 1) + C_L)`, a constant for fixed `α`; with the startup this is
`≤ C · (t + 1)`. (iii) *Converse:* the ruler host does not halt before `L`, nor `L` before `M`
(the two cuts), so every completed output of `U` is `M`'s on `x`.

**Implementation.** The steps of the sketch run in a different order. The startup
`Turing.exists_selfStartupTMK` runs first, on `pairEncode α x` (its endpoint does not depend on
`x`), embedded in the first `K + (k + 2)` of `K + (k + 3)` tapes. A finite-state scan then reads
the header from input position `1` in aligned pairs, marking one cell for each header cell on
tape `k + 2`, which the startup leaves blank, and stops at the separator with the input head at
`ℓ + 1`; the work-tape rewind `Turing.rewindTM` returns that tape's head to its first cell. After
`T + 2ℓ + 4` steps in all (seams included), the first `k + 3` tapes hold the ruler host's
presentation `Turing.rulerHostCfg` of the forwarding loop's encoding of `M`'s initial
configuration on `x`, with the ruler as the last of them and the initial tag `false` (virtual
input position `1`). From there the ruler host of `Turing.exists_rulerHostTM` runs the forwarding
loop of `Turing.StepBlock.exists_forwardLoopTM`. With `T` the startup's time, `D` the loop's
per-step bound `50 · (|tableBitsK| + 1) + C_L` and `C_R` the host's factor, the constant is
`C = T + 2ℓ + 5 + C_R (ℓ + 1) D`, which depends on `α` only. -/
theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  obtain ⟨V, fV, dV, H, inj, C_R, hCR, hH⟩ := exists_rulerHostTM L
  letI : Fintype V := fV
  letI : DecidableEq V := dV
  let A := uk_suffixStartupTM R exit
  let finish : P ⊕ (Fin 4 ⊕ RewindPhase) := Sum.inr (Sum.inr .done)
  let U : FinTM Bool :=
    { k := K + (k + 3), State := (P ⊕ (Fin 4 ⊕ RewindPhase)) ⊕ V,
      tm := startupLoopTM (k := k + 1) A finish H (inj entry false) }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, _, hRα⟩ := hR α
  let M := E.machine α
  let ℓ := 2 * α.length + 2
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let T_A := T + 1 + (2 * ℓ + 3)
  let F := C_R * (ℓ + 1)
  let C := T_A + 1 + F * D
  have hAC : T_A + 1 ≤ C := by dsimp only [C]; omega
  have hDC : F * D ≤ C := by dsimp only [C]; omega
  refine ⟨C, ?_⟩
  intro x
  let z := pairEncode α x
  have hz : z.length = ℓ + x.length := length_pairEncode α x
  have hlen : ℓ + 1 < z.length + 2 := by omega
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; omega
  obtain ⟨hrun, hcut, _, _⟩ := hRα x
  obtain ⟨aRun, aCut⟩ := uk_suffixStartup_run R exit M α x T hrun hcut
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  let d := rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c rt 0
  have hb : false = true ↔ c.inputPos.val = 0 := by
    rw [(StepBlock.forwardLoopCfg_init_fields entry M x).2.1]
    decide
  have host := hH ℓ hz hℓ (pairEncode_drop α x) rt 0
    (by intro p _ _; rw [zero_add]) c false hb
  have uRun := startupLoopTM_runFrom (k := k + 1) A finish H (inj entry false) d
    (suffixRulerCfg (K := K) finish M z ℓ hlen) T_A aRun (suffixRulerCfg_state _ _ _ _ _) aCut
    (suffixRulerCfg_embed finish entry inj M ℓ hz hlen).symm
  obtain ⟨cost, hlock, hcost, _⟩ := hL (x := x) M
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) x output t).mp hcomp
    obtain ⟨t₀, _, _, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun e he => (hcost e he).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)
    obtain ⟨w, _, hw, ⟨b, _, hhost⟩, _, _, _, _⟩ := host v
    have uHalt : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).state = none := by
      rw [uRun w, Cfg.mapState_state, embedEmitCfg_state, hhost, rulerHostCfg_state,
        hr, StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none,
        Option.map_none]
    have uOut : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).output = output := by
      rw [uRun w, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hhost,
        rulerHostCfg_output, hr, StepBlock.forwardLoopCfg_output]
      exact hout
    have bound : T_A + 1 + w ≤ C * (t + 1) := by
      calc
        _ ≤ C + F * v := Nat.add_le_add hAC hw
        _ ≤ C + F * (D * t) := Nat.add_le_add_left (Nat.mul_le_mul_left F hvbound) C
        _ = C + (F * D) * t := by ring
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    exact ((FinTM.computesInTime_iff U z output (T_A + 1 + w)).mpr ⟨uHalt, uOut⟩).mono bound
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨uhalt, uout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le (k := k + 1) A finish H (inj entry false) T_A
      (by rw [aRun, suffixRulerCfg_state]; exact Option.some_ne_none finish) aCut
    have after : T_A + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) uhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [uRun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at uhalt
    rw [uRun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at uout
    have loopHalts : ∃ r, (L.runFrom c r).state = none := by
      by_contra hn
      have forever : ∀ r, (L.runFrom c r).state ≠ none := by
        intro r hr
        exact hn ⟨r, hr⟩
      obtain ⟨w, hw, _, _, cut, _, _, _⟩ := host (v + 1)
      exact cut (fun r _ => forever r) v (by omega) uhalt
    obtain ⟨r, rHalt⟩ := loopHalts
    obtain ⟨w, _, _, ⟨b, _, endpoint⟩, _, _, _, _⟩ := host r
    have wHalt : (H.runFrom d w).state = none := by
      rw [endpoint, rulerHostCfg_state, rHalt, Option.map_none]
    have loopOutput : (L.runFrom c r).output = output := by
      calc
        _ = (H.runFrom d w).output := by rw [endpoint, rulerHostCfg_output]
        _ = (H.runFrom d (max v w)).output :=
          (MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_right v w) wHalt).symm
        _ = (H.runFrom d v).output :=
          MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_left v w) uhalt
        _ = _ := uout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost r rHalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) x output t).mpr
      ⟨ht, ho.trans loopOutput⟩⟩


/-! ## Seal controls (each closes unsealed and fails sealed) -/
example {k K : ℕ} {P Q : Type} [DecidableEq P] (R : MultiTapeTM (K + (k + 2)) Bool P) (e : P)
    (L : MultiTapeTM (k + 2) Bool Q) (en : Q) : (startupLoopTM R e L en).q₀ = Sum.inl R.q₀ := rfl
example {k : ℕ} (i : Fin k) : (headerScanTM i).q₀ = 0 := rfl
example {k : ℕ} {z : List Bool} (i : Fin k) (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : (headerScanCfg i d q t ht).state = some q := rfl
example {k : ℕ} (i : Fin k) : (headerRulerTM i).q₀ = Sum.inl 0 := rfl
example {k K n : ℕ} {P : Type} (q : P) (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool)
    (ℓ : ℕ) (h : ℓ + 1 < z.length + 2) : (suffixRulerCfg (K := K) q M z ℓ h).state = some q := rfl

end Turing

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealUK.out =====

Scratch/SealUK.lean:2132:94: error: Type mismatch
  rfl
has type
  ?m.32 = ?m.32
but is expected to have type
  (startupLoopTM R e L en).q₀ = Sum.inl R.q₀
Scratch/SealUK.lean:2133:57: error: Type mismatch
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  (headerScanTM i).q₀ = 0
Scratch/SealUK.lean:2135:92: error: Type mismatch
  rfl
has type
  ?m.32 = ?m.32
but is expected to have type
  (headerScanCfg i d q t ht).state = some q
Scratch/SealUK.lean:2136:66: error: Type mismatch
  rfl
has type
  ?m.11 = ?m.11
but is expected to have type
  (headerRulerTM i).q₀ = Sum.inl 0
Scratch/SealUK.lean:2138:95: error: Type mismatch
  rfl
has type
  ?m.32 = ?m.32
but is expected to have type
  (suffixRulerCfg q M z ℓ h).state = some q
exit=1 6s

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealUK0.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.UniversalParts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `k`-generic universal machine (U2)

[AB09, §1.4.1 and Theorem 1.9]: one universal machine for codes of `k`-work-tape binary
machines, for every `k`, with an overhead linear in the simulated time and a constant depending
on the code only. At `k = 2` it is the two-tape universal machine of the time hierarchy at
`f log f` (plan §2.1; the Hennie–Stearns conversion of [AB09, §1.7] lands machines there); at
`k = 1` it is the self-application universal `U₀` of the space hierarchy
(`Turing.exists_selfUniversal`, its `k = 1` corollary) and the code-first evaluator of
`Turing.universal` (the U-1 re-derivation, deferred). Design: `audits/evidence/u2/U2-design.md`;
the user's decisions of 2026-10-14 (`backlog.md` RD-5).

**Status.** Proved: the scheme interface and its two instances, the startup
`Turing.exists_selfStartupTMK`, and both machine contracts. They are built on the step block's
forwarding round loop `Turing.StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward.lean`)
and, for the code-first evaluator, on the ruler host `Turing.exists_rulerHostTM`
(`Build/InputDevice.lean`). The parts both contracts are assembled from (the startup–loop seam
`Turing.startupLoopTM` and its ledgers, the forwarding loop's readings at an initial
configuration, the header ruler `Turing.headerRulerTM` and the suffix-ruler layout
`Turing.suffixRulerCfg`) are public in `Build/UniversalParts.lean`, harvested from this file's
privates for their second consumer (the U2 harvest, user ruling of 2026-11-06).

## Design

* **One construction, generic in `k`.** The step block `Turing.StepBlock.roundTM k` simulates one
  transition of any `k`-tape table held as data at a cost `≤ 50 · (|table| + 1)`, a constant for
  a fixed code; H2-F forwards the emissions. Nothing here is specific to one or two work tapes.
* **The scheme interface** `Turing.EffectiveCodeK k`: a total decoding into `k`-tape machines and
  a canonizer computing the fixed serialization `Turing.serializeK` in arbitrary time. The
  received one-tape scheme and the Z3 two-tape scheme are instances. No uniformity is assumed:
  per-code constants absorb the canonizer's time.
* **Two input layouts.** Self-application (`Turing.exists_selfUniversalK`): on `pairEncode α w`
  the coded machine runs on that same input, through the native device, with no copy and no
  position counter. Code first (`Turing.universalK`): on `pairEncode α x` it runs on `x`,
  through H5's bounded-prefix ruler device, at a constant cost per step for a fixed code.
* **Both directions** in both layouts: forward time (and, for self-application, space) ledgers,
  and the converse that every completed output of the universal machine is one of the coded
  machine's.

## Main definitions

* `Turing.EffectiveCodeK`, `Turing.EffectiveCodeK.toFinTM` — the `k`-tape scheme interface;
  `Turing.EffectiveCodeK.ofSerialize` — its constructor from a scheme with its own serialization.
* `Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK` — the received one- and
  two-tape schemes as `k`-tape schemes.

## Main results

* `Turing.EffectiveMachineCode.toK_toFinTM`, `Turing.EffectiveMachineCode2.toK_toFinTM`,
  `Turing.EffectiveMachineCode.toK_machine`, `Turing.EffectiveMachineCode2.toK_machine` — the
  decoded machines agree, by definition.
* `Turing.exists_selfStartupTMK` — the startup, ending at the step block's seam (proved).
* `Turing.exists_selfUniversalK` — the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (proved).
* `Turing.universalK` — the code-first evaluator with time `C · (t + 1)` and the converse
  (proved).

Their assembly cites `Build/UniversalParts.lean`: `Turing.startupLoopTM_runFrom`,
`_live_of_le` and `_spaceUsed_le`; `Turing.StepBlock.forwardLoop_forward` and `_converse`;
`Turing.embedEmitCfg_forwardLoop_init`; `Turing.headerRulerTM_run`; `Turing.suffixRulerCfg_embed`
and `Turing.MultiTapeTM.initCfg_eq_mapState`. The code-first evaluator's own startup composition
(the startup embedded with one more tape, then the header ruler) stays private here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, machine codes; §1.4.1, Theorem 1.9 and its proof:
  the universal machine simulates one step of `M` in a number of steps depending only on `M`'s
  table; §1.7, the two-tape simulation; Exercise 4.1, the space-bounded universal machine.)
-/

namespace Turing

/-! ## The `k`-tape scheme interface -/

/-- **An effective scheme for `k`-work-tape codes** [AB09, §1.4]: a total decoding of every
string `α` into a `k`-work-tape binary machine `machine α` with state space
`Fin (numStates α + 1)`, together with a machine of this development, the canonizer, that
computes from `α` the fixed `k`-record serialization `Turing.serializeK (machine α)` within an
arbitrary time bound `canonizerTime`. As for `Turing.EffectiveMachineCode` (Argument A), the
canonizer targets the fixed, scheme-independent serialization, and its time bound is arbitrary:
fixed-code consumers absorb it into their constants. The received schemes are instances
(`Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK`). -/
structure EffectiveCodeK (k : ℕ) where
  /-- one less than the number of states of the machine a string denotes -/
  numStates : List Bool → ℕ
  /-- the machine a string denotes -/
  machine : (α : List Bool) → MultiTapeTM k Bool (Fin (numStates α + 1))
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serializeK ∘ machine` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => serializeK (machine α)) canonizerTime

/-- The bundled machine a string denotes in a `k`-tape scheme: `k` work tapes, the states
`Fin (numStates α + 1)`, the decoded machine. -/
def EffectiveCodeK.toFinTM {k : ℕ} (E : EffectiveCodeK k) (α : List Bool) : FinTM Bool where
  k := k
  State := Fin (E.numStates α + 1)
  tm := E.machine α

/-- **A `k`-tape scheme from a scheme with its own serialization** (the common constructor of
the two instances below): given a type of coded machines with their state counts and their
`k`-tape machines, a serialization equal to `serializeK` of the machine, a decoding, and a
canonizer computing the serialization of the decoded machine, the `k`-tape scheme with the same
decoding and canonizer. -/
def EffectiveCodeK.ofSerialize {k : ℕ} {Code : Type} (numStates : Code → ℕ)
    (tm : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))) (serialize : Code → List Bool)
    (serialize_eq : ∀ M, serialize M = serializeK (tm M)) (decode : List Bool → Code)
    (canonizer : FinTM Bool) (canonizerTime : ℕ → ℕ)
    (h : canonizer.ComputesFunInTime (fun α => serialize (decode α)) canonizerTime) :
    EffectiveCodeK k where
  numStates α := numStates (decode α)
  machine α := tm (decode α)
  canonizer := canonizer
  canonizerTime := canonizerTime
  canonizer_computes := by
    have e : (fun α => serialize (decode α)) = fun α => serializeK (tm (decode α)) :=
      funext fun α => serialize_eq (decode α)
    exact e ▸ h

/-- **The received one-tape scheme as a `k`-tape scheme** (`k = 1`): the same decoding and the
same canonizer, whose target `CodeTM.serialize` is `serializeK` at one work tape
(`Turing.oneTapeMachineFormat.serialize_eq`). [AB09, §1.4] -/
def EffectiveMachineCode.toK (c : EffectiveMachineCode) : EffectiveCodeK 1 :=
  EffectiveCodeK.ofSerialize CodeTM.numStates CodeTM.tm CodeTM.serialize
    oneTapeMachineFormat.serialize_eq c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- **The Z3 two-tape scheme as a `k`-tape scheme** (`k = 2`): the same decoding and the same
canonizer, whose target `Code2TM.serialize` is `serializeK` at two work tapes
(`Turing.Code2TM.serialize_eq_serializeK`). [AB09, §1.4] -/
def EffectiveMachineCode2.toK (c : EffectiveMachineCode2) : EffectiveCodeK 2 :=
  EffectiveCodeK.ofSerialize Code2TM.numStates Code2TM.tm Code2TM.serialize
    Code2TM.serialize_eq_serializeK c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- The one-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode.toK_toFinTM (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The two-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode2.toK_toFinTM (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The one-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode.toK_machine (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-- The two-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode2.toK_machine (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-! ## U2-S: the startup -/

/-- The canonizer, with the public cleanup machine restarted in its cleaning state. -/
private def ss_cleanCanonizer (F : FinTM Bool) : FinTM Bool where
  k := F.k + F.k
  State := Complexity.LogProg.CleanSt F.State F.k
  tm := { Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ }

/-- The bundled cleanup run is the run from the public cleaning entry. -/
private theorem ss_cleanCanonizer_run (F : FinTM Bool) (α : List Bool) (t : ℕ) :
    (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t =
      (Complexity.LogProg.cleanTM F.tm F.tm.q₀).runFrom
        (Cfg.init (.init F.tm.q₀) α) t := by
  change ({ Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ } :
    MultiTapeTM (F.k + F.k) Bool (Complexity.LogProg.CleanSt F.State F.k)).runFrom _ _ = _
  rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]

/-- Cleanup preserves a completed computation and blanks every work tape.

**Proof sketch.** Bound the original run's visited set on each tape by their finite
maximum. Apply the public cleanup theorem, then use the restart equations. -/
private theorem ss_cleanCanonizer_halts (F : FinTM Bool) (α out : List Bool) (t : ℕ)
    (h : F.ComputesInTime α out t) :
    ∃ u, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).output =
        out ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapePos =
        (fun _ => 0) := by
  classical
  have hc := (FinTM.computesInTime_iff F α out t).mp h
  rw [MultiTapeTM.initCfg_eq] at hc
  let s := Finset.univ.sup fun i : Fin F.k =>
    (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t i).card
  obtain ⟨u, hu, hout, hblank, hpos, _⟩ :=
    Complexity.LogProg.cleanTM_run F.tm F.tm.q₀ F.tm.q₀ α t hc.1 s
      (fun i => Finset.le_sup
        (f := fun j : Fin F.k => (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t j).card)
        (Finset.mem_univ i))
  refine ⟨u, ?_⟩
  simpa only [ss_cleanCanonizer_run] using ⟨hu, hout.trans hc.2, hblank, hpos⟩

/-- A string-dependent time is bounded by a function of string length. -/
private theorem ss_lengthBound (time : List Bool → ℕ) :
    ∃ bound : ℕ → ℕ, ∀ α, time α ≤ bound α.length := by
  classical
  refine ⟨fun n => Finset.univ.sup (fun f : Fin n → Bool => time (List.ofFn f)), ?_⟩
  intro α
  simpa only [List.ofFn_get] using
    (Finset.le_sup (f := fun f : Fin α.length → Bool => time (List.ofFn f))
      (Finset.mem_univ α.get))

/-- A total canonizer remains total after cleanup, at a bound depending only on length;
the same bound leaves every work tape blank and every work head at zero.

**Proof sketch.** Choose each input's cleaned halting time and take a finite maximum
at each input length. Absorbing halting preserves the output and cleanup at the maximum. -/
private theorem ss_cleanCanonizer_computes (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) :
    ∃ bound, (ss_cleanCanonizer F).ComputesFunInTime f bound ∧ ∀ α,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapes = (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapePos = (fun _ => 0) := by
  classical
  have hex := fun α => ss_cleanCanonizer_halts F α (f α) (τ α.length)
    ((FinTM.computesFunInTime_iff F f τ).mp hF α)
  choose time htime using hex
  obtain ⟨bound, hbound⟩ := ss_lengthBound time
  have hfreeze (α : List Bool) :
      (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (bound α.length) =
        (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (time α) := by
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (hbound α)
    calc
      _ = (ss_cleanCanonizer F).tm.runFrom
          ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
            (time α)) extra := by rw [heq, MultiTapeTM.runFrom_add]
      _ = _ := MultiTapeTM.runFrom_of_halt _ (htime α).1
  refine ⟨bound, (FinTM.computesFunInTime_iff _ _ _).mpr ?_, ?_⟩
  · intro α
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hfreeze α]
    exact ⟨(htime α).1, (htime α).2.1⟩
  · intro α
    rw [hfreeze α]
    exact (htime α).2.2

/-- A buffered second-phase configuration halts exactly when its source does. -/
private theorem ss_bufferedHalt_iff (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    (FinTM.bufferedSecondCfg M₁ M₂ c b p tapes heads).state = none ↔ c.state = none := by
  rw [FinTM.bufferedSecondCfg_state]
  simp only [FinTM.bufferedCompTM_State, Option.map_eq_none_iff]

/-- A first halt of the virtual canonizer is a first halt of the prefix canonizer,
after the fixed prefix phase, uniformly over all suffixes.

**Proof sketch.** The exact prefix formula identifies the state after the prefix phase.
Before that phase ends, absorbing halting and its live final state exclude a halt. -/
private theorem ss_prefix_first_halt (F : FinTM Bool) (α : List Bool) (t : ℕ)
    (hhalt : (F.tm.runFrom (F.tm.initCfg α) t).state = none)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg α) u).state ≠ none) (w : List Bool) :
    ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w))
      (3 * α.length + 4 + t)).state = none ∧
    ∀ u < 3 * α.length + 4 + t,
      ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w)) u).state ≠
        none := by
  rw [prefixCanonTM_eq]
  constructor
  · obtain ⟨b, hb⟩ := prefixCanon_run F α w t
    simp only [prefixCanonTM_eq] at hb
    rw [hb, ss_bufferedHalt_iff]
    exact hhalt
  · intro u hu
    by_cases hpre : u < 3 * α.length + 4
    · have hs := prefixCanon_start F α w
      simp only [prefixCanonTM_eq] at hs
      have hstart :
          ((FinTM.bufferedCompTM universalPrefixTM F).tm.runFrom
            ((FinTM.bufferedCompTM universalPrefixTM F).tm.initCfg (pairEncode α w))
            (3 * α.length + 4)).state ≠ none := by
        intro h
        rw [hs, ss_bufferedHalt_iff, MultiTapeTM.initCfg_eq, Cfg.init_state] at h
        exact Option.some_ne_none F.tm.q₀ h
      exact MultiTapeTM.runFrom_state_ne_none_of_le _ _ _ hstart u (by omega)
    · obtain ⟨b, hb⟩ := prefixCanon_run F α w (u - (3 * α.length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * α.length + 4 ≤ u)] at hb
      intro h
      rw [hb, ss_bufferedHalt_iff] at h
      exact hlive (u - (3 * α.length + 4)) (by omega) h

/-- The cleaned canonizer's first halt has the completed output and clean scratch.

**Proof sketch.** The public first-halt theorem identifies its configuration with the
one at the cleaned length bound, including all fields of that configuration. -/
private theorem ss_cleanCanonizer_first_halt (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) (α : List Bool) :
    ∃ t, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧
      ∀ u < t, ((ss_cleanCanonizer F).tm.runFrom
        ((ss_cleanCanonizer F).tm.initCfg α) u).state ≠ none := by
  obtain ⟨bound, hfun, hclean⟩ := ss_cleanCanonizer_computes F f τ hF
  have hc := (FinTM.computesInTime_iff _ _ _ _).mp
    ((FinTM.computesFunInTime_iff _ _ _).mp hfun α)
  obtain ⟨t, _, hbefore, hsame⟩ := MultiTapeTM.exists_first_halt _ _ hc.1
  refine ⟨t, ?_, ?_, ?_, ?_, hbefore⟩
  · rw [hsame]
    exact hc.1
  · rw [hsame]
    exact hc.2
  · rw [hsame]
    exact (hclean α).1
  · rw [hsame]
    exact (hclean α).2

/-- Capturing a fresh run starts with blank host tapes and zero work heads.

**Proof sketch.** Partition host tapes into selected tapes, the capture tape, and the frame.
The selected tapes inherit the blank initial configuration; the empty captured output makes
its tape blank; the frame is blank by construction. Compare all configuration fields. -/
private theorem ss_captureInitial {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
    (ι : Fin m ↪ Fin n) (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) :
    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
      (M.initCfg x)).mapState Sum.inl =
      Cfg.init (Sum.inl M.q₀ : S ⊕ Unit) x := by
  classical
  have hfields (j : Fin n) :
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapes j = (fun _ => none) ∧
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapePos j = 0 := by
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_tape, embedSilentCfg_selected_pos,
        MultiTapeTM.initCfg_eq]
      exact ⟨funext fun z => Cfg.init_workTapes _ _ i z, Cfg.init_workTapePos _ _ i⟩
    · by_cases he : j = cap
      · subst j
        have hh := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x)
        simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
          FinTM.bufferTape_nil, List.length_nil, Nat.cast_zero] using hh
      · exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x) j hj he
  apply Cfg.ext
  · rw [Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq,
      Cfg.init_state, Option.map_some, Cfg.init_state]
  · rw [Cfg.mapState_inputPos, embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq,
      Cfg.init_inputPos, Cfg.init_inputPos]
  · funext j z
    rw [Cfg.mapState_workTapes, Cfg.init_workTapes, (hfields j).1]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, (hfields j).2]
  · rw [Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]

/-- The returning capture host, restarted in the source's initial state. -/
private def ss_captureTM (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n) (cap : Fin n) :
    MultiTapeTM n Bool (F.State ⊕ Unit) :=
  { embedSilentRetTM ι cap F.tm with q₀ := Sum.inl F.tm.q₀ }

/-- The returning capture reaches its anchor exactly at the source's first halt and
is silent throughout. Its final tapes are the public silent embedding's exact tapes.

**Proof sketch.** Identify the blank initial configuration, use the returning embedding's
through-halt contract, and project its output field before and at the return. -/
private theorem ss_capture_run (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) (t : ℕ)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg x) u).state ≠ none)
    (hhalt : (F.tm.runFrom (F.tm.initCfg x) t).state = none) :
    (ss_captureTM F ι cap).runFrom ((ss_captureTM F ι cap).initCfg x) t =
      { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (F.tm.runFrom (F.tm.initCfg x) t) with state := some (Sum.inr ()) } ∧
    (∀ u < t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).state ≠ some (Sum.inr ())) ∧
    (∀ u ≤ t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).output = []) := by
  have hinit : (F.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hr := embedSilentRetTM_run ι cap hcap F.tm (fun _ _ => none) (fun _ => 0)
    [] [] (F.tm.initCfg x) t hinit hlive hhalt
  simp only [MultiTapeTM.initCfg_eq] at hr
  simp only [ss_captureTM, MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀,
    ← ss_captureInitial F.tm ι cap hcap x]
  refine ⟨hr.2.1, hr.2.2, ?_⟩
  intro u hu
  rcases lt_or_eq_of_le hu with hlt | rfl
  · rw [hr.1 u hlt, Cfg.mapState_output, embedSilentCfg_output]
  · simp only [hr.2.1, embedSilentCfg_output]

/-- With the prefix parser's empty left block, index zero is the buffer and every other
index belongs to the constant right block.

**Proof sketch.** Cast the composite index to the public block partition. Its value is either
zero, the buffer index, or one plus an index of the right block; apply the corresponding
published projection equation. -/
private theorem ss_tapeBlocks_zeroLeft {A : Type} (F : FinTM Bool)
    (left : Fin universalPrefixTM.k → A) (buffer right : A)
    (i : Fin (FinTM.bufferedCompTM universalPrefixTM F).k) :
    FinTM.tapeBlocks left buffer (fun _ : Fin F.k => right)
        (Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i) =
      if i.val = 0 then buffer else right := by
  have hp := universalPrefixTM_k
  have hk := FinTM.bufferedCompTM_k universalPrefixTM F
  have hi := i.isLt
  by_cases hz : i.val = 0
  · have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k (0 : Fin 1)) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_zero]
      omega
    rw [he, FinTM.tapeBlocks_buffer, if_pos hz]
  · let j : Fin F.k := ⟨i.val - 1, by omega⟩
    have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd]
      dsimp only [j]
      omega
    rw [he, FinTM.tapeBlocks_right, if_neg hz]

/-- After the canonizer's work tapes have been cleared, the prefix composite keeps only
the original code buffer, whose head is the virtual input position minus one.

**Proof sketch.** Read the exact prefix run through the published composite fields at its own
index type. The empty parser block leaves index zero for the code buffer; the cleaned right
block contributes blank tapes and zero heads. -/
private theorem ss_prefix_return_fields (F : FinTM Bool) (α w : List Bool) (t : ℕ)
    (hblank : (F.tm.runFrom (F.tm.initCfg α) t).workTapes = (fun _ _ => none))
    (hheads : (F.tm.runFrom (F.tm.initCfg α) t).workTapePos = (fun _ => 0)) :
    let c := F.tm.runFrom (F.tm.initCfg α) t
    let G := FinTM.bufferedCompTM universalPrefixTM F
    let d := G.tm.runFrom (G.tm.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
    d.inputPos.val = 2 * α.length + 3 ∧ d.output = c.output ∧
      (∀ i, d.workTapes i = if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      ∀ i, d.workTapePos i = if i.val = 0 then (c.inputPos.val : ℤ) - 1 else 0 := by
  dsimp only
  obtain ⟨b, hb⟩ := prefixCanon_run F α w t
  simp only [prefixCanonTM_eq] at hb
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FinTM.bufferedSecondCfg_inputPos]
  · rw [FinTM.bufferedSecondCfg_output]
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapes_cast, hblank]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapePos_cast, hheads]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i

/-- Capturing the cleaned prefix has a code-dependent first return, silence, and a
uniform space bound. The final configuration is expressed through the prefix run;
its cleaned source data are retained for the layout normalization below.

**Proof sketch.** Select the cleaned canonizer's first halt before quantifying the suffix.
The prefix first-halt lemma and the returning capture contract give the claimed run. -/
private theorem ss_capturedPrefix_run (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t : ℕ,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧ ∀ w : List Bool,
      R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) =
        { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
            (G.tm.runFrom (G.tm.initCfg (pairEncode α w))
              (3 * α.length + 4 + t)) with state := some (Sum.inr ()) } ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, ht, hout, hblank, hheads, hlive⟩ := ss_cleanCanonizer_first_halt F f τ hF α
  refine ⟨t, hout, hblank, hheads, fun w => ?_⟩
  have hp := ss_prefix_first_halt (ss_cleanCanonizer F) α t ht hlive w
  simp only [prefixCanonTM_eq] at hp
  have hr := ss_capture_run
    (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)) ι cap hcap
    (pairEncode α w) (3 * α.length + 4 + t) hp.2 hp.1
  exact ⟨hr.1, hr.2.1, hr.2.2, MultiTapeTM.spaceUsed_le_mul_succ _ _ _⟩

/-- The returned capture has exactly the code buffer, the captured result, and blank scratch.
Its code-buffer head is a code-dependent position between minus one and the code length.

**Proof sketch.** Retain the cleaned source's output and blankness at the first halt chosen
before the suffix. Project the exact captured return through the selected, capture, and frame
equations, and normalize the source fields with the cast-indexed composite equations. The
source input position determines the buffer head independently of the suffix. -/
private theorem ss_capturedPrefix_fields (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t p : ℕ, p ≤ α.length + 1 ∧ ∀ w : List Bool,
      let d := R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
      d.state = some (Sum.inr ()) ∧ d.inputPos.val = 2 * α.length + 3 ∧
      (∀ i, d.workTapes (ι i) =
        if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      (∀ i, d.workTapePos (ι i) = if i.val = 0 then (p : ℤ) - 1 else 0) ∧
      (d.workTapes cap = FinTM.bufferTape (f α) ∧ d.workTapePos cap = (f α).length) ∧
      (∀ j, j ∉ Set.range ι → j ≠ cap →
        d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0) ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, hout, hblank, hheads, hret⟩ := ss_capturedPrefix_run F f τ hF ι cap hcap α
  refine ⟨t, ((ss_cleanCanonizer F).tm.runFrom
    ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.val, ?_, fun w => ?_⟩
  · have h := ((ss_cleanCanonizer F).tm.runFrom
      ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.isLt
    omega
  · obtain ⟨hr, hcut, hsilent, hspace⟩ := hret w
    have hf := ss_prefix_return_fields (ss_cleanCanonizer F) α w t hblank hheads
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcut, hsilent, hspace⟩
    · rw [hr]
    · rw [hr]
      rw [embedSilentCfg_inputPos]
      exact hf.1
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_tape]
      exact hf.2.2.1 i
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_pos]
      exact hf.2.2.2 i
    · rw [hr]
      have hc := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
        [] [] ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.initCfg
            (pairEncode α w)) (3 * α.length + 4 + t))
      simpa only [List.nil_append, hf.2.1, hout] using hc
    · intro j hj hjc
      rw [hr]
      exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0) [] [] _ j hj hjc

/-- The public seam-layout machine redistributes a canonical serialization from its right
blank, at one time chosen before the input and the ambient configuration.

**Proof sketch.** Instantiate the layout contract with the state-count bits, unary initial
state, and transition table. The published serialization and unary-word equations identify
its source word and its two output words. -/
private theorem ss_serialized_layout (n : ℕ) (src tbl sm : Fin n)
    (hst : src ≠ tbl) (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM n Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k m : ℕ} (M : MultiTapeTM k Bool (Fin (m + 1))),
        ∃ T ≤ C * ((serializeK M).length + 1),
          ∀ {z : List Bool} (d : Cfg n Bool Q z),
            d.state = some entry →
            d.workTapes src = FinTM.bufferTape (serializeK M) →
            d.workTapePos src = (serializeK M).length →
            d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
            d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
            (L.runFrom d T).state = some done ∧
            (L.runFrom d T).inputPos = d.inputPos ∧
            (L.runFrom d T).workTapes =
              Function.update (Function.update (Function.update d.workTapes src
                (fun _ => none)) tbl (FinTM.bufferTape (tableBitsK M.tr)))
                sm (fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)) ∧
            (L.runFrom d T).workTapePos =
              Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0)
                sm 0 ∧
            (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
            ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ := exists_seamLayoutTM n src tbl sm hst hss hts
  refine ⟨Q, hQ, hD, L, entry, done, C, ?_⟩
  intro k m M
  have hw := serializeK_eq M
  rw [unaryFin_eq] at hw
  have h := hL m.bits (tableBitsK M.tr) M.q₀.val (serializeK M).length (by rw [← hw])
  rw [← hw] at h
  simpa only [← unaryFin_eq M.q₀] using h

/-- A one-step move of the tested head when its cell is blank. The catalog rows do not
supply this conditional single step; it joins two skips and restores an empty buffer's head.
The action itself is the public one-tape action. -/
private def ss_bufferLeaf (n : ℕ) (i : Fin n) (emptyMove : SignType) :
    MultiTapeTM n Bool Bool where
  q₀ := false
  tr := fun _ _ work =>
    tapeAction i 0 none (if work i = none then emptyMove else 0)
      true

/-- The buffer leaf performs its conditional move in one silent step, with every other
tape and head fixed; its exit is absent before that step.

**Proof sketch.** Apply the public one-step tape-action equation. Before time one there is
only the entry configuration, whose false state is distinct from the true exit. -/
private theorem ss_bufferLeaf_run {n : ℕ} (i : Fin n) (emptyMove : SignType)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false) :
    (ss_bufferLeaf n i emptyMove).runFrom d 1 =
      { d with
        state := some true
        workTapePos := Function.update d.workTapePos i
          (d.workTapePos i + if d.workTapeSymbols i = none then (emptyMove : ℤ) else 0) } ∧
      ∀ u < 1, ((ss_bufferLeaf n i emptyMove).runFrom d u).state ≠ some true := by
  constructor
  · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have h := step_of_tapeAction_move (ss_bufferLeaf n i emptyMove) d i 0
      (if d.workTapeSymbols i = none then emptyMove else 0) hstate rfl
    simpa only [moveInputPos_zero, apply_ite, SignType.coe_zero] using h
  · intro u hu
    have hu0 : u = 0 := by omega
    rw [hu0, MultiTapeTM.runFrom_zero, hstate]
    simp only [ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- The first rightward skip starts at the source's virtual input position minus one.
At the left blank it moves to zero; at a nonnegative position it skips the remaining suffix.

**Proof sketch.** For virtual position zero, use the empty-word instance of the catalog
skip at the left blank. Otherwise, use the dropped suffix and the public buffer equation.
The catalog supplies both the framed endpoint and the first-return cut. -/
private theorem ss_bufferSkip_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    (skipTM n i).runFrom d (v.length + 1) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if p = 0 then 0 else (α.length : ℤ) + 1) } ∧
      ∀ u < v.length + 1, ((skipTM n i).runFrom d u).state ≠ some .done := by
  dsimp only
  have hw : ∀ q : ℤ, 0 ≤ q → q ≤
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) →
      d.workTapes i (d.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then [] else α.drop (p - 1)) q := by
    intro q hq hqv
    rw [hbuf, hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0]
      simp only [Int.zero_sub, add_zero, FinTM.bufferTape_left, FinTM.bufferTape_nil]
    · simp only [if_neg h] at hqv ⊢
      rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos hq,
        if_pos (by omega), List.getElem?_drop]
      congr 1
      omega
  obtain ⟨hr, hc, _⟩ := skipTM_run_ofCfg i _ d hstate hw
  have he : d.workTapePos i +
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) + 1 =
      if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero]
      omega
    · simp only [if_neg h, List.length_drop]
      omega
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- The second part of the rightward positioning pass: step left at a blank, then skip.
It is the existing seam constructor applied to the one-step leaf and the catalog skip. -/
private def ss_bufferAdvance (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (Bool ⊕ SeekPhase) :=
  seamCompTM (ss_bufferLeaf n i .neg) true (skipTM n i) .run

/-- After the first skip, the conditional left step and second skip reach one beyond the
right delimiter of a nonempty word. For the empty word they preserve the virtual position.

**Proof sketch.** Read blankness through the configuration and buffer equations. At position
zero of a nonempty word the leaf stays put and the skip crosses the word; otherwise the leaf
steps left and the empty-word skip steps right again. The public seam theorem supplies the
joined run and its first-return cut, preserving every ambient field. -/
private theorem ss_bufferAdvance_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool Bool z)
    (hstate : d.state = some false) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1) :
    let v := if p = 0 then α else []
    (ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) (v.length + 3) =
      ⟨some (Sum.inr .done), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + 3,
        ((ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  dsimp only
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (-1 : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i .neg d hstate
  change (ss_bufferLeaf n i .neg).runFrom d 1 = a at hr
  let b := a.mapState (fun _ => SeekPhase.run)
  have hba : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  have hbp : b.workTapePos i =
      if p = 0 then (if α = [] then -1 else 0) else (α.length : ℤ) := by
    rw [Cfg.mapState_workTapePos]
    dsimp only [a]
    rw [Function.update_self, Cfg.workTapeSymbols_eq, hbuf, hpos]
    by_cases h : p = 0
    · simp only [if_pos h]
      cases α with
      | nil => simp only [FinTM.bufferTape_nil, ite_true]; omega
      | cons x xs =>
        rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
        simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, List.cons_ne_nil,
          Nat.cast_zero, add_zero]
    · rw [if_neg h]
      have hn : FinTM.bufferTape α ((α.length : ℤ) + 1) = none := by
        rw [show (α.length : ℤ) + 1 = ((α.length + 1 : ℕ) : ℤ) by omega,
          FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
        omega
      rw [hn, if_pos rfl]
      omega
  have hw : ∀ q : ℤ, 0 ≤ q →
      q ≤ ((if p = 0 then α else []).length : ℤ) →
      b.workTapes i (b.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then α else []) q := by
    intro q hq hqv
    rw [hba, hbp]
    by_cases h : p = 0
    · simp only [if_pos h] at hqv ⊢
      by_cases ha : α = []
      · subst α
        simp only [FinTM.bufferTape_nil]
      · rw [if_neg ha, zero_add]
    · simp only [if_neg h, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0, add_zero, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega),
        FinTM.bufferTape_nil]
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  obtain ⟨hs, hscut, _⟩ := skipTM_run_ofCfg i _ b hbstate hw
  have he : b.workTapePos i + ((if p = 0 then α else []).length : ℤ) + 1 =
      if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [hbp]
    by_cases h : p = 0
    · simp only [if_pos h]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero]
        omega
      · simp only [if_neg ha]
        omega
    · simp only [if_neg h, List.length_nil, Nat.cast_zero]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero] at hp ⊢
        omega
      · simp only [if_neg ha, add_zero]
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + ((if p = 0 then α else []).length + 1) =
      (if p = 0 then α else []).length + 3 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, he]
    change Function.update b.workTapePos i _ j = _
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Position the code buffer for the backward catalog row, using three existing phases. -/
private def ss_bufferSeek (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) :=
  seamCompTM (skipTM n i) .done (ss_bufferAdvance n i) (Sum.inl false)

/-- The two skips and their intervening conditional step find the right edge, with a time
that depends only on the code and its chosen virtual position.

**Proof sketch.** The first catalog skip has the dropped-suffix time. The proved advance
then has the whole-word or empty-word time. Compose their framed contracts by the general
seam equations and read the final head update through the state-map field equations. -/
private theorem ss_bufferSeek_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    (ss_bufferSeek n i).runFrom (d.mapState Sum.inl) (v.length + w.length + 5) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + w.length + 5,
        ((ss_bufferSeek n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSkip_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if p = 0 then 0 else (α.length : ℤ) + 1) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferAdvance_run i α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SeekPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length + 1 + 1 +
      ((if p = 0 then α else []).length + 3) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 5 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The backward catalog row restores the first cell of a nonempty buffer and the
original position of an empty buffer, preserving the full surrounding configuration.

**Proof sketch.** For a nonempty word the forward endpoint is one beyond its right blank,
so the catalog precondition is the buffer itself. For an empty word all cells are blank.
The resulting head formula is the catalog's subtraction of the word length and one. -/
private theorem ss_bufferBack_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (skipBackTM n i).runFrom d (α.length + 3) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if α = [] then (p : ℤ) - 1 else 0) } ∧
      ∀ u < α.length + 3, ((skipBackTM n i).runFrom d u).state ≠ some .done := by
  have he : d.workTapePos i - (α.length : ℤ) - 1 =
      if α = [] then (p : ℤ) - 1 else 0 := by
    rw [hpos]
    by_cases ha : α = []
    · subst α
      simp only [ite_true, List.length_nil, Nat.cast_zero, sub_zero]
    · simp only [if_neg ha]
      omega
  obtain ⟨hr, hc, _⟩ := skipBackTM_run_ofCfg i α d hstate (by
    intro q _ _
    rw [hbuf, he]
    by_cases ha : α = []
    · subst α
      simp only [FinTM.bufferTape_nil]
    · rw [if_neg ha, zero_add])
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- Restore the empty word's origin if necessary, then clear through the catalog row.
The parameter is the virtual position chosen for the empty code, fixed for the machine. -/
private def ss_bufferClear (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (Bool ⊕ SweepPhase) :=
  seamCompTM (ss_bufferLeaf n i (if emptyPos = 0 then .pos else 0)) true
    (clearTM n i) .sweep

/-- The final buffer phases erase the code and put its head at zero. The empty code uses
its one fixed virtual position, so the machine does not depend on the input suffix.

**Proof sketch.** A nonempty buffer has a symbol at zero, so the leaf does not move. On an
empty buffer, the fixed position is zero or one and the conditional step restores zero.
The catalog clear then erases the word interval; outside that interval the public buffer
formula is already blank. Compose by the framed seam and its first-return theorem. -/
private theorem ss_bufferClear_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) - 1 else 0) :
    (ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) (2 * α.length + 4) =
      ⟨some (Sum.inr .done), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 2 * α.length + 4,
        ((ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  let mv : SignType := if emptyPos = 0 then .pos else 0
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (mv : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i mv d hstate
  change (ss_bufferLeaf n i mv).runFrom d 1 = a at hr
  have haheads : a.workTapePos = Function.update d.workTapePos i 0 := by
    have hm : d.workTapePos i +
        (if d.workTapeSymbols i = none then (mv : ℤ) else 0) = 0 := by
      rw [Cfg.workTapeSymbols_eq, hbuf, hpos]
      by_cases ha : α = []
      · rw [if_pos ha, hp ha]
        subst α
        simp only [FinTM.bufferTape_nil, ite_true]
        by_cases h : emptyPos = 0
        · simp only [mv, if_pos h, SignType.pos_eq_one, SignType.coe_one, h, Nat.cast_zero]
          omega
        · have h1 : emptyPos = 1 := by omega
          simp only [mv, if_neg h, SignType.coe_zero, h1, Nat.cast_one]
          omega
      · rw [if_neg ha]
        cases α with
        | nil => exact False.elim (ha rfl)
        | cons x xs =>
          rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
          simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, Nat.cast_zero,
            add_zero]
    dsimp only [a]
    rw [hm]
  let b := a.mapState (fun _ => SweepPhase.sweep)
  have hbstate : b.state = some .sweep := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = 0 := by
    rw [Cfg.mapState_workTapePos, haheads, Function.update_self]
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨hs, hscut, _⟩ := clearTM_run_ofCfg i α b hbstate (by
    intro q _ _
    rw [hbbuf, hbpos, zero_add])
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + (2 * α.length + 2) = 2 * α.length + 4 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    by_cases hj : j = i
    · subst j
      simp only [hbpos, zero_add, Function.update_self, true_and]
      by_cases hq : 0 ≤ q ∧ q < (α.length : ℤ)
      · rw [if_pos hq]
      · rw [if_neg hq, hbbuf, FinTM.bufferTape_eq]
        by_cases hq0 : 0 ≤ q
        · rw [if_pos hq0, List.getElem?_eq_none (by omega)]
        · rw [if_neg hq0]
    · simp only [hj, false_and, if_false, Function.update_of_ne hj]
      rw [Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, haheads]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Backward positioning followed by the fixed-origin clear, joined by the public seam. -/
private def ss_bufferFinish (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
  seamCompTM (skipBackTM n i) .done (ss_bufferClear n i emptyPos) (Sum.inl false)

/-- The backward pass and clear erase a buffer from the forward pass's endpoint.

**Proof sketch.** Apply the backward catalog specialization, then the proved fixed-origin
clear. The public seam transports their first-return cuts. Its state-map equations and
idempotence of a head update identify the framed endpoint. -/
private theorem ss_bufferFinish_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) (3 * α.length + 8) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 3 * α.length + 8,
        ((ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  obtain ⟨hr, hc⟩ := ss_bufferBack_run i α p d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if α = [] then (p : ℤ) - 1 else 0) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) - 1 else 0 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferClear_run i emptyPos he α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SweepPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipBackTM n i) .done (ss_bufferClear n i emptyPos)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipBackTM n i) .done
    (ss_bufferClear n i emptyPos) (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : α.length + 3 + 1 + (2 * α.length + 4) = 3 * α.length + 8 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Clear the captured code buffer from any of its possible virtual input positions.
All positioning and erasure phases are joined by existing seam constructors. -/
private def ss_bufferCleanup (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) :=
  seamCompTM (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run)

/-- The complete code-buffer cleanup is uniform in the suffix and ambient configuration.
Its only fixed parameter is the virtual position assigned to the empty code.

**Proof sketch.** The forward sequence positions the head for the backward pass. The
backward and clear sequence restores zero and erases the buffer. Join the two proved
contracts with the general seam theorem; sum their code-dependent times. The inherited
first-return theorem makes the final right-tagged exit fresh until that time. -/
private theorem ss_bufferCleanup_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : p ≤ α.length + 1)
    (hpe : α = [] → p = emptyPos) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    let T := v.length + w.length + 3 * α.length + 14
    (ss_bufferCleanup n i emptyPos).runFrom
      ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) T =
      ⟨some (Sum.inr (Sum.inr (Sum.inr .done))), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < T, ((ss_bufferCleanup n i emptyPos).runFrom
        ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
          Sum.inl) u).state ≠ some (Sum.inr (Sum.inr (Sum.inr .done))) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSeek_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) z :=
    ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
      Function.update d.workTapePos i
        (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩
  let b := a.mapState (fun _ => SeekPhase.run)
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferFinish_run i emptyPos he α p hpe b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SweepPhase)) =
      a.mapState (fun _ => Sum.inl .run) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) (Sum.inr (Sum.inr .done))
    hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length +
      (if p = 0 then α else []).length + 5 + 1 + (3 * α.length + 8) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 3 * α.length + 14 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The native rewind has a separate pre-exit anchor so that the final exit is fresh. -/
private inductive ss_RewindState where
  | enter | scan | stop | done
  deriving DecidableEq, Fintype

/-- A native input-only leaf; its scan is handled by the published rewind contracts. -/
private def ss_inputRewind (n : ℕ) : MultiTapeTM n Bool ss_RewindState where
  q₀ := .enter
  tr := fun q inp _ => match q with
    | .enter => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .stop)
    | .stop => FinTM.controlAction 0 (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- The final rewind anchor is stationary for every further time.

**Proof sketch.** Its own transition is a zero control action. Induction through the public
successor equation preserves the configuration; the control-action equation fixes its fields. -/
private theorem ss_inputRewind_done {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .done) (t : ℕ) :
    (ss_inputRewind n).runFrom d t = d := by
  have hs : (ss_inputRewind n).step d = d := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply d = d
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · rfl
    · rfl
  induction t with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hs]

/-- The native input rewind returns at an exact position-dependent time, with a first exit
and fixed work heads throughout. Its time is independent of the input's suffix.

**Proof sketch.** One left step puts the input head within the word. The public scan equation
then reaches the pre-exit anchor after exactly the old position plus one steps. An earlier
final exit would be stationary and contradict that anchor. The public rewind-head theorem
has the same pre-exit time, since leaving that anchor enters the stationary final exit.
One final stationary step completes the run. -/
private theorem ss_inputRewind_run {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .enter)
    (hp : 0 < d.inputPos.val) :
    (ss_inputRewind n).runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } ∧
      (∀ u < d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).workTapePos = d.workTapePos := by
  let M := ss_inputRewind n
  let c : Cfg n Bool ss_RewindState z :=
    { d with state := some .scan, inputPos := moveInputPos d.inputPos .neg }
  have hstep : M.step d = c := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction .neg (some ss_RewindState.scan)).apply d = c
    rw [FinTM.controlAction_apply]
  have hcp : c.inputPos.val ≤ z.length := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    have := d.inputPos.isLt
    omega
  have hscan := FinTM.rewind_scan M .scan (some .stop)
    (fun inp _ => by cases inp <;> rfl) c rfl hcp
  have ht : 1 + (c.inputPos.val + 1) = d.inputPos.val + 1 := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    omega
  have hstop : M.runFrom d (d.inputPos.val + 1) =
      { d with state := some .stop, inputPos := 1 } := by
    rw [← ht, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step' (cfg := d) (t := 0),
      MultiTapeTM.runFrom_zero, hstep, hscan]
  have hlast : ∀ (a : Cfg n Bool ss_RewindState z), a.state = some .stop →
      M.step a = { a with state := some .done } := by
    intro a ha
    rw [MultiTapeTM.step_of_some ha]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply a = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
  have hcut : ∀ u ≤ d.inputPos.val + 1, (M.runFrom d u).state ≠ some .done := by
    intro u hu hdone
    have hf := ss_inputRewind_done (M.runFrom d u) hdone (d.inputPos.val + 1 - u)
    have hsum : u + (d.inputPos.val + 1 - u) = d.inputPos.val + 1 := by omega
    rw [← MultiTapeTM.runFrom_add, hsum, hstop] at hf
    have heq := congrArg Cfg.state hf
    rw [hdone] at heq
    cases heq
  have hret : M.runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } := by
    rw [show d.inputPos.val + 2 = (d.inputPos.val + 1) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', hstop, hlast _ rfl]
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads M .enter .scan (some .stop)
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have htime : r = d.inputPos.val + 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx : (M.runFrom d (r + 1)).state = some .done := by
        rw [MultiTapeTM.runFrom_succ_eq_step', hrun, hlast _ rfl]
      exact hcut (r + 1) (by omega) hx
    · have hf := ss_inputRewind_done
        ({ d with state := some .done, inputPos := 1 } : Cfg n Bool ss_RewindState z)
        rfl (r - (d.inputPos.val + 2))
      have hsum : d.inputPos.val + 2 + (r - (d.inputPos.val + 2)) = r := by omega
      rw [← hret, ← MultiTapeTM.runFrom_add, hsum, hrun, hret] at hf
      have heq := congrArg Cfg.state hf
      cases heq
  refine ⟨hret, fun u hu => hcut u (by omega), ?_⟩
  intro u hu
  by_cases h : u ≤ d.inputPos.val + 1
  · exact hheads u (by omega)
  · have heq : u = d.inputPos.val + 2 := by omega
    rw [heq, hret]

/-- A live configuration's state map preserves its physical frame, read through the public
field equations rather than through the definition of state renaming.

**Proof sketch.** Configuration extensionality reduces to the five published field equations;
the live-state equation reduces the option map to one constructor. -/
private theorem ss_live_map {n : ℕ} {P Q : Type} {z : List Bool}
    (d : Cfg n Bool P z) (q : P) (hq : d.state = some q) (f : P → Q) :
    d.mapState f = ⟨some (f q), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, hq, Option.map_some]
  · exact Cfg.mapState_inputPos _ _
  · funext i p
    exact Cfg.mapState_workTapes _ _ _ _
  · funext i
    exact Cfg.mapState_workTapePos _ _ _
  · exact Cfg.mapState_output _ _

/-- Selected code and capture cells give a two-update normal form for any field.

**Proof sketch.** At the capture index use its equation. In the selected block, injectivity
identifies index zero; every other selected field has the background value. Outside both
blocks use the framing equation. This single argument applies to tapes and head positions. -/
private theorem ss_block_updates {A : Type} {m n : ℕ} (ι : Fin m ↪ Fin n)
    (cap : Fin n) (zero : Fin m) (hz : zero.val = 0)
    (f : Fin n → A) (base code captured : A)
    (hsel : ∀ j, f (ι j) = if j.val = 0 then code else base)
    (hc : f cap = captured)
    (ho : ∀ j, j ∉ Set.range ι → j ≠ cap → f j = base) :
    f = Function.update (Function.update (fun _ => base) (ι zero) code) cap captured := by
  funext j
  by_cases hj : j = cap
  · subst j
    rw [hc, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hs : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hs
      rw [hsel]
      by_cases hi : i = zero
      · subst i
        rw [hz, if_pos rfl, Function.update_self]
      · have hival : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext (h.trans hz.symm))
        have hislot : ι i ≠ ι zero := fun h => hi (ι.injective h)
        rw [if_neg hival, Function.update_of_ne hislot]
    · have hjz : j ≠ ι zero := by
        intro h
        exact hs ⟨zero, h.symm⟩
      rw [ho j hs hj, Function.update_of_ne hjz]

/-- The source block sits after the simulated tapes, table, and summary. -/
private def ss_sourceSlot (m k : ℕ) : Fin m ↪ Fin ((m + 1) + (k + 2)) where
  toFun i := ⟨k + 2 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change k + 2 + i.val = k + 2 + j.val at hv
    omega

/-- The capture tape is last, beyond the source block. -/
private def ss_captureTape (m k : ℕ) : Fin ((m + 1) + (k + 2)) :=
  ⟨k + 2 + m, by omega⟩

/-- The capture tape is separate, and all first `k + 2` tapes lie outside both blocks.

**Proof sketch.** Every selected index lies between `k + 2` and `k + 2 + m - 1`.
The capture index is `k + 2 + m`, and each reserved index is smaller than `k + 2`. -/
private theorem ss_capture_indices (m k : ℕ) :
    ss_captureTape m k ∉ Set.range (ss_sourceSlot m k) ∧
    ∀ j : Fin ((m + 1) + (k + 2)), j.val < k + 2 →
      j ∉ Set.range (ss_sourceSlot m k) ∧ j ≠ ss_captureTape m k := by
  have hs (i : Fin m) : k + 2 ≤ (ss_sourceSlot m k i).val ∧
      (ss_sourceSlot m k i).val < (ss_captureTape m k).val := by
    change k + 2 ≤ k + 2 + i.val ∧ k + 2 + i.val < k + 2 + m
    omega
  constructor
  · rintro ⟨i, hi⟩
    have := (hs i).2
    rw [hi] at this
    exact (lt_irrefl _ this)
  · intro j hj
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have := (hs i).1
      rw [hi] at this
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = k + 2 + m at hv
      omega

/-- **U2-S, the `k`-generic startup** (the startup of `Turing.exists_selfStartupTM`, generic in
the work-tape count). For a `k`-tape scheme `E` there is a binary machine with `K + (k + 2)` work
tapes and an exit state such that for every code `α` there are a time `T` and a space bound `B`,
**depending on `α` only**, with the following property on every input `pairEncode α w`. At time
`T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before;
* tapes `0, …, k - 1`, the simulated work tapes, blank, and tape `k` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `k + 1` holding the decoded machine's initial state in unary from cell `2` (cells `0`
  and `1` blank), the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam
(`Turing.StepBlock.Rep`) for the decoded machine's initial configuration on the same input, and
its restriction to the first `k + 2` tapes is H2-F's encoding `Turing.StepBlock.forwardLoopCfg` of
that configuration. [AB09, §1.4.1, Theorem 1.9]

**Proof sketch.** As `Turing.exists_selfStartupTM`'s, at `k` mirrored tapes. Extract and
canonize: the prefix parser composed with the scheme's canonizer by buffered composition, its
emissions captured on a scratch tape (the pattern of `Turing.universalCanonTM` and
`Turing.universalCaptureTM`, with `E.canonizer` in place of the one-tape scheme's); it ends after
`3|α| + 4 + E.canonizerTime |α|` steps with `serializeK (E.machine α)` captured and the input
head at `2|α| + 3`. Skip the doubled state count and the separator of
`serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`, copy the unary initial state to
tape `k + 1` at offset `2` and the table to tape `k`; clear the scratch and the buffer. Rewind the
input head to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends
on `α` only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's
halting time bounds its cells).

**Implementation.** The scheme's canonizer runs behind the public cleaner, which blanks its work
tapes and returns its heads, and the capture uses that machine's first halting time `t α`
(`Turing.MultiTapeTM.exists_first_halt`): the capture ends after `3|α| + 4 + t α` steps rather
than at the bound `E.canonizerTime |α|`. The code buffer is cleared by the catalog skip, skip back
and clear around a one-step move that acts only on a blank cell; on the empty code the buffer is
all blank, so the canonizer's final head position on the empty code is a fixed parameter of the
machine, chosen from `E`. The input head is rewound by `Turing.FinTM.rewind_scan` and
`Turing.FinTM.rewind_heads`, in `2|α| + 5` steps. -/
theorem exists_selfStartupTMK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
              else if j.val = k + 1 then
                fun p => FinTM.bufferTape (unaryFin (E.machine α).q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  classical
  let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer E.canonizer)
  let n := (G.k + 1) + (k + 2)
  let ι := ss_sourceSlot G.k k
  let cap := ss_captureTape G.k k
  have hcap : cap ∉ Set.range ι := (ss_capture_indices G.k k).1
  have hm : 0 < G.k := by
    dsimp only [G]
    rw [FinTM.bufferedCompTM_k, universalPrefixTM_k]
    omega
  let zero : Fin G.k := ⟨0, hm⟩
  let code := ι zero
  let tbl : Fin n := ⟨k, by dsimp only [n]; omega⟩
  let sm : Fin n := ⟨k + 1, by dsimp only [n]; omega⟩
  have htbl := (ss_capture_indices G.k k).2 tbl (by dsimp only [tbl]; omega)
  have hsm := (ss_capture_indices G.k k).2 sm (by dsimp only [sm]; omega)
  have hts : tbl ≠ sm := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [tbl, sm] at hv
    omega
  have hct : code ≠ tbl := fun h => htbl.1 ⟨zero, h⟩
  have hcs : code ≠ sm := fun h => hsm.1 ⟨zero, h⟩
  have hcc : code ≠ cap := fun h => hcap ⟨zero, h⟩
  let A := ss_captureTM G ι cap
  have hcapture := fun α => ss_capturedPrefix_fields E.canonizer
    (fun β => serializeK (E.machine β)) E.canonizerTime E.canonizer_computes ι cap hcap α
  dsimp only at hcapture
  choose t p hp hc using hcapture
  have hp0 : p [] ≤ 1 := by simpa only [List.length_nil, zero_add] using hp []
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ :=
    ss_serialized_layout n cap tbl sm htbl.2.symm hsm.2.symm hts
  letI := hQ
  letI := hD
  let J := ss_bufferCleanup n code (p [])
  let jentry : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inl (Sum.inl .run)
  let jexit : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inr (Sum.inr (Sum.inr .done))
  let B := seamCompTM J jexit (ss_inputRewind n) .enter
  let D := seamCompTM L done B (Sum.inl jentry)
  let W := seamCompTM A (Sum.inr ()) D (Sum.inl entry)
  let R := { W with q₀ := Sum.inl A.q₀ }
  let exit : (G.State ⊕ Unit) ⊕ Q ⊕
      (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
        ss_RewindState) := Sum.inr (Sum.inr (Sum.inr .done))
  refine ⟨G.k + 1, _, inferInstance, inferInstance, R, exit, ?_⟩
  intro α
  obtain ⟨l, hl, hlayout⟩ := hL (E.machine α)
  let a := 3 * α.length + 4 + t α
  let v := if p α = 0 then [] else α.drop (p α - 1)
  let w₀ := if p α = 0 then α else []
  let b := v.length + w₀.length + 3 * α.length + 14
  let r := 2 * α.length + 5
  let T := a + 1 + (l + 1 + (b + 1 + r))
  refine ⟨T, n * (T + 1), ?_⟩
  intro w
  let d₀ := A.initCfg (pairEncode α w)
  let d₁ := A.runFrom d₀ a
  obtain ⟨hstate, hip, hsel, hheads, hcapt, hother, hcut, hsil, _⟩ := hc α w
  have hs₁ : d₁.state = some (Sum.inr ()) := hstate
  have ht₁ : d₁.workTapes = Function.update
      (Function.update (fun _ => fun _ => none) code (FinTM.bufferTape α))
      cap (FinTM.bufferTape (serializeK (E.machine α))) :=
    ss_block_updates ι cap zero rfl _ _ _ _ hsel hcapt.1
      (fun j hj hjc => (hother j hj hjc).1)
  have hh₁ : d₁.workTapePos = Function.update
      (Function.update (fun _ => 0) code ((p α : ℤ) - 1))
      cap (serializeK (E.machine α)).length :=
    ss_block_updates ι cap zero rfl _ _ _ _ hheads hcapt.2
      (fun j hj hjc => (hother j hj hjc).2)
  have ho₁ : d₁.output = [] := hsil a le_rfl
  let d₂ := d₁.mapState (fun _ => entry)
  have hd₂ : d₂.state = some entry := by
    rw [Cfg.mapState_state, hs₁, Option.map_some]
  have ht₂ (j : Fin n) : d₂.workTapes j = d₁.workTapes j := by
    funext q
    exact Cfg.mapState_workTapes _ _ _ _
  have hh₂ (j : Fin n) : d₂.workTapePos j = d₁.workTapePos j :=
    Cfg.mapState_workTapePos _ _ _
  obtain ⟨hs₃, hi₃, ht₃, hh₃, ho₃, hcut₃⟩ := hlayout d₂ hd₂
    ((ht₂ cap).trans hcapt.1) ((hh₂ cap).trans hcapt.2)
    ((ht₂ tbl).trans (hother tbl htbl.1 htbl.2).1)
    ((hh₂ tbl).trans (hother tbl htbl.1 htbl.2).2)
    ((ht₂ sm).trans (hother sm hsm.1 hsm.2).1)
    ((hh₂ sm).trans (hother sm hsm.1 hsm.2).2)
  let d₃ := L.runFrom d₂ l
  let c : Cfg n Bool SeekPhase (pairEncode α w) :=
    ⟨some .run, d₃.inputPos, d₃.workTapes, d₃.workTapePos, d₃.output⟩
  have hbuf : c.workTapes code = FinTM.bufferTape α := by
    change d₃.workTapes code = _
    rw [ht₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, ht₂]
    exact (hsel zero).trans (if_pos rfl)
  have hpos : c.workTapePos code = (p α : ℤ) - 1 := by
    change d₃.workTapePos code = _
    rw [hh₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, hh₂]
    exact (hheads zero).trans (if_pos rfl)
  obtain ⟨hj, hjcut⟩ := ss_bufferCleanup_run code (p []) hp0 α (p α) (hp α)
    (fun h => congrArg p h) c rfl hbuf hpos
  have hjstart :
      ((c.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) = d₃.mapState (fun _ => jentry) := by
    rw [ss_live_map c .run rfl,
      ss_live_map _ (Sum.inl .run) rfl, ss_live_map d₃ done hs₃]
  rw [hjstart] at hj hjcut
  let d₄ : Cfg n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)))
      (pairEncode α w) :=
    ⟨some jexit, d₃.inputPos, Function.update d₃.workTapes code (fun _ => none),
      Function.update d₃.workTapePos code 0, d₃.output⟩
  change J.runFrom (d₃.mapState (fun _ => jentry)) b = d₄ at hj
  change ∀ u < b, (J.runFrom (d₃.mapState (fun _ => jentry)) u).state ≠ some jexit at hjcut
  let d₅ := d₄.mapState (fun _ => ss_RewindState.enter)
  have hd₅ : d₅.state = some .enter := by rw [Cfg.mapState_state]; rfl
  have hi₅ : d₅.inputPos.val = 2 * α.length + 3 := by
    rw [Cfg.mapState_inputPos]
    change d₃.inputPos.val = _
    rw [hi₃, Cfg.mapState_inputPos]
    exact hip
  obtain ⟨hrew, hrewcut, _⟩ := ss_inputRewind_run d₅ hd₅ (by omega)
  have htime : d₅.inputPos.val + 2 = r := by dsimp only [r]; omega
  rw [htime] at hrew hrewcut
  have hb := seamCompTM_run_ofCfg J jexit (ss_inputRewind n) .enter hj rfl hjcut hrew
  have hbcut := seamCompTM_firstReturn_ofCfg J jexit (ss_inputRewind n) .enter .done
    hj rfl hjcut hrew rfl hrewcut
  have hbstart : (d₃.mapState (fun _ => jentry)).mapState
      (Sum.inl : _ → _ ⊕ ss_RewindState) = d₃.mapState (fun _ => Sum.inl jentry) := by
    rw [ss_live_map d₃ done hs₃, ss_live_map _ jentry rfl, ss_live_map d₃ done hs₃]
  rw [hbstart] at hb hbcut
  have hd := seamCompTM_run_ofCfg L done B (Sum.inl jentry) rfl hs₃ hcut₃ hb
  have hdcut := seamCompTM_firstReturn_ofCfg L done B (Sum.inl jentry) (Sum.inr .done)
    rfl hs₃ hcut₃ hb (by rw [Cfg.mapState_state]; rfl) hbcut
  have hdstart : (d₁.mapState (fun _ => entry)).mapState
      (Sum.inl : Q → Q ⊕
        (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
          ss_RewindState)) = d₁.mapState (fun _ => Sum.inl entry) := by
    rw [ss_live_map d₁ (Sum.inr ()) hs₁, ss_live_map _ entry rfl,
      ss_live_map d₁ (Sum.inr ()) hs₁]
  rw [hdstart] at hd hdcut
  have hw := seamCompTM_run_ofCfg A (Sum.inr ()) D (Sum.inl entry) rfl hs₁ hcut hd
  have hwcut := seamCompTM_firstReturn_ofCfg A (Sum.inr ()) D (Sum.inl entry)
    (Sum.inr (Sum.inr .done)) rfl hs₁ hcut hd
    (by rw [Cfg.mapState_state, Cfg.mapState_state]; rfl) hdcut
  have hinit : R.initCfg (pairEncode α w) = d₀.mapState Sum.inl := by
    apply Cfg.ext
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_state, Cfg.mapState_state,
        d₀, Option.map_some]
      rfl
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos, Cfg.mapState_inputPos,
        d₀]
    · funext j q
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes, Cfg.mapState_workTapes,
        d₀]
    · funext j
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos,
        Cfg.mapState_workTapePos, d₀]
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, Cfg.mapState_output,
        d₀]
  have htfinal : Function.update d₃.workTapes code (fun _ => none) =
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
        else if j.val = k + 1 then
          fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
        else fun _ => none := by
    funext j q
    rw [ht₃]
    have hdtapes : d₂.workTapes = d₁.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hdtapes, ht₁]
    by_cases hjt : j = tbl
    · subst j
      simp only [tbl, Function.update_of_ne hct.symm, Function.update_of_ne hts,
        Function.update_self, ite_true]
    · have hjtv : j.val ≠ k := fun h => hjt (Fin.ext h)
      by_cases hjs : j = sm
      · subst j
        simp only [sm, Function.update_of_ne hcs.symm, Function.update_self,
          if_neg hjtv, ite_true]
      · have hjsv : j.val ≠ k + 1 := fun h => hjs (Fin.ext h)
        simp only [if_neg hjtv, if_neg hjsv]
        by_cases hjc : j = code
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjc, Function.update_of_ne hjs,
            Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hhfinal : Function.update d₃.workTapePos code 0 = fun _ => 0 := by
    funext j
    rw [hh₃]
    have hdheads : d₂.workTapePos = d₁.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hdheads, hh₁]
    by_cases hjc : j = code
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hjc]
      by_cases hjs : j = sm
      · subst j
        rw [Function.update_self]
      · rw [Function.update_of_ne hjs]
        by_cases hjt : j = tbl
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hofinal : d₃.output = [] := by
    rw [ho₃ l le_rfl, Cfg.mapState_output]
    exact ho₁
  have hfinal : R.runFrom (R.initCfg (pairEncode α w)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
          else if j.val = k + 1 then
            fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
          else fun _ => none,
        fun _ => 0, []⟩ := by
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    rw [hw]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes]
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun htfinal j) q
    · funext j
      simp only [Cfg.mapState_workTapePos]
      rw [Cfg.mapState_workTapePos]
      exact congrFun hhfinal j
    · simp only [Cfg.mapState_output]
      rw [Cfg.mapState_output]
      exact hofinal
  refine ⟨hfinal, ?_, ?_, MultiTapeTM.spaceUsed_le_mul_succ R _ T⟩
  · intro u hu
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    exact hwcut u hu
  · intro u hu
    have hpre := MultiTapeTM.output_prefix R (R.initCfg (pairEncode α w)) hu
    rw [hfinal] at hpre
    exact List.prefix_nil.mp hpre

/-! ## U2-U: the self-application universal machine -/

/-- **U2-U, the self-application universal machine, with time and space ledgers and the
converse** [AB09, Theorem 1.9 and Exercise 4.1, at self-application]. For a `k`-tape scheme `E`
there is a binary machine `U` such that for every code `α` there is a constant `C > 0`
(depending on `α` only) with, for every `w`:
* whenever the machine coded by `α` halts on `pairEncode α w` with `output` within `t` steps,
  `U` halts on the same input with the same `output` within `C · (t + 1)` steps, having visited
  by then at most `C · (s + 1)` cells, `s` the coded machine's cells by time `t`;
* every completed output of `U` on `pairEncode α w` is a completed output of the coded machine
  there (so divergence is preserved).

`C` depends on the code string, as in `Turing.universal` (Argument E): it absorbs the canonizer's
arbitrary time and the table's length. B6's `Turing.exists_selfUniversal` is the case `k = 1`
(forward clause, space only).

**Proof sketch.** Startup, then H2-F. (i) U2-S reaches, after `T_α` steps and within `B_α`
cells, H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg (pairEncode α w))` of
the coded machine `M := E.machine α`, on the block's tapes, the other tapes blank; seam it into
H2-F's machine `L` (R2, R1 on the first `k + 2` tapes). (ii) H2-F's lockstep
(`Turing.Lockstep.runFrom`) runs `M` from its initial configuration through its first halt
`t₀ ≤ t`: `L` is then at the encoding of the halted configuration, halted, with `M`'s output,
after `Σ_{u < t₀} cost ≤ (50 · (|tableBitsK| + 1) + C_L) · t` steps; with the seam's one step,
the time is at most `T_α + 1 + (50 · (|tableBitsK| + 1) + C_L) · t ≤ C · (t + 1)`. (iii) Space:
the mirrored heads visit only `M`'s cells, at most `s`; the auxiliary heads stay in an interval
of length `2 (50 · (|tableBitsK| + 1) + C_L) + 1`; the startup `B_α`; in all `≤ C · (s + 1)`,
and the halted configuration is frozen afterwards. (iv) Converse: by the lockstep's cut
(`Turing.Lockstep.cut`) `L` is live while `M` is, and an encoded live configuration is live, so
`U` halts only at the encoding of a halted configuration of `M`, whose output is `M`'s. -/
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  let U : FinTM Bool :=
    { k := K + (k + 2), State := P ⊕ Q, tm := startupLoopTM R exit L entry }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, B, hRα⟩ := hR α
  let M := E.machine α
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let N := K + (k + 2)
  let C := T + 1 + D + B + N * (2 * D + 1) + N
  have hTC : T + 1 ≤ C := by dsimp only [C]; omega
  have hDC : D ≤ C := by dsimp only [C]; omega
  have hNC : N ≤ C := by dsimp only [C]; omega
  have hBC : B + N * (2 * D + 1) ≤ C := by dsimp only [C]; omega
  refine ⟨C, by omega, ?_⟩
  intro w
  let z := pairEncode α w
  obtain ⟨hrun, hcut, _, hB⟩ := hRα w
  obtain ⟨cost, hlock, hcost, hledger⟩ := hL (x := z) M
  have hUrun := startupLoopTM_runFrom R exit L entry
    (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
    (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) z output t).mp hcomp
    obtain ⟨t₀, ht₀, hfirst, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg z) u)
    have hUhalt : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).state = none := by
      rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, hr,
        StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none]
    have hUout : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).output = output := by
      rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hr,
        StepBlock.forwardLoopCfg_output]
      exact hout
    have htime : T + 1 + v ≤ C * (t + 1) := by
      calc
        _ ≤ C + D * t := Nat.add_le_add hTC hvbound
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    have hUcomp : U.ComputesInTime z output (T + 1 + v) :=
      (FinTM.computesInTime_iff U z output (T + 1 + v)).mpr ⟨hUhalt, hUout⟩
    refine ⟨hUcomp.mono htime, ?_⟩
    let s := M.spaceUsed (M.initCfg z) t
    have hloop : ∀ i, L.spaceUsedByTape
        (StepBlock.forwardLoopCfg entry M (M.initCfg z)) v i ≤ s + (2 * D + 1) := by
      intro i
      by_cases hi : i.val < k
      · let j : Fin k := ⟨i.val, hi⟩
        have hij : Fin.castAdd 2 j = i := Fin.ext rfl
        rw [← hij, MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t₀ j).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).1 j)
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card :=
            Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (M.initCfg z) ht₀ j)
          _ = M.spaceUsedByTape (M.initCfg z) t j :=
            (MultiTapeTM.spaceUsedByTape_eq_card (tm := M) _ t j).symm
          _ ≤ s := MultiTapeTM.spaceUsedByTape_le_spaceUsed (tm := M) _ t j
          _ ≤ _ := by omega
      · rw [MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (Finset.Icc (-(D : ℤ)) (D : ℤ)).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).2 i (by omega))
          _ = 2 * D + 1 := by rw [Int.card_Icc]; omega
          _ ≤ _ := by omega
    have hspace := startupLoopTM_spaceUsed_le R exit L entry
      (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
      (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
      v B (s + (2 * D + 1)) hB (by omega) hloop
    calc
      _ ≤ B + N * (s + (2 * D + 1)) :=
        FinTM.ComputesInTime.spaceUsed_le_of_halt hUcomp hspace _
      _ = N * s + (B + N * (2 * D + 1)) := by ring
      _ ≤ C * s + C := Nat.add_le_add (Nat.mul_le_mul_right s hNC) hBC
      _ = _ := by dsimp only [s, M, EffectiveCodeK.toFinTM]; ring
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le R exit L entry T
      (by rw [hrun]; exact Option.some_ne_none exit) hcut
    have hafter : T + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) hhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hafter
    rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at hhalt
    rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at hout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost v hhalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) z output t).mpr
      ⟨ht, ho.trans hout⟩⟩

/-! ## U2-E: the code-first evaluator -/


/-- The startup embedded with one extra tape, followed by the header ruler preparation. -/
private noncomputable def uk_suffixStartupTM {k K : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P) :
    MultiTapeTM (K + (k + 3)) Bool (P ⊕ (Fin 4 ⊕ RewindPhase)) :=
  { seamCompTM
      ({ embedEmitTM (Fin.castLEEmb (by omega)) R with q₀ := R.q₀ }) exit
      (headerRulerTM ⟨k + 2, by omega⟩) (Sum.inl 0) with q₀ := Sum.inl R.q₀ }

/-- The original startup followed by the header scan and rewind reaches the suffix seam.

**Proof sketch.** Embed the startup in one more tape and reconstruct its initial
and final configurations with the public embedding theorem. At the endpoint,
the tape immediately after the simulation bank is blank. The framed header
contract prepares it, and the public seam composes the two runs and their cuts. -/
private theorem uk_suffixStartup_run {k K n : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (α x : List Bool) (T : ℕ)
    (hrun : R.runFrom (R.initCfg (pairEncode α x)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
          else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
          else fun _ => none,
        fun _ => 0, []⟩)
    (hcut : ∀ t < T, (R.runFrom (R.initCfg (pairEncode α x)) t).state ≠ some exit) :
    let ℓ := 2 * α.length + 2
    let hlen : ℓ + 1 < (pairEncode α x).length + 2 := by rw [length_pairEncode]; omega
    (uk_suffixStartupTM R exit).runFrom ((uk_suffixStartupTM R exit).initCfg (pairEncode α x))
        (T + 1 + (2 * ℓ + 3)) = suffixRulerCfg (Sum.inr (Sum.inr .done)) M
          (pairEncode α x) ℓ hlen ∧
      (∀ t < T + 1 + (2 * ℓ + 3),
        ((uk_suffixStartupTM R exit).runFrom
          ((uk_suffixStartupTM R exit).initCfg (pairEncode α x)) t).state ≠
            some (Sum.inr (Sum.inr .done))) := by
  let z := pairEncode α x
  let ℓ := 2 * α.length + 2
  let σ := Fin.castLEEmb (by omega : K + (k + 2) ≤ K + (k + 3))
  let A := ({ embedEmitTM σ R with q₀ := R.q₀ } : MultiTapeTM (K + (k + 3)) Bool P)
  let i : Fin (K + (k + 3)) := ⟨k + 2, by omega⟩
  let B := headerRulerTM i
  let d : Cfg (K + (k + 3)) Bool P z :=
    ⟨some exit, 1,
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
        else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have initEmbed : embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (R.initCfg z) =
      A.initCfg z := by
    apply embedEmitCfg_eq
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_state]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, List.nil_append]
    · intro j
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
  have aRun : A.runFrom (A.initCfg z) T = d := by
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, z, hrun]
    apply embedEmitCfg_eq
    · rfl
    · rfl
    · rfl
    · intro j; exact ⟨rfl, rfl⟩
    · intro j hj
      have hge : K + (k + 2) ≤ j.val := by
        by_contra h
        apply hj
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext; rfl
      constructor
      · funext a
        simp only [d, if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
      · rfl
  have aCut : ∀ t < T, (A.runFrom (A.initCfg z) t).state ≠ some exit := by
    intro t ht
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, embedEmitCfg_state]
    exact hcut t ht
  let c := d.mapState (fun _ => (0 : Fin 4))
  have cstate : c.state = some 0 := by rw [Cfg.mapState_state]; rfl
  have cpos : c.inputPos.val = 1 + 0 := by rw [Cfg.mapState_inputPos]; rfl
  have cblank : ∀ a, c.workTapes i a = none := by
    intro a
    rw [Cfg.mapState_workTapes]
    simp only [d, i, if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1)]
  obtain ⟨bRun, bCut⟩ := headerRulerTM_run i c 0 cpos cstate α x
    (by rw [List.drop_zero]) cblank
  have cmap : c.mapState Sum.inl = d.mapState (fun _ => (Sum.inl 0 : Fin 4 ⊕ RewindPhase)) := by
    rw [Cfg.mapState_mapState]; rfl
  rw [cmap] at bRun bCut
  have clen : c.inputPos.val + ℓ < z.length + 2 := by
    rw [cpos]
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have plen : ℓ + 1 < z.length + 2 := by
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have final :
      (⟨some (Sum.inr RewindPhase.done),
        ⟨c.inputPos.val + ℓ, clen⟩,
        Function.update c.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - c.workTapePos i)),
        c.workTapePos, c.output⟩ : Cfg (K + (k + 3)) Bool (Fin 4 ⊕ RewindPhase) z).mapState
          Sum.inr =
        suffixRulerCfg (Sum.inr (Sum.inr .done) : P ⊕ (Fin 4 ⊕ RewindPhase)) M z ℓ plen := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, suffixRulerCfg_state]; rfl
    · rw [Cfg.mapState_inputPos, suffixRulerCfg_inputPos]
      apply Fin.ext
      change c.inputPos.val + ℓ = ℓ + 1
      rw [cpos]
      omega
    · funext j a
      rw [Cfg.mapState_workTapes, suffixRulerCfg_workTapes]
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, c, Cfg.mapState_workTapePos, d, sub_zero,
          i, if_neg (by omega : k + 2 ≠ k),
          if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · have hjv : j.val ≠ k + 2 := by intro h; apply hj; exact Fin.ext h
        simp only [Function.update_of_ne hj, c, Cfg.mapState_workTapes, d, if_neg hjv]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, suffixRulerCfg_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, suffixRulerCfg_output]
  have init : (uk_suffixStartupTM R exit).initCfg z = (A.initCfg z).mapState Sum.inl := by
    exact MultiTapeTM.initCfg_eq_mapState A (uk_suffixStartupTM R exit) Sum.inl rfl z
  constructor
  · rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact (seamCompTM_run_ofCfg A exit B (Sum.inl 0) aRun rfl aCut bRun).trans final
  · intro t ht
    rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg A exit B (Sum.inl 0) (Sum.inr .done)
      aRun rfl aCut bRun rfl bCut t ht

/-- **U2-E, the code-first evaluator** [AB09, Theorem 1.9, the evaluator `U(x, α) = M_α(x)`, in
the code-first layout of `Turing.universal`]. For a `k`-tape scheme `E` there is a binary
machine `U` such that for every code `α` there is a constant `C` (depending on `α` only) with,
for every input `x`:
* whenever the machine coded by `α` halts on `x` with `output` within `t` steps, `U` halts on
  `pairEncode α x` with the same `output` within `C · (t + 1)` steps (no term in `|x|`);
* every completed output of `U` on `pairEncode α x` is a completed output of the coded machine
  on `x`.

At `k = 1` and `E := c.toK` this is `Turing.universal c`'s statement (shown in the gate's
probe); re-deriving `Turing.universal` from it is deferred. At `k = 2` it is the core of
Theorem 1.9 at `T log T` with the Hennie–Stearns conversion (design note §4).

**Proof sketch.** (i) *Code-first startup:* scan the doubled code and its separator, writing
one ruler cell per header cell, so the ruler is `true^ℓ` with `ℓ = 2|α| + 2`, the header length
(`Turing.universal_pair_length`); extract and canonize `α` as U2-S does, installing H2-F's
encoding of `M := E.machine α`'s initial configuration on the virtual input `x` (virtual
position `1`, physical head at `ℓ + 1`). (ii) *Ruler host:* run H2-F's machine `L` through H5's
bounded-prefix ruler host (`Turing.exists_rulerHostTM`, `Turing.RulerAt`): a block simulation
of `L` on the suffix input `x`, with at most `C_R · (ℓ + 1)` host steps per step of `L`, the same
bank and output, and exit cut. Composing with H2-F's lockstep, each step of `M` costs at most
`C_R (ℓ + 1)(50 · (|tableBitsK| + 1) + C_L)`, a constant for fixed `α`; with the startup this is
`≤ C · (t + 1)`. (iii) *Converse:* the ruler host does not halt before `L`, nor `L` before `M`
(the two cuts), so every completed output of `U` is `M`'s on `x`.

**Implementation.** The steps of the sketch run in a different order. The startup
`Turing.exists_selfStartupTMK` runs first, on `pairEncode α x` (its endpoint does not depend on
`x`), embedded in the first `K + (k + 2)` of `K + (k + 3)` tapes. A finite-state scan then reads
the header from input position `1` in aligned pairs, marking one cell for each header cell on
tape `k + 2`, which the startup leaves blank, and stops at the separator with the input head at
`ℓ + 1`; the work-tape rewind `Turing.rewindTM` returns that tape's head to its first cell. After
`T + 2ℓ + 4` steps in all (seams included), the first `k + 3` tapes hold the ruler host's
presentation `Turing.rulerHostCfg` of the forwarding loop's encoding of `M`'s initial
configuration on `x`, with the ruler as the last of them and the initial tag `false` (virtual
input position `1`). From there the ruler host of `Turing.exists_rulerHostTM` runs the forwarding
loop of `Turing.StepBlock.exists_forwardLoopTM`. With `T` the startup's time, `D` the loop's
per-step bound `50 · (|tableBitsK| + 1) + C_L` and `C_R` the host's factor, the constant is
`C = T + 2ℓ + 5 + C_R (ℓ + 1) D`, which depends on `α` only. -/
theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  obtain ⟨V, fV, dV, H, inj, C_R, hCR, hH⟩ := exists_rulerHostTM L
  letI : Fintype V := fV
  letI : DecidableEq V := dV
  let A := uk_suffixStartupTM R exit
  let finish : P ⊕ (Fin 4 ⊕ RewindPhase) := Sum.inr (Sum.inr .done)
  let U : FinTM Bool :=
    { k := K + (k + 3), State := (P ⊕ (Fin 4 ⊕ RewindPhase)) ⊕ V,
      tm := startupLoopTM (k := k + 1) A finish H (inj entry false) }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, _, hRα⟩ := hR α
  let M := E.machine α
  let ℓ := 2 * α.length + 2
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let T_A := T + 1 + (2 * ℓ + 3)
  let F := C_R * (ℓ + 1)
  let C := T_A + 1 + F * D
  have hAC : T_A + 1 ≤ C := by dsimp only [C]; omega
  have hDC : F * D ≤ C := by dsimp only [C]; omega
  refine ⟨C, ?_⟩
  intro x
  let z := pairEncode α x
  have hz : z.length = ℓ + x.length := length_pairEncode α x
  have hlen : ℓ + 1 < z.length + 2 := by omega
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; omega
  obtain ⟨hrun, hcut, _, _⟩ := hRα x
  obtain ⟨aRun, aCut⟩ := uk_suffixStartup_run R exit M α x T hrun hcut
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  let d := rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c rt 0
  have hb : false = true ↔ c.inputPos.val = 0 := by
    rw [(StepBlock.forwardLoopCfg_init_fields entry M x).2.1]
    decide
  have host := hH ℓ hz hℓ (pairEncode_drop α x) rt 0
    (by intro p _ _; rw [zero_add]) c false hb
  have uRun := startupLoopTM_runFrom (k := k + 1) A finish H (inj entry false) d
    (suffixRulerCfg (K := K) finish M z ℓ hlen) T_A aRun (suffixRulerCfg_state _ _ _ _ _) aCut
    (suffixRulerCfg_embed finish entry inj M ℓ hz hlen).symm
  obtain ⟨cost, hlock, hcost, _⟩ := hL (x := x) M
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) x output t).mp hcomp
    obtain ⟨t₀, _, _, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun e he => (hcost e he).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)
    obtain ⟨w, _, hw, ⟨b, _, hhost⟩, _, _, _, _⟩ := host v
    have uHalt : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).state = none := by
      rw [uRun w, Cfg.mapState_state, embedEmitCfg_state, hhost, rulerHostCfg_state,
        hr, StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none,
        Option.map_none]
    have uOut : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).output = output := by
      rw [uRun w, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hhost,
        rulerHostCfg_output, hr, StepBlock.forwardLoopCfg_output]
      exact hout
    have bound : T_A + 1 + w ≤ C * (t + 1) := by
      calc
        _ ≤ C + F * v := Nat.add_le_add hAC hw
        _ ≤ C + F * (D * t) := Nat.add_le_add_left (Nat.mul_le_mul_left F hvbound) C
        _ = C + (F * D) * t := by ring
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    exact ((FinTM.computesInTime_iff U z output (T_A + 1 + w)).mpr ⟨uHalt, uOut⟩).mono bound
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨uhalt, uout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le (k := k + 1) A finish H (inj entry false) T_A
      (by rw [aRun, suffixRulerCfg_state]; exact Option.some_ne_none finish) aCut
    have after : T_A + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) uhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [uRun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at uhalt
    rw [uRun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at uout
    have loopHalts : ∃ r, (L.runFrom c r).state = none := by
      by_contra hn
      have forever : ∀ r, (L.runFrom c r).state ≠ none := by
        intro r hr
        exact hn ⟨r, hr⟩
      obtain ⟨w, hw, _, _, cut, _, _, _⟩ := host (v + 1)
      exact cut (fun r _ => forever r) v (by omega) uhalt
    obtain ⟨r, rHalt⟩ := loopHalts
    obtain ⟨w, _, _, ⟨b, _, endpoint⟩, _, _, _, _⟩ := host r
    have wHalt : (H.runFrom d w).state = none := by
      rw [endpoint, rulerHostCfg_state, rHalt, Option.map_none]
    have loopOutput : (L.runFrom c r).output = output := by
      calc
        _ = (H.runFrom d w).output := by rw [endpoint, rulerHostCfg_output]
        _ = (H.runFrom d (max v w)).output :=
          (MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_right v w) wHalt).symm
        _ = (H.runFrom d v).output :=
          MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_left v w) uhalt
        _ = _ := uout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost r rHalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) x output t).mpr
      ⟨ht, ho.trans loopOutput⟩⟩


/-! ## Seal controls (each closes unsealed and fails sealed) -/
example {k K : ℕ} {P Q : Type} [DecidableEq P] (R : MultiTapeTM (K + (k + 2)) Bool P) (e : P)
    (L : MultiTapeTM (k + 2) Bool Q) (en : Q) : (startupLoopTM R e L en).q₀ = Sum.inl R.q₀ := rfl
example {k : ℕ} (i : Fin k) : (headerScanTM i).q₀ = 0 := rfl
example {k : ℕ} {z : List Bool} (i : Fin k) (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : (headerScanCfg i d q t ht).state = some q := rfl
example {k : ℕ} (i : Fin k) : (headerRulerTM i).q₀ = Sum.inl 0 := rfl
example {k K n : ℕ} {P : Type} (q : P) (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool)
    (ℓ : ℕ) (h : ℓ + 1 < z.length + 2) : (suffixRulerCfg (K := K) q M z ℓ h).state = some q := rfl

end Turing

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/SealUK0.out =====

exit=0 7s

## ===== campaign/gates/112-u2-harvest-api/evidence/probes/probe.out =====

Scratch/Probe.lean:197:8: warning: declaration uses 'sorry'
'F6Probe.two_scans' depends on axioms: [propext, Classical.choice, Quot.sound]
'F6Probe.hosted_startup' depends on axioms: [propext, Classical.choice, Quot.sound]
'F6Probe.final_seam' depends on axioms: [propext, Classical.choice, Quot.sound]
'F6Probe.layout' depends on axioms: [propext, Quot.sound]
'F6Probe.route_space' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
exit=0 3s

## ===== campaign/gates/112-u2-harvest-api/evidence/screen/pairdiff.txt =====

head pairs 23; union of earlier 23; new at head 5; earlier-only 5
  NEW   UniversalParts.lean::startupLoopTM_live_of_le  reproduces  UniversalParts.lean::startupLoopTM_runFrom: 88/144 = 61%
  NEW   UniversalParts.lean::StepBlock.forwardLoopCfg_init_fields  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 66/109 = 61%
  NEW   UniversalParts.lean::suffixRulerCfg_embed  reproduces  UniversalParts.lean::rulerHostCfg_fields: 140/236 = 59%
  NEW   UniversalK.lean::universalK  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 62/109 = 57%
  NEW   UniversalK.lean::exists_selfUniversalK  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 62/109 = 57%
  GONE  UniversalK.lean::uk_encode_init_fields  reproduces  UniversalK.lean::uk_encode_halt: 66/109 = 61%
  GONE  UniversalK.lean::uk_embed_suffix  reproduces  UniversalK.lean::uk_ruler_fields: 140/236 = 59%
  GONE  UniversalK.lean::uk_loop_pre_live  reproduces  UniversalK.lean::uk_loop_run: 75/131 = 57%
  GONE  UniversalK.lean::universalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%
  GONE  UniversalK.lean::exists_selfUniversalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%

## ===== campaign/gates/112-u2-harvest-api/evidence/screen/pop-base.txt =====

TCSlib/Complexity/TuringMachine/UniversalK.lean TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean TCSlib/Complexity/TuringMachine/Build/InputDevice.lean TCSlib/Complexity/TuringMachine/Build/Rewind.lean TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean TCSlib/Complexity/TuringMachine/SelfUniversal.lean

## ===== campaign/gates/112-u2-harvest-api/evidence/screen/pop-head.txt =====

TCSlib/Complexity/TuringMachine/UniversalK.lean TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean TCSlib/Complexity/TuringMachine/Build/InputDevice.lean TCSlib/Complexity/TuringMachine/Build/Rewind.lean TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean TCSlib/Complexity/TuringMachine/SelfUniversal.lean TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean

## ===== campaign/gates/112-u2-harvest-api/evidence/screen/screen-base.txt =====

declarations screened: 134; copy pairs (target reproduces >= half of source): 23; reproduced text: 14,123 chars
   UniversalK.lean::ss_captureInitial  reproduces  InterpreterStartup.lean::embedSilentCfg_initCfg: 1110/1110 = 100%
   InterpreterStartup.lean::embedSilentCfg_initCfg  reproduces  UniversalK.lean::ss_captureInitial: 1110/1110 = 100%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1440/1718 = 84%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1396/1718 = 81%
   InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1670/2086 = 80%
   InputDevice.lean::exists_rulerTestTM  reproduces  InputDevice.lean::rd_test_return: 108/136 = 79%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1440/2086 = 69%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1670/2482 = 67%
   UniversalK.lean::uk_encode_init_fields  reproduces  UniversalK.lean::uk_encode_halt: 66/109 = 61%
   UniversalK.lean::uk_embed_suffix  reproduces  UniversalK.lean::uk_ruler_fields: 140/236 = 59%
   UniversalK.lean::uk_loop_pre_live  reproduces  UniversalK.lean::uk_loop_run: 75/131 = 57%
   UniversalK.lean::universalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%
   UniversalK.lean::exists_selfUniversalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1396/2482 = 56%
   UniversalK.lean::ss_capturedPrefix_fields  reproduces  UniversalK.lean::ss_capturedPrefix_run: 648/1163 = 56%
   UniversalK.lean::ss_inputRewind_run  reproduces  UniversalK.lean::ss_inputRewind_done: 177/321 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   StepBlockForward.lean::fl_restore  reproduces  StepBlockForward.lean::fl_home: 78/143 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferAdvance_run  reproduces  UniversalK.lean::ss_bufferClear_run: 1040/2075 = 50%

## ===== campaign/gates/112-u2-harvest-api/evidence/screen/screen-head.txt =====

declarations screened: 137; copy pairs (target reproduces >= half of source): 23; reproduced text: 14,136 chars
   UniversalK.lean::ss_captureInitial  reproduces  InterpreterStartup.lean::embedSilentCfg_initCfg: 1110/1110 = 100%
   InterpreterStartup.lean::embedSilentCfg_initCfg  reproduces  UniversalK.lean::ss_captureInitial: 1110/1110 = 100%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1440/1718 = 84%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1396/1718 = 81%
   InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1670/2086 = 80%
   InputDevice.lean::exists_rulerTestTM  reproduces  InputDevice.lean::rd_test_return: 108/136 = 79%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1440/2086 = 69%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1670/2482 = 67%
   UniversalParts.lean::startupLoopTM_live_of_le  reproduces  UniversalParts.lean::startupLoopTM_runFrom: 88/144 = 61%
   UniversalParts.lean::StepBlock.forwardLoopCfg_init_fields  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 66/109 = 61%
   UniversalParts.lean::suffixRulerCfg_embed  reproduces  UniversalParts.lean::rulerHostCfg_fields: 140/236 = 59%
   UniversalK.lean::universalK  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 62/109 = 57%
   UniversalK.lean::exists_selfUniversalK  reproduces  UniversalParts.lean::StepBlock.forwardLoopCfg_halt_iff: 62/109 = 57%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1396/2482 = 56%
   UniversalK.lean::ss_capturedPrefix_fields  reproduces  UniversalK.lean::ss_capturedPrefix_run: 648/1163 = 56%
   UniversalK.lean::ss_inputRewind_run  reproduces  UniversalK.lean::ss_inputRewind_done: 177/321 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   StepBlockForward.lean::fl_restore  reproduces  StepBlockForward.lean::fl_home: 78/143 = 55%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferAdvance_run  reproduces  UniversalK.lean::ss_bufferClear_run: 1040/2075 = 50%

## ===== TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.Rewind
import Mathlib.Algebra.Group.Action.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parts of the `k`-generic universal machines

[AB09, §1.4.1 and the proof of Theorem 1.9]: the pieces that the `k`-generic universal machines
of `TuringMachine/UniversalK.lean` (U2) are assembled from, published so that a second consumer
(the space-universal machine `Complexity.space_universal`, [AB09, Exercise 4.1]) composes them
instead of re-deriving them. Harvested from `UniversalK`'s privates (the U2 harvest API, user
ruling of 2026-11-06: a new `Build/` module; plan `campaign/items/roadmap3/PLAN.md`, §F6(c)).

* **The forwarding loop at an initial configuration.** H2-F's encoding
  `Turing.StepBlock.forwardLoopCfg` of a machine's initial configuration (its tapes, fields and
  halting), its embedding at the startup's endpoint, and the three readings of H2-F's lockstep
  used by both universal machines: the forward time bound to the first halt, liveness forever,
  and the converse on outputs.
* **The startup–loop seam.** `Turing.startupLoopTM`: a startup on `K + (k + 2)` tapes followed,
  at its exit, by a loop on the first `k + 2`; its start, its live prefix, its run after the
  seam from any seam endpoint, and its space ledger from any seam endpoint.
* **The header ruler.** `Turing.headerScanTM`: a finite-state scan of one doubled header
  `pairEncode u v`, from any input offset, writing one ruler cell per input cell; from an
  existing ruler prefix `true^m` it extends the ruler to `true^(m + 2|u| + 2)`, so consecutive
  headers give one ruler. `Turing.headerRulerTM`: the scan followed by the rewind.
* **The suffix-ruler layout.** `Turing.suffixRulerCfg`: the simulation bank, then the ruler
  `true^ℓ`, with the input head just past a header of length `ℓ`; it is the embedding of the
  ruler host's initial presentation (`Turing.rulerHostCfg`) of the forwarding loop's start.

## Main definitions

* `Turing.startupLoopTM` — the startup followed by the embedded loop.
* `Turing.headerScanTM`, `Turing.headerScanCfg` — the header scan and its presentation after
  `t` marks (with field equations).
* `Turing.headerRulerTM` — the header scan followed by the work-tape rewind.
* `Turing.suffixRulerCfg` — the suffix-ruler seam layout (with field equations).

## Main results

* `Turing.MultiTapeTM.initCfg_eq_mapState` — the restart identity (ledger RS-1's general form).
* `Turing.StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`,
  `Turing.embedEmitCfg_forwardLoop_init` — the forwarding loop's encoding at the start.
* `Turing.StepBlock.forwardLoop_forward`, `_live`, `_converse` — the lockstep's readings.
* `Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom`, `_spaceUsed_le` — the seam.
* `Turing.headerScanTM_run`, `Turing.headerScanCfg_ruler`, `Turing.headerRulerTM_run` — the
  header ruler.
* `Turing.rulerHostCfg_fields`, `Turing.suffixRulerCfg_embed` — the suffix-ruler layout.

All proved. The generalizations against the private forms are `startupLoopTM_spaceUsed_le` (any
seam endpoint, not only the native startup's) and `headerScanCfg_ruler` (from a ruler prefix
`true^m`, not only a blank tape); every other row is the private statement, renamed.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9 and its proof: the universal machine
  reads the code and simulates `M` step by step on a work-tape copy of its table; Exercise 4.1,
  the space-bounded universal machine.)
-/

namespace Turing

/-! ## The restart identity -/

/-- **The restart identity**: if a machine `B`'s initial state is the image `f A.q₀` of
another machine `A`'s, then `B`'s initial configuration on any input is `A`'s with its state
relabelled by `f`. Ledger RS-1's general form (`campaign/duplication-ledger.md`). [AB09, §1.4.1]
(glue for the universal machine's composed startups). -/
theorem MultiTapeTM.initCfg_eq_mapState {m : ℕ} {P Q : Type}
    (A : MultiTapeTM m Bool P) (B : MultiTapeTM m Bool Q) (f : P → Q)
    (hq : B.q₀ = f A.q₀) (x : List Bool) : B.initCfg x = (A.initCfg x).mapState f := by
  refine Cfg.ext ?_ ?_ (funext fun j => funext fun a => ?_) (funext fun j => ?_) ?_
  all_goals
    simp only [MultiTapeTM.initCfg_eq, Cfg.mapState_state, Cfg.mapState_inputPos,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
      Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes, Cfg.init_workTapePos,
      Cfg.init_output, Option.map_some, hq]

/-! ## The forwarding loop at an initial configuration -/

/-- **The forwarding loop's encoding of an initial configuration, its tapes**: H2-F's
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` of a `k`-tape binary machine's
initial configuration has, on its `k + 2` tapes, the table bits `tableBitsK M.tr` as a buffer on
tape `k`, the unary initial state `unaryFin M.q₀` from cell `2` on tape `k + 1` (cells `0` and
`1` blank), and blank mirrored tapes `0, …, k - 1`. This is the layout the universal machines'
startups install. [AB09, §1.4.1, the proof of Theorem 1.9: the work-tape copy of `M`'s table
and its current state]

**Proof sketch.** Split the tape index into a mirrored tape and one of the two
auxiliary tapes. The initial mirrored tapes are blank; the table is unchanged,
and the summary agrees cell by cell, including its blank cell at zero. -/
theorem StepBlock.forwardLoopCfg_init_workTapes {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) (j : Fin (k + 2)) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
      else fun _ => none := by
  have hw : (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapes j =
      Fin.addCases (motive := fun _ => ℤ → Option Bool) (M.initCfg x).workTapes (fun j =>
        if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
        else StepBlock.summaryCells none (((M.initCfg x).state.map unaryFin).getD [])) j :=
    funext fun a => StepBlock.forwardLoopCfg_workTapes entry M (M.initCfg x) j a
  rw [hw]
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq]
    have h1 : (Fin.castAdd 2 i).val ≠ k := by simp only [Fin.coe_castAdd]; omega
    have h2 : (Fin.castAdd 2 i).val ≠ k + 1 := by simp only [Fin.coe_castAdd]; omega
    rw [if_neg h1, if_neg h2]
    funext p
    rw [Cfg.init_workTapes]
  · rw [Fin.addCases_right, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some,
      Option.getD_some]
    by_cases h : j' = 0
    · subst h
      have h1 : (Fin.natAdd k (0 : Fin 2)).val = k := by simp only [Fin.coe_natAdd]; omega
      rw [if_pos rfl, if_pos h1]
    · have hj : j' = 1 := by omega
      subst hj
      have h1 : (Fin.natAdd k (1 : Fin 2)).val ≠ k := by simp only [Fin.coe_natAdd]; omega
      have h2 : (Fin.natAdd k (1 : Fin 2)).val = k + 1 := by simp only [Fin.coe_natAdd]; omega
      rw [if_neg (by decide), if_neg h1, if_pos h2]
      funext p
      rw [StepBlock.summaryCells_eq]
      by_cases hp : p = 0
      · rw [if_pos hp, hp]
        exact (FinTM.bufferTape_of_neg _ (by omega)).symm
      · rw [if_neg hp]

/-- **The forwarding loop's encoding of an initial configuration, its other fields**: the
encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg x)` is at the control `entry`, with
input head at cell `1`, every work head at `0` and an empty output. [AB09, §1.4.1, the proof of
Theorem 1.9] -/
theorem StepBlock.forwardLoopCfg_init_fields {k n : ℕ} {Q : Type} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    (StepBlock.forwardLoopCfg entry M (M.initCfg x)).state = some entry ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).inputPos.val = 1 ∧
      (∀ j, (StepBlock.forwardLoopCfg entry M (M.initCfg x)).workTapePos j = 0) ∧
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)).output = [] := by
  refine ⟨?_, ?_, fun j => ?_, ?_⟩
  · rw [StepBlock.forwardLoopCfg_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  · rw [StepBlock.forwardLoopCfg_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos]; rfl
  · rw [StepBlock.forwardLoopCfg_workTapePos]
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · rw [Fin.addCases_left, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    · rw [Fin.addCases_right]
  · rw [StepBlock.forwardLoopCfg_output, MultiTapeTM.initCfg_eq, Cfg.init_output]

/-- **The forwarding loop's encoding halts with its source**: for any configuration `c` of a
`k`-tape binary machine, the encoding `Turing.StepBlock.forwardLoopCfg entry M c` is halted
exactly when `c` is, and its output is `c`'s. Stated as the conjunction of the iff and the output
equation. [AB09, §1.4.1, the proof of Theorem 1.9: the universal machine halts with `M`'s
output] -/
theorem StepBlock.forwardLoopCfg_halt_iff {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    ((StepBlock.forwardLoopCfg entry M c).state = none ↔ c.state = none) ∧
      (StepBlock.forwardLoopCfg entry M c).output = c.output := by
  rw [StepBlock.forwardLoopCfg_state, StepBlock.forwardLoopCfg_output, Option.map_eq_none_iff]
  exact ⟨Iff.rfl, rfl⟩

/-- **The startup's native endpoint is the embedded initial encoding**: embedding the
forwarding loop's encoding of `M`'s initial configuration on `x` in the first `k + 2` of
`K + (k + 2)` tapes (the other tapes blank with their heads at `0`, no prior output) gives the
configuration at the control `exit`, input head `1`, the table on tape `k`, the unary initial
state from cell `2` on tape `k + 1`, every other tape blank, every head at `0` and an empty
output, with its control relabelled to `entry`. This is the endpoint of the startup
`Turing.exists_selfStartupTMK`, hence the seam hypothesis of `Turing.startupLoopTM_runFrom` for
the native layout. [AB09, §1.4.1, the proof of Theorem 1.9]

**Proof sketch.** Use the public reconstruction theorem for the emitting embedding.
The selected tapes and heads are the initial encoding's fields. An unselected
tape has index at least `k + 2`, so both tests in the startup layout are false. -/
theorem embedEmitCfg_forwardLoop_init {k n K : ℕ} {P Q : Type} (exit : P) (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (x : List Bool) :
    embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
      (fun _ _ => none) (fun _ => 0) []
      (StepBlock.forwardLoopCfg entry M (M.initCfg x)) =
        (⟨some exit, 1,
          fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
            else if j.val = k + 1 then fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)
            else fun _ => none,
          fun _ => 0, []⟩ : Cfg (K + (k + 2)) Bool P x).mapState (fun _ => entry) := by
  apply embedEmitCfg_eq
  · rw [Cfg.mapState_state]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).1
  · apply Fin.ext
    rw [Cfg.mapState_inputPos]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.1
  · rw [List.nil_append, Cfg.mapState_output]
    exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.2
  · intro i
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      exact congrFun (StepBlock.forwardLoopCfg_init_workTapes entry M x i) a
    · rw [Cfg.mapState_workTapePos]
      exact (StepBlock.forwardLoopCfg_init_fields entry M x).2.2.1 i
  · intro j hj
    have hjge : k + 2 ≤ j.val := by
      by_contra h
      have hlt : j.val < k + 2 := by omega
      apply hj
      refine ⟨⟨j.val, hlt⟩, ?_⟩
      apply Fin.ext
      rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      dsimp only
      rw [if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
    · rw [Cfg.mapState_workTapePos]

/-- **The forwarding loop's forward time bound**: let `L` simulate a `k`-tape binary machine
`M` in macro-step lockstep over H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M`
(the `Turing.Lockstep` of `Turing.StepBlock.exists_forwardLoopTM`), with every live step's cost
at most `D`. If `M` has halted on `x` by time `t`, there is its first halting time `t₀ ≤ t`
(live before `t₀`) such that the simulated time `Σ_{u < t₀} cost` is at most `D · t` and `L`,
started at the encoding of `M`'s initial configuration, is after that many steps at the
encoding of `M`'s configuration at time `t`. [AB09, §1.4.1, the proof of Theorem 1.9: each
step of `M` costs the universal machine a number of steps depending on `M` only]

**Proof sketch.** Choose the first source halt. The lockstep applies up to that
time, and each summand in its simulated time is bounded by the per-step bound.
Absorption identifies the first halted configuration with the given final one. -/
theorem StepBlock.forwardLoop_forward {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → cost c ≤ D) (t : ℕ)
    (hhalt : (M.runFrom (M.initCfg x) t).state = none) :
    ∃ t₀ ≤ t, (∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none) ∧
      (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) ≤ D * t ∧
      L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x))
          (∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)) =
        StepBlock.forwardLoopCfg entry M (M.runFrom (M.initCfg x) t) := by
  obtain ⟨t₀, hle, hfirst, hsame⟩ := MultiTapeTM.exists_first_halt M (M.initCfg x) hhalt
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
  · calc
      _ ≤ ∑ _u ∈ Finset.range t₀, D := Finset.sum_le_sum fun u hu =>
        hcost _ (hfirst u (Finset.mem_range.mp hu))
      _ = D * t₀ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ D * t := Nat.mul_le_mul_left D hle
  · rw [hlock.runFrom (M.initCfg x) t₀ (by
      simpa only [Set.mem_singleton_iff] using hfirst), hsame]

/-- **The forwarding loop diverges with its source**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` with positive costs at live configurations, if `M`
never halts on `x`, then `L` started at the encoding of `M`'s initial configuration is live at
every time. [AB09, §1.4.1, Theorem 1.9: the universal machine diverges when `M` does]

**Proof sketch.** For a target time `v`, simulate `v + 1` source steps. Every
cost is positive, so their sum exceeds `v`; the lockstep cut gives liveness. -/
theorem StepBlock.forwardLoop_live {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hpos : ∀ c, c.state ≠ none → 0 < cost c)
    (hlive : ∀ u, (M.runFrom (M.initCfg x) u).state ≠ none) (v : ℕ) :
    (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state ≠ none := by
  have hsum : v + 1 ≤ ∑ u ∈ Finset.range (v + 1), cost (M.runFrom (M.initCfg x) u) := by
    calc
      _ = ∑ _u ∈ Finset.range (v + 1), (1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      _ ≤ _ := Finset.sum_le_sum fun u _ => hpos _ (hlive u)
  have hcut := hlock.cut (M.initCfg x) (v + 1)
    (fun u _ => by simpa only [Set.mem_singleton_iff] using hlive u) v (by omega)
  simpa only [Set.mem_singleton_iff] using hcut

/-- **The forwarding loop's converse**: under a macro-step lockstep over
`Turing.StepBlock.forwardLoopCfg entry M` whose costs at live configurations lie in `[1, D]`,
if `L` started at the encoding of `M`'s initial configuration on `x` has halted at time `u`,
then `M` has halted on `x` at some time `t`, with the same output as `L` at `u`. So every
completed output of the loop is a completed output of `M`. [AB09, §1.4.1, Theorem 1.9: the
universal machine's output is `M`'s]

**Proof sketch.** If the source never halted, positivity and the lockstep cut
would keep the loop live at the given time. Choose a source halt and apply the
forward lemma. The loop is now halted at both times, so its output agrees at
their maximum; the encoding preserves the source's output. -/
theorem StepBlock.forwardLoop_converse {k n : ℕ} {Q : Type} {x : List Bool}
    (M : MultiTapeTM k Bool (Fin (n + 1))) (L : MultiTapeTM (k + 2) Bool Q)
    (entry : Q) (cost : Cfg k Bool (Fin (n + 1)) x → ℕ) (D : ℕ)
    (hlock : Lockstep M L (StepBlock.forwardLoopCfg entry M) cost {none} {none})
    (hcost : ∀ c, c.state ≠ none → 0 < cost c ∧ cost c ≤ D) (u : ℕ)
    (hhalt : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).state = none) :
    ∃ t, (M.runFrom (M.initCfg x) t).state = none ∧
      (M.runFrom (M.initCfg x) t).output =
        (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) u).output := by
  classical
  have hex : ∃ t, (M.runFrom (M.initCfg x) t).state = none := by
    by_contra h
    have hsource : ∀ t, (M.runFrom (M.initCfg x) t).state ≠ none :=
      fun t ht => h ⟨t, ht⟩
    exact (StepBlock.forwardLoop_live M L entry cost hlock (fun c hc => (hcost c hc).1)
      hsource u) hhalt
  obtain ⟨t, ht⟩ := hex
  obtain ⟨t₀, _, _, _, hr⟩ :=
    StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t ht
  let v := ∑ i ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) i)
  have hv : (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).state = none := by
    rw [hr]
    exact (StepBlock.forwardLoopCfg_halt_iff entry M _).1.mpr ht
  refine ⟨t, ht, ?_⟩
  calc
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) v).output := by
      rw [hr, (StepBlock.forwardLoopCfg_halt_iff entry M _).2]
    _ = (L.runFrom (StepBlock.forwardLoopCfg entry M (M.initCfg x)) (max u v)).output :=
      (MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_right u v) hv).symm
    _ = _ := MultiTapeTM.runFrom_output_eq_of_halt L _ (Nat.le_max_left u v) hhalt
/-! ## The startup–loop seam -/

/-- **The startup–loop seam machine**: a startup `R` on `K + (k + 2)` work tapes, followed at
its exit control `exit` by the loop `L` on the first `k + 2` of them, entered at `entry`
(`Turing.seamCompTM` of `R` and the emitting embedding `Turing.embedEmitTM` of `L` along
`Fin.castLEEmb`, the other tapes untouched), started in `R`'s initial control. Read through
`Turing.startupLoopTM_initCfg`, `_live_of_le`, `_runFrom` and `_spaceUsed_le`. [AB09, §1.4.1,
the proof of Theorem 1.9: the universal machine first prepares its work tapes, then simulates]
-/
noncomputable def startupLoopTM {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) :
    MultiTapeTM (K + (k + 2)) Bool (P ⊕ Q) :=
  { seamCompTM R exit
      (embedEmitTM (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))) L) entry with
    q₀ := Sum.inl R.q₀ }

/-- **The seam machine's start**: on every input, `Turing.startupLoopTM R exit L entry` starts
in the startup's initial configuration, its control relabelled by `Sum.inl`. [AB09, §1.4.1] -/
theorem startupLoopTM_initCfg {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) (x : List Bool) :
    (startupLoopTM R exit L entry).initCfg x = (R.initCfg x).mapState Sum.inl := by
  exact MultiTapeTM.initCfg_eq_mapState R (startupLoopTM R exit L entry) Sum.inl rfl x

/-- **The seam machine is live through the startup**: if the startup `R` is live at time `T`
on `x` and does not reach `exit` before `T`, then `Turing.startupLoopTM R exit L entry` is live
on `x` at every time `t ≤ T`. [AB09, §1.4.1] -/
theorem startupLoopTM_live_of_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool} (T : ℕ)
    (hlive : (R.runFrom (R.initCfg x) T).state ≠ none)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    ((startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x) t).state ≠
      none := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_left R exit _ entry hcut t ht, Cfg.mapState_state]
  intro hh
  exact MultiTapeTM.runFrom_state_ne_none_of_le R (R.initCfg x) T hlive t ht
    (Option.map_eq_none_iff.mp hh)

/-- **The seam machine after the seam, from any seam endpoint**: suppose the startup `R`
reaches the configuration `d` on `x` at exactly time `T`, at the control `exit`, and not
earlier, and that `d` with its control replaced by `entry` is the embedding of a loop
configuration `c` in the first `k + 2` tapes (the others blank with their heads at `0`, no
prior output). Then for every `t`, `Turing.startupLoopTM R exit L entry` at time `T + 1 + t` is
the embedding of `L`'s run from `c` for `t` steps, with its control relabelled by `Sum.inr`. The
loop may be the native forwarding loop (`c` its encoding, `d` the startup's native endpoint,
`Turing.embedEmitCfg_forwardLoop_init`) or its suffix host (`c` the ruler host's presentation,
`d` the suffix-ruler layout, `Turing.suffixRulerCfg_embed`). [AB09, §1.4.1] -/
theorem startupLoopTM_runFrom {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c) (t : ℕ) :
    (startupLoopTM R exit L entry).runFrom ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) =
      (embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] (L.runFrom c t)).mapState Sum.inr := by
  rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀,
    seamCompTM_runFrom_right R exit _ entry hrun hexit hcut t, hcfg, embedEmitTM_runFrom]

/-- **The seam machine's space ledger, from any seam endpoint**: under the seam hypotheses of
`Turing.startupLoopTM_runFrom` (the startup `R` reaches `d` on `x` at exactly `T`, at `exit`,
not earlier, and `d` relabelled at `entry` is the embedding of the loop configuration `c`), if
the startup uses at most `B` cells by `T` and the loop `L`, run from `c`, uses at most `S ≥ 1`
cells on each of its tapes by `t`, then `Turing.startupLoopTM R exit L entry` uses at most
`B + (K + (k + 2)) · S` cells on `x` by time `T + 1 + t`. [AB09, Exercise 4.1: the universal
machine's space is the simulated machine's up to a factor depending on the code]

*Generalization.* The private form fixed the native endpoint (`d` the startup's layout at input
position `1`, `c` the encoding of `M`'s initial configuration). It read that endpoint only
through its exit control and the embedding identity, now the hypotheses `hexit` and `hcfg`; at
the native endpoint they are `rfl` and `Turing.embedEmitCfg_forwardLoop_init`, which is the old
statement. At `(K, k + 1)`, `d` the suffix-ruler layout and `c` the ruler host's presentation
(`Turing.suffixRulerCfg_embed`) it is the ledger of the suffix layout.

**Proof sketch.** The seam's visited-set theorem bounds each tape by the union
of its startup and loop visits. A selected loop tape has the source loop's
visited set; an unselected tape visits just its initial cell. Count each union
and sum over the host's tapes, using the public space equations. -/
theorem startupLoopTM_spaceUsed_le {k K : ℕ} {P Q : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) {x : List Bool}
    (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
    (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
    (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
    (hcfg : d.mapState (fun _ => entry) =
      embedEmitCfg (Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2)))
        (fun _ _ => none) (fun _ => 0) [] c)
    (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
    (hloop : ∀ i, L.spaceUsedByTape c t i ≤ S) :
    (startupLoopTM R exit L entry).spaceUsed ((startupLoopTM R exit L entry).initCfg x)
        (T + 1 + t) ≤ B + (K + (k + 2)) * S := by
  classical
  let σ := Fin.castLEEmb (by omega : k + 2 ≤ K + (k + 2))
  let A := embedEmitTM σ L
  let e := embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] c
  have he : d.mapState (fun _ => entry) = e := hcfg
  have hA : ∀ j, A.spaceUsedByTape e t j ≤ S := by
    intro j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [(embedEmitTM_visitedByTapeHead σ L _ _ [] c t i).2]
      exact hloop i
    · rw [(embedEmitTM_visitedByTapeHead_frame σ L _ _ [] c t j hj).2]
      exact hS
  have htape (j : Fin (K + (k + 2))) :
      (startupLoopTM R exit L entry).spaceUsedByTape
          ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ≤
        R.spaceUsedByTape (R.initCfg x) T j + S := by
    rw [MultiTapeTM.spaceUsedByTape_eq_card]
    have hsub := seamCompTM_visitedByTapeHead_ofCfg R exit A entry
      (c₁ := d) (T₂ := t) hrun hexit hcut j
    rw [he] at hsub
    have hown : (startupLoopTM R exit L entry).visitedByTapeHead
        ((startupLoopTM R exit L entry).initCfg x) (T + 1 + t) j ⊆
        (seamCompTM R exit A entry).visitedByTapeHead
          ((R.initCfg x).mapState Sum.inl) (T + 1 + t) j := by
      intro p hp
      rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
      obtain ⟨u, hu, hp⟩ := hp
      refine ⟨u, hu, ?_⟩
      rw [startupLoopTM_initCfg, startupLoopTM, MultiTapeTM.runFrom_with_q₀] at hp
      exact hp
    calc
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j ∪ A.visitedByTapeHead e t j).card :=
        Finset.card_le_card (hown.trans hsub)
      _ ≤ (R.visitedByTapeHead (R.initCfg x) T j).card +
          (A.visitedByTapeHead e t j).card := Finset.card_union_le _ _
      _ = R.spaceUsedByTape (R.initCfg x) T j + A.spaceUsedByTape e t j := by
        rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      _ ≤ _ := Nat.add_le_add_left (hA j) _
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    _ ≤ ∑ j, (R.spaceUsedByTape (R.initCfg x) T j + S) :=
      Finset.sum_le_sum fun j _ => htape j
    _ = R.spaceUsed (R.initCfg x) T + (K + (k + 2)) * S := by
      rw [Finset.sum_add_distrib, ← MultiTapeTM.spaceUsed_eq_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right hB _

/-! ## The header scan and the header ruler -/

/-- **The header scan**: a finite-state machine on `k` work tapes that reads a doubled header
`pairEncode u v` (the bits of `u`, each written twice, then the separator `false, true`) in
aligned pairs from its input head, writing `true` on tape `i` and moving that head and the input
head right at every step, and stops at its control `3` just past the separator. States `0`, `1`
and `2` read a pair (`1` and `2` remember its first bit); `3` is the exit, where the machine idles.
So it writes one ruler cell per header cell. It is hand-built: no catalog row writes a ruler of a
doubled header's length. Read through `Turing.headerScanTM_run`. [AB09, §1.4.1, the proof of
Theorem 1.9: the universal machine reads the code at the start of its input; the pair encoding
of [AB09, §1.4]] -/
def headerScanTM {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Fin 4) where
  q₀ := 0
  tr := fun q b _ =>
    if q = 3 then inputMoveAction 0 3
    else tapeAction i .pos (some (some true)) .pos
      (if q = 0 then if b = some false then 1 else 2
       else if q = 1 ∧ b = some true then 3 else 0)

/-- **The header scan's presentation after `t` marks**: from a configuration `d`, the
configuration at control `q` with the input head and the head of tape `i` both `t` cells right
of `d`'s, the cells `[pos, pos + t)` of tape `i` (`pos` its head in `d`) set to `true` and every
other cell, tape, head and the output as in `d`. [AB09, §1.4.1] -/
def headerScanCfg {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) : Cfg k Bool (Fin 4) z :=
  ⟨some q, ⟨d.inputPos.val + t, ht⟩,
    Function.update d.workTapes i
      (fun a => if d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        then some true else d.workTapes i a),
    Function.update d.workTapePos i (d.workTapePos i + t), d.output⟩

/-! The header scan's presentation's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.headerScanCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  headerScanCfg

/-- Zero scan steps leave the initial live configuration unchanged. -/
private theorem up_scan_zero {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (hd : d.state = some 0) :
    headerScanCfg i d 0 0 (by have := d.inputPos.isLt; omega) = d := by
  apply Cfg.ext
  · exact hd.symm
  · apply Fin.ext; simp only [headerScanCfg, Nat.add_zero]
  · funext j a
    simp only [headerScanCfg, Nat.cast_zero, add_zero]
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]
  · simp only [headerScanCfg, Nat.cast_zero, add_zero, Function.update_eq_self]
  · rfl

/-- One scan step writes and advances both heads, preserving every frame field.

**Proof sketch.** Read the transition with the public writing-action equation. Its
updated cell is exactly the new right endpoint of the already marked interval;
all other cells retain their previous value. -/
private theorem up_scan_step {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 1) (hq : q ≠ 3) (b : Bool)
    (hb : (headerScanCfg i d q t (by omega)).inputSymbol = some b) :
    (headerScanTM i).step (headerScanCfg i d q t (by omega)) =
      headerScanCfg i d
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) (t + 1) (by omega) := by
  have ht' : (headerScanTM i).tr q (headerScanCfg i d q t (by omega)).inputSymbol
      (headerScanCfg i d q t (by omega)).workTapeSymbols = tapeAction i .pos
        (some (some true)) .pos
        (if q = 0 then if b = false then 1 else 2
         else if q = 1 ∧ b = true then 3 else 0) := by
    simp only [headerScanTM, if_neg hq, hb, Option.some.injEq]
  rw [step_of_tapeAction_write _ _ i .pos (some true) .pos rfl ht']
  apply Cfg.ext
  · rfl
  · rw [moveInputPos_pos_of_ne_right _ (by simp only [headerScanCfg]; omega)]
    apply Fin.ext
    simp only [headerScanCfg]
    omega
  · funext j a
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one]
      by_cases ha : a = d.workTapePos i + t
      · subst a
        rw [Function.update_self, if_pos (by omega)]
      · rw [Function.update_of_ne ha]
        by_cases ha' : d.workTapePos i ≤ a ∧ a < d.workTapePos i + t
        · rw [if_pos ha', if_pos (by omega)]
        · rw [if_neg ha', if_neg (by omega)]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · funext j
    by_cases hj : j = i
    · subst j
      simp only [headerScanCfg, Function.update_self, Nat.cast_add, Nat.cast_one,
        SignType.pos_eq_one, SignType.coe_one, add_assoc]
    · simp only [headerScanCfg, Function.update_of_ne hj]
  · rfl

/-- The scanner consumes one aligned pair, marking both input cells.

**Proof sketch.** The suffix equation gives the two input symbols through `getElem_drop`.
Apply the one-step result twice. The intermediate state stores the first bit,
and the second bit either returns on the separator or resumes the pair scan. -/
private theorem up_scan_pair {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p t : ℕ) (hp : d.inputPos.val = 1 + p)
    (a b : Bool) (rest : List Bool) (hz : z.drop (p + t) = a :: b :: rest) :
    let hlen : d.inputPos.val + (t + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      simp only [List.length_drop, List.length_cons] at h
      omega
    let c := headerScanCfg i d 0 t (by omega)
    (headerScanTM i).runFrom c 2 =
        headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) hlen ∧
      (∀ v < 2, ((headerScanTM i).runFrom c v).state ≠ some 3) := by
  have hlen : p + t + 2 ≤ z.length := by
    have h := congrArg List.length hz
    simp only [List.length_drop, List.length_cons] at h
    omega
  dsimp only
  have ha : z[p + t]'(by omega) = a := by
    have hh : (z.drop (p + t))[0]'(by rw [hz]; simp) = a := by
      simp only [hz, List.getElem_cons_zero]
    simpa only [List.getElem_drop, Nat.add_zero] using hh
  have hb : z[p + t + 1]'(by omega) = b := by
    have hh : (z.drop (p + t))[1]'(by rw [hz]; simp) = b := by
      simp only [hz, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa only [List.getElem_drop] using hh
  let q : Fin 4 := if a = false then 1 else 2
  have h1 : (headerScanTM i).step (headerScanCfg i d 0 t (by omega)) =
      headerScanCfg i d q (t + 1) (by omega) := by
    have read : (headerScanCfg i d 0 t (by omega)).inputSymbol = some a := by
      rw [inputSymbolInner (p + t) (by simp only [headerScanCfg]; omega) (by omega), ha]
    simpa only [if_pos rfl] using up_scan_step i d 0 t (by omega) (by decide) a read
  have h2 : (headerScanTM i).step (headerScanCfg i d q (t + 1) (by omega)) =
      headerScanCfg i d (if a = false ∧ b = true then 3 else 0) (t + 2) (by omega) := by
    have read : (headerScanCfg i d q (t + 1) (by omega)).inputSymbol = some b := by
      rw [inputSymbolInner (p + t + 1) (by simp only [headerScanCfg]; omega) (by omega), hb]
    have step := up_scan_step i d q (t + 1) (by omega)
      (by dsimp only [q]; split <;> decide) b read
    cases a <;> cases b <;> simpa only [q, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, and_self, and_false, false_and, true_and] using step
  have one (e : Cfg k Bool (Fin 4) z) :
      (headerScanTM i).runFrom e 1 = (headerScanTM i).step e := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  constructor
  · calc
      _ = (headerScanTM i).runFrom
          ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 1) 1 :=
        MultiTapeTM.runFrom_add _ 1 1
      _ = _ := by rw [one, one, h1, h2]
  · intro v hv
    have casesv : v = 0 ∨ v = 1 := by omega
    rcases casesv with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
      change some (0 : Fin 4) ≠ some 3
      decide
    · rw [one, h1]
      change some q ≠ some 3
      cases a <;> decide

/-- The scanner consumes one doubled header from any native input offset.

**Proof sketch.** Induct on the header word. Every doubled bit takes two steps
and returns to the pair-reading state; the separator takes two steps and returns.
The suffix equation is advanced with `drop_drop`, while the exact-time cut is
split before and after each pair. -/
private theorem up_scan_header {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (u v : List Bool) (t : ℕ) (hz : z.drop (p + t) = pairEncode u v) :
    let hlen : d.inputPos.val + (t + (2 * u.length + 2)) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) (2 * u.length + 2) =
        headerScanCfg i d 3 (t + (2 * u.length + 2)) hlen ∧
      (∀ r < 2 * u.length + 2,
        ((headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) r).state ≠ some 3) := by
  have length_bound : p + t + (2 * u.length + 2) ≤ z.length := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    omega
  dsimp only
  induction u generalizing t with
  | nil =>
    have hz' : z.drop (p + t) = false :: true :: v := by
      simpa only [pairEncode_eq, List.flatMap_nil, List.nil_append,
        List.cons_append] using hz
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, and_self, ↓reduceIte]
      using up_scan_pair i d p t hp false true v hz'
  | cons b u ih =>
    have hz' : z.drop (p + t) = b :: b :: pairEncode u v := by
      simpa only [pairEncode_eq, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hz
    have pair := up_scan_pair i d p t hp b b (pairEncode u v) hz'
    have hpair : (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega)) 2 =
        headerScanCfg i d 0 (t + 2) (by omega) := by
      cases b <;> simpa only [Bool.false_eq_true, Bool.true_eq_false,
        false_and, and_false, ↓reduceIte] using pair.1
    have suffix : z.drop (p + (t + 2)) = pairEncode u v := by
      rw [show p + (t + 2) = (p + t) + 2 by omega, ← List.drop_drop, hz']
      rfl
    have tail := ih (t + 2) suffix (by simp only [List.length_cons] at length_bound; omega)
    have duration : 2 * (b :: u).length + 2 = 2 + (2 * u.length + 2) := by
      simp only [List.length_cons]
      omega
    constructor
    · calc
        _ = (headerScanTM i).runFrom (headerScanCfg i d 0 t (by omega))
            (2 + (2 * u.length + 2)) := congrArg _ duration
        _ = headerScanCfg i d 3 (t + 2 + (2 * u.length + 2)) (by omega) := by
          rw [MultiTapeTM.runFrom_add, hpair, tail.1]
        _ = _ := by congr 1; omega
    · intro r hr
      by_cases hsmall : r < 2
      · exact pair.2 r hsmall
      · have hr' : r - 2 < 2 * u.length + 2 := by omega
        rw [show r = 2 + (r - 2) by omega, MultiTapeTM.runFrom_add, hpair]
        exact tail.2 (r - 2) hr'

/-- **The header scan's contract, from any input offset**: let `d` be at control `0` with its
input head at cell `1 + p` of `z`, where `z.drop p = pairEncode u v`. Then
`Turing.headerScanTM i` run from `d` is after exactly `2|u| + 2` steps at
`Turing.headerScanCfg i d 3 (2|u| + 2)` (the header's cells read and the same number of cells
`true` on tape `i` from its head, both heads just past them), it does not reach the control `3`
earlier, and its output is `d`'s throughout. The painted interval overwrites its old contents and
every cell outside it is preserved, so consecutive scans write one ruler for consecutive headers
(`Turing.headerScanCfg_ruler`). [AB09, §1.4.1, the proof of Theorem 1.9; the pair encoding of
[AB09, §1.4]]

**Proof sketch.** Instantiate the header induction at time zero. The endpoint has
the original output; output-prefix monotonicity in both directions gives silence
at every intermediate time. -/
theorem headerScanTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v) :
    let hlen : d.inputPos.val + (2 * u.length + 2) < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    (headerScanTM i).runFrom d (2 * u.length + 2) =
        headerScanCfg i d 3 (2 * u.length + 2) hlen ∧
      (∀ t < 2 * u.length + 2, ((headerScanTM i).runFrom d t).state ≠ some 3) ∧
      (∀ t ≤ 2 * u.length + 2, ((headerScanTM i).runFrom d t).output = d.output) := by
  have hz' : z.drop (p + 0) = pairEncode u v := by simpa only [Nat.add_zero] using hz
  have h := up_scan_header i d p hp u v 0 hz'
  simp only [Nat.zero_add, up_scan_zero i d hd] at h
  refine ⟨h.1, h.2, ?_⟩
  intro t ht
  have hle := MultiTapeTM.output_prefix (headerScanTM i) d ht
  have hge := MultiTapeTM.output_prefix (headerScanTM i) d (Nat.zero_le t)
  rw [h.1] at hle
  rw [MultiTapeTM.runFrom_zero] at hge
  exact hle.eq_of_length_le hge.length_le

/-- **The header scan extends a ruler**: if tape `i` of `d` holds exactly the ruler `true^m`
ending just before its head (cells `[pos - m, pos)` `true`, every other cell blank, `pos` the
head), then in `Turing.headerScanCfg i d q t` it holds exactly `true^(m + t)` from the same
first cell `pos - m`: as a unary buffer, `bufferTape (true^(m + t))` read from `pos - m`.
[AB09, §1.4.1]

*Generalization.* The private form assumed a blank tape `i` and read the buffer from `pos`; that
is the case `m = 0` (the hypothesis then says the tape is blank, since `bufferTape [] = none`, and
the conclusion is the old one up to `Nat.cast_zero`, `sub_zero` and `zero_add`). For two
consecutive headers of lengths `ℓ₁` and `ℓ₂` the first scan's conclusion (`m = 0`) is the second
scan's hypothesis at `m = ℓ₁`, because the head has moved to `pos + ℓ₁`; the two give
`true^(ℓ₁ + ℓ₂)`.

**Proof sketch.** Read both buffers through their public equation and the scanned tape through
its field equation. A cell in the painted interval is offset `m ≤ a < m + t` from the ruler's
start, hence inside the longer ruler. Any other cell keeps its old value: inside the old ruler
(`0 ≤ a < m`) it is `true` in both rulers, and outside both rulers it is blank. -/
theorem headerScanCfg_ruler {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (m : ℕ)
    (hpre : ∀ a : ℤ, d.workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate m true) a) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i - (m : ℤ) + a) =
      FinTM.bufferTape (List.replicate (m + t) true) a := by
  intro a
  have h := hpre a
  simp only [headerScanCfg_workTapes, Function.update_self]
  rw [FinTM.bufferTape_eq] at h ⊢
  by_cases hin : d.workTapePos i ≤ d.workTapePos i - (m : ℤ) + a ∧
      d.workTapePos i - (m : ℤ) + a < d.workTapePos i + t
  · rw [if_pos hin, if_pos (show 0 ≤ a by omega), List.getElem?_replicate,
      if_pos (show a.toNat < m + t by omega)]
  · rw [if_neg hin, h]
    by_cases ha : 0 ≤ a
    · rw [if_pos ha, if_pos ha, List.getElem?_replicate, List.getElem?_replicate]
      by_cases ham : a < m
      · rw [if_pos (show a.toNat < m by omega), if_pos (show a.toNat < m + t by omega)]
      · rw [if_neg (show ¬a.toNat < m by omega), if_neg (show ¬a.toNat < m + t by omega)]
    · rw [if_neg ha, if_neg ha]

/-- On an initially blank ruler tape, the marked interval is the standard unary buffer: the
case `m = 0` of `Turing.headerScanCfg_ruler`. -/
private theorem up_scan_ruler_blank {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (q : Fin 4) (t : ℕ)
    (ht : d.inputPos.val + t < z.length + 2) (hblank : ∀ a, d.workTapes i a = none) :
    ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i + a) =
      FinTM.bufferTape (List.replicate t true) a := by
  intro a
  have h := headerScanCfg_ruler i d q t ht 0 (fun b => by
    rw [hblank, List.replicate_zero, FinTM.bufferTape_eq, List.getElem?_nil, ite_self]) a
  simpa only [Nat.cast_zero, sub_zero, Nat.zero_add] using h

/-- **The header ruler machine**: `Turing.headerScanTM i` followed, at its exit `3`, by the
work-tape rewind `Turing.rewindTM k i` of tape `i` (`Turing.seamCompTM`), started at the scan's
control `0`. It reads one doubled header and leaves the ruler `true^(2|u| + 2)` on tape `i` with
that head back at the ruler's first cell. Read through `Turing.headerRulerTM_run`. [AB09,
§1.4.1] -/
def headerRulerTM {k : ℕ} (i : Fin k) :
    MultiTapeTM k Bool (Fin 4 ⊕ RewindPhase) :=
  { seamCompTM (headerScanTM i) 3 (rewindTM k i) .start with q₀ := Sum.inl 0 }

/-- **The header ruler's contract**: let `d` be at control `0` with its input head at cell
`1 + p` of `z`, where `z.drop p = pairEncode u v`, and tape `i` blank. With `ℓ = 2|u| + 2`,
`Turing.headerRulerTM i` run from `d` (control relabelled by `Sum.inl`) is after exactly
`2ℓ + 3` steps at the rewind's `done`, with the input head `ℓ` cells further, tape `i` holding the
ruler `true^ℓ` from its head's original cell, every head (that of tape `i` included) and every
other tape as in `d`, and `d`'s output; and it does not reach `done` earlier. [AB09, §1.4.1]

**Proof sketch.** The scan writes the unary buffer and ends immediately after it.
Its buffer equation supplies the framed rewind's hypothesis. The public seam
combines their exact runs and first-return cuts; its endpoint resets just the
ruler head, which restores the original vector of heads. -/
theorem headerRulerTM_run {k : ℕ} {z : List Bool} (i : Fin k)
    (d : Cfg k Bool (Fin 4) z) (p : ℕ) (hp : d.inputPos.val = 1 + p)
    (hd : d.state = some 0) (u v : List Bool) (hz : z.drop p = pairEncode u v)
    (hblank : ∀ a, d.workTapes i a = none) :
    let ℓ := 2 * u.length + 2
    let hlen : d.inputPos.val + ℓ < z.length + 2 := by
      have h := congrArg List.length hz
      rw [List.length_drop, length_pairEncode] at h
      omega
    let e : Cfg k Bool (Fin 4 ⊕ RewindPhase) z :=
      ⟨some (Sum.inr .done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩
    (headerRulerTM i).runFrom (d.mapState Sum.inl) (2 * ℓ + 3) = e ∧
      (∀ t < 2 * ℓ + 3,
        ((headerRulerTM i).runFrom (d.mapState Sum.inl) t).state ≠ some (Sum.inr .done)) := by
  dsimp only
  let ℓ := 2 * u.length + 2
  have hlen : d.inputPos.val + ℓ < z.length + 2 := by
    have h := congrArg List.length hz
    rw [List.length_drop, length_pairEncode] at h
    dsimp only [ℓ]; omega
  let c := headerScanCfg i d 3 ℓ hlen
  obtain ⟨hscan, hcut, _⟩ := headerScanTM_run i d p hp hd u v hz
  have hrewind := rewindTM_run_ofCfg i (List.replicate ℓ true) ℓ
    (by rw [List.length_replicate]) (c.mapState fun _ => RewindPhase.start)
    (by rw [Cfg.mapState_state]; rfl) (by
      intro a _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank a
      simpa only [c, headerScanCfg, Function.update_self, add_sub_cancel_right] using hh)
  let r : Cfg k Bool RewindPhase z :=
    { c.mapState (fun _ => RewindPhase.start) with
      state := some .done
      workTapePos := Function.update (c.mapState (fun _ => RewindPhase.start)).workTapePos i
        ((c.mapState (fun _ => RewindPhase.start)).workTapePos i - ℓ) }
  have endpoint : r.mapState Sum.inr =
      (⟨some (Sum.inr RewindPhase.done), ⟨d.inputPos.val + ℓ, hlen⟩,
        Function.update d.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - d.workTapePos i)),
        d.workTapePos, d.output⟩ : Cfg k Bool (Fin 4 ⊕ RewindPhase) z) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
    · funext j a
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      by_cases hj : j = i
      · subst j
        have hh := up_scan_ruler_blank i d 3 ℓ hlen hblank (a - d.workTapePos i)
        simpa only [add_sub_cancel, Function.update_self] using hh
      · simp only [c, headerScanCfg, Function.update_of_ne hj]
    · funext j
      rw [Cfg.mapState_workTapePos]
      by_cases hj : j = i
      · subst j
        simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg,
          Function.update_self, add_sub_cancel_right]
      · simp only [r, c, Cfg.mapState_workTapePos, headerScanCfg, Function.update_of_ne hj]
    · rw [Cfg.mapState_output, Cfg.mapState_output]; rfl
  have total : 2 * ℓ + 3 = ℓ + 1 + (ℓ + 2) := by omega
  constructor
  · rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀, total]
    exact (seamCompTM_run_ofCfg (headerScanTM i) 3 (rewindTM k i) .start
      hscan rfl hcut hrewind.1).trans endpoint
  · intro t ht
    rw [headerRulerTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg (headerScanTM i) 3 (rewindTM k i) .start .done
      hscan rfl hcut hrewind.1 rfl hrewind.2.1 t (by omega)

/-! ## The suffix-ruler layout -/

/-- **The suffix-ruler seam layout**: on `K + (k + 3)` work tapes over the input `z`, the
configuration at control `q` with the input head at cell `ℓ + 1` (just past a header of length
`ℓ`), the table bits `tableBitsK M.tr` on tape `k`, the unary initial state `unaryFin M.q₀` from
cell `2` on tape `k + 1`, the ruler `true^ℓ` on tape `k + 2`, every other tape blank, every head
at `0` and an empty output. It is where a startup and header scans leave the machine before the
ruler host runs the forwarding loop on the suffix `z.drop ℓ` (`Turing.suffixRulerCfg_embed`).
[AB09, §1.4.1, the proof of Theorem 1.9] -/
def suffixRulerCfg {k K n : ℕ} {P : Type} (q : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (z : List Bool) (ℓ : ℕ)
    (hℓ : ℓ + 1 < z.length + 2) : Cfg (K + (k + 3)) Bool P z :=
  ⟨some q, ⟨ℓ + 1, hℓ⟩,
    fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
      else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
      else if j.val = k + 2 then FinTM.bufferTape (List.replicate ℓ true)
      else fun _ => none,
    fun _ => 0, []⟩

/-! The suffix-ruler layout's fields as equations, generated by `simps` without the `simp`
attribute: `Turing.suffixRulerCfg_state`, `_inputPos`, `_workTapes` (pointwise in the tape and the
cell), `_workTapePos` and `_output`. -/
attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
  suffixRulerCfg

/-- **The ruler host's presentation, its fields**: in `Turing.rulerHostCfg ℓ hz q c rt rp` the
physical input head is at `ℓ` plus `c`'s, the last tape is the ruler `rt` with its head at `rp`,
the first `m` tapes are `c`'s, and the output is `c`'s. [AB09, §1.2, Exercise 4.1: a machine run
on a suffix of its input] -/
theorem rulerHostCfg_fields {m : ℕ} {S Q : Type} {y z : List Bool} (ℓ : ℕ)
    (hz : z.length = ℓ + y.length) (q : Option Q) (c : Cfg m Bool S y) (rt : ℤ → Option Bool)
    (rp : ℤ) :
    (rulerHostCfg ℓ hz q c rt rp).inputPos.val = ℓ + c.inputPos.val ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapes (Fin.last m) = rt ∧
      (rulerHostCfg ℓ hz q c rt rp).workTapePos (Fin.last m) = rp ∧
      (∀ i : Fin m, (rulerHostCfg ℓ hz q c rt rp).workTapes i.castSucc = c.workTapes i) ∧
      (rulerHostCfg ℓ hz q c rt rp).output = c.output := by
  refine ⟨by rw [rulerHostCfg_inputPos], ?_, ?_, fun i => ?_, rulerHostCfg_output _ _ _ _ _ _⟩
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_last]
  · rw [rulerHostCfg_workTapePos, Fin.lastCases_last]
  · funext a
    rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc]

/-- **The suffix-ruler layout is the embedded ruler-host start**: let `z` have length
`ℓ + |x|`. Present H2-F's encoding `c` of `M`'s initial configuration on the suffix `x` through
the ruler host's layout `Turing.rulerHostCfg` (control `inj q false` for `c`'s control `q`, the
ruler `true^ℓ` with its head at `0`) and embed it in the first `k + 3` of `K + (k + 3)` tapes (the
others blank with their heads at `0`, no prior output). The result is
`Turing.suffixRulerCfg exit M z ℓ` with its control relabelled to `inj entry false`. So it is the
seam hypothesis of `Turing.startupLoopTM_runFrom` and `Turing.startupLoopTM_spaceUsed_le` at
`(K, k + 1)` for a startup ending at the suffix-ruler layout. [AB09, §1.4.1, the proof of
Theorem 1.9]

**Proof sketch.** Reconstruct the embedding from its public field equations. Its
first bank is the initial forwarding-loop encoding, its last tape is the ruler,
and all unselected tapes are blank. The encoded input head is one, so the
physical head is exactly one cell after the header and its virtual-zero tag is false. -/
theorem suffixRulerCfg_embed {k K n : ℕ} {P Q H : Type} {x z : List Bool}
    (exit : P) (entry : Q) (inj : Q → Bool → H) (M : MultiTapeTM k Bool (Fin (n + 1)))
    (ℓ : ℕ) (hz : z.length = ℓ + x.length) (hlen : ℓ + 1 < z.length + 2) :
    let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
    embedEmitCfg (Fin.castLEEmb (by omega : k + 3 ≤ K + (k + 3)))
      (fun _ _ => none) (fun _ => 0) []
      (rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c
        (FinTM.bufferTape (List.replicate ℓ true)) 0) =
      (suffixRulerCfg (K := K) exit M z ℓ hlen).mapState (fun _ => inj entry false) := by
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  have fields := StepBlock.forwardLoopCfg_init_fields entry M x
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  have host := rulerHostCfg_fields ℓ hz (c.state.map fun q => inj q false) c rt 0
  apply embedEmitCfg_eq
  · rw [rulerHostCfg_state, fields.1, Option.map_some, Cfg.mapState_state]
    rfl
  · apply Fin.ext
    rw [host.1, Cfg.mapState_inputPos]
    change ℓ + c.inputPos.val = ℓ + 1
    rw [fields.2.1]
  · rw [List.nil_append, rulerHostCfg_output, fields.2.2.2, Cfg.mapState_output]
    rfl
  · intro j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_last, Cfg.mapState_workTapes]
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.val_last,
          if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_last, Cfg.mapState_workTapePos]
        rfl
    · constructor
      · funext b
        rw [rulerHostCfg_workTapes, Fin.lastCases_castSucc, Cfg.mapState_workTapes,
          StepBlock.forwardLoopCfg_init_workTapes]
        have ha : a.val ≠ k + 2 := by omega
        simp only [suffixRulerCfg, Fin.coe_castLEEmb, Fin.coe_castLE, Fin.coe_castSucc, if_neg ha]
      · rw [rulerHostCfg_workTapePos, Fin.lastCases_castSucc, Cfg.mapState_workTapePos,
          fields.2.2.1 a]
        rfl
  · intro j hj
    have hjge : k + 3 ≤ j.val := by
      by_contra h
      apply hj
      refine ⟨⟨j.val, by omega⟩, ?_⟩
      apply Fin.ext; rfl
    constructor
    · funext a
      rw [Cfg.mapState_workTapes]
      simp only [suffixRulerCfg, if_neg (by omega : j.val ≠ k),
        if_neg (by omega : j.val ≠ k + 1), if_neg (by omega : j.val ≠ k + 2)]
    · rw [Cfg.mapState_workTapePos]
      rfl
end Turing
```

## ===== TCSlib/Complexity/TuringMachine/UniversalK.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.UniversalParts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `k`-generic universal machine (U2)

[AB09, §1.4.1 and Theorem 1.9]: one universal machine for codes of `k`-work-tape binary
machines, for every `k`, with an overhead linear in the simulated time and a constant depending
on the code only. At `k = 2` it is the two-tape universal machine of the time hierarchy at
`f log f` (plan §2.1; the Hennie–Stearns conversion of [AB09, §1.7] lands machines there); at
`k = 1` it is the self-application universal `U₀` of the space hierarchy
(`Turing.exists_selfUniversal`, its `k = 1` corollary) and the code-first evaluator of
`Turing.universal` (the U-1 re-derivation, deferred). Design: `audits/evidence/u2/U2-design.md`;
the user's decisions of 2026-10-14 (`backlog.md` RD-5).

**Status.** Proved: the scheme interface and its two instances, the startup
`Turing.exists_selfStartupTMK`, and both machine contracts. They are built on the step block's
forwarding round loop `Turing.StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward.lean`)
and, for the code-first evaluator, on the ruler host `Turing.exists_rulerHostTM`
(`Build/InputDevice.lean`). The parts both contracts are assembled from (the startup–loop seam
`Turing.startupLoopTM` and its ledgers, the forwarding loop's readings at an initial
configuration, the header ruler `Turing.headerRulerTM` and the suffix-ruler layout
`Turing.suffixRulerCfg`) are public in `Build/UniversalParts.lean`, harvested from this file's
privates for their second consumer (the U2 harvest, user ruling of 2026-11-06).

## Design

* **One construction, generic in `k`.** The step block `Turing.StepBlock.roundTM k` simulates one
  transition of any `k`-tape table held as data at a cost `≤ 50 · (|table| + 1)`, a constant for
  a fixed code; H2-F forwards the emissions. Nothing here is specific to one or two work tapes.
* **The scheme interface** `Turing.EffectiveCodeK k`: a total decoding into `k`-tape machines and
  a canonizer computing the fixed serialization `Turing.serializeK` in arbitrary time. The
  received one-tape scheme and the Z3 two-tape scheme are instances. No uniformity is assumed:
  per-code constants absorb the canonizer's time.
* **Two input layouts.** Self-application (`Turing.exists_selfUniversalK`): on `pairEncode α w`
  the coded machine runs on that same input, through the native device, with no copy and no
  position counter. Code first (`Turing.universalK`): on `pairEncode α x` it runs on `x`,
  through H5's bounded-prefix ruler device, at a constant cost per step for a fixed code.
* **Both directions** in both layouts: forward time (and, for self-application, space) ledgers,
  and the converse that every completed output of the universal machine is one of the coded
  machine's.

## Main definitions

* `Turing.EffectiveCodeK`, `Turing.EffectiveCodeK.toFinTM` — the `k`-tape scheme interface;
  `Turing.EffectiveCodeK.ofSerialize` — its constructor from a scheme with its own serialization.
* `Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK` — the received one- and
  two-tape schemes as `k`-tape schemes.

## Main results

* `Turing.EffectiveMachineCode.toK_toFinTM`, `Turing.EffectiveMachineCode2.toK_toFinTM`,
  `Turing.EffectiveMachineCode.toK_machine`, `Turing.EffectiveMachineCode2.toK_machine` — the
  decoded machines agree, by definition.
* `Turing.exists_selfStartupTMK` — the startup, ending at the step block's seam (proved).
* `Turing.exists_selfUniversalK` — the self-application universal machine, with time
  `C · (t + 1)`, space `C · (s + 1)` and the converse (proved).
* `Turing.universalK` — the code-first evaluator with time `C · (t + 1)` and the converse
  (proved).

Their assembly cites `Build/UniversalParts.lean`: `Turing.startupLoopTM_runFrom`,
`_live_of_le` and `_spaceUsed_le`; `Turing.StepBlock.forwardLoop_forward` and `_converse`;
`Turing.embedEmitCfg_forwardLoop_init`; `Turing.headerRulerTM_run`; `Turing.suffixRulerCfg_embed`
and `Turing.MultiTapeTM.initCfg_eq_mapState`. The code-first evaluator's own startup composition
(the startup embedded with one more tape, then the header ruler) stays private here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, machine codes; §1.4.1, Theorem 1.9 and its proof:
  the universal machine simulates one step of `M` in a number of steps depending only on `M`'s
  table; §1.7, the two-tape simulation; Exercise 4.1, the space-bounded universal machine.)
-/

namespace Turing

/-! ## The `k`-tape scheme interface -/

/-- **An effective scheme for `k`-work-tape codes** [AB09, §1.4]: a total decoding of every
string `α` into a `k`-work-tape binary machine `machine α` with state space
`Fin (numStates α + 1)`, together with a machine of this development, the canonizer, that
computes from `α` the fixed `k`-record serialization `Turing.serializeK (machine α)` within an
arbitrary time bound `canonizerTime`. As for `Turing.EffectiveMachineCode` (Argument A), the
canonizer targets the fixed, scheme-independent serialization, and its time bound is arbitrary:
fixed-code consumers absorb it into their constants. The received schemes are instances
(`Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK`). -/
structure EffectiveCodeK (k : ℕ) where
  /-- one less than the number of states of the machine a string denotes -/
  numStates : List Bool → ℕ
  /-- the machine a string denotes -/
  machine : (α : List Bool) → MultiTapeTM k Bool (Fin (numStates α + 1))
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serializeK ∘ machine` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => serializeK (machine α)) canonizerTime

/-- The bundled machine a string denotes in a `k`-tape scheme: `k` work tapes, the states
`Fin (numStates α + 1)`, the decoded machine. -/
def EffectiveCodeK.toFinTM {k : ℕ} (E : EffectiveCodeK k) (α : List Bool) : FinTM Bool where
  k := k
  State := Fin (E.numStates α + 1)
  tm := E.machine α

/-- **A `k`-tape scheme from a scheme with its own serialization** (the common constructor of
the two instances below): given a type of coded machines with their state counts and their
`k`-tape machines, a serialization equal to `serializeK` of the machine, a decoding, and a
canonizer computing the serialization of the decoded machine, the `k`-tape scheme with the same
decoding and canonizer. -/
def EffectiveCodeK.ofSerialize {k : ℕ} {Code : Type} (numStates : Code → ℕ)
    (tm : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))) (serialize : Code → List Bool)
    (serialize_eq : ∀ M, serialize M = serializeK (tm M)) (decode : List Bool → Code)
    (canonizer : FinTM Bool) (canonizerTime : ℕ → ℕ)
    (h : canonizer.ComputesFunInTime (fun α => serialize (decode α)) canonizerTime) :
    EffectiveCodeK k where
  numStates α := numStates (decode α)
  machine α := tm (decode α)
  canonizer := canonizer
  canonizerTime := canonizerTime
  canonizer_computes := by
    have e : (fun α => serialize (decode α)) = fun α => serializeK (tm (decode α)) :=
      funext fun α => serialize_eq (decode α)
    exact e ▸ h

/-- **The received one-tape scheme as a `k`-tape scheme** (`k = 1`): the same decoding and the
same canonizer, whose target `CodeTM.serialize` is `serializeK` at one work tape
(`Turing.oneTapeMachineFormat.serialize_eq`). [AB09, §1.4] -/
def EffectiveMachineCode.toK (c : EffectiveMachineCode) : EffectiveCodeK 1 :=
  EffectiveCodeK.ofSerialize CodeTM.numStates CodeTM.tm CodeTM.serialize
    oneTapeMachineFormat.serialize_eq c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- **The Z3 two-tape scheme as a `k`-tape scheme** (`k = 2`): the same decoding and the same
canonizer, whose target `Code2TM.serialize` is `serializeK` at two work tapes
(`Turing.Code2TM.serialize_eq_serializeK`). [AB09, §1.4] -/
def EffectiveMachineCode2.toK (c : EffectiveMachineCode2) : EffectiveCodeK 2 :=
  EffectiveCodeK.ofSerialize Code2TM.numStates Code2TM.tm Code2TM.serialize
    Code2TM.serialize_eq_serializeK c.decode c.canonizer c.canonizerTime c.canonizer_computes

/-- The one-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode.toK_toFinTM (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The two-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode2.toK_toFinTM (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := rfl

/-- The one-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode.toK_machine (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-- The two-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode2.toK_machine (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := rfl

/-! ## U2-S: the startup -/

/-- The canonizer, with the public cleanup machine restarted in its cleaning state. -/
private def ss_cleanCanonizer (F : FinTM Bool) : FinTM Bool where
  k := F.k + F.k
  State := Complexity.LogProg.CleanSt F.State F.k
  tm := { Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ }

/-- The bundled cleanup run is the run from the public cleaning entry. -/
private theorem ss_cleanCanonizer_run (F : FinTM Bool) (α : List Bool) (t : ℕ) :
    (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t =
      (Complexity.LogProg.cleanTM F.tm F.tm.q₀).runFrom
        (Cfg.init (.init F.tm.q₀) α) t := by
  change ({ Complexity.LogProg.cleanTM F.tm F.tm.q₀ with q₀ := .init F.tm.q₀ } :
    MultiTapeTM (F.k + F.k) Bool (Complexity.LogProg.CleanSt F.State F.k)).runFrom _ _ = _
  rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]

/-- Cleanup preserves a completed computation and blanks every work tape.

**Proof sketch.** Bound the original run's visited set on each tape by their finite
maximum. Apply the public cleanup theorem, then use the restart equations. -/
private theorem ss_cleanCanonizer_halts (F : FinTM Bool) (α out : List Bool) (t : ℕ)
    (h : F.ComputesInTime α out t) :
    ∃ u, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).output =
        out ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) u).workTapePos =
        (fun _ => 0) := by
  classical
  have hc := (FinTM.computesInTime_iff F α out t).mp h
  rw [MultiTapeTM.initCfg_eq] at hc
  let s := Finset.univ.sup fun i : Fin F.k =>
    (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t i).card
  obtain ⟨u, hu, hout, hblank, hpos, _⟩ :=
    Complexity.LogProg.cleanTM_run F.tm F.tm.q₀ F.tm.q₀ α t hc.1 s
      (fun i => Finset.le_sup
        (f := fun j : Fin F.k => (F.tm.visitedByTapeHead (Cfg.init F.tm.q₀ α) t j).card)
        (Finset.mem_univ i))
  refine ⟨u, ?_⟩
  simpa only [ss_cleanCanonizer_run] using ⟨hu, hout.trans hc.2, hblank, hpos⟩

/-- A string-dependent time is bounded by a function of string length. -/
private theorem ss_lengthBound (time : List Bool → ℕ) :
    ∃ bound : ℕ → ℕ, ∀ α, time α ≤ bound α.length := by
  classical
  refine ⟨fun n => Finset.univ.sup (fun f : Fin n → Bool => time (List.ofFn f)), ?_⟩
  intro α
  simpa only [List.ofFn_get] using
    (Finset.le_sup (f := fun f : Fin α.length → Bool => time (List.ofFn f))
      (Finset.mem_univ α.get))

/-- A total canonizer remains total after cleanup, at a bound depending only on length;
the same bound leaves every work tape blank and every work head at zero.

**Proof sketch.** Choose each input's cleaned halting time and take a finite maximum
at each input length. Absorbing halting preserves the output and cleanup at the maximum. -/
private theorem ss_cleanCanonizer_computes (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) :
    ∃ bound, (ss_cleanCanonizer F).ComputesFunInTime f bound ∧ ∀ α,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapes = (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
        (bound α.length)).workTapePos = (fun _ => 0) := by
  classical
  have hex := fun α => ss_cleanCanonizer_halts F α (f α) (τ α.length)
    ((FinTM.computesFunInTime_iff F f τ).mp hF α)
  choose time htime using hex
  obtain ⟨bound, hbound⟩ := ss_lengthBound time
  have hfreeze (α : List Bool) :
      (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (bound α.length) =
        (ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) (time α) := by
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (hbound α)
    calc
      _ = (ss_cleanCanonizer F).tm.runFrom
          ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α)
            (time α)) extra := by rw [heq, MultiTapeTM.runFrom_add]
      _ = _ := MultiTapeTM.runFrom_of_halt _ (htime α).1
  refine ⟨bound, (FinTM.computesFunInTime_iff _ _ _).mpr ?_, ?_⟩
  · intro α
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hfreeze α]
    exact ⟨(htime α).1, (htime α).2.1⟩
  · intro α
    rw [hfreeze α]
    exact (htime α).2.2

/-- A buffered second-phase configuration halts exactly when its source does. -/
private theorem ss_bufferedHalt_iff (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    (FinTM.bufferedSecondCfg M₁ M₂ c b p tapes heads).state = none ↔ c.state = none := by
  rw [FinTM.bufferedSecondCfg_state]
  simp only [FinTM.bufferedCompTM_State, Option.map_eq_none_iff]

/-- A first halt of the virtual canonizer is a first halt of the prefix canonizer,
after the fixed prefix phase, uniformly over all suffixes.

**Proof sketch.** The exact prefix formula identifies the state after the prefix phase.
Before that phase ends, absorbing halting and its live final state exclude a halt. -/
private theorem ss_prefix_first_halt (F : FinTM Bool) (α : List Bool) (t : ℕ)
    (hhalt : (F.tm.runFrom (F.tm.initCfg α) t).state = none)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg α) u).state ≠ none) (w : List Bool) :
    ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w))
      (3 * α.length + 4 + t)).state = none ∧
    ∀ u < 3 * α.length + 4 + t,
      ((prefixCanonTM F).tm.runFrom ((prefixCanonTM F).tm.initCfg (pairEncode α w)) u).state ≠
        none := by
  rw [prefixCanonTM_eq]
  constructor
  · obtain ⟨b, hb⟩ := prefixCanon_run F α w t
    simp only [prefixCanonTM_eq] at hb
    rw [hb, ss_bufferedHalt_iff]
    exact hhalt
  · intro u hu
    by_cases hpre : u < 3 * α.length + 4
    · have hs := prefixCanon_start F α w
      simp only [prefixCanonTM_eq] at hs
      have hstart :
          ((FinTM.bufferedCompTM universalPrefixTM F).tm.runFrom
            ((FinTM.bufferedCompTM universalPrefixTM F).tm.initCfg (pairEncode α w))
            (3 * α.length + 4)).state ≠ none := by
        intro h
        rw [hs, ss_bufferedHalt_iff, MultiTapeTM.initCfg_eq, Cfg.init_state] at h
        exact Option.some_ne_none F.tm.q₀ h
      exact MultiTapeTM.runFrom_state_ne_none_of_le _ _ _ hstart u (by omega)
    · obtain ⟨b, hb⟩ := prefixCanon_run F α w (u - (3 * α.length + 4))
      simp only [prefixCanonTM_eq] at hb
      rw [Nat.add_sub_of_le (by omega : 3 * α.length + 4 ≤ u)] at hb
      intro h
      rw [hb, ss_bufferedHalt_iff] at h
      exact hlive (u - (3 * α.length + 4)) (by omega) h

/-- The cleaned canonizer's first halt has the completed output and clean scratch.

**Proof sketch.** The public first-halt theorem identifies its configuration with the
one at the cleaned length bound, including all fields of that configuration. -/
private theorem ss_cleanCanonizer_first_halt (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) (α : List Bool) :
    ∃ t, ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).state =
        none ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧
      ∀ u < t, ((ss_cleanCanonizer F).tm.runFrom
        ((ss_cleanCanonizer F).tm.initCfg α) u).state ≠ none := by
  obtain ⟨bound, hfun, hclean⟩ := ss_cleanCanonizer_computes F f τ hF
  have hc := (FinTM.computesInTime_iff _ _ _ _).mp
    ((FinTM.computesFunInTime_iff _ _ _).mp hfun α)
  obtain ⟨t, _, hbefore, hsame⟩ := MultiTapeTM.exists_first_halt _ _ hc.1
  refine ⟨t, ?_, ?_, ?_, ?_, hbefore⟩
  · rw [hsame]
    exact hc.1
  · rw [hsame]
    exact hc.2
  · rw [hsame]
    exact (hclean α).1
  · rw [hsame]
    exact (hclean α).2

/-- Capturing a fresh run starts with blank host tapes and zero work heads.

**Proof sketch.** Partition host tapes into selected tapes, the capture tape, and the frame.
The selected tapes inherit the blank initial configuration; the empty captured output makes
its tape blank; the frame is blank by construction. Compare all configuration fields. -/
private theorem ss_captureInitial {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
    (ι : Fin m ↪ Fin n) (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) :
    (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
      (M.initCfg x)).mapState Sum.inl =
      Cfg.init (Sum.inl M.q₀ : S ⊕ Unit) x := by
  classical
  have hfields (j : Fin n) :
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapes j = (fun _ => none) ∧
      (embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
        (M.initCfg x)).workTapePos j = 0 := by
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_tape, embedSilentCfg_selected_pos,
        MultiTapeTM.initCfg_eq]
      exact ⟨funext fun z => Cfg.init_workTapes _ _ i z, Cfg.init_workTapePos _ _ i⟩
    · by_cases he : j = cap
      · subst j
        have hh := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x)
        simpa only [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append,
          FinTM.bufferTape_nil, List.length_nil, Nat.cast_zero] using hh
      · exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0)
          [] [] (M.initCfg x) j hj he
  apply Cfg.ext
  · rw [Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq,
      Cfg.init_state, Option.map_some, Cfg.init_state]
  · rw [Cfg.mapState_inputPos, embedSilentCfg_inputPos, MultiTapeTM.initCfg_eq,
      Cfg.init_inputPos, Cfg.init_inputPos]
  · funext j z
    rw [Cfg.mapState_workTapes, Cfg.init_workTapes, (hfields j).1]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, (hfields j).2]
  · rw [Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]

/-- The returning capture host, restarted in the source's initial state. -/
private def ss_captureTM (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n) (cap : Fin n) :
    MultiTapeTM n Bool (F.State ⊕ Unit) :=
  { embedSilentRetTM ι cap F.tm with q₀ := Sum.inl F.tm.q₀ }

/-- The returning capture reaches its anchor exactly at the source's first halt and
is silent throughout. Its final tapes are the public silent embedding's exact tapes.

**Proof sketch.** Identify the blank initial configuration, use the returning embedding's
through-halt contract, and project its output field before and at the return. -/
private theorem ss_capture_run (F : FinTM Bool) {n : ℕ} (ι : Fin F.k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (x : List Bool) (t : ℕ)
    (hlive : ∀ u < t, (F.tm.runFrom (F.tm.initCfg x) u).state ≠ none)
    (hhalt : (F.tm.runFrom (F.tm.initCfg x) t).state = none) :
    (ss_captureTM F ι cap).runFrom ((ss_captureTM F ι cap).initCfg x) t =
      { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
          (F.tm.runFrom (F.tm.initCfg x) t) with state := some (Sum.inr ()) } ∧
    (∀ u < t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).state ≠ some (Sum.inr ())) ∧
    (∀ u ≤ t, ((ss_captureTM F ι cap).runFrom
      ((ss_captureTM F ι cap).initCfg x) u).output = []) := by
  have hinit : (F.tm.initCfg x).state ≠ none := by
    rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hr := embedSilentRetTM_run ι cap hcap F.tm (fun _ _ => none) (fun _ => 0)
    [] [] (F.tm.initCfg x) t hinit hlive hhalt
  simp only [MultiTapeTM.initCfg_eq] at hr
  simp only [ss_captureTM, MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀,
    ← ss_captureInitial F.tm ι cap hcap x]
  refine ⟨hr.2.1, hr.2.2, ?_⟩
  intro u hu
  rcases lt_or_eq_of_le hu with hlt | rfl
  · rw [hr.1 u hlt, Cfg.mapState_output, embedSilentCfg_output]
  · simp only [hr.2.1, embedSilentCfg_output]

/-- With the prefix parser's empty left block, index zero is the buffer and every other
index belongs to the constant right block.

**Proof sketch.** Cast the composite index to the public block partition. Its value is either
zero, the buffer index, or one plus an index of the right block; apply the corresponding
published projection equation. -/
private theorem ss_tapeBlocks_zeroLeft {A : Type} (F : FinTM Bool)
    (left : Fin universalPrefixTM.k → A) (buffer right : A)
    (i : Fin (FinTM.bufferedCompTM universalPrefixTM F).k) :
    FinTM.tapeBlocks left buffer (fun _ : Fin F.k => right)
        (Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i) =
      if i.val = 0 then buffer else right := by
  have hp := universalPrefixTM_k
  have hk := FinTM.bufferedCompTM_k universalPrefixTM F
  have hi := i.isLt
  by_cases hz : i.val = 0
  · have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.castAdd F.k (0 : Fin 1)) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_zero]
      omega
    rw [he, FinTM.tapeBlocks_buffer, if_pos hz]
  · let j : Fin F.k := ⟨i.val - 1, by omega⟩
    have he : Fin.cast (FinTM.bufferedCompTM_k universalPrefixTM F) i =
        Fin.natAdd universalPrefixTM.k (Fin.natAdd 1 j) := by
      apply Fin.ext
      simp only [Fin.coe_cast, Fin.coe_natAdd]
      dsimp only [j]
      omega
    rw [he, FinTM.tapeBlocks_right, if_neg hz]

/-- After the canonizer's work tapes have been cleared, the prefix composite keeps only
the original code buffer, whose head is the virtual input position minus one.

**Proof sketch.** Read the exact prefix run through the published composite fields at its own
index type. The empty parser block leaves index zero for the code buffer; the cleaned right
block contributes blank tapes and zero heads. -/
private theorem ss_prefix_return_fields (F : FinTM Bool) (α w : List Bool) (t : ℕ)
    (hblank : (F.tm.runFrom (F.tm.initCfg α) t).workTapes = (fun _ _ => none))
    (hheads : (F.tm.runFrom (F.tm.initCfg α) t).workTapePos = (fun _ => 0)) :
    let c := F.tm.runFrom (F.tm.initCfg α) t
    let G := FinTM.bufferedCompTM universalPrefixTM F
    let d := G.tm.runFrom (G.tm.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
    d.inputPos.val = 2 * α.length + 3 ∧ d.output = c.output ∧
      (∀ i, d.workTapes i = if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      ∀ i, d.workTapePos i = if i.val = 0 then (c.inputPos.val : ℤ) - 1 else 0 := by
  dsimp only
  obtain ⟨b, hb⟩ := prefixCanon_run F α w t
  simp only [prefixCanonTM_eq] at hb
  rw [hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FinTM.bufferedSecondCfg_inputPos]
  · rw [FinTM.bufferedSecondCfg_output]
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapes_cast, hblank]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i
  · intro i
    rw [FinTM.bufferedSecondCfg_workTapePos_cast, hheads]
    exact ss_tapeBlocks_zeroLeft F _ _ _ i

/-- Capturing the cleaned prefix has a code-dependent first return, silence, and a
uniform space bound. The final configuration is expressed through the prefix run;
its cleaned source data are retained for the layout normalization below.

**Proof sketch.** Select the cleaned canonizer's first halt before quantifying the suffix.
The prefix first-halt lemma and the returning capture contract give the claimed run. -/
private theorem ss_capturedPrefix_run (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t : ℕ,
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).output =
        f α ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapes =
        (fun _ _ => none) ∧
      ((ss_cleanCanonizer F).tm.runFrom ((ss_cleanCanonizer F).tm.initCfg α) t).workTapePos =
        (fun _ => 0) ∧ ∀ w : List Bool,
      R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) =
        { embedSilentCfg ι cap (fun _ _ => none) (fun _ => 0) [] []
            (G.tm.runFrom (G.tm.initCfg (pairEncode α w))
              (3 * α.length + 4 + t)) with state := some (Sum.inr ()) } ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, ht, hout, hblank, hheads, hlive⟩ := ss_cleanCanonizer_first_halt F f τ hF α
  refine ⟨t, hout, hblank, hheads, fun w => ?_⟩
  have hp := ss_prefix_first_halt (ss_cleanCanonizer F) α t ht hlive w
  simp only [prefixCanonTM_eq] at hp
  have hr := ss_capture_run
    (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)) ι cap hcap
    (pairEncode α w) (3 * α.length + 4 + t) hp.2 hp.1
  exact ⟨hr.1, hr.2.1, hr.2.2, MultiTapeTM.spaceUsed_le_mul_succ _ _ _⟩

/-- The returned capture has exactly the code buffer, the captured result, and blank scratch.
Its code-buffer head is a code-dependent position between minus one and the code length.

**Proof sketch.** Retain the cleaned source's output and blankness at the first halt chosen
before the suffix. Project the exact captured return through the selected, capture, and frame
equations, and normalize the source fields with the cast-indexed composite equations. The
source input position determines the buffer head independently of the suffix. -/
private theorem ss_capturedPrefix_fields (F : FinTM Bool) (f : List Bool → List Bool)
    (τ : ℕ → ℕ) (hF : F.ComputesFunInTime f τ) {n : ℕ}
    (ι : Fin (FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).k ↪ Fin n)
    (cap : Fin n) (hcap : cap ∉ Set.range ι) (α : List Bool) :
    let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)
    let R := ss_captureTM G ι cap
    ∃ t p : ℕ, p ≤ α.length + 1 ∧ ∀ w : List Bool,
      let d := R.runFrom (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t)
      d.state = some (Sum.inr ()) ∧ d.inputPos.val = 2 * α.length + 3 ∧
      (∀ i, d.workTapes (ι i) =
        if i.val = 0 then FinTM.bufferTape α else (fun _ => none)) ∧
      (∀ i, d.workTapePos (ι i) = if i.val = 0 then (p : ℤ) - 1 else 0) ∧
      (d.workTapes cap = FinTM.bufferTape (f α) ∧ d.workTapePos cap = (f α).length) ∧
      (∀ j, j ∉ Set.range ι → j ≠ cap →
        d.workTapes j = (fun _ => none) ∧ d.workTapePos j = 0) ∧
      (∀ u < 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some (Sum.inr ())) ∧
      (∀ u ≤ 3 * α.length + 4 + t,
        (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
      R.spaceUsed (R.initCfg (pairEncode α w)) (3 * α.length + 4 + t) ≤
        n * (3 * α.length + 4 + t + 1) := by
  dsimp only
  obtain ⟨t, hout, hblank, hheads, hret⟩ := ss_capturedPrefix_run F f τ hF ι cap hcap α
  refine ⟨t, ((ss_cleanCanonizer F).tm.runFrom
    ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.val, ?_, fun w => ?_⟩
  · have h := ((ss_cleanCanonizer F).tm.runFrom
      ((ss_cleanCanonizer F).tm.initCfg α) t).inputPos.isLt
    omega
  · obtain ⟨hr, hcut, hsilent, hspace⟩ := hret w
    have hf := ss_prefix_return_fields (ss_cleanCanonizer F) α w t hblank hheads
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcut, hsilent, hspace⟩
    · rw [hr]
    · rw [hr]
      rw [embedSilentCfg_inputPos]
      exact hf.1
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_tape]
      exact hf.2.2.1 i
    · intro i
      rw [hr]
      rw [embedSilentCfg_selected_pos]
      exact hf.2.2.2 i
    · rw [hr]
      have hc := embedSilentCfg_cap ι cap hcap (fun _ _ => none) (fun _ => 0)
        [] [] ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.runFrom
          ((FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer F)).tm.initCfg
            (pairEncode α w)) (3 * α.length + 4 + t))
      simpa only [List.nil_append, hf.2.1, hout] using hc
    · intro j hj hjc
      rw [hr]
      exact embedSilentCfg_unselected ι cap (fun _ _ => none) (fun _ => 0) [] [] _ j hj hjc

/-- The public seam-layout machine redistributes a canonical serialization from its right
blank, at one time chosen before the input and the ambient configuration.

**Proof sketch.** Instantiate the layout contract with the state-count bits, unary initial
state, and transition table. The published serialization and unary-word equations identify
its source word and its two output words. -/
private theorem ss_serialized_layout (n : ℕ) (src tbl sm : Fin n)
    (hst : src ≠ tbl) (hss : src ≠ sm) (hts : tbl ≠ sm) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM n Bool Q)
      (entry done : Q) (C : ℕ),
      ∀ {k m : ℕ} (M : MultiTapeTM k Bool (Fin (m + 1))),
        ∃ T ≤ C * ((serializeK M).length + 1),
          ∀ {z : List Bool} (d : Cfg n Bool Q z),
            d.state = some entry →
            d.workTapes src = FinTM.bufferTape (serializeK M) →
            d.workTapePos src = (serializeK M).length →
            d.workTapes tbl = (fun _ => none) → d.workTapePos tbl = 0 →
            d.workTapes sm = (fun _ => none) → d.workTapePos sm = 0 →
            (L.runFrom d T).state = some done ∧
            (L.runFrom d T).inputPos = d.inputPos ∧
            (L.runFrom d T).workTapes =
              Function.update (Function.update (Function.update d.workTapes src
                (fun _ => none)) tbl (FinTM.bufferTape (tableBitsK M.tr)))
                sm (fun p => FinTM.bufferTape (unaryFin M.q₀) (p - 2)) ∧
            (L.runFrom d T).workTapePos =
              Function.update (Function.update (Function.update d.workTapePos src 0) tbl 0)
                sm 0 ∧
            (∀ u ≤ T, (L.runFrom d u).output = d.output) ∧
            ∀ u < T, (L.runFrom d u).state ≠ some done := by
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ := exists_seamLayoutTM n src tbl sm hst hss hts
  refine ⟨Q, hQ, hD, L, entry, done, C, ?_⟩
  intro k m M
  have hw := serializeK_eq M
  rw [unaryFin_eq] at hw
  have h := hL m.bits (tableBitsK M.tr) M.q₀.val (serializeK M).length (by rw [← hw])
  rw [← hw] at h
  simpa only [← unaryFin_eq M.q₀] using h

/-- A one-step move of the tested head when its cell is blank. The catalog rows do not
supply this conditional single step; it joins two skips and restores an empty buffer's head.
The action itself is the public one-tape action. -/
private def ss_bufferLeaf (n : ℕ) (i : Fin n) (emptyMove : SignType) :
    MultiTapeTM n Bool Bool where
  q₀ := false
  tr := fun _ _ work =>
    tapeAction i 0 none (if work i = none then emptyMove else 0)
      true

/-- The buffer leaf performs its conditional move in one silent step, with every other
tape and head fixed; its exit is absent before that step.

**Proof sketch.** Apply the public one-step tape-action equation. Before time one there is
only the entry configuration, whose false state is distinct from the true exit. -/
private theorem ss_bufferLeaf_run {n : ℕ} (i : Fin n) (emptyMove : SignType)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false) :
    (ss_bufferLeaf n i emptyMove).runFrom d 1 =
      { d with
        state := some true
        workTapePos := Function.update d.workTapePos i
          (d.workTapePos i + if d.workTapeSymbols i = none then (emptyMove : ℤ) else 0) } ∧
      ∀ u < 1, ((ss_bufferLeaf n i emptyMove).runFrom d u).state ≠ some true := by
  constructor
  · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have h := step_of_tapeAction_move (ss_bufferLeaf n i emptyMove) d i 0
      (if d.workTapeSymbols i = none then emptyMove else 0) hstate rfl
    simpa only [moveInputPos_zero, apply_ite, SignType.coe_zero] using h
  · intro u hu
    have hu0 : u = 0 := by omega
    rw [hu0, MultiTapeTM.runFrom_zero, hstate]
    simp only [ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- The first rightward skip starts at the source's virtual input position minus one.
At the left blank it moves to zero; at a nonnegative position it skips the remaining suffix.

**Proof sketch.** For virtual position zero, use the empty-word instance of the catalog
skip at the left blank. Otherwise, use the dropped suffix and the public buffer equation.
The catalog supplies both the framed endpoint and the first-return cut. -/
private theorem ss_bufferSkip_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    (skipTM n i).runFrom d (v.length + 1) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if p = 0 then 0 else (α.length : ℤ) + 1) } ∧
      ∀ u < v.length + 1, ((skipTM n i).runFrom d u).state ≠ some .done := by
  dsimp only
  have hw : ∀ q : ℤ, 0 ≤ q → q ≤
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) →
      d.workTapes i (d.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then [] else α.drop (p - 1)) q := by
    intro q hq hqv
    rw [hbuf, hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0]
      simp only [Int.zero_sub, add_zero, FinTM.bufferTape_left, FinTM.bufferTape_nil]
    · simp only [if_neg h] at hqv ⊢
      rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos hq,
        if_pos (by omega), List.getElem?_drop]
      congr 1
      omega
  obtain ⟨hr, hc, _⟩ := skipTM_run_ofCfg i _ d hstate hw
  have he : d.workTapePos i +
      ((if p = 0 then [] else α.drop (p - 1)).length : ℤ) + 1 =
      if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [hpos]
    by_cases h : p = 0
    · subst p
      simp only [ite_true, List.length_nil, Nat.cast_zero]
      omega
    · simp only [if_neg h, List.length_drop]
      omega
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- The second part of the rightward positioning pass: step left at a blank, then skip.
It is the existing seam constructor applied to the one-step leaf and the catalog skip. -/
private def ss_bufferAdvance (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (Bool ⊕ SeekPhase) :=
  seamCompTM (ss_bufferLeaf n i .neg) true (skipTM n i) .run

/-- After the first skip, the conditional left step and second skip reach one beyond the
right delimiter of a nonempty word. For the empty word they preserve the virtual position.

**Proof sketch.** Read blankness through the configuration and buffer equations. At position
zero of a nonempty word the leaf stays put and the skip crosses the word; otherwise the leaf
steps left and the empty-word skip steps right again. The public seam theorem supplies the
joined run and its first-return cut, preserving every ambient field. -/
private theorem ss_bufferAdvance_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool Bool z)
    (hstate : d.state = some false) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1) :
    let v := if p = 0 then α else []
    (ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) (v.length + 3) =
      ⟨some (Sum.inr .done), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + 3,
        ((ss_bufferAdvance n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  dsimp only
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (-1 : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i .neg d hstate
  change (ss_bufferLeaf n i .neg).runFrom d 1 = a at hr
  let b := a.mapState (fun _ => SeekPhase.run)
  have hba : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  have hbp : b.workTapePos i =
      if p = 0 then (if α = [] then -1 else 0) else (α.length : ℤ) := by
    rw [Cfg.mapState_workTapePos]
    dsimp only [a]
    rw [Function.update_self, Cfg.workTapeSymbols_eq, hbuf, hpos]
    by_cases h : p = 0
    · simp only [if_pos h]
      cases α with
      | nil => simp only [FinTM.bufferTape_nil, ite_true]; omega
      | cons x xs =>
        rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
        simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, List.cons_ne_nil,
          Nat.cast_zero, add_zero]
    · rw [if_neg h]
      have hn : FinTM.bufferTape α ((α.length : ℤ) + 1) = none := by
        rw [show (α.length : ℤ) + 1 = ((α.length + 1 : ℕ) : ℤ) by omega,
          FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
        omega
      rw [hn, if_pos rfl]
      omega
  have hw : ∀ q : ℤ, 0 ≤ q →
      q ≤ ((if p = 0 then α else []).length : ℤ) →
      b.workTapes i (b.workTapePos i + q) =
        FinTM.bufferTape (if p = 0 then α else []) q := by
    intro q hq hqv
    rw [hba, hbp]
    by_cases h : p = 0
    · simp only [if_pos h] at hqv ⊢
      by_cases ha : α = []
      · subst α
        simp only [FinTM.bufferTape_nil]
      · rw [if_neg ha, zero_add]
    · simp only [if_neg h, List.length_nil, Nat.cast_zero] at hqv ⊢
      have hq0 : q = 0 := by omega
      rw [hq0, add_zero, FinTM.bufferTape_nat, List.getElem?_eq_none (by omega),
        FinTM.bufferTape_nil]
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  obtain ⟨hs, hscut, _⟩ := skipTM_run_ofCfg i _ b hbstate hw
  have he : b.workTapePos i + ((if p = 0 then α else []).length : ℤ) + 1 =
      if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [hbp]
    by_cases h : p = 0
    · simp only [if_pos h]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero]
        omega
      · simp only [if_neg ha]
        omega
    · simp only [if_neg h, List.length_nil, Nat.cast_zero]
      by_cases ha : α = []
      · subst α
        simp only [ite_true, List.length_nil, Nat.cast_zero] at hp ⊢
        omega
      · simp only [if_neg ha, add_zero]
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i .neg) true (skipTM n i)
    .run .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + ((if p = 0 then α else []).length + 1) =
      (if p = 0 then α else []).length + 3 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, he]
    change Function.update b.workTapePos i _ j = _
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Position the code buffer for the backward catalog row, using three existing phases. -/
private def ss_bufferSeek (n : ℕ) (i : Fin n) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) :=
  seamCompTM (skipTM n i) .done (ss_bufferAdvance n i) (Sum.inl false)

/-- The two skips and their intervening conditional step find the right edge, with a time
that depends only on the code and its chosen virtual position.

**Proof sketch.** The first catalog skip has the dropped-suffix time. The proved advance
then has the whole-word or empty-word time. Compose their framed contracts by the general
seam equations and read the final head update through the state-map field equations. -/
private theorem ss_bufferSeek_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    (hp : p ≤ α.length + 1) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    (ss_bufferSeek n i).runFrom (d.mapState Sum.inl) (v.length + w.length + 5) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
        Function.update d.workTapePos i
          (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩ ∧
      ∀ u < v.length + w.length + 5,
        ((ss_bufferSeek n i).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSkip_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if p = 0 then 0 else (α.length : ℤ) + 1) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if p = 0 then 0 else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferAdvance_run i α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SeekPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipTM n i) .done (ss_bufferAdvance n i)
    (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length + 1 + 1 +
      ((if p = 0 then α else []).length + 3) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 5 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The backward catalog row restores the first cell of a nonempty buffer and the
original position of an empty buffer, preserving the full surrounding configuration.

**Proof sketch.** For a nonempty word the forward endpoint is one beyond its right blank,
so the catalog precondition is the buffer itself. For an empty word all cells are blank.
The resulting head formula is the catalog's subtraction of the word length and one. -/
private theorem ss_bufferBack_run {n : ℕ} (i : Fin n) (α : List Bool) (p : ℕ)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (skipBackTM n i).runFrom d (α.length + 3) =
      { d with
        state := some .done
        workTapePos := Function.update d.workTapePos i
          (if α = [] then (p : ℤ) - 1 else 0) } ∧
      ∀ u < α.length + 3, ((skipBackTM n i).runFrom d u).state ≠ some .done := by
  have he : d.workTapePos i - (α.length : ℤ) - 1 =
      if α = [] then (p : ℤ) - 1 else 0 := by
    rw [hpos]
    by_cases ha : α = []
    · subst α
      simp only [ite_true, List.length_nil, Nat.cast_zero, sub_zero]
    · simp only [if_neg ha]
      omega
  obtain ⟨hr, hc, _⟩ := skipBackTM_run_ofCfg i α d hstate (by
    intro q _ _
    rw [hbuf, he]
    by_cases ha : α = []
    · subst α
      simp only [FinTM.bufferTape_nil]
    · rw [if_neg ha, zero_add])
  rw [he] at hr
  exact ⟨hr, hc⟩

/-- Restore the empty word's origin if necessary, then clear through the catalog row.
The parameter is the virtual position chosen for the empty code, fixed for the machine. -/
private def ss_bufferClear (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (Bool ⊕ SweepPhase) :=
  seamCompTM (ss_bufferLeaf n i (if emptyPos = 0 then .pos else 0)) true
    (clearTM n i) .sweep

/-- The final buffer phases erase the code and put its head at zero. The empty code uses
its one fixed virtual position, so the machine does not depend on the input suffix.

**Proof sketch.** A nonempty buffer has a symbol at zero, so the leaf does not move. On an
empty buffer, the fixed position is zero or one and the conditional step restores zero.
The catalog clear then erases the word interval; outside that interval the public buffer
formula is already blank. Compose by the framed seam and its first-return theorem. -/
private theorem ss_bufferClear_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool Bool z) (hstate : d.state = some false)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) - 1 else 0) :
    (ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) (2 * α.length + 4) =
      ⟨some (Sum.inr .done), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 2 * α.length + 4,
        ((ss_bufferClear n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr .done) := by
  let mv : SignType := if emptyPos = 0 then .pos else 0
  let a : Cfg n Bool Bool z :=
    { d with
      state := some true
      workTapePos := Function.update d.workTapePos i
        (d.workTapePos i + if d.workTapeSymbols i = none then (mv : ℤ) else 0) }
  obtain ⟨hr, hc⟩ := ss_bufferLeaf_run i mv d hstate
  change (ss_bufferLeaf n i mv).runFrom d 1 = a at hr
  have haheads : a.workTapePos = Function.update d.workTapePos i 0 := by
    have hm : d.workTapePos i +
        (if d.workTapeSymbols i = none then (mv : ℤ) else 0) = 0 := by
      rw [Cfg.workTapeSymbols_eq, hbuf, hpos]
      by_cases ha : α = []
      · rw [if_pos ha, hp ha]
        subst α
        simp only [FinTM.bufferTape_nil, ite_true]
        by_cases h : emptyPos = 0
        · simp only [mv, if_pos h, SignType.pos_eq_one, SignType.coe_one, h, Nat.cast_zero]
          omega
        · have h1 : emptyPos = 1 := by omega
          simp only [mv, if_neg h, SignType.coe_zero, h1, Nat.cast_one]
          omega
      · rw [if_neg ha]
        cases α with
        | nil => exact False.elim (ha rfl)
        | cons x xs =>
          rw [show (0 : ℤ) = (0 : ℕ) by rfl, FinTM.bufferTape_nat]
          simp only [List.getElem?_cons_zero, reduceCtorEq, if_false, Nat.cast_zero,
            add_zero]
    dsimp only [a]
    rw [hm]
  let b := a.mapState (fun _ => SweepPhase.sweep)
  have hbstate : b.state = some .sweep := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = 0 := by
    rw [Cfg.mapState_workTapePos, haheads, Function.update_self]
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨hs, hscut, _⟩ := clearTM_run_ofCfg i α b hbstate (by
    intro q _ _
    rw [hbbuf, hbpos, zero_add])
  have hrun := seamCompTM_run_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep hr rfl hc hs
  have hcut := seamCompTM_firstReturn_ofCfg (ss_bufferLeaf n i mv) true (clearTM n i)
    .sweep .done hr rfl hc hs rfl hscut
  have ht : 1 + 1 + (2 * α.length + 2) = 2 * α.length + 4 := by omega
  rw [ht] at hrun hcut
  refine ⟨hrun.trans ?_, hcut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    by_cases hj : j = i
    · subst j
      simp only [hbpos, zero_add, Function.update_self, true_and]
      by_cases hq : 0 ≤ q ∧ q < (α.length : ℤ)
      · rw [if_pos hq]
      · rw [if_neg hq, hbbuf, FinTM.bufferTape_eq]
        by_cases hq0 : 0 ≤ q
        · rw [if_pos hq0, List.getElem?_eq_none (by omega)]
        · rw [if_neg hq0]
    · simp only [hj, false_and, if_false, Function.update_of_ne hj]
      rw [Cfg.mapState_workTapes]
  · funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, haheads]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Backward positioning followed by the fixed-origin clear, joined by the public seam. -/
private def ss_bufferFinish (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
  seamCompTM (skipBackTM n i) .done (ss_bufferClear n i emptyPos) (Sum.inl false)

/-- The backward pass and clear erase a buffer from the forward pass's endpoint.

**Proof sketch.** Apply the backward catalog specialization, then the proved fixed-origin
clear. The public seam transports their first-return cuts. Its state-map equations and
idempotence of a head update identify the framed endpoint. -/
private theorem ss_bufferFinish_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : α = [] → p = emptyPos)
    {z : List Bool} (d : Cfg n Bool SeekPhase z) (hstate : d.state = some .run)
    (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1) :
    (ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) (3 * α.length + 8) =
      ⟨some (Sum.inr (Sum.inr .done)), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < 3 * α.length + 8,
        ((ss_bufferFinish n i emptyPos).runFrom (d.mapState Sum.inl) u).state ≠
          some (Sum.inr (Sum.inr .done)) := by
  obtain ⟨hr, hc⟩ := ss_bufferBack_run i α p d hstate hbuf hpos
  let a : Cfg n Bool SeekPhase z :=
    { d with
      state := some .done
      workTapePos := Function.update d.workTapePos i
        (if α = [] then (p : ℤ) - 1 else 0) }
  let b := a.mapState (fun _ => false)
  have hbstate : b.state = some false := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) - 1 else 0 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferClear_run i emptyPos he α p hp b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : Bool → Bool ⊕ SweepPhase) =
      a.mapState (fun _ => Sum.inl false) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (skipBackTM n i) .done (ss_bufferClear n i emptyPos)
    (Sum.inl false) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (skipBackTM n i) .done
    (ss_bufferClear n i emptyPos) (Sum.inl false) (Sum.inr .done) hr rfl hc ha rfl hacut
  have ht : α.length + 3 + 1 + (2 * α.length + 4) = 3 * α.length + 8 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- Clear the captured code buffer from any of its possible virtual input positions.
All positioning and erasure phases are joined by existing seam constructors. -/
private def ss_bufferCleanup (n : ℕ) (i : Fin n) (emptyPos : ℕ) :
    MultiTapeTM n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) :=
  seamCompTM (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run)

/-- The complete code-buffer cleanup is uniform in the suffix and ambient configuration.
Its only fixed parameter is the virtual position assigned to the empty code.

**Proof sketch.** The forward sequence positions the head for the backward pass. The
backward and clear sequence restores zero and erases the buffer. Join the two proved
contracts with the general seam theorem; sum their code-dependent times. The inherited
first-return theorem makes the final right-tagged exit fresh until that time. -/
private theorem ss_bufferCleanup_run {n : ℕ} (i : Fin n) (emptyPos : ℕ)
    (he : emptyPos ≤ 1) (α : List Bool) (p : ℕ) (hp : p ≤ α.length + 1)
    (hpe : α = [] → p = emptyPos) {z : List Bool} (d : Cfg n Bool SeekPhase z)
    (hstate : d.state = some .run) (hbuf : d.workTapes i = FinTM.bufferTape α)
    (hpos : d.workTapePos i = (p : ℤ) - 1) :
    let v := if p = 0 then [] else α.drop (p - 1)
    let w := if p = 0 then α else []
    let T := v.length + w.length + 3 * α.length + 14
    (ss_bufferCleanup n i emptyPos).runFrom
      ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) T =
      ⟨some (Sum.inr (Sum.inr (Sum.inr .done))), d.inputPos,
        Function.update d.workTapes i (fun _ => none),
        Function.update d.workTapePos i 0, d.output⟩ ∧
      ∀ u < T, ((ss_bufferCleanup n i emptyPos).runFrom
        ((d.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
          Sum.inl) u).state ≠ some (Sum.inr (Sum.inr (Sum.inr .done))) := by
  dsimp only
  obtain ⟨hr, hc⟩ := ss_bufferSeek_run i α p hp d hstate hbuf hpos
  let a : Cfg n Bool (SeekPhase ⊕ (Bool ⊕ SeekPhase)) z :=
    ⟨some (Sum.inr (Sum.inr .done)), d.inputPos, d.workTapes,
      Function.update d.workTapePos i
        (if α = [] then (p : ℤ) else (α.length : ℤ) + 1), d.output⟩
  let b := a.mapState (fun _ => SeekPhase.run)
  have hbstate : b.state = some .run := by
    rw [Cfg.mapState_state]
    rfl
  have hbpos : b.workTapePos i = if α = [] then (p : ℤ) else (α.length : ℤ) + 1 := by
    rw [Cfg.mapState_workTapePos]
    exact Function.update_self _ _ _
  have hbbuf : b.workTapes i = FinTM.bufferTape α := by
    funext q
    rw [Cfg.mapState_workTapes]
    exact congrFun hbuf q
  obtain ⟨ha, hacut⟩ := ss_bufferFinish_run i emptyPos he α p hpe b hbstate hbbuf hbpos
  have hm : b.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SweepPhase)) =
      a.mapState (fun _ => Sum.inl .run) := by
    apply Cfg.ext
    · simp only [b, Cfg.mapState_state, a, Option.map_some]
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
  rw [hm] at ha hacut
  have hs := seamCompTM_run_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) hr rfl hc ha
  have hscut := seamCompTM_firstReturn_ofCfg (ss_bufferSeek n i) (Sum.inr (Sum.inr .done))
    (ss_bufferFinish n i emptyPos) (Sum.inl .run) (Sum.inr (Sum.inr .done))
    hr rfl hc ha rfl hacut
  have ht : (if p = 0 then [] else α.drop (p - 1)).length +
      (if p = 0 then α else []).length + 5 + 1 + (3 * α.length + 8) =
      (if p = 0 then [] else α.drop (p - 1)).length +
        (if p = 0 then α else []).length + 3 * α.length + 14 := by omega
  rw [ht] at hs hscut
  refine ⟨hs.trans ?_, hscut⟩
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Cfg.mapState_workTapes]
    have hbtapes : b.workTapes = d.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hbtapes]
  · funext j
    rw [Cfg.mapState_workTapePos]
    have hbheads : b.workTapePos = a.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hbheads]
    simp only [a, Function.update_idem]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- The native rewind has a separate pre-exit anchor so that the final exit is fresh. -/
private inductive ss_RewindState where
  | enter | scan | stop | done
  deriving DecidableEq, Fintype

/-- A native input-only leaf; its scan is handled by the published rewind contracts. -/
private def ss_inputRewind (n : ℕ) : MultiTapeTM n Bool ss_RewindState where
  q₀ := .enter
  tr := fun q inp _ => match q with
    | .enter => FinTM.controlAction .neg (some .scan)
    | .scan => match inp with
      | some _ => FinTM.controlAction .neg (some .scan)
      | none => FinTM.controlAction .pos (some .stop)
    | .stop => FinTM.controlAction 0 (some .done)
    | .done => FinTM.controlAction 0 (some .done)

/-- The final rewind anchor is stationary for every further time.

**Proof sketch.** Its own transition is a zero control action. Induction through the public
successor equation preserves the configuration; the control-action equation fixes its fields. -/
private theorem ss_inputRewind_done {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .done) (t : ℕ) :
    (ss_inputRewind n).runFrom d t = d := by
  have hs : (ss_inputRewind n).step d = d := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply d = d
    rw [FinTM.controlAction_apply, moveInputPos_zero]
    apply Cfg.ext
    · exact hd.symm
    · rfl
    · rfl
    · rfl
    · rfl
  induction t with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hs]

/-- The native input rewind returns at an exact position-dependent time, with a first exit
and fixed work heads throughout. Its time is independent of the input's suffix.

**Proof sketch.** One left step puts the input head within the word. The public scan equation
then reaches the pre-exit anchor after exactly the old position plus one steps. An earlier
final exit would be stationary and contradict that anchor. The public rewind-head theorem
has the same pre-exit time, since leaving that anchor enters the stationary final exit.
One final stationary step completes the run. -/
private theorem ss_inputRewind_run {n : ℕ} {z : List Bool}
    (d : Cfg n Bool ss_RewindState z) (hd : d.state = some .enter)
    (hp : 0 < d.inputPos.val) :
    (ss_inputRewind n).runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } ∧
      (∀ u < d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 2,
        ((ss_inputRewind n).runFrom d u).workTapePos = d.workTapePos := by
  let M := ss_inputRewind n
  let c : Cfg n Bool ss_RewindState z :=
    { d with state := some .scan, inputPos := moveInputPos d.inputPos .neg }
  have hstep : M.step d = c := by
    rw [MultiTapeTM.step_of_some hd]
    change (FinTM.controlAction .neg (some ss_RewindState.scan)).apply d = c
    rw [FinTM.controlAction_apply]
  have hcp : c.inputPos.val ≤ z.length := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    have := d.inputPos.isLt
    omega
  have hscan := FinTM.rewind_scan M .scan (some .stop)
    (fun inp _ => by cases inp <;> rfl) c rfl hcp
  have ht : 1 + (c.inputPos.val + 1) = d.inputPos.val + 1 := by
    dsimp only [c]
    rw [FinTM.moveInputPos_neg_val]
    omega
  have hstop : M.runFrom d (d.inputPos.val + 1) =
      { d with state := some .stop, inputPos := 1 } := by
    rw [← ht, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step' (cfg := d) (t := 0),
      MultiTapeTM.runFrom_zero, hstep, hscan]
  have hlast : ∀ (a : Cfg n Bool ss_RewindState z), a.state = some .stop →
      M.step a = { a with state := some .done } := by
    intro a ha
    rw [MultiTapeTM.step_of_some ha]
    change (FinTM.controlAction 0 (some ss_RewindState.done)).apply a = _
    rw [FinTM.controlAction_apply, moveInputPos_zero]
  have hcut : ∀ u ≤ d.inputPos.val + 1, (M.runFrom d u).state ≠ some .done := by
    intro u hu hdone
    have hf := ss_inputRewind_done (M.runFrom d u) hdone (d.inputPos.val + 1 - u)
    have hsum : u + (d.inputPos.val + 1 - u) = d.inputPos.val + 1 := by omega
    rw [← MultiTapeTM.runFrom_add, hsum, hstop] at hf
    have heq := congrArg Cfg.state hf
    rw [hdone] at heq
    cases heq
  have hret : M.runFrom d (d.inputPos.val + 2) =
      { d with state := some .done, inputPos := 1 } := by
    rw [show d.inputPos.val + 2 = (d.inputPos.val + 1) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', hstop, hlast _ rfl]
  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads M .enter .scan (some .stop)
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have htime : r = d.inputPos.val + 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hx : (M.runFrom d (r + 1)).state = some .done := by
        rw [MultiTapeTM.runFrom_succ_eq_step', hrun, hlast _ rfl]
      exact hcut (r + 1) (by omega) hx
    · have hf := ss_inputRewind_done
        ({ d with state := some .done, inputPos := 1 } : Cfg n Bool ss_RewindState z)
        rfl (r - (d.inputPos.val + 2))
      have hsum : d.inputPos.val + 2 + (r - (d.inputPos.val + 2)) = r := by omega
      rw [← hret, ← MultiTapeTM.runFrom_add, hsum, hrun, hret] at hf
      have heq := congrArg Cfg.state hf
      cases heq
  refine ⟨hret, fun u hu => hcut u (by omega), ?_⟩
  intro u hu
  by_cases h : u ≤ d.inputPos.val + 1
  · exact hheads u (by omega)
  · have heq : u = d.inputPos.val + 2 := by omega
    rw [heq, hret]

/-- A live configuration's state map preserves its physical frame, read through the public
field equations rather than through the definition of state renaming.

**Proof sketch.** Configuration extensionality reduces to the five published field equations;
the live-state equation reduces the option map to one constructor. -/
private theorem ss_live_map {n : ℕ} {P Q : Type} {z : List Bool}
    (d : Cfg n Bool P z) (q : P) (hq : d.state = some q) (f : P → Q) :
    d.mapState f = ⟨some (f q), d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, hq, Option.map_some]
  · exact Cfg.mapState_inputPos _ _
  · funext i p
    exact Cfg.mapState_workTapes _ _ _ _
  · funext i
    exact Cfg.mapState_workTapePos _ _ _
  · exact Cfg.mapState_output _ _

/-- Selected code and capture cells give a two-update normal form for any field.

**Proof sketch.** At the capture index use its equation. In the selected block, injectivity
identifies index zero; every other selected field has the background value. Outside both
blocks use the framing equation. This single argument applies to tapes and head positions. -/
private theorem ss_block_updates {A : Type} {m n : ℕ} (ι : Fin m ↪ Fin n)
    (cap : Fin n) (zero : Fin m) (hz : zero.val = 0)
    (f : Fin n → A) (base code captured : A)
    (hsel : ∀ j, f (ι j) = if j.val = 0 then code else base)
    (hc : f cap = captured)
    (ho : ∀ j, j ∉ Set.range ι → j ≠ cap → f j = base) :
    f = Function.update (Function.update (fun _ => base) (ι zero) code) cap captured := by
  funext j
  by_cases hj : j = cap
  · subst j
    rw [hc, Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hs : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hs
      rw [hsel]
      by_cases hi : i = zero
      · subst i
        rw [hz, if_pos rfl, Function.update_self]
      · have hival : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext (h.trans hz.symm))
        have hislot : ι i ≠ ι zero := fun h => hi (ι.injective h)
        rw [if_neg hival, Function.update_of_ne hislot]
    · have hjz : j ≠ ι zero := by
        intro h
        exact hs ⟨zero, h.symm⟩
      rw [ho j hs hj, Function.update_of_ne hjz]

/-- The source block sits after the simulated tapes, table, and summary. -/
private def ss_sourceSlot (m k : ℕ) : Fin m ↪ Fin ((m + 1) + (k + 2)) where
  toFun i := ⟨k + 2 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change k + 2 + i.val = k + 2 + j.val at hv
    omega

/-- The capture tape is last, beyond the source block. -/
private def ss_captureTape (m k : ℕ) : Fin ((m + 1) + (k + 2)) :=
  ⟨k + 2 + m, by omega⟩

/-- The capture tape is separate, and all first `k + 2` tapes lie outside both blocks.

**Proof sketch.** Every selected index lies between `k + 2` and `k + 2 + m - 1`.
The capture index is `k + 2 + m`, and each reserved index is smaller than `k + 2`. -/
private theorem ss_capture_indices (m k : ℕ) :
    ss_captureTape m k ∉ Set.range (ss_sourceSlot m k) ∧
    ∀ j : Fin ((m + 1) + (k + 2)), j.val < k + 2 →
      j ∉ Set.range (ss_sourceSlot m k) ∧ j ≠ ss_captureTape m k := by
  have hs (i : Fin m) : k + 2 ≤ (ss_sourceSlot m k i).val ∧
      (ss_sourceSlot m k i).val < (ss_captureTape m k).val := by
    change k + 2 ≤ k + 2 + i.val ∧ k + 2 + i.val < k + 2 + m
    omega
  constructor
  · rintro ⟨i, hi⟩
    have := (hs i).2
    rw [hi] at this
    exact (lt_irrefl _ this)
  · intro j hj
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      have := (hs i).1
      rw [hi] at this
      omega
    · intro h
      have hv := congrArg Fin.val h
      change j.val = k + 2 + m at hv
      omega

/-- **U2-S, the `k`-generic startup** (the startup of `Turing.exists_selfStartupTM`, generic in
the work-tape count). For a `k`-tape scheme `E` there is a binary machine with `K + (k + 2)` work
tapes and an exit state such that for every code `α` there are a time `T` and a space bound `B`,
**depending on `α` only**, with the following property on every input `pairEncode α w`. At time
`T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before;
* tapes `0, …, k - 1`, the simulated work tapes, blank, and tape `k` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `k + 1` holding the decoded machine's initial state in unary from cell `2` (cells `0`
  and `1` blank), the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam
(`Turing.StepBlock.Rep`) for the decoded machine's initial configuration on the same input, and
its restriction to the first `k + 2` tapes is H2-F's encoding `Turing.StepBlock.forwardLoopCfg` of
that configuration. [AB09, §1.4.1, Theorem 1.9]

**Proof sketch.** As `Turing.exists_selfStartupTM`'s, at `k` mirrored tapes. Extract and
canonize: the prefix parser composed with the scheme's canonizer by buffered composition, its
emissions captured on a scratch tape (the pattern of `Turing.universalCanonTM` and
`Turing.universalCaptureTM`, with `E.canonizer` in place of the one-tape scheme's); it ends after
`3|α| + 4 + E.canonizerTime |α|` steps with `serializeK (E.machine α)` captured and the input
head at `2|α| + 3`. Skip the doubled state count and the separator of
`serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`, copy the unary initial state to
tape `k + 1` at offset `2` and the table to tape `k`; clear the scratch and the buffer. Rewind the
input head to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends
on `α` only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's
halting time bounds its cells).

**Implementation.** The scheme's canonizer runs behind the public cleaner, which blanks its work
tapes and returns its heads, and the capture uses that machine's first halting time `t α`
(`Turing.MultiTapeTM.exists_first_halt`): the capture ends after `3|α| + 4 + t α` steps rather
than at the bound `E.canonizerTime |α|`. The code buffer is cleared by the catalog skip, skip back
and clear around a one-step move that acts only on a blank cell; on the empty code the buffer is
all blank, so the canonizer's final head position on the empty code is a fixed parameter of the
machine, chosen from `E`. The input head is rewound by `Turing.FinTM.rewind_scan` and
`Turing.FinTM.rewind_heads`, in `2|α| + 5` steps. -/
theorem exists_selfStartupTMK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
              else if j.val = k + 1 then
                fun p => FinTM.bufferTape (unaryFin (E.machine α).q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  classical
  let G := FinTM.bufferedCompTM universalPrefixTM (ss_cleanCanonizer E.canonizer)
  let n := (G.k + 1) + (k + 2)
  let ι := ss_sourceSlot G.k k
  let cap := ss_captureTape G.k k
  have hcap : cap ∉ Set.range ι := (ss_capture_indices G.k k).1
  have hm : 0 < G.k := by
    dsimp only [G]
    rw [FinTM.bufferedCompTM_k, universalPrefixTM_k]
    omega
  let zero : Fin G.k := ⟨0, hm⟩
  let code := ι zero
  let tbl : Fin n := ⟨k, by dsimp only [n]; omega⟩
  let sm : Fin n := ⟨k + 1, by dsimp only [n]; omega⟩
  have htbl := (ss_capture_indices G.k k).2 tbl (by dsimp only [tbl]; omega)
  have hsm := (ss_capture_indices G.k k).2 sm (by dsimp only [sm]; omega)
  have hts : tbl ≠ sm := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [tbl, sm] at hv
    omega
  have hct : code ≠ tbl := fun h => htbl.1 ⟨zero, h⟩
  have hcs : code ≠ sm := fun h => hsm.1 ⟨zero, h⟩
  have hcc : code ≠ cap := fun h => hcap ⟨zero, h⟩
  let A := ss_captureTM G ι cap
  have hcapture := fun α => ss_capturedPrefix_fields E.canonizer
    (fun β => serializeK (E.machine β)) E.canonizerTime E.canonizer_computes ι cap hcap α
  dsimp only at hcapture
  choose t p hp hc using hcapture
  have hp0 : p [] ≤ 1 := by simpa only [List.length_nil, zero_add] using hp []
  obtain ⟨Q, hQ, hD, L, entry, done, C, hL⟩ :=
    ss_serialized_layout n cap tbl sm htbl.2.symm hsm.2.symm hts
  letI := hQ
  letI := hD
  let J := ss_bufferCleanup n code (p [])
  let jentry : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inl (Sum.inl .run)
  let jexit : (SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)) :=
    Sum.inr (Sum.inr (Sum.inr .done))
  let B := seamCompTM J jexit (ss_inputRewind n) .enter
  let D := seamCompTM L done B (Sum.inl jentry)
  let W := seamCompTM A (Sum.inr ()) D (Sum.inl entry)
  let R := { W with q₀ := Sum.inl A.q₀ }
  let exit : (G.State ⊕ Unit) ⊕ Q ⊕
      (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
        ss_RewindState) := Sum.inr (Sum.inr (Sum.inr .done))
  refine ⟨G.k + 1, _, inferInstance, inferInstance, R, exit, ?_⟩
  intro α
  obtain ⟨l, hl, hlayout⟩ := hL (E.machine α)
  let a := 3 * α.length + 4 + t α
  let v := if p α = 0 then [] else α.drop (p α - 1)
  let w₀ := if p α = 0 then α else []
  let b := v.length + w₀.length + 3 * α.length + 14
  let r := 2 * α.length + 5
  let T := a + 1 + (l + 1 + (b + 1 + r))
  refine ⟨T, n * (T + 1), ?_⟩
  intro w
  let d₀ := A.initCfg (pairEncode α w)
  let d₁ := A.runFrom d₀ a
  obtain ⟨hstate, hip, hsel, hheads, hcapt, hother, hcut, hsil, _⟩ := hc α w
  have hs₁ : d₁.state = some (Sum.inr ()) := hstate
  have ht₁ : d₁.workTapes = Function.update
      (Function.update (fun _ => fun _ => none) code (FinTM.bufferTape α))
      cap (FinTM.bufferTape (serializeK (E.machine α))) :=
    ss_block_updates ι cap zero rfl _ _ _ _ hsel hcapt.1
      (fun j hj hjc => (hother j hj hjc).1)
  have hh₁ : d₁.workTapePos = Function.update
      (Function.update (fun _ => 0) code ((p α : ℤ) - 1))
      cap (serializeK (E.machine α)).length :=
    ss_block_updates ι cap zero rfl _ _ _ _ hheads hcapt.2
      (fun j hj hjc => (hother j hj hjc).2)
  have ho₁ : d₁.output = [] := hsil a le_rfl
  let d₂ := d₁.mapState (fun _ => entry)
  have hd₂ : d₂.state = some entry := by
    rw [Cfg.mapState_state, hs₁, Option.map_some]
  have ht₂ (j : Fin n) : d₂.workTapes j = d₁.workTapes j := by
    funext q
    exact Cfg.mapState_workTapes _ _ _ _
  have hh₂ (j : Fin n) : d₂.workTapePos j = d₁.workTapePos j :=
    Cfg.mapState_workTapePos _ _ _
  obtain ⟨hs₃, hi₃, ht₃, hh₃, ho₃, hcut₃⟩ := hlayout d₂ hd₂
    ((ht₂ cap).trans hcapt.1) ((hh₂ cap).trans hcapt.2)
    ((ht₂ tbl).trans (hother tbl htbl.1 htbl.2).1)
    ((hh₂ tbl).trans (hother tbl htbl.1 htbl.2).2)
    ((ht₂ sm).trans (hother sm hsm.1 hsm.2).1)
    ((hh₂ sm).trans (hother sm hsm.1 hsm.2).2)
  let d₃ := L.runFrom d₂ l
  let c : Cfg n Bool SeekPhase (pairEncode α w) :=
    ⟨some .run, d₃.inputPos, d₃.workTapes, d₃.workTapePos, d₃.output⟩
  have hbuf : c.workTapes code = FinTM.bufferTape α := by
    change d₃.workTapes code = _
    rw [ht₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, ht₂]
    exact (hsel zero).trans (if_pos rfl)
  have hpos : c.workTapePos code = (p α : ℤ) - 1 := by
    change d₃.workTapePos code = _
    rw [hh₃, Function.update_of_ne hcs, Function.update_of_ne hct,
      Function.update_of_ne hcc, hh₂]
    exact (hheads zero).trans (if_pos rfl)
  obtain ⟨hj, hjcut⟩ := ss_bufferCleanup_run code (p []) hp0 α (p α) (hp α)
    (fun h => congrArg p h) c rfl hbuf hpos
  have hjstart :
      ((c.mapState (Sum.inl : SeekPhase → SeekPhase ⊕ (Bool ⊕ SeekPhase))).mapState
        Sum.inl) = d₃.mapState (fun _ => jentry) := by
    rw [ss_live_map c .run rfl,
      ss_live_map _ (Sum.inl .run) rfl, ss_live_map d₃ done hs₃]
  rw [hjstart] at hj hjcut
  let d₄ : Cfg n Bool
      ((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase)))
      (pairEncode α w) :=
    ⟨some jexit, d₃.inputPos, Function.update d₃.workTapes code (fun _ => none),
      Function.update d₃.workTapePos code 0, d₃.output⟩
  change J.runFrom (d₃.mapState (fun _ => jentry)) b = d₄ at hj
  change ∀ u < b, (J.runFrom (d₃.mapState (fun _ => jentry)) u).state ≠ some jexit at hjcut
  let d₅ := d₄.mapState (fun _ => ss_RewindState.enter)
  have hd₅ : d₅.state = some .enter := by rw [Cfg.mapState_state]; rfl
  have hi₅ : d₅.inputPos.val = 2 * α.length + 3 := by
    rw [Cfg.mapState_inputPos]
    change d₃.inputPos.val = _
    rw [hi₃, Cfg.mapState_inputPos]
    exact hip
  obtain ⟨hrew, hrewcut, _⟩ := ss_inputRewind_run d₅ hd₅ (by omega)
  have htime : d₅.inputPos.val + 2 = r := by dsimp only [r]; omega
  rw [htime] at hrew hrewcut
  have hb := seamCompTM_run_ofCfg J jexit (ss_inputRewind n) .enter hj rfl hjcut hrew
  have hbcut := seamCompTM_firstReturn_ofCfg J jexit (ss_inputRewind n) .enter .done
    hj rfl hjcut hrew rfl hrewcut
  have hbstart : (d₃.mapState (fun _ => jentry)).mapState
      (Sum.inl : _ → _ ⊕ ss_RewindState) = d₃.mapState (fun _ => Sum.inl jentry) := by
    rw [ss_live_map d₃ done hs₃, ss_live_map _ jentry rfl, ss_live_map d₃ done hs₃]
  rw [hbstart] at hb hbcut
  have hd := seamCompTM_run_ofCfg L done B (Sum.inl jentry) rfl hs₃ hcut₃ hb
  have hdcut := seamCompTM_firstReturn_ofCfg L done B (Sum.inl jentry) (Sum.inr .done)
    rfl hs₃ hcut₃ hb (by rw [Cfg.mapState_state]; rfl) hbcut
  have hdstart : (d₁.mapState (fun _ => entry)).mapState
      (Sum.inl : Q → Q ⊕
        (((SeekPhase ⊕ (Bool ⊕ SeekPhase)) ⊕ (SeekPhase ⊕ (Bool ⊕ SweepPhase))) ⊕
          ss_RewindState)) = d₁.mapState (fun _ => Sum.inl entry) := by
    rw [ss_live_map d₁ (Sum.inr ()) hs₁, ss_live_map _ entry rfl,
      ss_live_map d₁ (Sum.inr ()) hs₁]
  rw [hdstart] at hd hdcut
  have hw := seamCompTM_run_ofCfg A (Sum.inr ()) D (Sum.inl entry) rfl hs₁ hcut hd
  have hwcut := seamCompTM_firstReturn_ofCfg A (Sum.inr ()) D (Sum.inl entry)
    (Sum.inr (Sum.inr .done)) rfl hs₁ hcut hd
    (by rw [Cfg.mapState_state, Cfg.mapState_state]; rfl) hdcut
  have hinit : R.initCfg (pairEncode α w) = d₀.mapState Sum.inl := by
    apply Cfg.ext
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_state, Cfg.mapState_state,
        d₀, Option.map_some]
      rfl
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos, Cfg.mapState_inputPos,
        d₀]
    · funext j q
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes, Cfg.mapState_workTapes,
        d₀]
    · funext j
      simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos,
        Cfg.mapState_workTapePos, d₀]
    · simp only [R, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, Cfg.mapState_output,
        d₀]
  have htfinal : Function.update d₃.workTapes code (fun _ => none) =
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
        else if j.val = k + 1 then
          fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
        else fun _ => none := by
    funext j q
    rw [ht₃]
    have hdtapes : d₂.workTapes = d₁.workTapes := by
      funext j q
      exact Cfg.mapState_workTapes _ _ _ _
    rw [hdtapes, ht₁]
    by_cases hjt : j = tbl
    · subst j
      simp only [tbl, Function.update_of_ne hct.symm, Function.update_of_ne hts,
        Function.update_self, ite_true]
    · have hjtv : j.val ≠ k := fun h => hjt (Fin.ext h)
      by_cases hjs : j = sm
      · subst j
        simp only [sm, Function.update_of_ne hcs.symm, Function.update_self,
          if_neg hjtv, ite_true]
      · have hjsv : j.val ≠ k + 1 := fun h => hjs (Fin.ext h)
        simp only [if_neg hjtv, if_neg hjsv]
        by_cases hjc : j = code
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjc, Function.update_of_ne hjs,
            Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hhfinal : Function.update d₃.workTapePos code 0 = fun _ => 0 := by
    funext j
    rw [hh₃]
    have hdheads : d₂.workTapePos = d₁.workTapePos := by
      funext j
      exact Cfg.mapState_workTapePos _ _ _
    rw [hdheads, hh₁]
    by_cases hjc : j = code
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hjc]
      by_cases hjs : j = sm
      · subst j
        rw [Function.update_self]
      · rw [Function.update_of_ne hjs]
        by_cases hjt : j = tbl
        · subst j
          rw [Function.update_self]
        · rw [Function.update_of_ne hjt, Function.update_idem]
          by_cases hjcap : j = cap
          · subst j
            rw [Function.update_self]
          · rw [Function.update_of_ne hjcap, Function.update_of_ne hjc]
  have hofinal : d₃.output = [] := by
    rw [ho₃ l le_rfl, Cfg.mapState_output]
    exact ho₁
  have hfinal : R.runFrom (R.initCfg (pairEncode α w)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
          else if j.val = k + 1 then
            fun q => FinTM.bufferTape (unaryFin (E.machine α).q₀) (q - 2)
          else fun _ => none,
        fun _ => 0, []⟩ := by
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    rw [hw]
    apply Cfg.ext
    · simp only [Cfg.mapState_state, Option.map_some]
      rfl
    · simp only [Cfg.mapState_inputPos]
    · funext j q
      simp only [Cfg.mapState_workTapes]
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun htfinal j) q
    · funext j
      simp only [Cfg.mapState_workTapePos]
      rw [Cfg.mapState_workTapePos]
      exact congrFun hhfinal j
    · simp only [Cfg.mapState_output]
      rw [Cfg.mapState_output]
      exact hofinal
  refine ⟨hfinal, ?_, ?_, MultiTapeTM.spaceUsed_le_mul_succ R _ T⟩
  · intro u hu
    rw [hinit, MultiTapeTM.runFrom_with_q₀]
    exact hwcut u hu
  · intro u hu
    have hpre := MultiTapeTM.output_prefix R (R.initCfg (pairEncode α w)) hu
    rw [hfinal] at hpre
    exact List.prefix_nil.mp hpre

/-! ## U2-U: the self-application universal machine -/

/-- **U2-U, the self-application universal machine, with time and space ledgers and the
converse** [AB09, Theorem 1.9 and Exercise 4.1, at self-application]. For a `k`-tape scheme `E`
there is a binary machine `U` such that for every code `α` there is a constant `C > 0`
(depending on `α` only) with, for every `w`:
* whenever the machine coded by `α` halts on `pairEncode α w` with `output` within `t` steps,
  `U` halts on the same input with the same `output` within `C · (t + 1)` steps, having visited
  by then at most `C · (s + 1)` cells, `s` the coded machine's cells by time `t`;
* every completed output of `U` on `pairEncode α w` is a completed output of the coded machine
  there (so divergence is preserved).

`C` depends on the code string, as in `Turing.universal` (Argument E): it absorbs the canonizer's
arbitrary time and the table's length. B6's `Turing.exists_selfUniversal` is the case `k = 1`
(forward clause, space only).

**Proof sketch.** Startup, then H2-F. (i) U2-S reaches, after `T_α` steps and within `B_α`
cells, H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg (pairEncode α w))` of
the coded machine `M := E.machine α`, on the block's tapes, the other tapes blank; seam it into
H2-F's machine `L` (R2, R1 on the first `k + 2` tapes). (ii) H2-F's lockstep
(`Turing.Lockstep.runFrom`) runs `M` from its initial configuration through its first halt
`t₀ ≤ t`: `L` is then at the encoding of the halted configuration, halted, with `M`'s output,
after `Σ_{u < t₀} cost ≤ (50 · (|tableBitsK| + 1) + C_L) · t` steps; with the seam's one step,
the time is at most `T_α + 1 + (50 · (|tableBitsK| + 1) + C_L) · t ≤ C · (t + 1)`. (iii) Space:
the mirrored heads visit only `M`'s cells, at most `s`; the auxiliary heads stay in an interval
of length `2 (50 · (|tableBitsK| + 1) + C_L) + 1`; the startup `B_α`; in all `≤ C · (s + 1)`,
and the halted configuration is frozen afterwards. (iv) Converse: by the lockstep's cut
(`Turing.Lockstep.cut`) `L` is live while `M` is, and an encoded live configuration is live, so
`U` halts only at the encoding of a halted configuration of `M`, whose output is `M`'s. -/
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  let U : FinTM Bool :=
    { k := K + (k + 2), State := P ⊕ Q, tm := startupLoopTM R exit L entry }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, B, hRα⟩ := hR α
  let M := E.machine α
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let N := K + (k + 2)
  let C := T + 1 + D + B + N * (2 * D + 1) + N
  have hTC : T + 1 ≤ C := by dsimp only [C]; omega
  have hDC : D ≤ C := by dsimp only [C]; omega
  have hNC : N ≤ C := by dsimp only [C]; omega
  have hBC : B + N * (2 * D + 1) ≤ C := by dsimp only [C]; omega
  refine ⟨C, by omega, ?_⟩
  intro w
  let z := pairEncode α w
  obtain ⟨hrun, hcut, _, hB⟩ := hRα w
  obtain ⟨cost, hlock, hcost, hledger⟩ := hL (x := z) M
  have hUrun := startupLoopTM_runFrom R exit L entry
    (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
    (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) z output t).mp hcomp
    obtain ⟨t₀, ht₀, hfirst, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun c hc => (hcost c hc).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg z) u)
    have hUhalt : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).state = none := by
      rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, hr,
        StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none]
    have hUout : (U.tm.runFrom (U.tm.initCfg z) (T + 1 + v)).output = output := by
      rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hr,
        StepBlock.forwardLoopCfg_output]
      exact hout
    have htime : T + 1 + v ≤ C * (t + 1) := by
      calc
        _ ≤ C + D * t := Nat.add_le_add hTC hvbound
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    have hUcomp : U.ComputesInTime z output (T + 1 + v) :=
      (FinTM.computesInTime_iff U z output (T + 1 + v)).mpr ⟨hUhalt, hUout⟩
    refine ⟨hUcomp.mono htime, ?_⟩
    let s := M.spaceUsed (M.initCfg z) t
    have hloop : ∀ i, L.spaceUsedByTape
        (StepBlock.forwardLoopCfg entry M (M.initCfg z)) v i ≤ s + (2 * D + 1) := by
      intro i
      by_cases hi : i.val < k
      · let j : Fin k := ⟨i.val, hi⟩
        have hij : Fin.castAdd 2 j = i := Fin.ext rfl
        rw [← hij, MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t₀ j).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).1 j)
          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card :=
            Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (M.initCfg z) ht₀ j)
          _ = M.spaceUsedByTape (M.initCfg z) t j :=
            (MultiTapeTM.spaceUsedByTape_eq_card (tm := M) _ t j).symm
          _ ≤ s := MultiTapeTM.spaceUsedByTape_le_spaceUsed (tm := M) _ t j
          _ ≤ _ := by omega
      · rw [MultiTapeTM.spaceUsedByTape_eq_card]
        calc
          _ ≤ (Finset.Icc (-(D : ℤ)) (D : ℤ)).card :=
            Finset.card_le_card ((hledger (M.initCfg z) t₀ hfirst).2 i (by omega))
          _ = 2 * D + 1 := by rw [Int.card_Icc]; omega
          _ ≤ _ := by omega
    have hspace := startupLoopTM_spaceUsed_le R exit L entry
      (StepBlock.forwardLoopCfg entry M (M.initCfg z)) (R.runFrom (R.initCfg z) T) T rfl
      (by rw [hrun]) hcut (by rw [hrun]; exact (embedEmitCfg_forwardLoop_init exit entry M z).symm)
      v B (s + (2 * D + 1)) hB (by omega) hloop
    calc
      _ ≤ B + N * (s + (2 * D + 1)) :=
        FinTM.ComputesInTime.spaceUsed_le_of_halt hUcomp hspace _
      _ = N * s + (B + N * (2 * D + 1)) := by ring
      _ ≤ C * s + C := Nat.add_le_add (Nat.mul_le_mul_right s hNC) hBC
      _ = _ := by dsimp only [s, M, EffectiveCodeK.toFinTM]; ring
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le R exit L entry T
      (by rw [hrun]; exact Option.some_ne_none exit) hcut
    have hafter : T + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) hhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hafter
    rw [hUrun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at hhalt
    rw [hUrun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at hout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost v hhalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) z output t).mpr
      ⟨ht, ho.trans hout⟩⟩

/-! ## U2-E: the code-first evaluator -/


/-- The startup embedded with one extra tape, followed by the header ruler preparation. -/
private noncomputable def uk_suffixStartupTM {k K : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P) :
    MultiTapeTM (K + (k + 3)) Bool (P ⊕ (Fin 4 ⊕ RewindPhase)) :=
  { seamCompTM
      ({ embedEmitTM (Fin.castLEEmb (by omega)) R with q₀ := R.q₀ }) exit
      (headerRulerTM ⟨k + 2, by omega⟩) (Sum.inl 0) with q₀ := Sum.inl R.q₀ }

/-- The original startup followed by the header scan and rewind reaches the suffix seam.

**Proof sketch.** Embed the startup in one more tape and reconstruct its initial
and final configurations with the public embedding theorem. At the endpoint,
the tape immediately after the simulation bank is blank. The framed header
contract prepares it, and the public seam composes the two runs and their cuts. -/
private theorem uk_suffixStartup_run {k K n : ℕ} {P : Type} [DecidableEq P]
    (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (α x : List Bool) (T : ℕ)
    (hrun : R.runFrom (R.initCfg (pairEncode α x)) T =
      ⟨some exit, 1,
        fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
          else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
          else fun _ => none,
        fun _ => 0, []⟩)
    (hcut : ∀ t < T, (R.runFrom (R.initCfg (pairEncode α x)) t).state ≠ some exit) :
    let ℓ := 2 * α.length + 2
    let hlen : ℓ + 1 < (pairEncode α x).length + 2 := by rw [length_pairEncode]; omega
    (uk_suffixStartupTM R exit).runFrom ((uk_suffixStartupTM R exit).initCfg (pairEncode α x))
        (T + 1 + (2 * ℓ + 3)) = suffixRulerCfg (Sum.inr (Sum.inr .done)) M
          (pairEncode α x) ℓ hlen ∧
      (∀ t < T + 1 + (2 * ℓ + 3),
        ((uk_suffixStartupTM R exit).runFrom
          ((uk_suffixStartupTM R exit).initCfg (pairEncode α x)) t).state ≠
            some (Sum.inr (Sum.inr .done))) := by
  let z := pairEncode α x
  let ℓ := 2 * α.length + 2
  let σ := Fin.castLEEmb (by omega : K + (k + 2) ≤ K + (k + 3))
  let A := ({ embedEmitTM σ R with q₀ := R.q₀ } : MultiTapeTM (K + (k + 3)) Bool P)
  let i : Fin (K + (k + 3)) := ⟨k + 2, by omega⟩
  let B := headerRulerTM i
  let d : Cfg (K + (k + 3)) Bool P z :=
    ⟨some exit, 1,
      fun j => if j.val = k then FinTM.bufferTape (tableBitsK M.tr)
        else if j.val = k + 1 then fun a => FinTM.bufferTape (unaryFin M.q₀) (a - 2)
        else fun _ => none,
      fun _ => 0, []⟩
  have initEmbed : embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (R.initCfg z) =
      A.initCfg z := by
    apply embedEmitCfg_eq
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_state]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_inputPos]
    · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_output, List.nil_append]
    · intro j
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
    · intro j _
      constructor
      · funext a
        simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapes]
      · simp only [A, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos]
  have aRun : A.runFrom (A.initCfg z) T = d := by
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, z, hrun]
    apply embedEmitCfg_eq
    · rfl
    · rfl
    · rfl
    · intro j; exact ⟨rfl, rfl⟩
    · intro j hj
      have hge : K + (k + 2) ≤ j.val := by
        by_contra h
        apply hj
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        apply Fin.ext; rfl
      constructor
      · funext a
        simp only [d, if_neg (by omega : j.val ≠ k), if_neg (by omega : j.val ≠ k + 1)]
      · rfl
  have aCut : ∀ t < T, (A.runFrom (A.initCfg z) t).state ≠ some exit := by
    intro t ht
    rw [← initEmbed]
    simp only [A, MultiTapeTM.runFrom_with_q₀, embedEmitTM_runFrom, embedEmitCfg_state]
    exact hcut t ht
  let c := d.mapState (fun _ => (0 : Fin 4))
  have cstate : c.state = some 0 := by rw [Cfg.mapState_state]; rfl
  have cpos : c.inputPos.val = 1 + 0 := by rw [Cfg.mapState_inputPos]; rfl
  have cblank : ∀ a, c.workTapes i a = none := by
    intro a
    rw [Cfg.mapState_workTapes]
    simp only [d, i, if_neg (by omega : k + 2 ≠ k), if_neg (by omega : k + 2 ≠ k + 1)]
  obtain ⟨bRun, bCut⟩ := headerRulerTM_run i c 0 cpos cstate α x
    (by rw [List.drop_zero]) cblank
  have cmap : c.mapState Sum.inl = d.mapState (fun _ => (Sum.inl 0 : Fin 4 ⊕ RewindPhase)) := by
    rw [Cfg.mapState_mapState]; rfl
  rw [cmap] at bRun bCut
  have clen : c.inputPos.val + ℓ < z.length + 2 := by
    rw [cpos]
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have plen : ℓ + 1 < z.length + 2 := by
    dsimp only [z, ℓ]
    rw [length_pairEncode]
    omega
  have final :
      (⟨some (Sum.inr RewindPhase.done),
        ⟨c.inputPos.val + ℓ, clen⟩,
        Function.update c.workTapes i
          (fun a => FinTM.bufferTape (List.replicate ℓ true) (a - c.workTapePos i)),
        c.workTapePos, c.output⟩ : Cfg (K + (k + 3)) Bool (Fin 4 ⊕ RewindPhase) z).mapState
          Sum.inr =
        suffixRulerCfg (Sum.inr (Sum.inr .done) : P ⊕ (Fin 4 ⊕ RewindPhase)) M z ℓ plen := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, suffixRulerCfg_state]; rfl
    · rw [Cfg.mapState_inputPos, suffixRulerCfg_inputPos]
      apply Fin.ext
      change c.inputPos.val + ℓ = ℓ + 1
      rw [cpos]
      omega
    · funext j a
      rw [Cfg.mapState_workTapes, suffixRulerCfg_workTapes]
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, c, Cfg.mapState_workTapePos, d, sub_zero,
          i, if_neg (by omega : k + 2 ≠ k),
          if_neg (by omega : k + 2 ≠ k + 1), ↓reduceIte]
      · have hjv : j.val ≠ k + 2 := by intro h; apply hj; exact Fin.ext h
        simp only [Function.update_of_ne hj, c, Cfg.mapState_workTapes, d, if_neg hjv]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, suffixRulerCfg_workTapePos]
    · rw [Cfg.mapState_output, Cfg.mapState_output, suffixRulerCfg_output]
  have init : (uk_suffixStartupTM R exit).initCfg z = (A.initCfg z).mapState Sum.inl := by
    exact MultiTapeTM.initCfg_eq_mapState A (uk_suffixStartupTM R exit) Sum.inl rfl z
  constructor
  · rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact (seamCompTM_run_ofCfg A exit B (Sum.inl 0) aRun rfl aCut bRun).trans final
  · intro t ht
    rw [init, uk_suffixStartupTM, MultiTapeTM.runFrom_with_q₀]
    exact seamCompTM_firstReturn_ofCfg A exit B (Sum.inl 0) (Sum.inr .done)
      aRun rfl aCut bRun rfl bCut t ht

/-- **U2-E, the code-first evaluator** [AB09, Theorem 1.9, the evaluator `U(x, α) = M_α(x)`, in
the code-first layout of `Turing.universal`]. For a `k`-tape scheme `E` there is a binary
machine `U` such that for every code `α` there is a constant `C` (depending on `α` only) with,
for every input `x`:
* whenever the machine coded by `α` halts on `x` with `output` within `t` steps, `U` halts on
  `pairEncode α x` with the same `output` within `C · (t + 1)` steps (no term in `|x|`);
* every completed output of `U` on `pairEncode α x` is a completed output of the coded machine
  on `x`.

At `k = 1` and `E := c.toK` this is `Turing.universal c`'s statement (shown in the gate's
probe); re-deriving `Turing.universal` from it is deferred. At `k = 2` it is the core of
Theorem 1.9 at `T log T` with the Hennie–Stearns conversion (design note §4).

**Proof sketch.** (i) *Code-first startup:* scan the doubled code and its separator, writing
one ruler cell per header cell, so the ruler is `true^ℓ` with `ℓ = 2|α| + 2`, the header length
(`Turing.universal_pair_length`); extract and canonize `α` as U2-S does, installing H2-F's
encoding of `M := E.machine α`'s initial configuration on the virtual input `x` (virtual
position `1`, physical head at `ℓ + 1`). (ii) *Ruler host:* run H2-F's machine `L` through H5's
bounded-prefix ruler host (`Turing.exists_rulerHostTM`, `Turing.RulerAt`): a block simulation
of `L` on the suffix input `x`, with at most `C_R · (ℓ + 1)` host steps per step of `L`, the same
bank and output, and exit cut. Composing with H2-F's lockstep, each step of `M` costs at most
`C_R (ℓ + 1)(50 · (|tableBitsK| + 1) + C_L)`, a constant for fixed `α`; with the startup this is
`≤ C · (t + 1)`. (iii) *Converse:* the ruler host does not halt before `L`, nor `L` before `M`
(the two cuts), so every completed output of `U` is `M`'s on `x`.

**Implementation.** The steps of the sketch run in a different order. The startup
`Turing.exists_selfStartupTMK` runs first, on `pairEncode α x` (its endpoint does not depend on
`x`), embedded in the first `K + (k + 2)` of `K + (k + 3)` tapes. A finite-state scan then reads
the header from input position `1` in aligned pairs, marking one cell for each header cell on
tape `k + 2`, which the startup leaves blank, and stops at the separator with the input head at
`ℓ + 1`; the work-tape rewind `Turing.rewindTM` returns that tape's head to its first cell. After
`T + 2ℓ + 4` steps in all (seams included), the first `k + 3` tapes hold the ruler host's
presentation `Turing.rulerHostCfg` of the forwarding loop's encoding of `M`'s initial
configuration on `x`, with the ruler as the last of them and the initial tag `false` (virtual
input position `1`). From there the ruler host of `Turing.exists_rulerHostTM` runs the forwarding
loop of `Turing.StepBlock.exists_forwardLoopTM`. With `T` the startup's time, `D` the loop's
per-step bound `50 · (|tableBitsK| + 1) + C_L` and `C_R` the host's factor, the constant is
`C = T + 2ℓ + 5 + C_R (ℓ + 1) D`, which depends on `α` only. -/
theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  classical
  obtain ⟨K, P, fP, dP, R, exit, hR⟩ := exists_selfStartupTMK k E
  letI : Fintype P := fP
  letI : DecidableEq P := dP
  obtain ⟨Q, fQ, dQ, L, entry, C_L, hL⟩ := StepBlock.exists_forwardLoopTM k
  letI : Fintype Q := fQ
  letI : DecidableEq Q := dQ
  obtain ⟨V, fV, dV, H, inj, C_R, hCR, hH⟩ := exists_rulerHostTM L
  letI : Fintype V := fV
  letI : DecidableEq V := dV
  let A := uk_suffixStartupTM R exit
  let finish : P ⊕ (Fin 4 ⊕ RewindPhase) := Sum.inr (Sum.inr .done)
  let U : FinTM Bool :=
    { k := K + (k + 3), State := (P ⊕ (Fin 4 ⊕ RewindPhase)) ⊕ V,
      tm := startupLoopTM (k := k + 1) A finish H (inj entry false) }
  refine ⟨U, ?_⟩
  intro α
  obtain ⟨T, _, hRα⟩ := hR α
  let M := E.machine α
  let ℓ := 2 * α.length + 2
  let D := 50 * ((tableBitsK M.tr).length + 1) + C_L
  let T_A := T + 1 + (2 * ℓ + 3)
  let F := C_R * (ℓ + 1)
  let C := T_A + 1 + F * D
  have hAC : T_A + 1 ≤ C := by dsimp only [C]; omega
  have hDC : F * D ≤ C := by dsimp only [C]; omega
  refine ⟨C, ?_⟩
  intro x
  let z := pairEncode α x
  have hz : z.length = ℓ + x.length := length_pairEncode α x
  have hlen : ℓ + 1 < z.length + 2 := by omega
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; omega
  obtain ⟨hrun, hcut, _, _⟩ := hRα x
  obtain ⟨aRun, aCut⟩ := uk_suffixStartup_run R exit M α x T hrun hcut
  let c := StepBlock.forwardLoopCfg entry M (M.initCfg x)
  let rt := FinTM.bufferTape (List.replicate ℓ true)
  let d := rulerHostCfg ℓ hz (c.state.map fun q => inj q false) c rt 0
  have hb : false = true ↔ c.inputPos.val = 0 := by
    rw [(StepBlock.forwardLoopCfg_init_fields entry M x).2.1]
    decide
  have host := hH ℓ hz hℓ (pairEncode_drop α x) rt 0
    (by intro p _ _; rw [zero_add]) c false hb
  have uRun := startupLoopTM_runFrom (k := k + 1) A finish H (inj entry false) d
    (suffixRulerCfg (K := K) finish M z ℓ hlen) T_A aRun (suffixRulerCfg_state _ _ _ _ _) aCut
    (suffixRulerCfg_embed finish entry inj M ℓ hz hlen).symm
  obtain ⟨cost, hlock, hcost, _⟩ := hL (x := x) M
  constructor
  · intro output t hcomp
    obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff (E.toFinTM α) x output t).mp hcomp
    obtain ⟨t₀, _, _, hvbound, hr⟩ :=
      StepBlock.forwardLoop_forward M L entry cost D hlock (fun e he => (hcost e he).2) t hhalt
    let v := ∑ u ∈ Finset.range t₀, cost (M.runFrom (M.initCfg x) u)
    obtain ⟨w, _, hw, ⟨b, _, hhost⟩, _, _, _, _⟩ := host v
    have uHalt : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).state = none := by
      rw [uRun w, Cfg.mapState_state, embedEmitCfg_state, hhost, rulerHostCfg_state,
        hr, StepBlock.forwardLoopCfg_state, hhalt, Option.map_none, Option.map_none,
        Option.map_none]
    have uOut : (U.tm.runFrom (U.tm.initCfg z) (T_A + 1 + w)).output = output := by
      rw [uRun w, Cfg.mapState_output, embedEmitCfg_output, List.nil_append, hhost,
        rulerHostCfg_output, hr, StepBlock.forwardLoopCfg_output]
      exact hout
    have bound : T_A + 1 + w ≤ C * (t + 1) := by
      calc
        _ ≤ C + F * v := Nat.add_le_add hAC hw
        _ ≤ C + F * (D * t) := Nat.add_le_add_left (Nat.mul_le_mul_left F hvbound) C
        _ = C + (F * D) * t := by ring
        _ ≤ C + C * t := Nat.add_le_add_left (Nat.mul_le_mul_right t hDC) C
        _ = _ := by ring
    exact ((FinTM.computesInTime_iff U z output (T_A + 1 + w)).mpr ⟨uHalt, uOut⟩).mono bound
  · intro output hcomp
    obtain ⟨u, hu⟩ := hcomp
    obtain ⟨uhalt, uout⟩ := (FinTM.computesInTime_iff U z output u).mp hu
    have hprefix := startupLoopTM_live_of_le (k := k + 1) A finish H (inj entry false) T_A
      (by rw [aRun, suffixRulerCfg_state]; exact Option.some_ne_none finish) aCut
    have after : T_A + 1 ≤ u := by
      by_contra h
      exact hprefix u (by omega) uhalt
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [uRun v, Cfg.mapState_state, embedEmitCfg_state, Option.map_eq_none_iff] at uhalt
    rw [uRun v, Cfg.mapState_output, embedEmitCfg_output, List.nil_append] at uout
    have loopHalts : ∃ r, (L.runFrom c r).state = none := by
      by_contra hn
      have forever : ∀ r, (L.runFrom c r).state ≠ none := by
        intro r hr
        exact hn ⟨r, hr⟩
      obtain ⟨w, hw, _, _, cut, _, _, _⟩ := host (v + 1)
      exact cut (fun r _ => forever r) v (by omega) uhalt
    obtain ⟨r, rHalt⟩ := loopHalts
    obtain ⟨w, _, _, ⟨b, _, endpoint⟩, _, _, _, _⟩ := host r
    have wHalt : (H.runFrom d w).state = none := by
      rw [endpoint, rulerHostCfg_state, rHalt, Option.map_none]
    have loopOutput : (L.runFrom c r).output = output := by
      calc
        _ = (H.runFrom d w).output := by rw [endpoint, rulerHostCfg_output]
        _ = (H.runFrom d (max v w)).output :=
          (MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_right v w) wHalt).symm
        _ = (H.runFrom d v).output :=
          MultiTapeTM.runFrom_output_eq_of_halt H d (Nat.le_max_left v w) uhalt
        _ = _ := uout
    obtain ⟨t, ht, ho⟩ := StepBlock.forwardLoop_converse M L entry cost D hlock hcost r rHalt
    exact ⟨t, (FinTM.computesInTime_iff (E.toFinTM α) x output t).mpr
      ⟨ht, ho.trans loopOutput⟩⟩

end Turing
```

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
import TCSlib.Complexity.TuringMachine.CfgFacts
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
import TCSlib.Complexity.TuringMachine.Build.ZoneStep
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
import TCSlib.Complexity.TuringMachine.Build.UniversalParts
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
* `CfgFacts` — four elementary configuration facts: the input read depends on the input head
  only, a redirected live configuration is a phase's tagged configuration, a tagged configuration
  is at no other phase's state, and equal-length chunks have the expected total length.
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
* `Build/ZoneStep` — one track's step from the rows, as a contract, and the amortized
  `O(T log T)` cost of a run ([AB09, §1.7]). Proved.
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
* `Build/UniversalParts` — the parts of the `k`-generic universal machines [AB09, §1.4.1,
  Theorem 1.9]: the startup–loop seam with its run and space ledger from any seam endpoint, the
  forwarding loop's readings at an initial configuration, the header ruler (a doubled-header scan
  that extends a ruler, then the rewind) and the suffix-ruler layout. Proved; harvested from
  `UniversalK` (the U2 harvest, 2026-11-06).
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
