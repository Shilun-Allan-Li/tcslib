## ===== campaign/gates/110-epad-statements/pack.md =====

# External audit pack: the E-PAD statements, `Complexity.mem_SPACE_padLang` (PR #219, a statement gate)

## Why this PR

B6's H fill (#218, gate 109) proved `space_hierarchy` and ended `SPACE_linear_ne_NP`
([AB09, Exercise 3.2]) in the named escalation **E-PAD**. The library has no host for the
padded-language space decider. The user ruled on 2026-11-06:
- E-PAD's API publishes a **general** lemma (any space bound, a polynomial unary pad);
- it goes in a **new `SpaceComplexity/Padding`** module, for later reuse by Ladner's padding;
- `Hierarchy` may import it, and the maintainer then closes `SPACE_linear_ne_NP` in a small PR.

This PR lands the **statements only**. The proof of `mem_SPACE_padLang` is a fill, briefed after
this gate closes.

**The PR:** #219 on `lean/epad-statements`, head `7cd74fff` (full hash in the bundle header). It
consists of the change `b635f73b` and merges of the campaign. It adds
`TCSlib/Complexity/SpaceComplexity/Padding.lean` (77 lines) and its line in the
`SpaceComplexity` facade.

## The statements (verify)

```lean
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry
```

All three are in namespace `Complexity`. The module imports `SpaceComplexity/Basic` only, which
brings in `SPACE` and, through `Encoding`, `pairEncode`. `|pairEncode x w| = 2|x| + 2 + |w|`
(`Turing.length_pairEncode`), so the padded length is `2n + 2 + C (n + 1)^d`.

**Why it should be true (the fill's route, in the docstring's sketch).** Let `M` decide `L` in
`c · S` cells. On input `y`:
1. Check that `y` is `pairEncode x w` with `w = 1^{C (|x|+1)^d}`, and reject otherwise. This
   needs `O(|y|)` cells, which `hT` pays for at every length, valid or not.
2. Run `M` on `x`, copied or read through a bounded input device, within `c · S |x|` cells,
   which `hST` pays for at the padded length.

`DecidesInSpace` asks for `O(T |y|)` on every input. Invalid inputs cost only the check.

## Brief for the auditor

1. **Truth and form:** is `mem_SPACE_padLang` true as stated, for every `S`, `T`, `C` and `d`?
   Check in particular:
   - `C = 0` and `d = 0`;
   - a non-monotone `T`;
   - invalid inputs;
   - the empty `x`;
   - that `DecidesInSpace` needs the bound at every input length.

   Are the hypotheses the natural ones? Is anything stronger than needed in a way that would
   block the reuse the ruling intends (Ladner's padding, which is time-based and would need its
   own statement)?
2. **The consumer:** does the statement give exactly the hypothesis that `Hierarchy`'s private
   `sph_linear_ne_NP_of_padding` consumes at `S n = n² + 1`, `T n = n + 1`, `C = 1` and `d = 2`?
   Answer through `mem_padLang_iff` only, with no unfolding of `padLang` (rule 10);
   `evidence/probe/`.
3. **Public text:** are the docstrings accurate and attributed, and is the module docstring
   complete?

## Repository-side attestations (verify or challenge)

- **Consumer probe** (`evidence/probe/EPadProbe.lean.txt`, `.out`). The probe:
  - copies the module's text inline;
  - derives `sph_linear_ne_NP_of_padding`'s `hpad` hypothesis from `mem_SPACE_padLang`
    through `mem_padLang_iff` and `Set.ext`, with `n² + 1 ≤ 2n + 2 + (n + 1)² + 1` from
    `Nat.pow_le_pow_left` and `omega`;
  - instantiates the edge case `C = 0`, `d = 0`;
  - prints `mem_padLang_iff`'s axioms.

  It elaborates with **exit 0**. The only `sorry` warning is the statement's own, and
  `mem_padLang_iff` depends on no axioms.
- **Replay** (`evidence/merged-tree/`): `replay-lep2` at `7cd74fff` (the new module and the
  facade), chained from the campaign snapshot after #216: **2 modules, 0 failed**. The one
  `sorry` warning is `mem_SPACE_padLang`'s. The static check finds 0 mismatches. #217 and #211
  merged afterwards. Neither touches `Padding`'s import closure (`SpaceComplexity/Basic` and
  upstream).
- **Lint** (`evidence/lint/`):
  - The policy linter on `Padding` gives 0 findings.
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 82 WARN over 113 files. The one new
    WARN is check 8 ("public def without a lemma beside it: `padLang`"). That check recognizes
    only `padLang_…` names. The definition's published characterization is
    `mem_padLang_iff`, in the `mem_SPACE_iff` pattern of `SpaceComplexity/Basic`. This is
    disclosed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/110-epad-statements/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `epad-statements-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/110-epad-statements/STATUS.md =====

# Gate 110 (#219, the E-PAD statements, a statement gate)

- 2026-11-06: #219 opened; consumer probe; `replay-lep2` (2/0, after #216); lint; pack written; staged.

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

## ===== campaign/gates/110-epad-statements/evidence/lint/campaign-SpaceComplexity-head.txt =====

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
WARN  TCSlib/Complexity/SpaceComplexity/Padding.lean                        1 public def(s) without a lemma beside them (check 8): padLang
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
INFO  TCSlib/Complexity/SpaceComplexity/Padding.lean                        77 lines; 3 public / 0 private declarations
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

style_lint: 0 FAIL, 82 WARN over 113 files

## ===== campaign/gates/110-epad-statements/evidence/lint/policy-head.txt =====


0 findings in 1 files


## ===== campaign/gates/110-epad-statements/evidence/merged-tree/down-lep2.txt =====

TCSlib/Complexity/SpaceComplexity/Padding
TCSlib/Complexity/SpaceComplexity

## ===== campaign/gates/110-epad-statements/evidence/merged-tree/replay-lep2-static.txt =====

modules 2, mismatches 0, static total 1

## ===== campaign/gates/110-epad-statements/evidence/merged-tree/replay-lep2.log =====

# replay-lep2 at 7cd74fff: #219, E-PAD statements, on the campaign after #216 (2 modules), fresh .oleans into oleans-lep2
TCSlib/Complexity/SpaceComplexity/Padding exit=0 errors=0 sorry=1
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
# modules=2 failed=0

## ===== campaign/gates/110-epad-statements/evidence/merged-tree/replay-lep2.sh =====

#!/usr/bin/env bash
# Replay lep2 (#219, E-PAD statements, on the campaign after #216; branch lean/epad-statements, stacked on the campaign after #216 (oleans-lcamp3)): its downstream closure (2 modules),
# fresh .oleans into oleans-lep2, a copy of oleans-lcamp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-epad"
LIST="/home/user/tcslib-scratch/fills/replay/down-lep2.txt"
LOG="$S/fills/replay/replay-lep2.log"
PINS="TCSlib/Complexity/SpaceComplexity.lean:2c7a771f631cd96ffdb58fc6db20db75d54a0ed4
TCSlib/Complexity/SpaceComplexity/Padding.lean:39a59037fb3b7582ef154cd8819640ac05c1b6ea"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/epad-statements 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD || { echo "precheck: the head must contain the campaign after #216 (oleans-lcamp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #216 (oleans-lcamp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lep2" ] && { echo "precheck: $S/oleans-lep2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp3" ] || { echo "precheck: oleans-lcamp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp3" "$S/oleans-lep2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lep2 at $(git rev-parse --short HEAD): #219, E-PAD statements, on the campaign after #216 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lep2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lep2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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

## ===== campaign/gates/110-epad-statements/evidence/probe/EPadProbe.lean.txt =====

import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding transfers space bounds down

Padding a language by a polynomial number of ones lowers the space it needs, measured in the
padded length: if `L ∈ SPACE S`, the language of its members padded by `C · (|x| + 1)^d` ones,
`padLang L (fun n => C * (n + 1) ^ d)`, lies in `SPACE T` for every `T` that is at least linear
and dominates `S` at the padded length. This is the space form of the padding argument
[AB09, Exercise 3.2] calls for; `Complexity.SPACE_linear_ne_NP` uses it at `S n = n² + 1`,
`T n = n + 1` and the pad `(|x| + 1)²`.

## Main definitions

* `Complexity.padLang` — the members `x` of `L`, each padded by `pad |x|` ones:
  `pairEncode x 1^{pad |x|}`.

## Main results

* `Complexity.mem_padLang_iff` — `padLang`'s defining formula.
* `Complexity.mem_SPACE_padLang` — the padded language is in `SPACE T`. (Statement; its proof is
  a fill.)

## Implementation notes

The pad is a unary block after `pairEncode`, so a member's first component and its length are
recovered from the padded word (`Turing.length_pairEncode`). The lower bound `m + 1 ≤ T m` pays
for checking that the input is a padded word at all, and for the copy of its first component;
`S n ≤ T (2n + 2 + C (n + 1)^d)` pays for deciding `L` on that component.

## References

* [AB09] S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009.
-/

namespace Complexity

open Turing

/-- **The padded language**: the members `x` of `L`, each followed by `pad |x|` ones, as the
pair `pairEncode x 1^{pad |x|}`. [AB09, Exercise 3.2] -/
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

/-- **Membership in `padLang`, unfolded**: `y ∈ padLang L pad` exactly when `y` is a member `x`
of `L` paired with `pad |x|` ones. -/
theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

/-- **Padding transfers space bounds down** ([AB09, Exercise 3.2], the padding argument in space
form): if `L ∈ SPACE S`, then the language of `L`'s members padded by `C · (|x| + 1)^d` ones lies
in `SPACE T` for every `T` with `m + 1 ≤ T m` (room to validate the padding and to copy the first
component) and `S n ≤ T (2n + 2 + C (n + 1)^d)` (room for `L`'s decider, at the padded length
`|pairEncode x 1^{C (|x|+1)^d}| = 2|x| + 2 + C (|x| + 1)^d`).

**Proof sketch.** Let `M` decide `L` within `c · S` cells. On input `y`, first check that `y` is a
pair `pairEncode x w` whose second component `w` consists of exactly `C (|x| + 1)^d` ones;
reject otherwise. That needs `O(|y|)` cells. Then run `M` on `x` (copied to a work tape, or read
in place through a bounded input device) and answer as `M` does, within `c · S |x|` cells. For a
validated `y`, `|y| = 2|x| + 2 + C (|x| + 1)^d`, so both phases fit in `O(T |y|)`. -/
theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry

/-- The E-PAD interface `SPACE_linear_ne_NP`'s private lemma consumes, from the general statement
(through `mem_padLang_iff` only). -/
example : ∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
    ({y | ∃ x ∈ L,
      y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
      SPACE (fun n => n + 1) := by
  intro L hL
  have h := mem_SPACE_padLang (T := fun n => n + 1) 1 2 hL
    (fun n => by
      have : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
      dsimp only; omega) (fun m => le_rfl)
  have he : padLang L (fun n => 1 * (n + 1) ^ 2) =
      {y | ∃ x ∈ L, y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} := by
    ext y; exact mem_padLang_iff
  rwa [he] at h

/-- Edge cases are well-formed: a constant pad (`d = 0`) and the empty pad (`C = 0`). -/
example (L : Language Bool) (S T : ℕ → ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + 0 * (n + 1) ^ 0)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => 0 * (n + 1) ^ 0) ∈ SPACE T :=
  mem_SPACE_padLang 0 0 hL hST hT

#print axioms mem_padLang_iff

end Complexity

## ===== campaign/gates/110-epad-statements/evidence/probe/EPadProbe.out =====

Scratch/EPadProbeInline.lean:67:8: warning: declaration uses 'sorry'
'Complexity.mem_padLang_iff' does not depend on any axioms
exit=0

## ===== TCSlib/Complexity/SpaceComplexity/Padding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding transfers space bounds down

Padding a language by a polynomial number of ones lowers the space it needs, measured in the
padded length: if `L ∈ SPACE S`, the language of its members padded by `C · (|x| + 1)^d` ones,
`padLang L (fun n => C * (n + 1) ^ d)`, lies in `SPACE T` for every `T` that is at least linear
and dominates `S` at the padded length. This is the space form of the padding argument
[AB09, Exercise 3.2] calls for; `Complexity.SPACE_linear_ne_NP` uses it at `S n = n² + 1`,
`T n = n + 1` and the pad `(|x| + 1)²`.

## Main definitions

* `Complexity.padLang` — the members `x` of `L`, each padded by `pad |x|` ones:
  `pairEncode x 1^{pad |x|}`.

## Main results

* `Complexity.mem_padLang_iff` — `padLang`'s defining formula.
* `Complexity.mem_SPACE_padLang` — the padded language is in `SPACE T`. (Statement; its proof is
  a fill.)

## Implementation notes

The pad is a unary block after `pairEncode`, so a member's first component and its length are
recovered from the padded word (`Turing.length_pairEncode`). The lower bound `m + 1 ≤ T m` pays
for checking that the input is a padded word at all, and for the copy of its first component;
`S n ≤ T (2n + 2 + C (n + 1)^d)` pays for deciding `L` on that component.

## References

* [AB09] S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009.
-/

namespace Complexity

open Turing

/-- **The padded language**: the members `x` of `L`, each followed by `pad |x|` ones, as the
pair `pairEncode x 1^{pad |x|}`. [AB09, Exercise 3.2] -/
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

/-- **Membership in `padLang`, unfolded**: `y ∈ padLang L pad` exactly when `y` is a member `x`
of `L` paired with `pad |x|` ones. -/
theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

/-- **Padding transfers space bounds down** ([AB09, Exercise 3.2], the padding argument in space
form): if `L ∈ SPACE S`, then the language of `L`'s members padded by `C · (|x| + 1)^d` ones lies
in `SPACE T` for every `T` with `m + 1 ≤ T m` (room to validate the padding and to copy the first
component) and `S n ≤ T (2n + 2 + C (n + 1)^d)` (room for `L`'s decider, at the padded length
`|pairEncode x 1^{C (|x|+1)^d}| = 2|x| + 2 + C (|x| + 1)^d`).

**Proof sketch.** Let `M` decide `L` within `c · S` cells. On input `y`, first check that `y` is a
pair `pairEncode x w` whose second component `w` consists of exactly `C (|x| + 1)^d` ones;
reject otherwise. That needs `O(|y|)` cells. Then run `M` on `x` (copied to a work tape, or read
in place through a bounded input device) and answer as `M` does, within `c · S |x|` cells. For a
validated `y`, `|y| = 2|x| + 2 + C (|x| + 1)^d`, so both phases fit in `O(T |y|)`. -/
theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Basic.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded computation, `SPACE`, `L`, and implicitly logspace computable functions

[AB09, Def 4.1]: a language is in `SPACE(s(n))` when some machine decides it while
visiting at most `c · s(n)` work-tape cells on every input of length `n`; `L = SPACE(log n)`
[AB09, Def 4.5]. [AB09, Def 4.16]: a function `f` is *implicitly logspace computable* when it
is polynomially bounded and the two languages "the `i`-th bit of `f(x)` is `1`" and
"`i` is a position of `f(x)`" are in `L`.

## The machine model

We reuse the campaign's machines (`Turing.FinTM Bool`) unchanged. They already have the
shape of [AB09, Fig. 4.1]:

* **the input tape is read-only**: a transition (`Turing.Action`) has no write component
  for the input tape, only a head move, clamped to the input and its two boundary blanks;
* **the output tape is write-once, append-only**: a step appends at most one symbol;
* **space is the number of work-tape cells visited** (`Turing.MultiTapeTM.spaceUsed`, the
  sum over the work tapes of the visited cells), exactly the measure of [AB09, Def 4.1]
  ("at most `c · s(n)` locations on M's work tapes (excluding the input tape) are ever
  visited by M's head").

## Main definitions

* `Turing.FinTM.ComputesInSpace` — `M` computes `f`, halting on every input, visiting at most
  `s(|x|)` work cells.
* `Turing.FinTM.DecidesInSpace` — `M` decides `L` within space `s`. [AB09, Def 4.1]
* `Complexity.SPACE` — the class of languages decidable in space `c · s(n)`. [AB09, Def 4.1]
* `Complexity.logSpace` — the logarithmic space bound `⌊log₂ n⌋ + 1`.
* `Complexity.LOGSPACE` — the class `L = SPACE(log n)`. [AB09, Def 4.5]
* `Complexity.indexLang` — the language `{⟨x, i⟩ | p x i}` with `i` in binary.
* `Complexity.ImplicitlyLogspaceComputable` — [AB09, Def 4.16].

## Main results

* `Turing.FinTM.computesInSpace_iff`, `Complexity.logSpace_eq` — the definitions of
  `ComputesInSpace` and `logSpace` as an equivalence and an equation.
* `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff`, `Complexity.LOGSPACE_eq` —
  the definitions of `DecidesInSpace`, `SPACE` and `LOGSPACE`, unfolded.
* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.
* `Complexity.logSpace_le_succ`, `Complexity.logSpace_le_of_le_mul_two_pow` — the logarithmic
  bound is at most linear, and at most `(A + 1) s` below `A · 2^s`.
* `Complexity.logSpace_le_size_succ` — the logarithmic bound is at most one more than the
  binary length.
* `Complexity.SPACE.mono_const` — `SPACE` absorbs constant factors (added 2026-10-10).
* `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` — no work tapes, zero space (added
  2026-10-10).

## Divergences from [AB09]

* **The logarithm.** [AB09] writes `SPACE(log n)` and requires `s(n) ≥ log n` (p. 79). We use
  `logSpace n = ⌊log₂ n⌋ + 1`, which is at least `1` (so short inputs get constant space, the
  standard reading of the convention) and is `Θ(log n)` for `n ≥ 2`.
* **Pairs and indices** (Def 4.16). The pair `⟨x, i⟩` is `Turing.pairEncode x (Nat.bits i)`:
  the campaign's self-delimiting pairing with the index in little-endian binary without
  redundant zeros (`Nat.bits 0 = []`). Indices are **`0`-based**: the bit language is
  `{⟨x, i⟩ | f(x)ᵢ = 1}` with `f(x)ᵢ` the `i`-th bit from `0`, and the length language is
  `{⟨x, i⟩ | i < |f(x)|}` where [AB09] writes `i ≤ |f(x)|` for `1`-based `i`.
* **Polynomial bound** (Def 4.16). [AB09] asks `|f(x)| ≤ |x|^c`; at `x = ε` that forces
  `f(ε) = ε` for `c ≥ 1`. We use the campaign normal form `|f(x)| ≤ C · (|x| + 1)^c`
  (`Complexity.PolyBound` shape).
* **Halting.** Deciding (resp. computing) includes halting on every input, as in [AB09]
  ("a TM M deciding L"); the space bound is checked at the halting time, and since space is
  monotone in time and frozen after halting this is the space of the whole computation.
* **One measure for both classes.** [AB09, Def 4.1]'s own wording splits: *visited*
  work-tape locations for `SPACE` (the clause quoted above) but *nonblank* locations for
  `NSPACE`. The campaign convention is the visited-cells measure for both; the planned
  `NSPACE` (`AroraBarakChapters3-4Plan.md`, phase P4.1) counts visited cells along every
  choice word, with all branches halting.
* **Zero bounds collapse the class** (P0 reception audit, round 1, finding 1): every
  work tape's visited set contains its origin, so every machine satisfies
  `M.k ≤ spaceUsed` on every input at every time. A single length with `s n = 0`
  therefore forces a deciding machine to have **no work tapes at all** — and then it
  has zero space on *every* input — so `SPACE s = SPACE (fun _ => 0)` (semantically
  the two-way-finite-automaton class) whenever `s` has a zero; multiplicative
  absorption cannot repair this, since `c * 0 = 0`. In particular the literal
  `SPACE (fun n => n)` is **not** linear space: `n = 0` collapses it. **Campaign
  convention:** every asymptotic chapter statement uses an everywhere-positive bound —
  `fun n => n + 1`, `fun n => n ^ c + 1`, `Complexity.logSpace` — never a bound with a
  zero. The characterization and the harmless-normalization identities are the sanity
  layer `TCSlib.Complexity.SpaceComplexity.ZeroSpace`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5; §4.3, Definition 4.16.)
-/

namespace Turing.FinTM

/-- The machine `M` computes `f` in space `s`: on every input `x` it halts with output `f x`,
and up to that time it has visited at most `s |x|` work-tape cells (summed over its work
tapes). The input tape (read-only) and the output tape (append-only) do not count.
[AB09, Def 4.1, for functions] -/
def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length

/-- **Computing in space, unfolded**: `M` computes `f` in space `s` exactly when on every input
`x` there is a time `t` at which `M` has halted with output `f x`
(`Turing.FinTM.ComputesInTime`), having visited at most `s |x|` work-tape cells by then. -/
theorem computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length :=
  Iff.rfl

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

/-- **Deciding in space, unfolded**: `M` decides `L` in space `s` exactly when it computes the
one-bit indicator `x ↦ [x ∈ L]` in space `s`. -/
theorem decidesInSpace_iff (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
    M.DecidesInSpace L s ↔
      M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s :=
  Iff.rfl

/-- A space bound can be weakened. -/
theorem ComputesInSpace.mono {M : FinTM Bool} {f : List Bool → List Bool} {s s' : ℕ → ℕ}
    (h : M.ComputesInSpace f s) (hs : ∀ n, s n ≤ s' n) : M.ComputesInSpace f s' := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact ⟨t, ht, hsp.trans (hs _)⟩

/-- A machine with no work tapes computes in zero space whatever it computes at all: the
space measure counts only work-tape cells. (Shared by the zero-space layer; added
2026-10-10.)

**Proof sketch.** With `M.k = 0` the space measure is an empty sum
(`Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`), at every halting time. -/
theorem computesInSpace_zero_of_k_eq_zero {M : FinTM Bool} {f : List Bool → List Bool}
    (hk : M.k = 0) (h : ∀ x, ∃ t, M.ComputesInTime x (f x) t) :
    M.ComputesInSpace f fun _ => 0 := by
  intro x
  obtain ⟨t, ht⟩ := h x
  exact ⟨t, ht, (MultiTapeTM.spaceUsed_zero_tapes_eq_zero (tm := M.tm) _ t hk).le⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- **`SPACE(s)`** [AB09, Def 4.1]: the languages decided by some finite binary-alphabet
machine visiting at most `c · s(n)` work-tape cells on inputs of length `n`, for some
constant `c`. -/
def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}

/-- **Membership in `SPACE`, unfolded**: `L ∈ SPACE s` exactly when some machine decides `L` in
space `c · s` for some constant `c`. -/
theorem mem_SPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
    L ∈ SPACE s ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n :=
  Iff.rfl

/-- `SPACE` is monotone in the space bound. -/
theorem SPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, hM.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `SPACE` absorbs constant factors: if `s₁ ≤ a · s₂` pointwise, then
`SPACE s₁ ⊆ SPACE s₂`. [AB09, Def 4.1: the constant `c` absorbs `a`] (Shared by the
zero-space layer and the hierarchy arguments; added 2026-10-10.)

**Proof sketch.** A witness at constant `c` for `s₁` is a witness at constant `c · a`
for `s₂`, since `c · s₁ n ≤ c · (a · s₂ n) = (c · a) · s₂ n`
(`Turing.FinTM.ComputesInSpace.mono`). -/
theorem SPACE.mono_const {s₁ s₂ : ℕ → ℕ} {a : ℕ} (h : ∀ n, s₁ n ≤ a * s₂ n) :
    SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  refine ⟨c * a, M, hM.mono fun n => ?_⟩
  calc c * s₁ n ≤ c * (a * s₂ n) := Nat.mul_le_mul_left c (h n)
    _ = c * a * s₂ n := (Nat.mul_assoc c a (s₂ n)).symm

/-- The logarithmic space bound `⌊log₂ n⌋ + 1`: `Θ(log n)`, and at least `1`, following the
convention `s(n) ≥ log n` of [AB09, p. 79]. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The logarithmic bound's formula: `logSpace n = Nat.log 2 n + 1`. -/
theorem logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl

/-- The logarithmic bound is at most linear: `logSpace n ≤ n + 1`.

**Proof sketch.** `Nat.log 2 n ≤ n` (`Nat.log_le_self`), then `Complexity.logSpace_eq`. -/
theorem logSpace_le_succ (n : ℕ) : logSpace n ≤ n + 1 := by
  have := Nat.log_le_self 2 n
  rw [logSpace_eq]
  omega

/-- The logarithmic width is at most one more than the binary length:
`logSpace n ≤ Nat.size n + 1`.

**Proof sketch.** At `n = 0` both sides are `1`. Otherwise `2 ^ Nat.log 2 n ≤ n < 2 ^ Nat.size n`
(`Nat.pow_log_le_self`, `Nat.lt_size_self`), so `Nat.log 2 n < Nat.size n`. -/
lemma logSpace_le_size_succ (n : ℕ) : logSpace n ≤ Nat.size n + 1 := by
  unfold logSpace
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have : Nat.log 2 n < Nat.size n :=
      (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp (lt_of_le_of_lt h1 h2)
    omega

/-- A number at most `A · 2^s` (with `s ≥ 1`) has `logSpace` at most `(A + 1) s`. -/
theorem logSpace_le_of_le_mul_two_pow {v A s : ℕ} (h : v ≤ A * 2 ^ s) (hs : 1 ≤ s) :
    logSpace v ≤ (A + 1) * s := by
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hlt : v < 2 ^ (A + s) := by
    rw [pow_add]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos s))
  have hle : A + s ≤ (A + 1) * s := by
    have := Nat.le_mul_of_pos_right A (show 0 < s by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [logSpace, Nat.log_zero_right]; omega
  · have := Nat.log_lt_of_lt_pow (by omega) hlt
    simp only [logSpace]; omega

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

/-- `LOGSPACE` is `SPACE logSpace`. -/
theorem LOGSPACE_eq : LOGSPACE = SPACE logSpace := rfl

/-- The language `{⟨x, i⟩ | p x i}`, the pair encoded as `Turing.pairEncode x (Nat.bits i)`
(index in little-endian binary). The shape of the two languages of [AB09, Def 4.16]. -/
def indexLang (p : List Bool → ℕ → Prop) : Language Bool :=
  {w | ∃ x i, w = pairEncode x (Nat.bits i) ∧ p x i}

/-- **Implicitly logspace computable functions** [AB09, Def 4.16]: `f` is polynomially
bounded, `|f(x)| ≤ C · (|x| + 1)^c`, and both the bit language
`{⟨x, i⟩ | f(x)ᵢ = 1}` and the length language `{⟨x, i⟩ | i < |f(x)|}` are in `L`.
Indices are `0`-based and written in binary (`Nat.bits`); see the module docstring for the
divergences (`0`-based `i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`, and the `+ 1`
in the polynomial bound). -/
def ImplicitlyLogspaceComputable (f : List Bool → List Bool) : Prop :=
  (∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c) ∧
  indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE ∧
  indexLang (fun x i => i < (f x).length) ∈ LOGSPACE

/-- `logSpace` is monotone. -/
lemma logSpace_mono {a b : ℕ} (h : a ≤ b) : logSpace a ≤ logSpace b := by
  unfold logSpace
  have := Nat.log_mono_right (b := 2) h
  omega

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Machines.Layout
import TCSlib.Complexity.SpaceComplexity.Machines.Program
import TCSlib.Complexity.SpaceComplexity.Machines.Sim
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn
import TCSlib.Complexity.SpaceComplexity.Machines.Call
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec
import TCSlib.Complexity.SpaceComplexity.Machines.Frag
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain
import TCSlib.Complexity.SpaceComplexity.Machines.Parse
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp
import TCSlib.Complexity.SpaceComplexity.Machines.ARM
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace
import TCSlib.Complexity.SpaceComplexity.CounterProgSim
import TCSlib.Complexity.SpaceComplexity.CounterProgSimRun
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Inclusions
import TCSlib.Complexity.SpaceComplexity.Examples
import TCSlib.Complexity.SpaceComplexity.ZeroSpace
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.SpaceComplexity.Savitch
import TCSlib.Complexity.SpaceComplexity.Hierarchy
import TCSlib.Complexity.SpaceComplexity.Padding
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi
import TCSlib.Complexity.SpaceComplexity.Logspace.Mult
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidthExample
import TCSlib.Complexity.SpaceComplexity.Machines.ARMReach
import TCSlib.Complexity.SpaceComplexity.Machines.NARM
import TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile
import TCSlib.Complexity.SpaceComplexity.Machines.NARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.NARMExample
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProb
import TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem
import TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Codec.Word
import TCSlib.Complexity.SpaceComplexity.Codec.Scan
import TCSlib.Complexity.SpaceComplexity.Codec.Valid
import TCSlib.Complexity.SpaceComplexity.Codec.Step
import TCSlib.Complexity.SpaceComplexity.Codec.Langs
import TCSlib.Complexity.SpaceComplexity.Codec.Checks
import TCSlib.Complexity.SpaceComplexity.Codec.Engine
import TCSlib.Complexity.SpaceComplexity.Codec.Regs
import TCSlib.Complexity.SpaceComplexity.Codec.Machine
import TCSlib.Complexity.SpaceComplexity.Codec.Run
import TCSlib.Complexity.SpaceComplexity.Codec.Parse
import TCSlib.Complexity.SpaceComplexity.Codec.Layout
import TCSlib.Complexity.SpaceComplexity.Codec.Layout2
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Machine
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Run
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Search
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Deepen
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Window
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs
import TCSlib.Complexity.SpaceComplexity.Machines.MARM
import TCSlib.Complexity.SpaceComplexity.Machines.MARMCompile
import TCSlib.Complexity.SpaceComplexity.Machines.MARMTime
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Machine
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Run
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Relax
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Search
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Main
import TCSlib.Complexity.SpaceComplexity.ExpTime
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHard
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect

/-!
# Space complexity

Space-bounded computation and logarithmic space [AB09, §4.1, §4.3]: the classes `SPACE(s)`
and `L`, `L ⊆ P` by configuration counting, implicitly logspace computable functions and
their polynomial-time computability, with a toolkit of logspace machines (register-tape
programs calling logspace deciders on virtual inputs, and abstract register machines
compiled onto them).

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Contents

- `SpaceComplexity.Basic`: Def 4.1 space-bounded computation, `SPACE(s)`, `L`; Def 4.16
  implicitly logspace computable functions
- `SpaceComplexity.ConfigCount`: configuration counting; `L ⊆ P`; logspace functions run in
  polynomial time
- `SpaceComplexity.Machines.Layout`: virtual inputs assembled from segments
- `SpaceComplexity.Machines.Program`: register-tape programs with call nodes and their
  compilation
- `SpaceComplexity.Machines.Sim`: the lockstep simulation of a call's decider
- `SpaceComplexity.Machines.CallReturn`: compiled configurations; the return phase of a call
- `SpaceComplexity.Machines.Call`: the run of a call node
- `SpaceComplexity.Machines.Compile`: correctness and space of compiled programs
- `SpaceComplexity.Machines.CleanSweep`: the cleaned machine; the cleanup sweeps of one tape
- `SpaceComplexity.Machines.Clean`: the clean normal form of deciders (the whole run)
- `SpaceComplexity.Machines.Bank`: a bank of clean deciders
- `SpaceComplexity.Machines.Bin`: binary words of numbers
- `SpaceComplexity.Machines.Lib`: register steps and the increment fragment
- `SpaceComplexity.Machines.FragDec`: decrement and clear fragments
- `SpaceComplexity.Machines.Frag`: halve and equality fragments
- `SpaceComplexity.Machines.ParsePlain`: input shapes; the format check on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse`: comparisons on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse2`: the format check on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ParseCmp`: comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ARM`: abstract register machines and their compilation
- `SpaceComplexity.Machines.ARMSim`: per-instruction simulation
- `SpaceComplexity.Machines.ARMRun`: the run and space theorems of compiled machines
- `SpaceComplexity.Machines.ARMProof`: proving abstract machines correct; `arm_decides`
- `SpaceComplexity.Machines.ARMKit`: calls on unary inputs; `arm_decides_poly`
- `SpaceComplexity.Machines.ARMWidth`: abstract machines with wide registers;
  `arm_decides_space`, `arm_decides_SPACE`, `arm_decides_pspace`; `L ⊆ PSPACE`
- `SpaceComplexity.Machines.ARMWidthExample`: exhaustive search over `|x|`-bit witnesses
  with a polynomially wide register (`PSPACE` is closed under it)
- `SpaceComplexity.Machines.ARMReach`: compiled runs to live abstract configurations
  (`arm_step`, `arm_reach`)
- `SpaceComplexity.Machines.NARM`: nondeterministic abstract register machines (`choose`),
  their choice-word semantics and correctness combinators
- `SpaceComplexity.Machines.NARMCompile`: their compilation onto `FinNDTM`
- `SpaceComplexity.Machines.NARMRun`: the run and space theorems of compiled
  nondeterministic machines (`narm_space`)
- `SpaceComplexity.Machines.NARMProof`: `narm_decides_space`, `narm_decides` (`NL`),
  `narm_decides_npspace` (`NPSPACE`)
- `SpaceComplexity.Machines.NARMExample`: a guessing machine deciding a language in `NL`
- `SpaceComplexity.Machines.ARMLoops`: the bounded-run guard `GuardLe` and generic counting
  loops of abstract register machines
- `SpaceComplexity.Machines.VWord`: small shared lemmas on reading inputs by index
- `SpaceComplexity.Machines.NARMKit`: proving nondeterministic register machines correct by
  continuation (`NTerm`, `NAcc`, `NSem`), their step lemmas and generic nondeterministic
  loops
- `SpaceComplexity.Machines.NARMProb`: compilation preserves acceptance probabilities when
  `choose` bits are fair coins (`narm_randProb`) [AB09, Def 7.1, §7.7]
- `SpaceComplexity.Machines.NARMPSem`: the probabilistic continuation semantics `PSem` of
  such machines [AB09, §7.7]
- `SpaceComplexity.Machines.NARMLogspace`: their compilation to logspace PTMs
  (`narm_logspace_ptm`) and the bridge `narm_mem_RL` to `RL` [AB09, §7.7]
- `SpaceComplexity.Machines.DblLang`: reading the unary length `⟨1ⁿ, bits (2n)⟩` in
  logarithmic space
- `SpaceComplexity.ImplicitPoly`: implicitly logspace computable functions are
  polynomial-time computable
- `SpaceComplexity.UnaryLogspace`: functions of the unary length computable in logarithmic
  space (`UnaryLogspace`, `unaryExt`)
- `SpaceComplexity.CounterProgSim`, `SpaceComplexity.CounterProgSimRun`: polynomially
  running counter programs on unary-logspace inputs are unary-logspace
- `SpaceComplexity.NSPACE`: Def 4.1's nondeterministic clause, `NSPACE(s)` (chapters-3-4
  campaign, phase P4.1)
- `SpaceComplexity.SpaceClasses`: Def 4.5's `PSPACE`, `NPSPACE`, `NL`, and `coNL`
- `SpaceComplexity.Constructible`: space-constructible functions (p. 79)
- `SpaceComplexity.Inclusions`: Thm 4.2's first two inclusions; `P ⊆ PSPACE`;
  Example 4.6 (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)
- `SpaceComplexity.Examples`: Example 4.7's parity language
- `SpaceComplexity.ZeroSpace`: the zero-bound collapse of unnormalized `SPACE` and the
  positive-normalization identities (P0 reception audit, round 1)
- `SpaceComplexity.ConfigGraph`: configuration graphs and the ND Claim 4.4(1) (chapters-3-4
  campaign, phase P4.2; Thm 4.2(iii), `NL ⊆ P` and Ex 4.3 are in `SpaceComplexity.ExpTime`)
- `SpaceComplexity.WindowClock`: the windowed runner (host H3) under a configuration-count
  clock, window containment, and the windowed run of a halting space-bounded computation
  (the space hierarchy's window route; statement gate passed 2026-10-14)
- `SpaceComplexity.Savitch`: Savitch's theorem and `PSPACE = NPSPACE` (phase P4.2)
- `SpaceComplexity.Hierarchy`: the space-bounded universal machine, Thm 4.8,
  `L ⊊ PSPACE`, Ex 3.2 (phase P4.3)
- `SpaceComplexity.Logspace.{InputAccess, PreimageHost, QueryReshape}`: random access to a
  general input (a register-program read fragment; `id` implicitly logspace), the
  oracle-input simulator of Fig. 4.3 (logspace preimages along implicit functions), and the
  query reshapings of composition (phase P4.4b)
- `SpaceComplexity.Logspace.{Reductions, Path, ImmermanSzelepcsenyi, Mult}`: `≤ₗ` and
  Lemma 4.17, `PATH` and Thm 4.18, Thm 4.20 and Cor 4.21, `MULT ∈ L` (phase P4.4)
- `SpaceComplexity.Logspace.{PathWalk, PathWalkMachine, PathWalkProof}`: the
  nondeterministic walk deciding `PATH` (`PATH ∈ NL`, §4.1.2)
- `SpaceComplexity.Codec.{Word, Scan, Valid, Step, Langs, Checks}`: an `O(s + log n)`-bit
  codec for window-bounded configurations of a nondeterministic machine, the four code
  languages (valid, initial, accepting, step) and their word-level checks
- `SpaceComplexity.Codec.{Engine, Regs, Machine, Run, Parse, Layout, Layout2, Deciders,
  StepDecider}`: the four code languages are in `L` (an abstract register machine reading
  its input by index)
- `SpaceComplexity.Codec.Bridge`: acceptance of a space-bounded decider as a chain of codes
- `SpaceComplexity.SavitchARM.{Reach, Machine, Run}`: midpoint reachability over codes; the
  Savitch register machine and its arithmetic and stack routines
- `SpaceComplexity.SavitchARM.{Recursion, Setup, Search, Correct}`: the machine evaluates the
  midpoint recursion with an explicit stack; `NPSPACE ⊆ PSPACE` (Thm 4.14 at polynomial
  bounds, consumed by `PSPACE = NPSPACE` in `SpaceComplexity.Savitch`)
- `SpaceComplexity.SavitchARM.Window`: windows without a known space bound; no reachable
  edge code makes membership midpoint reachability at that radius, and none is reachable beyond
  the space bound (iterative deepening for Thm 4.14 without constructibility, after
  [Sip13, Thm 8.5])
- `SpaceComplexity.SavitchARM.Deepen`: the deepening machine, Savitch's search run as a block
  at radius `1, 2, …`; its contract gives Thm 4.14 for every `S ≥ logSpace`
- `SpaceComplexity.Machines.{MARM, MARMCompile, MARMTime}`: abstract register machines with
  a monotone memory tape, their compilation, and their time bound by configuration counting
  (`marm_dtime`)
- `SpaceComplexity.ExpBFS.{Radius, Machine, Run, Relax, Search, Main}`: reachable codes at
  growing radii; the breadth-first search memory machine;
  `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))` for `S ≥ logSpace`
- `SpaceComplexity.ExpTime`: Thm 4.2(iii), `NL ⊆ P`, Ex 4.3 (moved from
  `SpaceComplexity.ConfigGraph`, after the codec)
- `SpaceComplexity.Logspace.{PathHard, PathHardRegs, PathHardMachine, PathHardWalk,
  PathHardRun, PathHardDecide}`: the configuration-graph reduction to `PATH`, the register
  file and deciders of its query register machine, the machine and its runs; every `NL`
  language logspace-reduces to `PATH` (Thm 4.18, consumed by `PATH_NLComplete` in
  `SpaceComplexity.Logspace.Path`)
- `SpaceComplexity.Logspace.{ISCountMath, ISCountRegs}`: the combinatorics of inductive
  counting (balls, guessed enumerations) and the register file of the counting machine
- `SpaceComplexity.Logspace.ISCountGen{Machine, Walk, Stage, Loop, Radius, Correct}`: the
  window-growing inductive-counting machine; `L ∈ NSPACE S → Lᶜ ∈ NSPACE S` for
  `S ≥ logSpace` (`compl_mem_NSPACE`, consumed by `NSPACE_compl_eq`, Cor 4.21) and its case
  `L ∈ NL → Lᶜ ∈ NL` (`compl_mem_NL`, consumed by `compl_PATH_mem_NL` and `NL_eq_coNL`,
  Thm 4.20)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/
```
