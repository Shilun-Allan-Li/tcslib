## ===== campaign/gates/111-cl1-dedup/pack.md =====

# External audit pack: dedup CL-1, the codec languages' shared lemma and decider wrapper (PR #220, a dedup gate)

## Why this PR

**CL-1** (`campaign/duplication-ledger.md`) concerns the five code languages of
`SpaceComplexity/Codec`: `validLang`, `initLang`, `acceptLang`, `stepLang` and `edgeLang`. Each
had its own membership lemma, its own `_iff` through the word-level check, and its own decider.
Two pieces were repeated across them:
- the decoding of `⟨x, ⟨bits c, bits s⟩⟩` (`pairEncode_inj` twice, then `bits_injective`);
- the decider wrapper (`arm_decides_poly` on `CA`, the `one_run` split, the indicator rewrite and
  the reject branch).

At gate 91 they formed 31 copy pairs, plus 25 more with `edgeLang`.

The user accepted CL-1 as debt on 2026-11-04. On 2026-11-06, with the owner (Hydroxyi) inactive,
the user ruled the **full refactor**:
- **Q1:** add `mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff` and
  `mem_stepLang_iff` (`Iff.rfl`) beside the existing `mem_edgeLang_iff`, so that rule 10 holds
  without unfolding;
- **Q2:** one shared lemma with a generic injective tail; `stepLang_mem` stays outside the
  wrapper, because its run goes through `parse_run₂` with no `one_run` split.

**The PR:** #220 on `lean/dedup-cl1`, head `c4aa5dc0` (full hash in the bundle header). It
consists of `2e9ec6fc` (the shared lemma and characterizations; `Langs`, `Checks`), `533af323`
(the wrapper; `Deciders`), and merges of the campaign. It changes 3 files: 209 lines added, 175
removed (`evidence/landing/cl1.diff`).

## What changed (verify)

**New public declarations:**
- In `Langs`:
  - the four `mem_X_iff`, each `Iff.rfl` with a docstring stating the formula;
  - ```lean
    theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
        {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
        (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
          y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
        (x w : List Bool) (t : τ) :
        pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t
    ```
    The tail is `bits s` for the four triple languages and `⟨w', bits s⟩` for `stepLang`.
- In `Deciders`: `oneCode_mem (hm : mode ≠ .step) … : L ∈ LOGSPACE`. Its hypotheses are:
  - `hL`: the triple characterization;
  - `hP`: the predicate makes `c` a configuration code;
  - `hchk`: the word-level `_iff`;
  - `hval`: the check implies `ValidChk`;
  - `htail`: the mode's tail answers `b` with `Chk x s w ↔ b = true` from `one_run`'s registers.

**Re-proved through them (14 members, statements unchanged):**
- the five `mem_X` (`Langs`);
- the five `X_iff` (`Checks`);
- the four deciders `validLang_mem`, `acceptLang_mem`, `initLang_mem` and `edgeLang_mem`
  (`Deciders`). These keep their own tail and check-to-verdict conversion. Their reject branches
  now read the language through `mem_X_iff`.

**Not changed:**
- `stepLang_mem`, as ruled;
- the shape-uniqueness decodes (`Shape1`/`Shape2`), which decode word against word;
- the `Parse` sites;
- `TQBFHardMachine`'s two decodes, which are outside CL-1. They are recorded in the scope as later
  candidates (`campaign/items/dedup/cl1-SCOPE.md`).

`cfgWord_eq_bits_iff` (`Checks`) is kept, though now unused: it is public and not a copy.

## Known deviations (for the audit)

- **Pre-existing rule-10 reads not in CL-1:** the deciders still unfold `AcceptChk`, `InitChk`
  and `CA`, as at the base (`simp [PreS, CA]`, `rw [AcceptChk]`, `rw [InitChk]`). The read
  `hval := h.1` moved from the old reject branches. `CA` is ledger family MT-1's kind (machine
  tables). The check predicates are to be recorded with it.
- **A small sibling pair within the family:** each step proof needs the three-line reshuffle of
  `stepLang`'s `∃ x c c' s` into the generic tail (`mem_stepLang` with `ℕ × ℕ`, `stepLang_iff`
  with `List Bool × ℕ`).

## Brief for the auditor

1. **The shared lemma and the wrapper:** are they correctly stated and general enough? Do all 14
   members now go through them? Is anything left repeating the decoding or the wrapper skeleton?
2. **Rule 10:** do `Checks` and `Deciders` read the five languages only through the published
   `mem_X_iff`? The seal is below.
3. **Scope:** are the exclusions right (`stepLang_mem`, the shape decodes, `Parse`)?
4. **Public text:** are docstrings, attributions and sketches in place? The files are a
   colleague's.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`, the head against the campaign `e4e7a419`):
  - `Langs`: 12 → 17 public (the four `mem_X_iff` and `mem_codeLang_iff`), with the five `mem_X`
    bodies changed;
  - `Checks`: 31 → 31, with the five `X_iff` bodies changed;
  - `Deciders`: 20 → 21 (`oneCode_mem`), with the four `X_mem` bodies changed.

  No statement changes, and no private declarations added, removed or changed.
- **Rule 10** (`evidence/seal/`): copies of `Checks` and `Deciders` with
  `attribute [local irreducible]` on the five languages. They are elaborated against an overlay in
  which the PR's `Langs` and `Checks` are compiled (`compile-*.out`, exit 0).
  - The controls: an unsealed destructuring of a `validLang` membership succeeds, and the same
    destructuring fails under the seal for each of the five languages (`fail_if_success`).
  - **Both copies give exit 0 and 0 errors.** The only warnings are the controls' unused
    variables.
- **Screen** (`evidence/screen/`, all `Codec` files): the base has 183 declarations, 82 pairs
  and 28,119 characters; the head has 185, 59 and 17,519. **0 new pairs, 23 gone** (the family's
  copies: `mem_stepLang` against the other `mem_X` at 94%, the deciders against each other at
  67–79%, …; `pairdiff.txt`).
- **Lint** (`evidence/lint/`):
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 81 WARN over 112 files at base and head.
  - The policy linter gives 0 findings on the 3 files at both.
- **Replay** (`evidence/merged-tree/`): `replay-lcl2` at `c4aa5dc0` covers the downstream closure
  of the 3 files (60 modules), chained from the campaign snapshot after #216. **60 modules, 0
  failed.** The static check finds 0 mismatches. The 21 `sorry` warnings are `ClassPSPACE/TQBF`'s
  existing ones. #217, #211, #218 and #219 merged afterwards. None of the 3 files imports a module
  they changed in a way that matters, and #220 changes only proof bodies and adds lemmas.
  `Randomized/SpaceAmplifyPolyCode` and `SpaceAmplifyPolyRun` define same-named
  `Randomized.PolyAmp.mem_initLang_iff`/`…acceptLang_iff`/`…stepLang_iff` while opening
  `Complexity.Codec`. Both are in the replay and resolve to their own lemmas.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/111-cl1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `cl1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/111-cl1-dedup/STATUS.md =====

# Gate 111 (#220, dedup CL-1)

- 2026-11-06: #220 opened (the user ruled the full refactor, Q1 (a), Q2 generic tail); `replay-lcl2` (60/0, after #216); freeze, lint, screen (0 new, 23 gone), seal with controls; pack written; staged.

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

**AS-2, implicit `astep` reductions by unification** (gate 105 round 2, finding 1; **acknowledged,
the user, 2026-11-06**). `AReach.step`/`AHalt.step` leave a premise that starts at `astep`, and a
following `change`/`exact` on the concrete continuation reduces it with no `astep` in the text.
Named members: `Logspace/Mult`'s `mult_row_start`, `mult_contribution`, `mult_inner_loop`,
`mult_outer_loop`, `mult_next_column`, `mult_columns_run` and `mult_last_bit`;
`Logspace/QueryReshape`'s `comp_factor_run`, `comp_valid_inner`, `comp_multiply` and
`comp_separator_run`; and `NARMPSem`'s `PSem.of_areach` (`Function.iterate_fixed rfl` at halted
configurations, inside an exclusion). `Mult` crosses one fifth (13/62). **Resolution:** a census by
an `astep` irreducibility seal over every consumer, with controls, then a re-pointing PR after
#214 merges.

**MT-1, machine instruction tables read across files** (gate 105 round 2, finding 2; **acknowledged,
the user, 2026-11-06**). Consumers read a machine's instruction table (`A`, `CA`, …) by
`show A .l = _ from rfl` or `simp [A]` in files other than the table's home: `TQBFARM/Machine`,
`Logspace/PathHardMachine`, `Codec/Machine`, the SavitchARM, ExpBFS, circuit, `CounterProgSimRun`
and `SpaceAmplifyPolyRun` machines. This predates AS-1. `NARMExample`'s `guessValidA` reduces
`NARM.detPart` and should use `NARM.detPart_det`. **Resolution:** per-label instruction equations
(`A_<label>`) published in each machine's own file and the consumers re-pointed, one PR per machine
directory in the dedup window; colleague files mechanical, with an FYI.

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

## ===== campaign/items/dedup/cl1-SCOPE.md =====

# CL-1 scope: the codec languages' sibling idiom

Worktree `/home/user/tcslib-scratch/wt-cl1`, branch `lean/dedup-cl1` at `origin/complexity/arora-barak-ch3-4`
(`f4dfc3f3`). Line numbers are at that base. Paths are relative to `TCSlib/Complexity/`.

**Status: stopped after scope.** The brief's stop rule applies: two deviations from the ledger's
disposition are needed (questions Q1 and Q2 at the end). No Lean file has been edited.

## 1. Members

Closing forms:
- **D3** (decode, triple, at `bits c`): `rintro ⟨x', c', s', h, hC⟩`, then `pairEncode_inj` twice,
  `rw [bits_injective h3, bits_injective h4]`, `exact`; reverse direction `⟨x, c, s, rfl, h⟩`.
- **D3w** (decode, triple, at a word `w`): `rintro ⟨x', c, s', h, …⟩` through the set-builder, then
  `pairEncode_inj` twice (`rfl`, `rfl`), `obtain rfl := bits_injective h4`, `cfgWord_eq_bits_iff`;
  reverse direction `⟨x, cfgCode s C, s, by rw [bits_cfgCode], …⟩`.
- **D4 / D4w**: the same for the quadruple `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`, with `pairEncode_inj`
  three times.
- **W1** (decider wrapper): the `arm_decides_poly (CA N mode) .lenScan codecAs codecAs_mem
  (8 * W N + 8) 1` preamble, `rw [← val_empty]`, `AHalt.mono … gd_mono`, the `one_run` case split,
  the accepting branch (`indicator_eq_of_iff`, `hsh.1`, `X_iff`, `validChk_iff_pre`, `hst`), and the
  reject branch (decode the member, `shape_of_code`, `X_iff.mp`, `validChk_iff_pre`, `hfail`).
- **R10**: the proof reads a `Codec/Langs` definition in another file by definitional unfolding
  (`rintro`/`obtain` through the set-builder, or an anonymous constructor that builds a member).
  Rule 10 forbids this.

| # | Declaration | File:line | Closing form | Reads the language through |
|---|---|---|---|---|
| 1 | `mem_validLang` | `SpaceComplexity/Codec/Langs.lean:117-126` | D3 | home file (allowed) |
| 2 | `mem_initLang` | `Langs.lean:129-138` | D3 | home file |
| 3 | `mem_acceptLang` | `Langs.lean:141-151` | D3 | home file |
| 4 | `mem_stepLang` | `Langs.lean:154-167` | D4 | home file |
| 5 | `mem_edgeLang` | `Langs.lean:172-183` | D3, after `rw [mem_edgeLang_iff]` | `mem_edgeLang_iff` |
| 6 | `validLang_iff` | `SpaceComplexity/Codec/Checks.lean:388-398` | D3w | **R10** (`rintro`, :392; constructor, :398) |
| 7 | `initLang_iff` | `Checks.lean:402-412` | D3w (init form) | **R10** (:406, :412) |
| 8 | `acceptLang_iff` | `Checks.lean:416-426` | D3w | **R10** (:420, :426) |
| 9 | `stepLang_iff` | `Checks.lean:430-444` | D4w | **R10** (:435, :443) |
| 10 | `edgeLang_iff` | `Checks.lean:512-522` | D3w, after `rw [mem_edgeLang_iff]` | `mem_edgeLang_iff` |
| 11 | `validLang_mem` | `SpaceComplexity/Codec/Deciders.lean:198-220` | W1, tail = `AHalt.ret` | **R10** (reject branch :215 `obtain`, :217 constructor) |
| 12 | `acceptLang_mem` | `Deciders.lean:226-248` | W1, tail = `AHalt.ret` | **R10** (:243, :245) |
| 13 | `initLang_mem` | `Deciders.lean:385-416` | W1, tail = `init_tail`, plus the `hyl`/`hs` lines (:392-394) | **R10** (:411, :413) |
| 14 | `edgeLang_mem` | `Deciders.lean:760-788` | W1, tail = `edge_tail`, plus `rw [← orc_eq]` and the same `hyl`/`hs` lines (:768-770) | `mem_edgeLang_iff` (:783) |

The shared pieces already in place are kept: `pairEncode_inj` (`Langs:110`), `mem_edgeLang_iff`
(`Langs:103`), `cfgWord_eq_bits_iff` (`Checks:380`), and in `Deciders` the lemmas
`indicator_eq_of_iff` (:179), `shape_of_code` (:185), `gd_mono` (:72), `val_empty` (:77),
`validChk_iff_pre` (:95) and `one_run` (:107).

The census matches the ledger: `Langs` has 5 membership lemmas (plus the 5 definitions, which stay),
`Checks` has 5 `_iff` lemmas, and `Deciders` has 4 deciders.

## 2. Same closing form, not members (skipped)

| Site | File:line | Why it is skipped |
|---|---|---|
| `stepLang_mem` | `SpaceComplexity/Codec/StepDecider.lean:297-423` | It is not in the ledger's census (`Deciders` 3/16 → 4/22 only). Its run is `parse_run₂`, `layout_run`, `layout2_run`, `insym_run`, `vscan_run` and `step_tail`, with no `one_run` split, so a one-code wrapper does not fit it. It shares only the 3-line preamble and the reject helper `hnon` (:304-312, which is also **R10**: :309, :312). |
| `one_run`'s `huniq` | `Deciders.lean:130-135` | Uniqueness of the `Shape1` decomposition: `pairEncode_inj` twice, then `bits_injective`, word against word. This is not a language membership, so the membership lemma does not serve it. |
| `stepLang_mem`'s `huniq` | `StepDecider.lean:324-330` | The same, for `Shape2` (`pairEncode_inj` three times). |
| `parse_run`, `parse_run₂` | `SpaceComplexity/Codec/Parse.lean:289-292, 325-332, 369, 411-413, 454-458` | `pairEncode_inj` on a shape, then `pairDecode`/`canon`. A different closing; no `bits_injective`. |
| `reflTransGen_stepRel` | `ClassPSPACE/TQBFHardMachine.lean:116-122` | Decodes a `stepLang` member at a word (`obtain … := id hst`, then `pairEncode_inj` three times and `bits_injective` twice). This is **R10** in Seyoon's file, outside `SpaceComplexity` and outside the five languages' declarations. Once Q1 is settled, it is a natural consumer of the shared lemma. |
| `mem_iff_mid` | `TQBFHardMachine.lean:192-199` | Decodes `initLang` and `acceptLang` members at words (D3w twice). **R10**; same remark. |
| `PathHard`, `PathHardDecide` | `SpaceComplexity/Logspace/PathHard.lean:244-251`, `PathHardDecide.lean:174` | Other encodings (`pathRaw`, `qLang`), not the code triple. |

All other consumers of the five languages read them through `mem_initLang`, `mem_acceptLang`,
`mem_stepLang`, `mem_edgeLang`, the `_iff` lemmas or `_mem`: `Bridge`, `SavitchARM/*`, `ExpBFS/*`,
`Logspace/ISCountGen*`, `PathHard*`, `Randomized/SpaceAmplifyPoly*` and `TQBFHardVerifier`. None of
them changes.

## 3. Proposed statements

### 3a. The shared membership lemma (`Codec/Langs`, after `pairEncode_inj`)

```lean
/-- **Membership in a language of encoded triples.** Let `L` be a language whose members are
exactly the encodings `⟨x, ⟨bits c, enc t⟩⟩` with `P x c t`, for an injective encoding `enc` of
the tail. Then, for every word `w`, `⟨x, ⟨w, enc t⟩⟩ ∈ L` exactly when `w` is the binary word of
some `c` with `P x c t`. The code languages are of this shape: tail `bits s` for `validLang`,
`initLang`, `acceptLang` and `edgeLang`, and tail `⟨w', bits s⟩` for `stepLang`.

Configuration-graph infrastructure ([AB09, §4.1.1]); not a result of [AB09].

**Proof sketch.** A member `⟨x', ⟨bits c, enc t'⟩⟩` equal to `⟨x, ⟨w, enc t⟩⟩` has `x' = x` and
`bits c = w` by injectivity of the pairing, in both layers, and `t' = t` by injectivity of `enc`.
Conversely, `⟨x, ⟨bits c, enc t⟩⟩` is a member when `P x c t` holds. -/
theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
    {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
      y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
    (x w : List Bool) (t : τ) :
    pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t
```

The re-proofs would be:
- `mem_X` for the four triple languages: `(mem_codeLang_iff bits_injective hL x (bits c) s)`, then
  `simp only [bits_injective.eq_iff, exists_eq_left]`.
- `mem_stepLang`: the same with `τ := List Bool × ℕ`, `enc t := pairEncode t.1 (bits t.2)`, and
  `P x c t := ∃ c', bits c' = t.1 ∧ …`. Here `hL` is a three-line reshuffle of `stepLang`'s
  `∃ x c c' s`.
- `X_iff` in `Checks`: `rw [chkIff, mem_codeLang_iff bits_injective hL]`, then the word/code
  conversion through `bits_cfgCode` and `cfgWord_eq_bits_iff`. That conversion could go in one
  private helper in `Checks`, for the `∃ C, InWindow ∧ cfgCode = c ∧ R C` shape.

### 3b. The decider wrapper (`Codec/Deciders`, after `shape_of_code`)

```lean
/-- **The decider wrapper of the one-code modes.** Let `L` be a language of encoded triples
`⟨x, ⟨bits c, bits s⟩⟩` with `P x c s`, where `P x c s` makes `c` the code of some configuration.
Let `Chk` be a word-level check that is membership at `⟨x, ⟨w, bits s⟩⟩` and implies the validity
test. Suppose that, in the one-code mode `mode`, the tail of the codec machine after the
validity scan answers `Chk x s w` from the registers `one_run` leaves, on every well-shaped
input that passes the pre-scan checks. Then `L` is in `L` (logspace).

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a result of
[AB09] by itself.

**Proof sketch.** Apply `arm_decides_poly` with the codec machine in mode `mode` and the register
bound `bnd`. In the common run (`one_run`), either the machine reaches the end of the scan, where
the tail answers the check, which is membership; or it rejects, and then no decomposition of the
input passes the pre-scan checks. In that case the input is not a member: a member is well
shaped (`shape_of_code`) and passes the check, hence the validity test and so the pre-scan checks
(`validChk_iff_pre`). -/
theorem oneCode_mem (hm : mode ≠ .step) {L : Language Bool} {P : List Bool → ℕ → ℕ → Prop}
    {Chk : List Bool → ℕ → List Bool → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧ P x c s)
    (hP : ∀ x c s, P x c s → ∃ C : Cfg N.k Bool N.State x, cfgCode s C = c)
    (hchk : ∀ x w s, pairEncode x (pairEncode w (Nat.bits s)) ∈ L ↔ Chk x s w)
    (hval : ∀ x s w, Chk x s w → ValidChk (N := N) x.length s w)
    (htail : ∀ (y x w : List Bool) (s : ℕ) (st : VAd N) (R : Regs), Shape1 y x w s →
      PreChk N x.length s w → s ≤ 2 * y.length → W N * (2 * s + 1) ≤ w.length →
      st.1 = vScan N (w.take (W N * (2 * s + 1))) → R.Bd (bnd N y) →
      R.A = 2 * x.length + 2 → R.S = s → R.T = 0 →
      R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) →
      ∃ b : Bool, (b = true ↔ Chk x s w) ∧
        AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
          (some (.vDone st), R.val, none) b) :
    L ∈ LOGSPACE
```

`htail` is the mode's tail. It returns the existing `AHalt.ret …` for `valid` and `accept`,
`init_tail …` for `init` and `edge_tail …` for `edge`, each with its existing `hind` conversion
(the check against the tail's verdict) as the `b = true ↔ Chk` part. The wrapper takes over the
`hyl`/`hs` lines that `initLang_mem` and `edgeLang_mem` repeat, and the `rw [← orc_eq]`.
`stepLang_mem` stays as it is (§2).

Neither statement adds an import: `Langs` already has `pairEncode`, `bits` and `bits_injective`, and
`Deciders` has everything 3b names. No existing statement or name changes.

## 4. Questions for the user (why I stopped)

**Q1 (blocking): rule 10 needs four more public declarations.** The `_iff` lemmas of `Checks`
(rows 6-9) and the deciders of `Deciders` (rows 11-13) can only use 3a/3b if they can read
`validLang`, `initLang`, `acceptLang` and `stepLang` as sets of encoded tuples. That is the `hL`
hypothesis. Both directions need it:
- the `→` direction of `X_iff` has to rule out a word `w` that is no `bits c`;
- the reject branch has to decompose a member.

`mem_X` (at `bits c`) cannot supply it. Today these files read the definitions by `rintro`, which is
the R10 column. Only `edgeLang` has a published characterization (`mem_edgeLang_iff := Iff.rfl`,
`Langs:103`, the precedent cited by gate 96 F1). A Rule-10-clean re-proof therefore needs, beside
`mem_edgeLang_iff`:
`mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`, `mem_stepLang_iff`
(each `y ∈ X N ↔ <the set-builder body>`, `Iff.rfl`, with a docstring stating the formula). These are
four public declarations beyond the disposition's two, on Hydroxyi's interface. `policy.md` §1
allows them ("definitions that predate the rule … are covered as consumers need them"). Options:
- **(a)** Add the four (recommended). All 14 members are then re-proved and the R10 reads in rows
  6-9 and 11-13 disappear.
- **(b)** Re-point only what is clean without them: rows 1-5, 10 and 14. Leave rows 6-9 and 11-13 at
  their base text, about two thirds of the family.
- **(c)** Re-prove rows 6-9 and 11-13 with `hL := fun _ => Iff.rfl` in `Checks`/`Deciders`. This
  breaks rule 10 in new text, so I would not do it without an explicit waiver.

**Q2: `stepLang` is a quadruple.** The disposition names "one membership lemma for languages of
encoded triples". `stepLang` is `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`, and `stepLang_iff` is at two
words `w`, `w'`. My proposal (3a) keeps one lemma by making the tail generic: an injective `enc`,
with tail `⟨w', bits s⟩` for `stepLang`. The cost is a three-line `hL` reshuffle for `stepLang`.
The alternative is a second, quadruple lemma. Please confirm the generic-tail reading. Also confirm
that `stepLang_mem` stays out of the wrapper, as the census implies: its run has no `one_run` split.

**Q3 (not blocking, for later): sites outside CL-1.** Two items:
- `TQBFHardMachine`'s `reflTransGen_stepRel` and `mem_iff_mid` (Seyoon's file) decode the same tuples
  by R10 reads; with (a) they could be re-pointed to 3a.
- The `Shape1`/`Shape2` uniqueness decodes in `one_run`/`stepLang_mem` repeat the same
  `pairEncode_inj`/`bits_injective` chain on words, which a decoding lemma would serve.

Both are outside the disposition, and I would not touch them in this PR.

## 5. Environment

- The worktree is created and clean; `.lake/packages` is symlinked.
- No olean overlay was made, so there is nothing to remove.
- When I stopped, the replay `oleans-lcamp2` was about 35 of 195 modules in, with no
  `# modules=195 failed=0` line yet.

## ===== campaign/gates/111-cl1-dedup/evidence/freeze/declfreeze-Checks.txt =====

public before/after: 31 31 private before/after: 0 0
public added: []
public removed: []
authorized body change: Complexity.Codec.acceptLang_iff
authorized body change: Complexity.Codec.edgeLang_iff
authorized body change: Complexity.Codec.initLang_iff
authorized body change: Complexity.Codec.stepLang_iff
authorized body change: Complexity.Codec.validLang_iff
private removed: []
private added: []
private changed: []

## ===== campaign/gates/111-cl1-dedup/evidence/freeze/declfreeze-Deciders.txt =====

public before/after: 20 21 private before/after: 2 2
public added: ['Complexity.Codec.oneCode_mem']
public removed: []
authorized body change: Complexity.Codec.acceptLang_mem
authorized body change: Complexity.Codec.edgeLang_mem
authorized body change: Complexity.Codec.initLang_mem
authorized body change: Complexity.Codec.validLang_mem
private removed: []
private added: []
private changed: []

## ===== campaign/gates/111-cl1-dedup/evidence/freeze/declfreeze-Langs.txt =====

public before/after: 12 17 private before/after: 0 0
public added: ['Complexity.Codec.mem_acceptLang_iff', 'Complexity.Codec.mem_codeLang_iff', 'Complexity.Codec.mem_initLang_iff', 'Complexity.Codec.mem_stepLang_iff', 'Complexity.Codec.mem_validLang_iff']
public removed: []
authorized body change: Complexity.Codec.mem_acceptLang
authorized body change: Complexity.Codec.mem_edgeLang
authorized body change: Complexity.Codec.mem_initLang
authorized body change: Complexity.Codec.mem_stepLang
authorized body change: Complexity.Codec.mem_validLang
private removed: []
private added: []
private changed: []

## ===== campaign/gates/111-cl1-dedup/evidence/landing/cl1.diff =====

diff --git a/TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean b/TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean
index b99e6461..a4030d85 100644
--- a/TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean
@@ -387,60 +387,57 @@ variable (N) in
 `validLang` is the validity test of `w`. -/
 theorem validLang_iff (x w : List Bool) (s : ℕ) :
     pairEncode x (pairEncode w (Nat.bits s)) ∈ validLang N ↔ ValidChk (N := N) x.length s w := by
-  rw [validChk_iff]
+  rw [validChk_iff, mem_codeLang_iff bits_injective (mem_validLang_iff N)]
   constructor
-  · rintro ⟨x', c, s', h, C, hC, hc⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
-    obtain rfl := bits_injective h4
-    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc⟩
+  · rintro ⟨c, rfl, C, hC, rfl⟩
+    exact ⟨C, hC, (bits_cfgCode s C).symm⟩
   · rintro ⟨C, hC, rfl⟩
-    exact ⟨x, cfgCode s C, s, by rw [bits_cfgCode], C, hC, rfl⟩
+    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl⟩
 
 variable (N) in
 /-- **Initial codes through the check.** -/
 theorem initLang_iff (x w : List Bool) (s : ℕ) :
     pairEncode x (pairEncode w (Nat.bits s)) ∈ initLang N ↔ InitChk N x s w := by
-  rw [initChk_iff]
+  rw [initChk_iff, mem_codeLang_iff bits_injective (mem_initLang_iff N)]
   constructor
-  · rintro ⟨x', c, s', h, hc⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
-    obtain rfl := bits_injective h4
-    exact ((cfgWord_eq_bits_iff _ _ c).mp hc).symm
+  · rintro ⟨c, rfl, rfl⟩
+    exact bits_cfgCode s _
   · rintro rfl
-    exact ⟨x, cfgCode s (N.tm.initCfg x), s, by rw [bits_cfgCode], rfl⟩
+    exact ⟨cfgCode s (N.tm.initCfg x), bits_cfgCode s _, rfl⟩
 
 variable (N) in
 /-- **Accepting codes through the check.** -/
 theorem acceptLang_iff (x w : List Bool) (s : ℕ) :
     pairEncode x (pairEncode w (Nat.bits s)) ∈ acceptLang N ↔ AcceptChk N x s w := by
-  rw [acceptChk_iff]
+  rw [acceptChk_iff, mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
   constructor
-  · rintro ⟨x', c, s', h, C, hC, hc, hst, hout⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
-    obtain rfl := bits_injective h4
-    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc, hst, hout⟩
+  · rintro ⟨c, rfl, C, hC, rfl, hst, hout⟩
+    exact ⟨C, hC, (bits_cfgCode s C).symm, hst, hout⟩
   · rintro ⟨C, hC, rfl, hst, hout⟩
-    exact ⟨x, cfgCode s C, s, by rw [bits_cfgCode], C, hC, rfl, hst, hout⟩
+    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hst, hout⟩
 
 variable (N) in
 /-- **Step pairs through the check.** -/
 theorem stepLang_iff (x w w' : List Bool) (s : ℕ) :
     pairEncode x (pairEncode w (pairEncode w' (Nat.bits s))) ∈ stepLang N ↔
       StepChk N x s w w' := by
-  rw [stepChk_iff]
+  -- the tail `⟨w', bits s⟩` is the injective image of the pair `(w', s)`
+  have henc : Function.Injective fun t : List Bool × ℕ => pairEncode t.1 (Nat.bits t.2) :=
+    fun _ _ h => Prod.ext (pairEncode_inj h).1 (bits_injective (pairEncode_inj h).2)
+  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : List Bool × ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode t.1 (Nat.bits t.2))) ∧
+      ∃ c', Nat.bits c' = t.1 ∧ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧
+        cfgCode t.2 C = c ∧ ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧
+          Cfg.InWindow t.2 C' ∧ cfgCode t.2 C' = c' := fun y => (mem_stepLang_iff N y).trans
+    ⟨fun ⟨x, c, c', s, h, hP⟩ => ⟨x, c, (Nat.bits c', s), h, c', rfl, hP⟩,
+      fun ⟨x, c, t, h, c', hc', hP⟩ => ⟨x, c, c', t.2, by rw [hc']; exact h, hP⟩⟩
+  rw [stepChk_iff, mem_codeLang_iff henc hL x w (w', s)]
+  dsimp only
   constructor
-  · rintro ⟨x', c, c', s', h, C, hC, hc, C', hstep, hC', hc'⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
-    obtain ⟨rfl, h6⟩ := pairEncode_inj h4
-    obtain rfl := bits_injective h6
-    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc, C', hstep, hC',
-      (cfgWord_eq_bits_iff _ C' c').mp hc'⟩
+  · rintro ⟨c, rfl, c', rfl, C, hC, rfl, C', hstep, hC', rfl⟩
+    exact ⟨C, hC, (bits_cfgCode s C).symm, C', hstep, hC', (bits_cfgCode s C').symm⟩
   · rintro ⟨C, hC, rfl, C', hstep, hC', rfl⟩
-    exact ⟨x, cfgCode s C, cfgCode s C', s, by rw [bits_cfgCode, bits_cfgCode], C, hC, rfl, C',
+    exact ⟨cfgCode s C, bits_cfgCode s C, cfgCode s C', bits_cfgCode s C', C, hC, rfl, C',
       hstep, hC', rfl⟩
 
 /-! ## Edge codes -/
@@ -511,14 +508,11 @@ variable (N) in
 `x`, `w` and `bits s` is in the edge-code language exactly when `w` passes the edge-code check. -/
 theorem edgeLang_iff (x w : List Bool) (s : ℕ) :
     pairEncode x (pairEncode w (Nat.bits s)) ∈ edgeLang N ↔ EdgeChk N x s w := by
-  rw [edgeChk_iff, mem_edgeLang_iff]
+  rw [edgeChk_iff, mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
   constructor
-  · rintro ⟨x', c, s', h, C, hC, hc, hi⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨rfl, h4⟩ := pairEncode_inj h2
-    obtain rfl := bits_injective h4
-    exact ⟨C, hC, (cfgWord_eq_bits_iff _ C c).mp hc, hi⟩
+  · rintro ⟨c, rfl, C, hC, rfl, hi⟩
+    exact ⟨C, hC, (bits_cfgCode s C).symm, hi⟩
   · rintro ⟨C, hC, rfl, hi⟩
-    exact ⟨x, cfgCode s C, s, by rw [bits_cfgCode], C, hC, rfl, hi⟩
+    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hi⟩
 
 end Complexity.Codec
diff --git a/TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean b/TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean
index 7e1d6fd2..4cbb3299 100644
--- a/TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean
@@ -18,7 +18,8 @@ parses (`parse_run`), lays out the code word (`layout_run`), compares the input
 (`le_phase`), scans the chunk region (`vscan_run`), and answers from the scan state — for
 the initial code after testing the input position and the head flag of the middle cell, for an
 edge code after testing, tape by tape, the head flags of the first and last cells.
-`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`.
+`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`, once for all four
+modes in the wrapper `Complexity.Codec.oneCode_mem`, which takes the mode's tail as a hypothesis.
 
 Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
 result of [AB09] by itself.
@@ -31,6 +32,7 @@ result of [AB09] by itself.
 ## Main results
 
 * `Complexity.Codec.one_run` — the common run of the one-code modes.
+* `Complexity.Codec.oneCode_mem` — the decider wrapper of the one-code modes.
 * `Complexity.Codec.init_tail` — the tail of the initial-code mode.
 * `Complexity.Codec.edge_round`, `Complexity.Codec.edge_loop`, `Complexity.Codec.edge_tail` —
   the tail of the edge-code mode.
@@ -189,63 +191,93 @@ lemma shape_of_code {y x : List Bool} {c s : ℕ}
   rw [hy, ← hc, bits_cfgCode]
   exact cfgWord_le_length s C _
 
-/-- **Valid codes form a logspace language** (`Complexity.Codec.validLang`).
-
-**Proof sketch.** `arm_decides_poly` with the codec machine in mode `valid`: on a well-shaped
-input passing the pre-scan checks it answers the scan verdict, which is then membership
-(`validLang_iff`, `validChk_iff_pre`); otherwise it rejects, and the input is no member
-(members are well shaped, `shape_of_code`, and pass all checks). -/
-theorem validLang_mem : validLang N ∈ LOGSPACE := by
-  refine arm_decides_poly (CA N .valid) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
+/-- **The decider wrapper of the one-code modes.** Let `L` be a language of encoded triples
+`⟨x, ⟨bits c, bits s⟩⟩` with `P x c s`, where `P x c s` makes `c` the code of some
+configuration, and let `Chk` be a word-level check that is membership at `⟨x, ⟨w, bits s⟩⟩` and
+implies the validity test. If, in the one-code mode `mode`, the tail of the codec machine after
+the validity scan answers `Chk x s w` from the registers the common run leaves, on every
+well-shaped input passing the pre-scan checks, then `L` is in `L`.
+
+Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a result of
+[AB09] by itself.
+
+**Proof sketch.** `arm_decides_poly` with the codec machine in mode `mode` and the register bound
+`bnd`. By the common run (`one_run`), either the machine reaches the end of the scan, where the
+tail answers the check, which is membership; or it rejects, and then no decomposition of the input
+passes the pre-scan checks, so the input is no member: a member is well shaped
+(`shape_of_code`) and passes the check, hence the validity test and so the pre-scan checks
+(`validChk_iff_pre`). -/
+theorem oneCode_mem (hm : mode ≠ .step) {L : Language Bool} {P : List Bool → ℕ → ℕ → Prop}
+    {Chk : List Bool → ℕ → List Bool → Prop}
+    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c s : ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧ P x c s)
+    (hP : ∀ x c s, P x c s → ∃ C : Cfg N.k Bool N.State x, cfgCode s C = c)
+    (hchk : ∀ x w s, pairEncode x (pairEncode w (Nat.bits s)) ∈ L ↔ Chk x s w)
+    (hval : ∀ x s w, Chk x s w → ValidChk (N := N) x.length s w)
+    (htail : ∀ (y x w : List Bool) (s : ℕ) (st : VAd N) (R : Regs), Shape1 y x w s →
+      PreChk N x.length s w → s ≤ 2 * y.length → W N * (2 * s + 1) ≤ w.length →
+      st.1 = vScan N (w.take (W N * (2 * s + 1))) → R.Bd (bnd N y) →
+      R.A = 2 * x.length + 2 → R.S = s → R.T = 0 →
+      R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) →
+      ∃ b : Bool, (Chk x s w ↔ b = true) ∧
+        AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
+          (some (.vDone st), R.val, none) b) :
+    L ∈ LOGSPACE := by
+  refine arm_decides_poly (CA N mode) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
     fun y => ?_
   rw [← val_empty]
   refine AHalt.mono ?_ (fun a h => gd_mono a h)
-  rcases one_run (N := N) (mode := .valid) (by decide) y with
-    ⟨x, w, s, hsh, hpre, st, R, hst, hR, -, -, -, -, run⟩ | ⟨hfail, hhalt⟩
-  · have hind : MultiTapeTM.indicator (validLang N : Set (List Bool)) y =
-        decide (VAcc N st.1) := by
-      apply indicator_eq_of_iff
-      rw [hsh.1, validLang_iff, validChk_iff_pre, hst]
-      exact ⟨fun h => h.2, fun h => ⟨hpre, h⟩⟩
+  rw [← orc_eq]
+  rcases one_run (N := N) (mode := mode) hm y with
+    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, hPos, run⟩ | ⟨hfail, hhalt⟩
+  · -- the end of the scan: the tail answers the check
+    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
+      rw [hsh.eq, length_pairEncode, length_pairEncode]; ring
+    have hs := s_le_of_width y s (by omega) hsh.width
+    obtain ⟨b, hb, tail⟩ := htail y x w s st R hsh hpre hs (by have := hpre.1; omega) hst hR hA
+      hS hT hPos
+    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = b := by
+      rw [indicator_eq_of_iff (P := b = true) (by rw [hsh.eq, hchk, hb])]
+      cases b <;> rfl
     rw [hind]
-    exact AReach.halt run (AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩)
-  · have hind : MultiTapeTM.indicator (validLang N : Set (List Bool)) y = false := by
+    exact AReach.halt run tail
+  · -- a rejection: members are well shaped and pass the pre-scan checks
+    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = false := by
       rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
       · rfl
-      obtain ⟨x, c, s, hy, C, hC, hc⟩ := h
+      obtain ⟨x, c, s, hy, hPc⟩ := (hL y).mp h
+      obtain ⟨C, hc⟩ := hP x c s hPc
       have hsh := shape_of_code hy C hc
-      have hv := (validLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, C, hC, hc⟩
+      have hv := hval x s _ ((hchk x (Nat.bits c) s).mp (hy ▸ h))
       exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv).1
     rw [hind]
     exact hhalt
 
+/-- **Valid codes form a logspace language** (`Complexity.Codec.validLang`).
+
+**Proof sketch.** The one-code wrapper (`oneCode_mem`) in mode `valid`: the tail answers the
+scan verdict at once, which on inputs passing the pre-scan checks is the validity test
+(`validChk_iff_pre`), i.e. membership (`validLang_iff`). -/
+theorem validLang_mem : validLang N ∈ LOGSPACE := by
+  refine oneCode_mem (mode := .valid) (by decide) (mem_validLang_iff N)
+    (fun _ _ _ ⟨C, _, hc⟩ => ⟨C, hc⟩) (validLang_iff N) (fun _ _ _ h => h) ?_
+  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
+  refine ⟨decide (VAcc N st.1), ?_, AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
+  rw [decide_eq_true_eq, validChk_iff_pre, hst]
+  exact ⟨fun h => h.2, fun h => ⟨hpre, h⟩⟩
+
 /-- **Accepting codes form a logspace language** (`Complexity.Codec.acceptLang`).
 
 **Proof sketch.** As `validLang_mem`, answering the scan verdict together with the header
 `(halted, accept)` (`acceptLang_iff`). -/
 theorem acceptLang_mem : acceptLang N ∈ LOGSPACE := by
-  refine arm_decides_poly (CA N .accept) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
-    fun y => ?_
-  rw [← val_empty]
-  refine AHalt.mono ?_ (fun a h => gd_mono a h)
-  rcases one_run (N := N) (mode := .accept) (by decide) y with
-    ⟨x, w, s, hsh, hpre, st, R, hst, hR, -, -, -, -, run⟩ | ⟨hfail, hhalt⟩
-  · have hind : MultiTapeTM.indicator (acceptLang N : Set (List Bool)) y =
-        decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)) := by
-      apply indicator_eq_of_iff
-      rw [hsh.1, acceptLang_iff, AcceptChk, validChk_iff_pre, hst]
-      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hpre, h.1⟩, h.2⟩⟩
-    rw [hind]
-    exact AReach.halt run (AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩)
-  · have hind : MultiTapeTM.indicator (acceptLang N : Set (List Bool)) y = false := by
-      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
-      · rfl
-      obtain ⟨x, c, s, hy, C, hC, hc, hst, hout⟩ := h
-      have hsh := shape_of_code hy C hc
-      have hv := (acceptLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, C, hC, hc, hst, hout⟩
-      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv.1).1
-    rw [hind]
-    exact hhalt
+  refine oneCode_mem (mode := .accept) (by decide) (mem_acceptLang_iff N)
+    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (acceptLang_iff N) (fun _ _ _ h => h.1) ?_
+  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
+  refine ⟨decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)), ?_,
+    AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
+  rw [decide_eq_true_eq, AcceptChk, validChk_iff_pre, hst]
+  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hpre, h.1⟩, h.2⟩⟩
 
 /-! ## The initial code -/
 
@@ -383,37 +415,16 @@ theorem init_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w
 **Proof sketch.** As `validLang_mem`, with the initial-code tail (`init_tail`) and the
 initial-code check (`initLang_iff`). -/
 theorem initLang_mem : initLang N ∈ LOGSPACE := by
-  refine arm_decides_poly (CA N .init) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
-    fun y => ?_
-  rw [← val_empty]
-  refine AHalt.mono ?_ (fun a h => gd_mono a h)
-  rcases one_run (N := N) (mode := .init) (by decide) y with
-    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, hPos, run⟩ | ⟨hfail, hhalt⟩
-  · have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
-      rw [hsh.1, length_pairEncode, length_pairEncode]; ring
-    have hs := s_le_of_width y s (by omega) hsh.2
-    have hind : MultiTapeTM.indicator (initLang N : Set (List Bool)) y =
-        decide (InitScan N st.1 ∧ R.Pos = 1 ∧
-          (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) := by
-      apply indicator_eq_of_iff
-      rw [hsh.1, initLang_iff, InitChk, validChk_iff_pre, hst, InitScan, hPos]
-      constructor
-      · rintro ⟨⟨-, hv⟩, h2, h3, h4, h5⟩
-        exact ⟨⟨hv, h2, h3⟩, h4, h5⟩
-      · rintro ⟨⟨hv, h2, h3⟩, h4, h5⟩
-        exact ⟨⟨hpre, hv⟩, h2, h3, h4, h5⟩
-    rw [hind]
-    exact AReach.halt run (init_tail y x w (Nat.bits s) hsh.1 R s st hR hA hS hT hs
-      (by have := hpre.1; omega))
-  · have hind : MultiTapeTM.indicator (initLang N : Set (List Bool)) y = false := by
-      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
-      · rfl
-      obtain ⟨x, c, s, hy, hc⟩ := h
-      have hsh := shape_of_code hy (N.tm.initCfg x) hc
-      have hv := (initLang_iff N x (Nat.bits c) s).mp ⟨x, c, s, rfl, hc⟩
-      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv.1).1
-    rw [hind]
-    exact hhalt
+  refine oneCode_mem (mode := .init) (by decide) (mem_initLang_iff N)
+    (fun x _ _ hc => ⟨N.tm.initCfg x, hc⟩) (initLang_iff N) (fun _ _ _ h => h.1) ?_
+  intro y x w s st R hsh hpre hs hw hst hR hA hS hT hPos
+  refine ⟨_, ?_, init_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
+  rw [decide_eq_true_eq, InitChk, validChk_iff_pre, hst, InitScan, hPos]
+  constructor
+  · rintro ⟨⟨-, hv⟩, h2, h3, h4, h5⟩
+    exact ⟨⟨hv, h2, h3⟩, h4, h5⟩
+  · rintro ⟨⟨hv, h2, h3⟩, h4, h5⟩
+    exact ⟨⟨hpre, hv⟩, h2, h3, h4, h5⟩
 
 
 /-! ## Edge codes
@@ -758,33 +769,12 @@ theorem edge_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w
 **Proof sketch.** As `validLang_mem`, with the edge-code tail (`edge_tail`) and the edge-code
 check (`edgeLang_iff`). -/
 theorem edgeLang_mem : edgeLang N ∈ LOGSPACE := by
-  refine arm_decides_poly (CA N .edge) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
-    fun y => ?_
-  rw [← val_empty]
-  refine AHalt.mono ?_ (fun a h => gd_mono a h)
-  rw [← orc_eq]
-  rcases one_run (N := N) (mode := .edge) (by decide) y with
-    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, -, run⟩ | ⟨hfail, hhalt⟩
-  · have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
-      rw [hsh.eq, length_pairEncode, length_pairEncode]; ring
-    have hs := s_le_of_width y s (by omega) hsh.width
-    have hind : MultiTapeTM.indicator (edgeLang N : Set (List Bool)) y =
-        decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
-          w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true) := by
-      apply indicator_eq_of_iff
-      rw [hsh.eq, edgeLang_iff, edgeChk_def, validChk_iff_pre, hst]
-      exact ⟨fun ⟨⟨_, hv⟩, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨⟨hpre, hv⟩, h⟩⟩
-    rw [hind]
-    exact AReach.halt run (edge_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs
-      (by have := hpre.1; omega))
-  · have hind : MultiTapeTM.indicator (edgeLang N : Set (List Bool)) y = false := by
-      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
-      · rfl
-      obtain ⟨x, c, s, hy, C, hC, hc, -⟩ := (mem_edgeLang_iff N y).mp h
-      have hsh := shape_of_code hy C hc
-      have hv := (edgeLang_iff N x (Nat.bits c) s).mp (hy ▸ h)
-      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp ((edgeChk_def N x s _).mp hv).1).1
-    rw [hind]
-    exact hhalt
+  refine oneCode_mem (mode := .edge) (by decide) (mem_edgeLang_iff N)
+    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (edgeLang_iff N)
+    (fun x s w h => ((edgeChk_def N x s w).mp h).1) ?_
+  intro y x w s st R hsh hpre hs hw hst hR hA hS hT _
+  refine ⟨_, ?_, edge_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
+  rw [decide_eq_true_eq, edgeChk_def, validChk_iff_pre, hst]
+  exact ⟨fun ⟨⟨_, hv⟩, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨⟨hpre, hv⟩, h⟩⟩
 
 end Complexity.Codec
diff --git a/TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean b/TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean
index 80233718..5555d7e8 100644
--- a/TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean
@@ -40,6 +40,9 @@ Configuration-graph infrastructure; not a result of [AB09].
 
 ## Main results
 
+* `Complexity.Codec.mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`,
+  `mem_stepLang_iff`, `mem_edgeLang_iff` — the defining equations of the languages.
+* `Complexity.Codec.mem_codeLang_iff` — membership in a language of encoded triples.
 * `Complexity.Codec.mem_validLang`, `mem_initLang`, `mem_acceptLang`, `mem_stepLang`,
   `mem_edgeLang` —
   membership through the codec.
@@ -97,6 +100,40 @@ def edgeLang : Language Bool :=
     ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
       ∃ i, |C.workTapePos i| = (s : ℤ)}
 
+/-- A word is in the valid-code language exactly when it encodes an input `x`, a code `c` and a
+radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the window
+of radius `s`. -/
+lemma mem_validLang_iff (y : List Bool) :
+    y ∈ validLang N ↔ ∃ (x : List Bool) (c s : ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
+      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := Iff.rfl
+
+/-- A word is in the initial-code language exactly when it encodes an input `x`, a code `c` and a
+radius `s` such that `c` is the radius-`s` code of the initial configuration of `N` on `x`. -/
+lemma mem_initLang_iff (y : List Bool) :
+    y ∈ initLang N ↔ ∃ (x : List Bool) (c s : ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
+      cfgCode s (N.tm.initCfg x) = c := Iff.rfl
+
+/-- A word is in the accepting-code language exactly when it encodes an input `x`, a code `c` and
+a radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
+window of radius `s`, is halted and has output exactly `[true]`. -/
+lemma mem_acceptLang_iff (y : List Bool) :
+    y ∈ acceptLang N ↔ ∃ (x : List Bool) (c s : ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
+      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
+        C.output = [true] := Iff.rfl
+
+/-- A word is in the step language exactly when it encodes an input `x`, two codes `c`, `c'` and a
+radius `s` such that `c` and `c'` are the radius-`s` codes of configurations `C`, `C'` on `x` that
+stay in the window of radius `s`, with a configuration-graph edge from `C` to `C'`. -/
+lemma mem_stepLang_iff (y : List Bool) :
+    y ∈ stepLang N ↔ ∃ (x : List Bool) (c c' s : ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∧
+      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
+        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
+          cfgCode s C' = c' := Iff.rfl
+
 /-- A word is in the edge-code language exactly when it encodes an input `x`, a code `c` and a
 radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
 window of radius `s` and has some work head at `-s` or `+s`. -/
@@ -113,42 +150,55 @@ lemma pairEncode_inj {a b a' b' : List Bool} (h : pairEncode a b = pairEncode a'
     (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a', b') from h)
   simpa using this
 
+/-- **Membership in a language of encoded triples.** Let `L` be a language whose members are
+exactly the encodings `⟨x, ⟨bits c, enc t⟩⟩` with `P x c t`, for an injective encoding `enc` of
+the tail. Then for every word `w`, `⟨x, ⟨w, enc t⟩⟩ ∈ L` exactly when `w` is the binary word of
+some `c` with `P x c t`. The code languages are of this shape: with tail `bits s` for
+`validLang`, `initLang`, `acceptLang` and `edgeLang`, and with tail `⟨w', bits s⟩` for
+`stepLang`.
+
+Configuration-graph infrastructure ([AB09, §4.1.1]); not a result of [AB09].
+
+**Proof sketch.** A member `⟨x', ⟨bits c, enc t'⟩⟩` equal to `⟨x, ⟨w, enc t⟩⟩` has `x' = x` and
+`bits c = w` by injectivity of the pairing, in both layers, and `t' = t` by injectivity of `enc`.
+Conversely `⟨x, ⟨bits c, enc t⟩⟩` is a member when `P x c t` holds. -/
+theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
+    {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
+    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
+      y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
+    (x w : List Bool) (t : τ) :
+    pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t := by
+  rw [hL]
+  constructor
+  · rintro ⟨x', c, t', h, hP⟩
+    obtain ⟨rfl, h2⟩ := pairEncode_inj h
+    obtain ⟨hw, ht⟩ := pairEncode_inj h2
+    obtain rfl := henc ht
+    exact ⟨c, hw.symm, hP⟩
+  · rintro ⟨c, rfl, hP⟩
+    exact ⟨x, c, t, rfl, hP⟩
+
 /-- **Membership in the valid-code language.** -/
 theorem mem_validLang (x : List Bool) (c s : ℕ) :
     pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ validLang N ↔
       ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := by
-  constructor
-  · rintro ⟨x', c', s', h, hC⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨h3, h4⟩ := pairEncode_inj h2
-    rw [bits_injective h3, bits_injective h4]
-    exact hC
-  · intro h; exact ⟨x, c, s, rfl, h⟩
+  rw [mem_codeLang_iff bits_injective (mem_validLang_iff N)]
+  simp only [bits_injective.eq_iff, exists_eq_left]
 
 /-- **Membership in the initial-code language.** -/
 theorem mem_initLang (x : List Bool) (c s : ℕ) :
     pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ initLang N ↔
       cfgCode s (N.tm.initCfg x) = c := by
-  constructor
-  · rintro ⟨x', c', s', h, hC⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨h3, h4⟩ := pairEncode_inj h2
-    rw [bits_injective h3, bits_injective h4]
-    exact hC
-  · intro h; exact ⟨x, c, s, rfl, h⟩
+  rw [mem_codeLang_iff bits_injective (mem_initLang_iff N)]
+  simp only [bits_injective.eq_iff, exists_eq_left]
 
 /-- **Membership in the accepting-code language.** -/
 theorem mem_acceptLang (x : List Bool) (c s : ℕ) :
     pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N ↔
       ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
         C.output = [true] := by
-  constructor
-  · rintro ⟨x', c', s', h, hC⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨h3, h4⟩ := pairEncode_inj h2
-    rw [bits_injective h3, bits_injective h4]
-    exact hC
-  · intro h; exact ⟨x, c, s, rfl, h⟩
+  rw [mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
+  simp only [bits_injective.eq_iff, exists_eq_left]
 
 /-- **Membership in the step language.** -/
 theorem mem_stepLang (x : List Bool) (c c' s : ℕ) :
@@ -157,14 +207,20 @@ theorem mem_stepLang (x : List Bool) (c c' s : ℕ) :
       ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
         ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
           cfgCode s C' = c' := by
-  constructor
-  · rintro ⟨x', c₁, c₂, s', h, hC⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨h3, h4⟩ := pairEncode_inj h2
-    obtain ⟨h5, h6⟩ := pairEncode_inj h4
-    rw [bits_injective h3, bits_injective h5, bits_injective h6]
-    exact hC
-  · intro h; exact ⟨x, c, c', s, rfl, h⟩
+  -- the tail `⟨bits c', bits s⟩` is the injective image of the pair `(c', s)`
+  have henc : Function.Injective fun t : ℕ × ℕ => pairEncode (Nat.bits t.1) (Nat.bits t.2) :=
+    fun t t' h => by
+      obtain ⟨h1, h2⟩ := pairEncode_inj h
+      exact Prod.ext (bits_injective h1) (bits_injective h2)
+  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : ℕ × ℕ),
+      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits t.1) (Nat.bits t.2))) ∧
+      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧ cfgCode t.2 C = c ∧
+        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow t.2 C' ∧
+          cfgCode t.2 C' = t.1 := fun y => by
+    rw [mem_stepLang_iff]
+    simp only [Prod.exists]
+  rw [mem_codeLang_iff henc hL x (Nat.bits c) (c', s)]
+  simp only [bits_injective.eq_iff, exists_eq_left]
 
 /-- **Membership in the edge-code language.** The encoding of `x`, `bits c` and `bits s` is in
 the language exactly when `c` is the radius-`s` code of a configuration on `x` inside the window
@@ -173,13 +229,7 @@ theorem mem_edgeLang (x : List Bool) (c s : ℕ) :
     pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ edgeLang N ↔
       ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
         ∃ i, |C.workTapePos i| = (s : ℤ) := by
-  rw [mem_edgeLang_iff]
-  constructor
-  · rintro ⟨x', c', s', h, hC⟩
-    obtain ⟨rfl, h2⟩ := pairEncode_inj h
-    obtain ⟨h3, h4⟩ := pairEncode_inj h2
-    rw [bits_injective h3, bits_injective h4]
-    exact hC
-  · intro h; exact ⟨x, c, s, rfl, h⟩
+  rw [mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
+  simp only [bits_injective.eq_iff, exists_eq_left]
 
 end Complexity.Codec

## ===== campaign/gates/111-cl1-dedup/evidence/lint/campaign-SpaceComplexity-base.txt =====

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

## ===== campaign/gates/111-cl1-dedup/evidence/lint/campaign-SpaceComplexity-head.txt =====

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
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean                   518 lines; 31 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 780 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean                 780 lines; 20 public / 2 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean                   347 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean                    235 lines; 17 public / 0 private declarations
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

## ===== campaign/gates/111-cl1-dedup/evidence/lint/policy-base.txt =====


0 findings in 3 files




## ===== campaign/gates/111-cl1-dedup/evidence/lint/policy-head.txt =====


0 findings in 3 files




## ===== campaign/gates/111-cl1-dedup/evidence/merged-tree/down-lcl2.txt =====

TCSlib/Complexity/SpaceComplexity/Codec/Langs
TCSlib/Complexity/SpaceComplexity/Codec/Checks
TCSlib/Complexity/SpaceComplexity/Codec/Bridge
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine
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
TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/Randomized/UPath
TCSlib/Complexity/Randomized/UPathMachine
TCSlib/Complexity/Randomized/UPathLoops
TCSlib/Complexity/Randomized/UPathParse
TCSlib/Complexity/Randomized/UPathSearch
TCSlib/Complexity/Randomized/UPathWalk
TCSlib/Complexity/Randomized/UPathRL
TCSlib/Complexity/Randomized
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

## ===== campaign/gates/111-cl1-dedup/evidence/merged-tree/replay-lcl2-static.txt =====

modules 60, mismatches 0, static total 21

## ===== campaign/gates/111-cl1-dedup/evidence/merged-tree/replay-lcl2.log =====

# replay-lcl2 at c4aa5dc0: #220, CL-1, on the campaign after #216 (60 modules), fresh .oleans into oleans-lcl2
TCSlib/Complexity/SpaceComplexity/Codec/Langs exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Checks exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Bridge exit=0 errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHardMachine exit=0 errors=0 sorry=0
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
TCSlib/Complexity/SpaceComplexity/Logspace/Path exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPath exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathMachine exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathLoops exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathParse exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathSearch exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathWalk exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathRL exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized exit=0 errors=0 sorry=0
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
# modules=60 failed=0

## ===== campaign/gates/111-cl1-dedup/evidence/merged-tree/replay-lcl2.sh =====

#!/usr/bin/env bash
# Replay lcl2 (#220, CL-1, on the campaign after #216; branch lean/dedup-cl1, stacked on the campaign after #216 (oleans-lcamp3)): its downstream closure (60 modules),
# fresh .oleans into oleans-lcl2, a copy of oleans-lcamp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-cl1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lcl2.txt"
LOG="$S/fills/replay/replay-lcl2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean:a4030d8548f65f58d232382b4ad80309c5a74dd4
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:4cbb3299b77b6e17cfcead37d250adcbdeae0c25
TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean:5555d7e8301cbda531e64f9800ebfb2f725a8c95"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-cl1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD || { echo "precheck: the head must contain the campaign after #216 (oleans-lcamp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #216 (oleans-lcamp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "60" ] || { echo "precheck: the replay list must have 60 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcl2" ] && { echo "precheck: $S/oleans-lcl2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp3" ] || { echo "precheck: oleans-lcamp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp3" "$S/oleans-lcl2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcl2 at $(git rev-parse --short HEAD): #220, CL-1, on the campaign after #216 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcl2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcl2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=60 failed=0" || { echo "replay: a module failed, or the count is not 60" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/111-cl1-dedup/evidence/screen/pairdiff.txt =====

head pairs 59; union of earlier 82; new at head 0; earlier-only 23
  GONE  Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_validLang: 157/167 = 94%
  GONE  Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_initLang: 157/167 = 94%
  GONE  Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_acceptLang: 157/167 = 94%
  GONE  Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::validLang_mem: 622/790 = 79%
  GONE  Deciders.lean::initLang_mem  reproduces  Deciders.lean::validLang_mem: 582/790 = 74%
  GONE  Deciders.lean::initLang_mem  reproduces  Deciders.lean::acceptLang_mem: 632/877 = 72%
  GONE  Langs.lean::mem_validLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
  GONE  Langs.lean::mem_initLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
  GONE  Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
  GONE  Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::acceptLang_mem: 621/877 = 71%
  GONE  Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::initLang_mem: 772/1151 = 67%
  GONE  Deciders.lean::initLang_mem  reproduces  Deciders.lean::edgeLang_mem: 772/1154 = 67%
  GONE  Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_edgeLang: 132/206 = 64%
  GONE  Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_stepLang: 132/221 = 60%
  GONE  Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::initLang_mem: 632/1151 = 55%
  GONE  Deciders.lean::validLang_mem  reproduces  Deciders.lean::edgeLang_mem: 622/1154 = 54%
  GONE  Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::edgeLang_mem: 621/1154 = 54%
  GONE  Checks.lean::stepLang_iff  reproduces  Checks.lean::validLang_iff: 142/264 = 54%
  GONE  Checks.lean::validLang_iff  reproduces  Checks.lean::initLang_iff: 135/260 = 52%
  GONE  Checks.lean::acceptLang_iff  reproduces  Checks.lean::initLang_iff: 134/260 = 52%
  GONE  Checks.lean::initLang_iff  reproduces  Checks.lean::validLang_iff: 135/264 = 51%
  GONE  Deciders.lean::validLang_mem  reproduces  Deciders.lean::initLang_mem: 582/1151 = 51%
  GONE  Checks.lean::edgeLang_iff  reproduces  Checks.lean::initLang_iff: 130/260 = 50%

## ===== campaign/gates/111-cl1-dedup/evidence/screen/screen-base.txt =====

declarations screened: 183; copy pairs (target reproduces >= half of source): 82; reproduced text: 28,119 chars
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_initLang: 167/167 = 100%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_acceptLang: 167/167 = 100%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_validLang: 167/167 = 100%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_acceptLang: 167/167 = 100%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_validLang: 167/167 = 100%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_initLang: 167/167 = 100%
   Valid.lean::ValidChk  reproduces  Deciders.lean::PreChk: 102/102 = 100%
   Langs.lean::edgeLang  reproduces  Langs.lean::validLang: 119/120 = 99%
   Langs.lean::acceptLang  reproduces  Langs.lean::validLang: 119/120 = 99%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_validLang: 165/167 = 99%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_initLang: 165/167 = 99%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_acceptLang: 165/167 = 99%
   Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_validLang: 157/167 = 94%
   Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_initLang: 157/167 = 94%
   Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_acceptLang: 157/167 = 94%
   Valid.lean::cfgWord_pos  reproduces  Valid.lean::cfgWord_take: 76/83 = 92%
   Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::validLang_mem: 714/790 = 90%
   Checks.lean::InitChk  reproduces  Checks.lean::AcceptChk: 63/70 = 90%
   Parse.lean::Shape2  reproduces  Parse.lean::Shape1: 73/82 = 89%
   Run.lean::orc_len  reproduces  Run.lean::orc_bit: 75/87 = 86%
   Valid.lean::validChk_iff  reproduces  Checks.lean::word_split: 341/403 = 85%
   Checks.lean::acceptLang_iff  reproduces  Checks.lean::validLang_iff: 223/264 = 84%
   Checks.lean::edgeLang_iff  reproduces  Checks.lean::validLang_iff: 220/264 = 83%
   Langs.lean::acceptLang  reproduces  Langs.lean::edgeLang: 120/146 = 82%
   Parse.lean::parse_run₂  reproduces  Parse.lean::parse_run: 1615/1970 = 82%
   Langs.lean::validLang  reproduces  Langs.lean::edgeLang: 119/146 = 82%
   Deciders.lean::validLang_mem  reproduces  Deciders.lean::acceptLang_mem: 714/877 = 81%
   Run.lean::s_run  reproduces  Run.lean::v_run: 289/358 = 81%
   Langs.lean::edgeLang  reproduces  Langs.lean::acceptLang: 120/149 = 81%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_edgeLang: 165/206 = 80%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_edgeLang: 165/206 = 80%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_edgeLang: 165/206 = 80%
   Langs.lean::validLang  reproduces  Langs.lean::acceptLang: 119/149 = 80%
   Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::validLang_mem: 622/790 = 79%
   Langs.lean::stepLang  reproduces  Langs.lean::validLang: 92/120 = 77%
   Layout.lean::layout_run  reproduces  Layout2.lean::layout2_run: 4139/5416 = 76%
   Parse.lean::Shape1  reproduces  Parse.lean::Shape2: 73/96 = 76%
   Checks.lean::acceptLang_iff  reproduces  Checks.lean::edgeLang_iff: 226/298 = 76%
   Checks.lean::edgeLang_iff  reproduces  Checks.lean::acceptLang_iff: 226/301 = 75%
   Deciders.lean::PreChk  reproduces  Valid.lean::ValidChk: 102/136 = 75%
   Checks.lean::validLang_iff  reproduces  Checks.lean::acceptLang_iff: 223/301 = 74%
   Checks.lean::validLang_iff  reproduces  Checks.lean::edgeLang_iff: 220/298 = 74%
   Deciders.lean::initLang_mem  reproduces  Deciders.lean::validLang_mem: 582/790 = 74%
   Langs.lean::validLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Langs.lean::edgeLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Langs.lean::acceptLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Word.lean::coreSum_eq_of_cfgWord_eq  reproduces  Valid.lean::cfgWord_take: 60/83 = 72%
   Checks.lean::getD_cfgWord_chunk  reproduces  Valid.lean::cfgWord_take: 60/83 = 72%
   Deciders.lean::initLang_mem  reproduces  Deciders.lean::acceptLang_mem: 632/877 = 72%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_stepLang: 157/221 = 71%
   Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::acceptLang_mem: 621/877 = 71%
   Run.lean::v_run  reproduces  Run.lean::s_run: 289/415 = 70%
   Deciders.lean::edgeLang_mem  reproduces  Deciders.lean::initLang_mem: 772/1151 = 67%
   Deciders.lean::initLang_mem  reproduces  Deciders.lean::edgeLang_mem: 772/1154 = 67%
   Langs.lean::stepLang  reproduces  Langs.lean::edgeLang: 94/146 = 64%
   Langs.lean::mem_stepLang  reproduces  Langs.lean::mem_edgeLang: 132/206 = 64%
   StepDecider.lean::stepLang_mem  reproduces  Deciders.lean::one_run: 1308/2062 = 63%
   Langs.lean::stepLang  reproduces  Langs.lean::acceptLang: 93/149 = 62%
   Layout2.lean::layout2_run  reproduces  Layout.lean::layout_run: 4139/6674 = 62%
   Run.lean::orc_bit  reproduces  Run.lean::orc_len: 75/122 = 61%
   Word.lean::eq_bits_append_replicate  reproduces  Word.lean::bitsVal_lt_two_pow: 67/110 = 61%
   Valid.lean::cfgWord_pos  reproduces  Word.lean::length_cfgWord: 90/148 = 61%
   Checks.lean::StepChk  reproduces  Checks.lean::InitChk: 125/209 = 60%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_stepLang: 132/221 = 60%
   Langs.lean::initLang  reproduces  Langs.lean::validLang: 71/120 = 59%
   StepDecider.lean::step_tail  reproduces  Checks.lean::getD_flatten_block: 81/140 = 58%
   Layout2.lean::layout2_run  reproduces  Checks.lean::getD_flatten_block: 80/140 = 57%
   Layout.lean::layout_run  reproduces  Checks.lean::getD_flatten_block: 80/140 = 57%
   Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::initLang_mem: 632/1151 = 55%
   Deciders.lean::validLang_mem  reproduces  Deciders.lean::edgeLang_mem: 622/1154 = 54%
   Word.lean::length_cfgWord  reproduces  Valid.lean::cfgWord_pos: 90/167 = 54%
   Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::edgeLang_mem: 621/1154 = 54%
   Checks.lean::stepLang_iff  reproduces  Checks.lean::validLang_iff: 142/264 = 54%
   Word.lean::cfgWord_congr  reproduces  Word.lean::cellOf_congr: 70/131 = 53%
   Checks.lean::initChk_iff  reproduces  Checks.lean::acceptChk_iff: 180/346 = 52%
   Checks.lean::validLang_iff  reproduces  Checks.lean::initLang_iff: 135/260 = 52%
   Checks.lean::acceptLang_iff  reproduces  Checks.lean::initLang_iff: 134/260 = 52%
   Checks.lean::initLang_iff  reproduces  Checks.lean::validLang_iff: 135/264 = 51%
   Deciders.lean::validLang_mem  reproduces  Deciders.lean::initLang_mem: 582/1151 = 51%
   Checks.lean::edgeLang_iff  reproduces  Checks.lean::initLang_iff: 130/260 = 50%

## ===== campaign/gates/111-cl1-dedup/evidence/screen/screen-head.txt =====

declarations screened: 185; copy pairs (target reproduces >= half of source): 59; reproduced text: 17,519 chars
   Valid.lean::ValidChk  reproduces  Deciders.lean::PreChk: 102/102 = 100%
   Langs.lean::edgeLang  reproduces  Langs.lean::validLang: 119/120 = 99%
   Langs.lean::acceptLang  reproduces  Langs.lean::validLang: 119/120 = 99%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_initLang: 98/101 = 97%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_initLang: 97/101 = 96%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_initLang: 97/101 = 96%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_acceptLang: 98/103 = 95%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_validLang: 97/102 = 95%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_validLang: 97/102 = 95%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_validLang: 97/102 = 95%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_acceptLang: 97/103 = 94%
   Langs.lean::mem_edgeLang  reproduces  Langs.lean::mem_acceptLang: 97/103 = 94%
   Valid.lean::cfgWord_pos  reproduces  Valid.lean::cfgWord_take: 76/83 = 92%
   Checks.lean::InitChk  reproduces  Checks.lean::AcceptChk: 63/70 = 90%
   Parse.lean::Shape2  reproduces  Parse.lean::Shape1: 73/82 = 89%
   Run.lean::orc_len  reproduces  Run.lean::orc_bit: 75/87 = 86%
   Valid.lean::validChk_iff  reproduces  Checks.lean::word_split: 341/403 = 85%
   Langs.lean::acceptLang  reproduces  Langs.lean::edgeLang: 120/146 = 82%
   Parse.lean::parse_run₂  reproduces  Parse.lean::parse_run: 1615/1970 = 82%
   Langs.lean::validLang  reproduces  Langs.lean::edgeLang: 119/146 = 82%
   Langs.lean::mem_validLang  reproduces  Langs.lean::mem_edgeLang: 97/120 = 81%
   Langs.lean::mem_initLang  reproduces  Langs.lean::mem_edgeLang: 97/120 = 81%
   Langs.lean::mem_acceptLang  reproduces  Langs.lean::mem_edgeLang: 97/120 = 81%
   Run.lean::s_run  reproduces  Run.lean::v_run: 289/358 = 81%
   Langs.lean::edgeLang  reproduces  Langs.lean::acceptLang: 120/149 = 81%
   Langs.lean::validLang  reproduces  Langs.lean::acceptLang: 119/149 = 80%
   Checks.lean::edgeLang_iff  reproduces  Checks.lean::validLang_iff: 160/206 = 78%
   Checks.lean::acceptLang_iff  reproduces  Checks.lean::validLang_iff: 160/206 = 78%
   Langs.lean::stepLang  reproduces  Langs.lean::validLang: 92/120 = 77%
   Layout.lean::layout_run  reproduces  Layout2.lean::layout2_run: 4139/5416 = 76%
   Parse.lean::Shape1  reproduces  Parse.lean::Shape2: 73/96 = 76%
   Deciders.lean::PreChk  reproduces  Valid.lean::ValidChk: 102/136 = 75%
   Checks.lean::acceptLang_iff  reproduces  Checks.lean::edgeLang_iff: 166/222 = 75%
   Langs.lean::validLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Langs.lean::edgeLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Langs.lean::acceptLang  reproduces  Langs.lean::initLang: 71/97 = 73%
   Word.lean::coreSum_eq_of_cfgWord_eq  reproduces  Valid.lean::cfgWord_take: 60/83 = 72%
   Checks.lean::getD_cfgWord_chunk  reproduces  Valid.lean::cfgWord_take: 60/83 = 72%
   Checks.lean::validLang_iff  reproduces  Checks.lean::edgeLang_iff: 160/222 = 72%
   Run.lean::v_run  reproduces  Run.lean::s_run: 289/415 = 70%
   Checks.lean::edgeLang_iff  reproduces  Checks.lean::acceptLang_iff: 166/244 = 68%
   Checks.lean::validLang_iff  reproduces  Checks.lean::acceptLang_iff: 160/244 = 66%
   Langs.lean::stepLang  reproduces  Langs.lean::edgeLang: 94/146 = 64%
   StepDecider.lean::stepLang_mem  reproduces  Deciders.lean::one_run: 1308/2062 = 63%
   Deciders.lean::acceptLang_mem  reproduces  Deciders.lean::validLang_mem: 180/286 = 63%
   Langs.lean::stepLang  reproduces  Langs.lean::acceptLang: 93/149 = 62%
   Layout2.lean::layout2_run  reproduces  Layout.lean::layout_run: 4139/6674 = 62%
   Run.lean::orc_bit  reproduces  Run.lean::orc_len: 75/122 = 61%
   Word.lean::eq_bits_append_replicate  reproduces  Word.lean::bitsVal_lt_two_pow: 67/110 = 61%
   Valid.lean::cfgWord_pos  reproduces  Word.lean::length_cfgWord: 90/148 = 61%
   Checks.lean::StepChk  reproduces  Checks.lean::InitChk: 125/209 = 60%
   Langs.lean::initLang  reproduces  Langs.lean::validLang: 71/120 = 59%
   StepDecider.lean::step_tail  reproduces  Checks.lean::getD_flatten_block: 81/140 = 58%
   Layout2.lean::layout2_run  reproduces  Checks.lean::getD_flatten_block: 80/140 = 57%
   Layout.lean::layout_run  reproduces  Checks.lean::getD_flatten_block: 80/140 = 57%
   Word.lean::length_cfgWord  reproduces  Valid.lean::cfgWord_pos: 90/167 = 54%
   Word.lean::cfgWord_congr  reproduces  Word.lean::cellOf_congr: 70/131 = 53%
   Checks.lean::initChk_iff  reproduces  Checks.lean::acceptChk_iff: 180/346 = 52%
   Deciders.lean::validLang_mem  reproduces  Deciders.lean::acceptLang_mem: 180/354 = 51%

## ===== campaign/gates/111-cl1-dedup/evidence/seal/SealChecks.lean.txt =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Langs
-- unsealed control: the membership destructures
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by
  obtain ⟨x, c, s, -, -⟩ := h
  trivial
attribute [local irreducible] Complexity.Codec.validLang Complexity.Codec.initLang Complexity.Codec.acceptLang Complexity.Codec.stepLang Complexity.Codec.edgeLang
-- sealed controls: the same destructuring fails for each language
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.initLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.acceptLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.stepLang N) : True := by
  fail_if_success obtain ⟨x, c, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.edgeLang N) : True := by
  fail_if_success obtain ⟨x, -⟩ := h
  trivial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word-level checks of the code languages

What the logspace deciders of the five code languages actually test, as predicates on the
code words: the validity test `Complexity.Codec.ValidChk` of
`TCSlib.Complexity.SpaceComplexity.Codec.Valid`, plus

* for the initial code: header `(q₀, empty)`, the initial cell shape, input position `1`,
  and the head flag of tape `0` in the middle cell;
* for an accepting code: header `(halted, accept)`;
* for a step: the second word has the right length and final letter, and for one of the two
  choice bits its input position is the moved one and the sliding check of the two chunk
  regions accepts under the local rule of that bit's action;
* for an edge code: the head flag of some tape is set in the first or the last cell
  (`Complexity.Codec.EdgeChk`).

Each check recognizes exactly the code words of the corresponding configurations, and so
decides membership in the code languages on well-shaped inputs.

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.InitChk`, `Complexity.Codec.AcceptChk`, `Complexity.Codec.StepChk`,
  `Complexity.Codec.EdgeChk`.
* `Complexity.Codec.movePos`, `Complexity.Codec.inpOf`, `Complexity.Codec.aI`,
  `Complexity.Codec.Gs` — the arithmetic and finite data of a step check.

## Main results

* `Complexity.Codec.initChk_iff`, `acceptChk_iff`, `stepChk_iff`, `edgeChk_iff`.
* `Complexity.Codec.validLang_iff`, `initLang_iff`, `acceptLang_iff`, `stepLang_iff`,
  `edgeLang_iff` —
  membership of well-shaped inputs in terms of the checks.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## Reading single letters of a code word -/

/-- Letter `t` of block `j` of a concatenation of fixed-width blocks. -/
lemma getD_flatten_block {α : Type} (L : List (List α)) (w : ℕ)
    (hL : ∀ b ∈ L, b.length = w) (j t : ℕ) (hj : j < L.length) (ht : t < w) (d : α) :
    L.flatten.getD (w * j + t) d = L[j].getD t d := by
  have e := take_drop_flatten L w hL j hj
  rw [← e, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos ht, List.getElem?_drop]

/-- Letter `t` of chunk `j` of a code word is bit `t` of the chunk of cell `j`. -/
lemma getD_cfgWord_chunk (s : ℕ) (C : Cfg N.k Bool N.State x) (j t : ℕ) (hj : j < 2 * s + 1)
    (ht : t < W N) :
    (cfgWord s C).getD (W N * j + t) false = chunkBit N (cellOf s C j) t := by
  have hlt : W N * j + t < W N * (2 * s + 1) := by
    calc W N * j + t < W N * j + W N := by omega
      _ = W N * (j + 1) := by ring
      _ ≤ W N * (2 * s + 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [cfgWord, List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [length_chunksWord]; exact hlt),
    ← List.getD_eq_getElem?_getD]
  unfold chunksWord
  rw [getD_flatten_block _ (W N) (by simp) j t (by simpa using hj) ht]
  simp only [List.getElem_ofFn]
  exact getD_encChunk N _ t ht

/-! ## Initial and accepting codes -/

variable (N) in
/-- **The initial-code check** on a word `w`: valid, header `(q₀, empty)`, every cell of the
initial shape (blank, all heads or none), input position `1`, and (with at least one work
tape) the head of tape `0` flagged in the middle cell `s`. -/
def InitChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (some N.tm.q₀, 0) ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.2.2.2.2 = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) = 1 ∧
    (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)

/-- **The initial-code check recognizes the code of the initial configuration.**

**Proof sketch.** (⇐) Read the header, the initial shape, the position field and the middle
cell off the layout (`vScan_cfgWord`, `cfgWord_pos`, `getD_cfgWord_chunk`). (⇒) The word
is the code of some window-bounded `C` (`validChk_iff`); the header gives the state `q₀` and
the empty output; the initial shape makes every cell blank (and outside the window cells are
blank anyway) and puts all heads in one cell, and the middle-cell flag puts the head of tape
`0`, hence all heads, at position `0`. So `C` has the vertex of the initial configuration,
and codes depend only on the vertex (`cfgWord_congr`). -/
theorem initChk_iff (s : ℕ) (w : List Bool) :
    InitChk N x s w ↔ w = cfgWord s (N.tm.initCfg x) := by
  have hWin : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s
  constructor
  · rintro ⟨hval, hhd, hiok, hpos, hcen⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s C hC
    rw [h1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    obtain ⟨hst, hsum⟩ := hhd
    have hout : C.output = [] := by
      apply (outSummary_eq_empty_iff _).mp
      exact sumIdx_injective (by rw [hsum]; rfl)
    rw [h4, decide_eq_true_eq] at hiok
    rw [cfgWord_pos, bitsVal_padBits] at hpos
    have hblank : ∀ i z, C.workTapes i z = none := by
      intro i z
      by_cases hz : |z| ≤ s
      · have := (hiok (z + s).toNat (by rw [abs_le] at hz; omega)).1 i
        simp only [cellOf] at this
        rwa [show (((z + s).toNat : ℕ) : ℤ) - s = z by rw [abs_le] at hz; omega] at this
      · exact hC.2 i z (not_le.mp hz)
    have hheads : ∀ i, C.workTapePos i = 0 := by
      intro i
      have hk : 0 < N.k := Fin.pos i
      have h0 : C.workTapePos ⟨0, hk⟩ = 0 := by
        rcases hcen with h | h
        · omega
        · have := getD_cfgWord_chunk s C s (hH N + 2) (by omega) (by simp [W]; omega)
          rw [show W N * s + (hH N + 2) = W N * s + (hH N + 2) from rfl, this] at h
          rw [show hH N + 2 = hH N + 3 * (⟨0, hk⟩ : Fin N.k) + 2 by simp,
            chunkBit_tape N _ _ 2 (by omega)] at h
          simpa [cellOf] using h
      have tog := (hiok s (by omega)).2
      simp only [cellOf, sub_self] at tog
      rcases tog with h | h
      · simpa using h i
      · have := h ⟨0, hk⟩
        simp [h0] at this
    have hcore : NDTM.coreSum C = NDTM.coreSum (N.tm.initCfg x) := by
      simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, NDTM.initCfg, Cfg.init, hst, hout,
        Prod.mk.injEq, true_and]
      refine ⟨⟨Fin.ext (by simpa using hpos), funext fun i => funext fun z => hblank i z,
        funext hheads⟩, trivial⟩
    exact cfgWord_congr hcore
  · rintro rfl
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s (N.tm.initCfg x) hWin
    refine ⟨(validChk_iff x s _).mpr ⟨_, hWin, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [h1]; simp [NDTM.initCfg, Cfg.init, outSummary, sumIdx]
    · rw [h4, decide_eq_true_eq]
      intro j hj
      refine ⟨fun i => by simp [cellOf, NDTM.initCfg, Cfg.init], ?_⟩
      by_cases hjs : (j : ℤ) - s = 0
      · left; intro i; simp [cellOf, NDTM.initCfg, Cfg.init, hjs]
      · right; intro i; simp [cellOf, NDTM.initCfg, Cfg.init]; omega
    · rw [cfgWord_pos, bitsVal_padBits]; rfl
    · by_cases hk : N.k = 0
      · exact Or.inl hk
      · right
        have hk' : 0 < N.k := Nat.pos_of_ne_zero hk
        rw [getD_cfgWord_chunk s _ s (hH N + 2) (by omega) (by simp [W]; omega),
          show hH N + 2 = hH N + 3 * (⟨0, hk'⟩ : Fin N.k) + 2 by simp,
          chunkBit_tape N _ _ 2 (by omega)]
        simp [cellOf, NDTM.initCfg, Cfg.init]

variable (N) in
/-- **The accepting-code check** on a word `w`: valid with header `(halted, accept)`. -/
def AcceptChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (none, 1)

/-- **The accepting-code check recognizes the codes of accepting configurations.**

**Proof sketch.** The header of a code word is the state and the summary index
(`vScan_cfgWord`); summary index `1` is the summary `accept`, i.e. output `[true]`
(`outSummary_eq_accept_iff`). -/
theorem acceptChk_iff (s : ℕ) (w : List Bool) :
    AcceptChk N x s w ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      C.state = none ∧ C.output = [true] := by
  constructor
  · rintro ⟨hval, hhd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    rw [(vScan_cfgWord s C hC).1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    refine ⟨C, hC, rfl, hhd.1, (outSummary_eq_accept_iff _).mp ?_⟩
    exact sumIdx_injective (by rw [hhd.2]; rfl)
  · rintro ⟨C, hC, rfl, hst, hout⟩
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, ?_⟩
    rw [(vScan_cfgWord s C hC).1, hst, hout]
    rfl

/-! ## Steps -/

/-- The input position after a move, clamped to `[0, n + 1]`: the arithmetic of
`Turing.moveInputPos`. -/
def movePos (n p : ℕ) : SignType → ℕ
  | .zero => p
  | .pos => if p = n + 1 then p else p + 1
  | .neg => p - 1

/-- `movePos` is the value of the clamped move. -/
lemma val_moveInputPos {n : ℕ} (p : Fin (n + 2)) (mv : SignType) :
    (moveInputPos p mv).val = movePos n p.val mv := by
  have := p.isLt
  cases mv with
  | zero => simp [moveInputPos_zero, movePos]
  | pos =>
    simp only [movePos, moveInputPos, SignType.pos_eq_one, SignType.coe_one]
    split_ifs with h1 h2 h2 <;> simp_all <;> omega
  | neg =>
    simp only [movePos, moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg,
      SignType.coe_one]
    split_ifs with h1 <;> simp_all <;> omega

/-- The input symbol at position `p` (shifted by one; blank at both ends). -/
def inpOf (x : List Bool) (p : ℕ) : Option Bool :=
  if p = 0 ∨ p = x.length + 1 then none else some (x.getD (p - 1) false)

/-- The input symbol of a configuration is `inpOf` of its input position. -/
lemma inputSymbol_eq (C : Cfg N.k Bool N.State x) : C.inputSymbol = inpOf x C.inputPos.val := by
  have := C.inputPos.isLt
  unfold Cfg.inputSymbol inpOf
  by_cases h0 : C.inputPos = 0
  · simp [h0]
  · by_cases h1 : C.inputPos.val = x.length + 1
    · have : C.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h1
      simp [this]
    · have hv : C.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      rw [dif_neg h0, dif_neg h1, if_neg (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show C.inputPos.val - 1 <
        x.length by omega)]

variable (N) in
/-- The finite data a step check needs: the validity-scan state of the first word and the
input symbol under its input head. -/
abbrev SInfo := VSt N × Option Bool

set_option synthInstance.maxSize 1000 in
/-- Step data are finitely many. -/
instance SInfo.instFintype : Fintype (SInfo N) := inferInstance

set_option synthInstance.maxSize 1000 in
/-- Step data have decidable equality. -/
instance SInfo.instDecidableEq : DecidableEq (SInfo N) := inferInstance

/-- The header recorded by a validity scan (a default if none). -/
def hdOfV (st : VSt N) : Hd N := st.2.1.getD (none, 0)

variable (N) in
/-- The action of a step under the choice bit `b`, from the step data. -/
def aI (I : SInfo N) (b : Bool) : Action N.k Bool N.State :=
  effAct N (hdOfV I.1).1 I.2 I.1.2.2.2.1 b

variable (N) in
/-- The local rule of a step under the choice bit `b`, from the step data. -/
def Gs (I : SInfo N) (b : Bool) : SX N → SX N → SX N → SX N :=
  stepG (aI N I b) (newHd (aI N I b) (hdOfV I.1))

variable (N) in
/-- **The step check** on words `w`, `w'`: `w` is valid; `w'` has the code length and final
letter `1`; and for one choice bit `b`, the input position of `w'` is that of `w` moved by
`b`'s action, and the sliding check of the chunk regions under `b`'s local rule accepts. -/
def StepChk (x : List Bool) (s : ℕ) (w w' : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧ w'.length = W N * (2 * s + 1) + wP x.length + 1 ∧
    w'.getD (W N * (2 * s + 1) + wP x.length) false = true ∧
    ∃ b : Bool,
      bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)) =
        movePos x.length (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))
          (aI N (vScan N (w.take (W N * (2 * s + 1))),
            inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b).inputTape ∧
      sDone N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
          inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b)
        ((if b then Prod.snd else Prod.fst)
          (sScan N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) false)
            (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) true)
            (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))))) = true

/-- A word of length `a + b + 1` ending with `1` splits into its first `a` letters, the next
`b`, and the final `1`. -/
lemma word_split (w : List Bool) (a b : ℕ) (hlen : w.length = a + b + 1)
    (hlast : w.getD (a + b) false = true) :
    w = w.take a ++ (w.drop a).take b ++ [true] := by
  have htail : w.drop (a + b) = [true] := by
    have hl : (w.drop (a + b)).length = 1 := by simp; omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hl
    rw [hc]
    have h0 := congrArg (fun l : List Bool => l[0]?) hc
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    rw [List.getD_eq_getElem?_getD, h0] at hlast
    simp only [Option.getD_some] at hlast
    rw [hlast]
  rw [← htail, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- A component of the double sliding scan, by the choice bit. -/
lemma sScan_sel (G : Bool → SX N → SX N → SX N → SX N) (u u' : List Bool) (m : ℕ)
    (hu : u.length = W N * m) (hu' : u'.length = W N * m) (b : Bool) :
    (if b then Prod.snd else Prod.fst) (sScan N (G false) (G true) u u') =
      (List.zip (blocksD N u m) (blocksD N u' m)).foldl (slStep (G b)) (sInit N) := by
  rw [sScan_eq (G false) (G true) u u' m hu hu']
  cases b <;> rfl

/-- The step data of a code word: the action and local rule they determine are those of the
coded configuration. -/
lemma aI_cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : Cfg.InWindow s C) (b : Bool) :
    aI N (vScan N ((cfgWord s C).take (W N * (2 * s + 1))),
        inpOf x (bitsVal (((cfgWord s C).drop (W N * (2 * s + 1))).take (wP x.length)))) b =
      effAct N C.state C.inputSymbol C.workTapeSymbols b ∧
    hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
  obtain ⟨h1, -, h3, -⟩ := vScan_cfgWord s C hC
  have hhd : hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
    simp only [hdOfV, h1, Option.getD_some, hdOf]
  refine ⟨?_, hhd⟩
  simp only [aI, hhd, hdOf, cfgWord_pos, bitsVal_padBits, ← inputSymbol_eq]
  congr 1
  funext i
  exact h3 i

/-- **The step check recognizes code words of configuration-graph edges.**

**Proof sketch.** Both directions go through the coded configuration `C` of the first word
(`validChk_iff`), whose scan data determine the action of each choice bit (`aI_cfgWord`).
For a choice bit `b`, with `C' = stepWith b C` (`stepWith_eq_apply`): the sliding check of
`b` accepts iff the chunk region of the second word is that of `C'` and `C'` is
window-bounded (`sScan_sel`, `sDone_step`); the input position of `C'` is the moved one
(`val_moveInputPos`), and a position field is determined by its value (`eq_padBits`); with
the length and the final letter (`word_split`), the second word is the code word of `C'`. -/
theorem stepChk_iff (s : ℕ) (w w' : List Bool) :
    StepChk N x s w w' ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧ cfgWord s C' = w' := by
  constructor
  · rintro ⟨hval, hlen', hlast', b, hpos', hsd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    have hA' : (w'.take (W N * (2 * s + 1))).length = W N * (2 * s + 1) := by
      simp only [List.length_take]; omega
    rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1) (by simp [length_cfgWord]; omega) hA'] at hsd
    simp only [Gs] at hsd
    rw [ha, hhd, cfgWord_take] at hsd
    obtain ⟨hcells, hwin'⟩ := (sDone_step s C hC a _ hA').mp hsd
    refine ⟨C, hC, rfl, a.apply C, ⟨b, stepWith_eq_apply b C⟩, hwin', ?_⟩
    rw [word_split w' (W N * (2 * s + 1)) (wP x.length) hlen' hlast', hcells]
    simp only [cfgWord]
    congr 2
    have hP : ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length := by
      simp only [List.length_take, List.length_drop]; omega
    rw [eq_padBits ((w'.drop (W N * (2 * s + 1))).take (wP x.length)), hP, hpos', ha]
    simp only [cfgWord_pos, bitsVal_padBits]
    rw [← val_moveInputPos]
    rfl
  · rintro ⟨C, hC, rfl, C', ⟨b, hstep⟩, hC', rfl⟩
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    rw [stepWith_eq_apply] at hstep
    subst hstep
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, length_cfgWord s _, cfgWord_last s _, b, ?_, ?_⟩
    · rw [ha, cfgWord_pos, bitsVal_padBits, cfgWord_pos, bitsVal_padBits]
      exact val_moveInputPos _ _
    · have hA' : ((cfgWord s (a.apply C)).take (W N * (2 * s + 1))).length =
          W N * (2 * s + 1) := by simp only [List.length_take, length_cfgWord]; omega
      rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1)
        (by simp only [List.length_take, length_cfgWord]; omega) hA']
      simp only [Gs]
      rw [ha, hhd]
      simp only [cfgWord_take]
      exact (sDone_step s C hC a _ (length_chunksWord N _ _)).mpr ⟨rfl, hC'⟩

/-! ## Membership through the checks -/

/-- The code word of a configuration is the binary word of its code; a word equal to a code
word is the binary word of a number. -/
lemma cfgWord_eq_bits_iff (s : ℕ) (C : Cfg N.k Bool N.State x) (c : ℕ) :
    cfgCode s C = c ↔ cfgWord s C = Nat.bits c := by
  rw [← bits_cfgCode]
  exact ⟨fun h => h ▸ rfl, fun h => bits_injective h⟩

variable (N) in
/-- **Valid codes through the check**: on `⟨x, ⟨w, bits s⟩⟩` with any word `w`, membership in
`validLang` is the validity test of `w`. -/
theorem validLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ validLang N ↔ ValidChk (N := N) x.length s w := by
  rw [validChk_iff, mem_codeLang_iff bits_injective (mem_validLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl⟩

variable (N) in
/-- **Initial codes through the check.** -/
theorem initLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ initLang N ↔ InitChk N x s w := by
  rw [initChk_iff, mem_codeLang_iff bits_injective (mem_initLang_iff N)]
  constructor
  · rintro ⟨c, rfl, rfl⟩
    exact bits_cfgCode s _
  · rintro rfl
    exact ⟨cfgCode s (N.tm.initCfg x), bits_cfgCode s _, rfl⟩

variable (N) in
/-- **Accepting codes through the check.** -/
theorem acceptLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ acceptLang N ↔ AcceptChk N x s w := by
  rw [acceptChk_iff, mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl, hst, hout⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, hst, hout⟩
  · rintro ⟨C, hC, rfl, hst, hout⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hst, hout⟩

variable (N) in
/-- **Step pairs through the check.** -/
theorem stepLang_iff (x w w' : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (pairEncode w' (Nat.bits s))) ∈ stepLang N ↔
      StepChk N x s w w' := by
  -- the tail `⟨w', bits s⟩` is the injective image of the pair `(w', s)`
  have henc : Function.Injective fun t : List Bool × ℕ => pairEncode t.1 (Nat.bits t.2) :=
    fun _ _ h => Prod.ext (pairEncode_inj h).1 (bits_injective (pairEncode_inj h).2)
  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : List Bool × ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode t.1 (Nat.bits t.2))) ∧
      ∃ c', Nat.bits c' = t.1 ∧ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧
        cfgCode t.2 C = c ∧ ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧
          Cfg.InWindow t.2 C' ∧ cfgCode t.2 C' = c' := fun y => (mem_stepLang_iff N y).trans
    ⟨fun ⟨x, c, c', s, h, hP⟩ => ⟨x, c, (Nat.bits c', s), h, c', rfl, hP⟩,
      fun ⟨x, c, t, h, c', hc', hP⟩ => ⟨x, c, c', t.2, by rw [hc']; exact h, hP⟩⟩
  rw [stepChk_iff, mem_codeLang_iff henc hL x w (w', s)]
  dsimp only
  constructor
  · rintro ⟨c, rfl, c', rfl, C, hC, rfl, C', hstep, hC', rfl⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, C', hstep, hC', (bits_cfgCode s C').symm⟩
  · rintro ⟨C, hC, rfl, C', hstep, hC', rfl⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, cfgCode s C', bits_cfgCode s C', C, hC, rfl, C',
      hstep, hC', rfl⟩

/-! ## Edge codes -/

variable (N) in
/-- **The edge-code check** on a word `w`: valid, and some tape `i` has its head flag set in the
first cell (work position `-s`) or in the last (work position `s`). -/
def EdgeChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
      w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true

variable (N) in
/-- The edge-code check holds of a word `w` exactly when `w` passes the validity check at radius
`s` for inputs of length `|x|` and, for some work tape `i`, tape `i`'s head flag is set in chunk
`0` or in chunk `2s` of `w`, the cells at `-s` and `+s`. -/
lemma edgeChk_def (x : List Bool) (s : ℕ) (w : List Bool) :
    EdgeChk N x s w ↔ ValidChk (N := N) x.length s w ∧
      ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true := Iff.rfl

/-- The head flag of tape `i` in cell `j` of a code word: letter `hH + 3i + 2` of chunk `j` is
set exactly when the head of tape `i` is at work position `j - s`. -/
lemma getD_cfgWord_head (s : ℕ) (C : Cfg N.k Bool N.State x) (j : ℕ) (hj : j < 2 * s + 1)
    (i : Fin N.k) :
    (cfgWord s C).getD (W N * j + (hH N + 3 * (i : ℕ) + 2)) false =
      decide (C.workTapePos i = (j : ℤ) - s) := by
  have hi : hH N + 3 * (i : ℕ) + 2 < W N := by have := i.isLt; rw [W_eq]; omega
  rw [getD_cfgWord_chunk s C j _ hj hi, chunkBit_tape N _ i 2 (by omega), if_neg (by omega),
    if_neg (by omega), cellOf_head]

/-- **The edge-code check recognizes the codes with a head on the window's boundary.**

**Proof sketch.** A valid word is the code word of a window-bounded `C` (`validChk_iff`). Its
letter `hH + 3i + 2` of chunk `j` is the head flag of tape `i` at work position `j - s`
(`getD_cfgWord_head`). Chunk `0` is position `-s`, chunk `2s` is position `s`, and `|p| = s`
exactly when `p = -s` or `p = s`. -/
theorem edgeChk_iff (s : ℕ) (w : List Bool) :
    EdgeChk N x s w ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      ∃ i, |C.workTapePos i| = (s : ℤ) := by
  have h0 : ∀ (C : Cfg N.k Bool N.State x) (i : Fin N.k),
      (cfgWord s C).getD (hH N + 3 * (i : ℕ) + 2) false =
        decide (C.workTapePos i = -(s : ℤ)) := by
    intro C i
    have := getD_cfgWord_head s C 0 (by omega) i
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [this]; congr 1; simp
  have h2 : ∀ (C : Cfg N.k Bool N.State x) (i : Fin N.k),
      (cfgWord s C).getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false =
        decide (C.workTapePos i = (s : ℤ)) := by
    intro C i
    rw [getD_cfgWord_head s C (2 * s) (by omega) i]; congr 1; push_cast; ring_nf
  constructor
  · rintro ⟨hval, i, hi⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    refine ⟨C, hC, rfl, i, ?_⟩
    rw [h0, h2, decide_eq_true_eq, decide_eq_true_eq] at hi
    rcases hi with h | h <;> rw [h] <;> simp
  · rintro ⟨C, hC, rfl, i, hi⟩
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, i, ?_⟩
    rw [h0, h2, decide_eq_true_eq, decide_eq_true_eq]
    rcases (abs_eq (by positivity)).mp hi with h | h
    · exact Or.inr h
    · exact Or.inl h

variable (N) in
/-- **Edge codes through the check.** For every word `w`, not only for codes, the encoding of
`x`, `w` and `bits s` is in the edge-code language exactly when `w` passes the edge-code check. -/
theorem edgeLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ edgeLang N ↔ EdgeChk N x s w := by
  rw [edgeChk_iff, mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl, hi⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, hi⟩
  · rintro ⟨C, hC, rfl, hi⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hi⟩

end Complexity.Codec

## ===== campaign/gates/111-cl1-dedup/evidence/seal/SealDeciders.lean.txt =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Layout
-- unsealed control: the membership destructures
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by
  obtain ⟨x, c, s, -, -⟩ := h
  trivial
attribute [local irreducible] Complexity.Codec.validLang Complexity.Codec.initLang Complexity.Codec.acceptLang Complexity.Codec.stepLang Complexity.Codec.edgeLang
-- sealed controls: the same destructuring fails for each language
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.initLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.acceptLang N) : True := by
  fail_if_success obtain ⟨x, c, s, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.stepLang N) : True := by
  fail_if_success obtain ⟨x, c, -, -⟩ := h
  trivial
example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.edgeLang N) : True := by
  fail_if_success obtain ⟨x, -⟩ := h
  trivial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The one-code languages are logspace

The codec machine `Complexity.Codec.CA` in the modes `valid`, `accept`, `init`, `edge` decides
the languages `Complexity.Codec.validLang N`, `acceptLang N`, `initLang N`, `edgeLang N`: it
parses (`parse_run`), lays out the code word (`layout_run`), compares the input position
(`le_phase`), scans the chunk region (`vscan_run`), and answers from the scan state — for
the initial code after testing the input position and the head flag of the middle cell, for an
edge code after testing, tape by tape, the head flags of the first and last cells.
`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`, once for all four
modes in the wrapper `Complexity.Codec.oneCode_mem`, which takes the mode's tail as a hypothesis.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.PreChk` — the checks done before the scan.
* `Complexity.Codec.InitScan` — the scan-state part of the initial-code test.

## Main results

* `Complexity.Codec.one_run` — the common run of the one-code modes.
* `Complexity.Codec.oneCode_mem` — the decider wrapper of the one-code modes.
* `Complexity.Codec.init_tail` — the tail of the initial-code mode.
* `Complexity.Codec.edge_round`, `Complexity.Codec.edge_loop`, `Complexity.Codec.edge_tail` —
  the tail of the edge-code mode.
* `Complexity.Codec.validLang_mem`, `Complexity.Codec.acceptLang_mem`,
  `Complexity.Codec.initLang_mem`, `Complexity.Codec.edgeLang_mem` — the four languages are in
  `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {mode : CMode}

/-! ## Members are well shaped -/

/-- A code at radius `s` is longer than `s`, so a well-formed input `⟨x, ⟨bits c, bits s⟩⟩`
with `c` a code passes the width check of its radius field. -/
lemma width_of_code {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (y : List Bool)
    (hy : (cfgWord s C).length ≤ y.length) :
    (Nat.bits s).length ≤ (Nat.bits y.length).length := by
  apply length_bits_mono
  have := length_cfgWord s C
  have hW : 1 ≤ W N := by simp [W]
  have : 2 * s + 1 ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_left _ hW
  omega

/-- The input length is at least the code word's. -/
lemma cfgWord_le_length {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (rest : List Bool) :
    (cfgWord s C).length ≤ (pairEncode x (pairEncode (cfgWord s C) rest)).length := by
  simp [length_pairEncode]; omega

/-- The register bound in the form of `arm_decides_poly`. -/
lemma gd_mono {y : List Bool} (a : AConf 21 (Lab N)) (h : GuardLe (CA N mode) y (bnd N y) a) :
    PreS (CA N mode) y a ∧ ∀ r, a.2.1 r ≤ (8 * W N + 8) * (y.length + 1) ^ 1 := by
  simpa [bnd] using h

/-- The empty register file is the zero valuation. -/
lemma val_empty : ({} : Regs).val = fun _ => 0 := by
  funext r; fin_cases r <;> rfl

/-- The radius of a well-shaped input is at most twice the input length. -/
lemma s_le_of_width (y : List Bool) (s : ℕ) (hy : 1 ≤ y.length)
    (h : (Nat.bits s).length ≤ (Nat.bits y.length).length) : s ≤ 2 * y.length := by
  have h1 := bitsVal_le_of_width (Nat.bits s) y.length hy h 0
  simpa [bitsVal_bits] using h1

/-! ## The common run of the one-code modes -/

variable (N) in
/-- The checks done before the scan: the length, the final letter, and the input position. -/
def PreChk (n s : ℕ) (w : List Bool) : Prop :=
  w.length = W N * (2 * s + 1) + wP n + 1 ∧ w.getD (W N * (2 * s + 1) + wP n) false = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1

/-- The validity test is the pre-scan checks and the scan verdict. -/
lemma validChk_iff_pre (n s : ℕ) (w : List Bool) :
    ValidChk (N := N) n s w ↔ PreChk N n s w ∧ VAcc N (vScan N (w.take (W N * (2 * s + 1)))) := by
  unfold ValidChk PreChk
  tauto

/-- **The common run of the one-code modes**: on a well-shaped input passing the pre-scan
checks the machine reaches the end of the validity scan, with the scan state of the chunk
region and the layout in its registers; otherwise it rejects, and then no decomposition of
the input passes the pre-scan checks.

**Proof sketch.** `parse_run`, `layout_run`, `le_phase`, `vscan_run` in sequence; each
rejection is matched with the failed shape or check. -/
theorem one_run (hm : mode ≠ .step) (y : List Bool) :
    (∃ (x w : List Bool) (s : ℕ), Shape1 y x w s ∧ PreChk N x.length s w ∧
      ∃ (st : VAd N) (R : Regs), st.1 = vScan N (w.take (W N * (2 * s + 1))) ∧
        R.Bd (bnd N y) ∧ R.A = 2 * x.length + 2 ∧ R.S = s ∧ R.T = 0 ∧
        R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) ∧
        Reach N mode y (bnd N y) .lenScan ({} : Regs).val (.vDone st) R.val) ∨
    ((∀ x w s, Shape1 y x w s → ¬ PreChk N x.length s w) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
        (some .lenScan, ({} : Regs).val, none)
        false) := by
  set B := bnd N y
  rcases parse_run (N := N) hm y with ⟨x, w, s, q1, cap, hsh, hq1, hcap, r1⟩ | ⟨hno, hhalt⟩
  · obtain ⟨hy, hwid⟩ := hsh
    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hy, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hwid
    have hbig := bnd_ge (N := N) y s hs
    have hlink : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
    have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    set R1 : Regs := { L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
                       Q1 := q1, Cap := cap, Q2 := 2 * x.length + 2 * w.length + 4, S := s }
    have hR1 : R1.Bd B := by simp only [R1, Regs.Bd]; omega
    -- uniqueness of the decomposition
    have huniq : ∀ x' w' s', Shape1 y x' w' s' → x' = x ∧ w' = w ∧ s' = s := by
      rintro x' w' s' ⟨hy', -⟩
      rw [hy] at hy'
      obtain ⟨h1, h2⟩ := pairEncode_inj hy'
      obtain ⟨h3, h4⟩ := pairEncode_inj h2
      exact ⟨h1.symm, h3.symm, (bits_injective h4).symm⟩
    rcases layout_run (N := N) (mode := mode) y x w (Nat.bits s) hy R1 s hR1 rfl rfl rfl hs rfl
      rfl rfl rfl rfl rfl rfl (by simp [R1, hm]) with ⟨hlen, hterm, r2⟩ | ⟨hbad, hhalt⟩
    · set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
      set R2 := layR N R1 x.length s pos
      have hpos_lt : pos < 2 * (x.length + 1) := by
        have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
        have h2 : 2 ^ ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
            2 * (x.length + 1) := by
          rw [show ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
            simp; omega]
          exact two_pow_bits_le _ (by omega)
        omega
      have hwP := wP_le x.length
      have hR2 : R2.Bd B := by simp only [R2, R1, layR, Regs.Bd]; omega
      obtain ⟨hle, hgt⟩ := le_phase (N := N) (mode := mode) y R2 hR2 (by simp [R2, R1, layR])
      by_cases hp : pos ≤ x.length + 1
      · left
        have r3 := hle (by simpa [R2, R1, layR] using hp)
        rw [if_neg hm] at r3
        obtain ⟨st, hst, r4⟩ := vscan_run (N := N) (mode := mode) y x w (Nat.bits s) hy R2 s hR2
          (by simp [R2, R1, layR]) (by simp [R2, layR]) (by omega)
        refine ⟨x, w, s, ⟨hy, hwid⟩, ⟨hlen, hterm, hp⟩, st, _, hst, ?_, ?_, ?_, ?_, ?_,
          r1.trans (r2.trans (r3.trans r4))⟩
        · simp only [R2, R1, layR, Regs.Bd]; omega
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, layR, pos]
      · right
        refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt (r1.trans r2) (hgt (by
          simpa [R2, R1, layR] using hp))⟩
        obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
        exact hp hpre.2.2
    · right
      refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt r1 hhalt⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
      exact hbad ⟨hpre.1, hpre.2.1⟩
  · right
    exact ⟨fun x w s h => absurd ⟨x, w, s, h⟩ hno, hhalt⟩

/-! ## Valid and accepting codes -/

/-- An indicator through a decidable characterization. -/
lemma indicator_eq_of_iff {L : Language Bool} {y : List Bool} {P : Prop} [Decidable P]
    (h : y ∈ L ↔ P) : MultiTapeTM.indicator (L : Set (List Bool)) y = decide P := by
  rw [indicator_eq_decide]
  exact decide_eq_decide.mpr h

/-- Members of the one-code languages are well shaped. -/
lemma shape_of_code {y x : List Bool} {c s : ℕ}
    (hy : y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)))
    (C : Cfg N.k Bool N.State x) (hc : cfgCode s C = c) : Shape1 y x (Nat.bits c) s := by
  refine ⟨hy, width_of_code s C y ?_⟩
  rw [hy, ← hc, bits_cfgCode]
  exact cfgWord_le_length s C _

/-- **The decider wrapper of the one-code modes.** Let `L` be a language of encoded triples
`⟨x, ⟨bits c, bits s⟩⟩` with `P x c s`, where `P x c s` makes `c` the code of some
configuration, and let `Chk` be a word-level check that is membership at `⟨x, ⟨w, bits s⟩⟩` and
implies the validity test. If, in the one-code mode `mode`, the tail of the codec machine after
the validity scan answers `Chk x s w` from the registers the common run leaves, on every
well-shaped input passing the pre-scan checks, then `L` is in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a result of
[AB09] by itself.

**Proof sketch.** `arm_decides_poly` with the codec machine in mode `mode` and the register bound
`bnd`. By the common run (`one_run`), either the machine reaches the end of the scan, where the
tail answers the check, which is membership; or it rejects, and then no decomposition of the input
passes the pre-scan checks, so the input is no member: a member is well shaped
(`shape_of_code`) and passes the check, hence the validity test and so the pre-scan checks
(`validChk_iff_pre`). -/
theorem oneCode_mem (hm : mode ≠ .step) {L : Language Bool} {P : List Bool → ℕ → ℕ → Prop}
    {Chk : List Bool → ℕ → List Bool → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧ P x c s)
    (hP : ∀ x c s, P x c s → ∃ C : Cfg N.k Bool N.State x, cfgCode s C = c)
    (hchk : ∀ x w s, pairEncode x (pairEncode w (Nat.bits s)) ∈ L ↔ Chk x s w)
    (hval : ∀ x s w, Chk x s w → ValidChk (N := N) x.length s w)
    (htail : ∀ (y x w : List Bool) (s : ℕ) (st : VAd N) (R : Regs), Shape1 y x w s →
      PreChk N x.length s w → s ≤ 2 * y.length → W N * (2 * s + 1) ≤ w.length →
      st.1 = vScan N (w.take (W N * (2 * s + 1))) → R.Bd (bnd N y) →
      R.A = 2 * x.length + 2 → R.S = s → R.T = 0 →
      R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) →
      ∃ b : Bool, (Chk x s w ↔ b = true) ∧
        AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
          (some (.vDone st), R.val, none) b) :
    L ∈ LOGSPACE := by
  refine arm_decides_poly (CA N mode) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rw [← orc_eq]
  rcases one_run (N := N) (mode := mode) hm y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, hPos, run⟩ | ⟨hfail, hhalt⟩
  · -- the end of the scan: the tail answers the check
    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hsh.eq, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hsh.width
    obtain ⟨b, hb, tail⟩ := htail y x w s st R hsh hpre hs (by have := hpre.1; omega) hst hR hA
      hS hT hPos
    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = b := by
      rw [indicator_eq_of_iff (P := b = true) (by rw [hsh.eq, hchk, hb])]
      cases b <;> rfl
    rw [hind]
    exact AReach.halt run tail
  · -- a rejection: members are well shaped and pass the pre-scan checks
    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, hPc⟩ := (hL y).mp h
      obtain ⟨C, hc⟩ := hP x c s hPc
      have hsh := shape_of_code hy C hc
      have hv := hval x s _ ((hchk x (Nat.bits c) s).mp (hy ▸ h))
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv).1
    rw [hind]
    exact hhalt

/-- **Valid codes form a logspace language** (`Complexity.Codec.validLang`).

**Proof sketch.** The one-code wrapper (`oneCode_mem`) in mode `valid`: the tail answers the
scan verdict at once, which on inputs passing the pre-scan checks is the validity test
(`validChk_iff_pre`), i.e. membership (`validLang_iff`). -/
theorem validLang_mem : validLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .valid) (by decide) (mem_validLang_iff N)
    (fun _ _ _ ⟨C, _, hc⟩ => ⟨C, hc⟩) (validLang_iff N) (fun _ _ _ h => h) ?_
  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
  refine ⟨decide (VAcc N st.1), ?_, AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
  rw [decide_eq_true_eq, validChk_iff_pre, hst]
  exact ⟨fun h => h.2, fun h => ⟨hpre, h⟩⟩

/-- **Accepting codes form a logspace language** (`Complexity.Codec.acceptLang`).

**Proof sketch.** As `validLang_mem`, answering the scan verdict together with the header
`(halted, accept)` (`acceptLang_iff`). -/
theorem acceptLang_mem : acceptLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .accept) (by decide) (mem_acceptLang_iff N)
    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (acceptLang_iff N) (fun _ _ _ h => h.1) ?_
  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
  refine ⟨decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)), ?_,
    AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
  rw [decide_eq_true_eq, AcceptChk, validChk_iff_pre, hst]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hpre, h.1⟩, h.2⟩⟩

/-! ## The initial code -/

variable (N) in
/-- The scan-state part of the initial-code test. -/
def InitScan (st : VSt N) : Prop :=
  VAcc N st ∧ st.2.1 = some (some N.tm.q₀, 0) ∧ st.2.2.2.2.2 = true

instance (st : VSt N) : Decidable (InitScan N st) := by unfold InitScan; infer_instance

/-- **The tail of the initial-code mode**: after the scan, test the scan state, the input
position (`= 1`) and, with work tapes, the head flag of tape `0` in the middle cell.

**Proof sketch.** A finite branch on the scan state; two zero tests around one decrement for
the position; for the middle cell, the address `a + 2(W s + hH + 2)` is computed by a copy, a
scale and an increment chain, and read through the bit oracle (`getD_w`). -/
theorem init_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .init) orc y (GuardLe (CA N .init) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true))) := by
  set B := bnd N y
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
  -- answering from a label whose instruction is `ret`
  have hret : ∀ (l : Lab N) (v : Fin 21 → ℕ) (b : Bool), (∀ r, v r ≤ B) →
      CA N .init l = .ret b →
        AHalt (CA N .init) orc y (GuardLe (CA N .init) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  have hv0 := hBd.val_le
  by_cases hscan : InitScan N st.1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hscan]]
    have r1 : Reach N .init y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
        (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
    exact AReach.halt r1 (hret _ _ _ hv0 rfl)
  have r1 : Reach N .init y B (.vDone st) R.val .iz1 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
      (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
  by_cases hp0 : R.Pos = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp0]]
    have r2 : Reach N .init y B .iz1 R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
    exact AReach.halt (r1.trans r2) (hret _ _ _ hv0 rfl)
  have r2 : Reach N .init y B .iz1 R.val .iz2 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
  have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
  have r3 : Reach N .init y B .iz2 R.val .iz3 ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA])
  by_cases hp1 : R.Pos = 1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp1]]
    have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .rej
        ({R with Pos := R.Pos - 1} : Regs).val :=
      Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
        (by simp [astep, CA]; omega)
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le rfl)
  have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .icen
      ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA]; omega)
  set R1 : Regs := {R with Pos := R.Pos - 1}
  by_cases hk : N.k = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = true by simp [hscan, hp1, hk]]
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le (by simp [CA, hk]))
  -- the middle cell
  have hkpos : 1 ≤ N.k := Nat.one_le_iff_ne_zero.mpr hk
  have hWh : hH N + 3 ≤ W N := by simp [W]; omega
  have hidx : W N * s + (hH N + 2) < W N * (2 * s + 1) := by
    have : W N * (2 * s + 1) = W N * s + W N * s + W N := by ring
    have : 0 ≤ W N * s := Nat.zero_le _
    omega
  have hAB : R.A ≤ y.length := by rw [hA]; omega
  have r5 : Reach N .init y B .icen R1.val .clrUc R1.val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA, hk, goto])) (by simp [astep, CA, hk, goto])
  have r6 : Reach N .init y B .clrUc R1.val (.cp .Uc) ({R1 with U := 0} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA])
  have r7 : Reach N .init y B (.cp .Uc) ({R1 with U := 0} : Regs).val (.cp .Tsc)
      ({R1 with U := R.A} : Regs).val :=
    Reach.cast (cp_run y B .Uc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc, R1])
  have r8 : Reach N .init y B (.cp .Tsc) ({R1 with U := R.A} : Regs).val (.sc .C)
      ({R1 with U := R.A, T := s} : Regs).val :=
    Reach.cast (cp_run y B .Tsc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, R1, hT])) (by simp [cpDst, cpSrc, R1, hS])
  have hscl : R.A + 2 * W N * s + 2 * (hH N + 2) ≤ B := by
    have : 2 * W N * s + 2 * (hH N + 2) ≤ 2 * (W N * (2 * s + 1)) := by
      have : 2 * W N * s = 2 * (W N * s) := by ring
      omega
    omega
  have r9 : Reach N .init y B (.sc .C) ({R1 with U := R.A, T := s} : Regs).val (icL N .C 0)
      ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val :=
    Reach.cast (sc_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor, R1]; omega)) (by simp [scDst, scSrc, scFactor, R1])
  have r10 : Reach N .init y B (icL N .C 0) ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val
      .cenRead ({R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0} : Regs).val :=
    Reach.cast (ic_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [icReg, icCount, R1]; omega)) (by simp [icReg, icCount, R1])
  set R2 : Regs := {R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0}
  have hR2 : R2.Bd B := by simp only [R2, R1, Regs.Bd]; omega
  have hbit : y.getD (R.A + 2 * W N * s + 2 * (hH N + 2)) false =
      w.getD (W N * s + (hH N + 2)) false := by
    rw [hA, show 2 * x.length + 2 + 2 * W N * s + 2 * (hH N + 2) =
      2 * x.length + 2 + 2 * (W N * s + (hH N + 2)) by ring, hy, getD_w _ _ _ _ (by omega)]
  rw [List.getD_eq_getElem?_getD] at hbit
  rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
      (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) =
      w.getD (W N * s + (hH N + 2)) false by
    rw [List.getD_eq_getElem?_getD]; simp [hscan, hp1, hk]]
  rw [List.getD_eq_getElem?_getD]
  cases hb : (w[W N * s + (hH N + 2)]?).getD false
  · have r11 : Reach N .init y B .cenRead R2.val .rej R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)
  · have r11 : Reach N .init y B .cenRead R2.val .acc R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)

/-- **The initial code forms a logspace language** (`Complexity.Codec.initLang`).

**Proof sketch.** As `validLang_mem`, with the initial-code tail (`init_tail`) and the
initial-code check (`initLang_iff`). -/
theorem initLang_mem : initLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .init) (by decide) (mem_initLang_iff N)
    (fun x _ _ hc => ⟨N.tm.initCfg x, hc⟩) (initLang_iff N) (fun _ _ _ h => h.1) ?_
  intro y x w s st R hsh hpre hs hw hst hR hA hS hT hPos
  refine ⟨_, ?_, init_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
  rw [decide_eq_true_eq, InitChk, validChk_iff_pre, hst, InitScan, hPos]
  constructor
  · rintro ⟨⟨-, hv⟩, h2, h3, h4, h5⟩
    exact ⟨⟨hv, h2, h3⟩, h4, h5⟩
  · rintro ⟨⟨hv, h2, h3⟩, h4, h5⟩
    exact ⟨⟨hpre, hv⟩, h2, h3, h4, h5⟩


/-! ## Edge codes

The edge-code mode reads, tape by tape, the head flags of the first and last cells of the chunk
region. Its run is proved from the table equations of `CA` at its labels (`CA_eRd1`, …), the
step equations of `astep` and the published loop runs, without unfolding `CA` or `astep`. -/

section Edge

variable (N) in
/-- The syntactic preconditions an instruction of the edge tail meets: distinct registers in an
equality test, distinct call arguments, and no input comparison. -/
private def EdgeOK : Ins 21 2 (Lab N) → Prop
  | .jeq r s _ _ => r ≠ s
  | .call _ _ args _ _ => args.Nodup
  | .jeqIn _ _ _ => False
  | .jeqFst _ _ _ => False
  | .jeqSnd _ _ _ => False
  | _ => True

variable {y : List Bool} {B : ℕ}

/-- The guard at a label of the edge tail, from its instruction's table equation. -/
private lemma edge_gd {l : Lab N} {v : Fin 21 → ℕ} (hv : ∀ r, v r ≤ B) {i : Ins 21 2 (Lab N)}
    (hl : CA N .edge l = i) (hi : EdgeOK N i) : GuardLe (CA N .edge) y B (some l, v, none) := by
  subst hl
  refine gd_of hv (preS_of_ins ?_ ?_ ?_ ?_ ?_)
  · intro r s l₁ l₀ h; rw [h] at hi; exact hi
  · intro j md args l₁ l₀ h; rw [h] at hi; exact hi
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim

/-- **One round of the edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape
`i` in the first cell, `Q3 = q + 1` and `T = 0`, the machine answers `true` if tape `i`'s flag is
set in the first or the last cell, and otherwise reaches `eTest` with `Q3 = q` and the other
registers it reads unchanged.

**Proof sketch.** Read the flag at `U` (`orc_bit`, `getD_w`); on `1` answer `true`. Otherwise copy
`U` to `Q1`, add `4W · s` (copy `S` to `T`, then the scale loop) and read the flag of the last cell;
on `1` answer `true`. Otherwise count `Q3` down. -/
theorem edge_round (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B)
    (i : ℕ) (hi : i < N.k) (q : ℕ) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hS : v rS = s) (hT : v rT = 0)
    (hU : v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2)) (hQ : v rQ3 = q + 1) :
    ((w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none) true) ∧
    (¬ (w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      ∃ v', Reach N .edge y B .eRd1 v .eTest v' ∧ (∀ r, v' r ≤ B) ∧
        v' rS = s ∧ v' rT = 0 ∧ v' rU = v rU ∧ v' rQ3 = q) := by
  have hW0 : hH N + 3 * i + 2 < W N := by rw [W_eq]; omega
  have hWs : W N * (2 * s + 1) = W N * (2 * s) + W N := by ring
  -- the flag of tape `i` in the first cell
  have hidx0 : hH N + 3 * i + 2 < w.length := by
    have : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hbit0 : y.getD (v rU) false = w.getD (hH N + 3 * i + 2) false := by
    rw [hU, hy]; exact getD_w x w rest _ hidx0
  have e1 : astep (CA N .edge) orc y (some .eRd1, v, none) =
      (some (if w.getD (hH N + 3 * i + 2) false = true then .acc else .eFar), v, none) := by
    rw [astep_call (CA_eRd1 .edge)]; simp only [vword_whole₁, orc_bit, hbit0]
  have hg1 : GuardLe (CA N .edge) y B (some .eRd1, v, none) :=
    edge_gd hv (CA_eRd1 .edge) (by simp [EdgeOK])
  have r1 : ¬ w.getD (hH N + 3 * i + 2) false = true → Reach N .edge y B .eRd1 v .eFar v :=
    fun h => Reach.single' hg1 (by rw [e1, if_neg h])
  -- the address of the flag in the last cell: `Q1 := U + 4W · s`
  set v1 := Function.update v rQ1 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rQ1 _ _ hv (Nat.zero_le _)
  have r2 : Reach N .edge y B .eFar v (.cp .Qe) v1 :=
    Reach.single' (edge_gd hv (CA_eFar .edge) trivial) (astep_clr (CA_eFar .edge))
  have h1U : v1 rU = v rU := by rw [hv1, Function.update_of_ne (by decide)]
  have h1Q : v1 rQ1 = 0 := by rw [hv1, Function.update_self]
  set v2 := Function.update v1 rQ1 (v rU) with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rQ1 _ _ hv1B (hv rU)
  have r3 : Reach N .edge y B (.cp .Qe) v1 (.cp .Te) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Qe v1 hv1B
      (by rw [cpDst_Qe, cpSrc_Qe, h1Q]; exact Nat.zero_le _)
    rwa [cpNext_Qe, cpDst_Qe, cpSrc_Qe, h1U] at h
  have h2T : v2 rT = 0 := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hT]
  have h2S : v2 rS = s := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hS]
  set v3 := Function.update v2 rT s with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rT _ _ hv2B hsB
  have r4 : Reach N .edge y B (.cp .Te) v2 (.sc .Ee) v3 := by
    have h := cp_run (N := N) (mode := .edge) y B .Te v2 hv2B
      (by rw [cpDst_Te, cpSrc_Te, h2T]; exact Nat.zero_le _)
    rwa [cpNext_Te, cpDst_Te, cpSrc_Te, h2S] at h
  have h3T : v3 rT = s := by rw [hv3, Function.update_self]
  have h3Q : v3 rQ1 = v rU := by
    rw [hv3, Function.update_of_ne (by decide), hv2, Function.update_self]
  have hfar : v rU + 4 * W N * s ≤ B := by
    have : 4 * W N * s = 2 * (W N * (2 * s)) := by ring
    omega
  set v4 := Function.update (Function.update v3 rT 0) rQ1 (v rU + 4 * W N * s) with hv4
  have hv4B : ∀ r, v4 r ≤ B :=
    register_update_le _ rQ1 _ _ (register_update_le _ rT _ _ hv3B (Nat.zero_le _)) hfar
  have r5 : Reach N .edge y B (.sc .Ee) v3 .eRd2 v4 := by
    have h := sc_run (N := N) (mode := .edge) y B .Ee v3 hv3B
      (by rw [scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T]; exact hfar)
    rwa [scNext_Ee, scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T] at h
  -- the flag of tape `i` in the last cell
  have h4Q : v4 rQ1 = v rU + 4 * W N * s := by rw [hv4, Function.update_self]
  have hidx1 : W N * (2 * s) + (hH N + 3 * i + 2) < w.length := by omega
  have hbit1 : y.getD (v4 rQ1) false =
      w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false := by
    rw [h4Q, hU, hy, show 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) + 4 * W N * s =
      2 * x.length + 2 + 2 * (W N * (2 * s) + (hH N + 3 * i + 2)) by ring]
    exact getD_w x w rest _ hidx1
  have e2 : astep (CA N .edge) orc y (some .eRd2, v4, none) =
      (some (if w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true then .acc else .eNext),
        v4, none) := by
    rw [astep_call (CA_eRd2 .edge)]; simp only [vword_whole₁, orc_bit, hbit1]
  have hg2 : GuardLe (CA N .edge) y B (some .eRd2, v4, none) :=
    edge_gd hv4B (CA_eRd2 .edge) (by simp [EdgeOK])
  -- count the tape down
  set v5 := Function.update v4 rQ3 (v4 rQ3 - 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B :=
    register_update_le _ rQ3 _ _ hv4B (le_trans (Nat.sub_le _ _) (hv4B rQ3))
  have r6 : Reach N .edge y B .eNext v4 .eTest v5 :=
    Reach.single' (edge_gd hv4B (CA_eNext .edge) trivial) (astep_dec (CA_eNext .edge))
  constructor
  · intro hP
    by_cases hb0 : w.getD (hH N + 3 * i + 2) false = true
    · refine AHalt.step hg1 ?_
      rw [e1, if_pos hb0]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv (CA_acc .edge) trivial)
    · have hb1 := hP.resolve_left hb0
      refine AReach.halt ((r1 hb0).trans (r2.trans (r3.trans (r4.trans r5)))) (AHalt.step hg2 ?_)
      rw [e2, if_pos hb1]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv4B (CA_acc .edge) trivial)
  · intro hP
    rw [not_or] at hP
    refine ⟨v5, (r1 hP.1).trans (r2.trans (r3.trans (r4.trans (r5.trans
      ((Reach.single' hg2 (by rw [e2, if_neg hP.2])).trans r6))))), hv5B, ?_, ?_, ?_, ?_⟩
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), h2S]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_self]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), hv2,
        Function.update_of_ne (by decide), h1U]
    · have h4Q3 : v4 rQ3 = q + 1 := by
        rw [hv4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hv3,
          Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
          Function.update_of_ne (by decide), hQ]
      rw [hv5, Function.update_self, h4Q3, Nat.add_sub_cancel]

/-- **The edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape `i` in the
first cell, `Q3 = k - i` and `T = 0`, the machine answers whether some tape `i' ≥ i` has its head
flag set in the first or the last cell of the chunk region.

**Proof sketch.** Induction on `k - i`, one tape per round (`edge_round`). After a round without
a set flag, `Q3` is tested: at `0` there is no further tape and the machine answers `false`;
otherwise `U` advances by `6` (two increment chains of `3`) to the next tape. -/
theorem edge_loop (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B) :
    ∀ m (i : ℕ) (v : Fin 21 → ℕ), i + (m + 1) = N.k → (∀ r, v r ≤ B) →
      v rS = s → v rT = 0 → v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) →
      v rQ3 = m + 1 →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none)
        (decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ := edge_round x w rest hy s hw hB hsB i (by omega) 0 v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, -, -, -, hQ'⟩ := hno hP
      rw [decide_eq_false (by
        rintro ⟨i', hle, hP'⟩
        have hi' : (i' : ℕ) = i := by have := i'.isLt; omega
        rw [hi'] at hP'
        exact hP hP')]
      refine AReach.halt r (AHalt.step (edge_gd hv'B (CA_eTest .edge) trivial) ?_)
      rw [astep_jz (CA_eTest .edge), if_pos hQ']
      exact AHalt.ret (CA_rej .edge) (edge_gd hv'B (CA_rej .edge) trivial)
  | succ m ih =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ :=
      edge_round x w rest hy s hw hB hsB i (by omega) (m + 1) v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, hS', hT', hU', hQ'⟩ := hno hP
      have r7 : Reach N .edge y B .eTest v' (icL N .S1 0) v' :=
        Reach.single' (edge_gd hv'B (CA_eTest .edge) trivial)
          (by rw [astep_jz (CA_eTest .edge), if_neg (by omega)])
      have hW1 : hH N + 3 * (i + 1) + 2 < W N := by rw [W_eq]; omega
      have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have hU6 : v' rU + 6 ≤ B := by omega
      set v6 := Function.update v' rU (v' rU + 3) with hv6
      have hv6B : ∀ r, v6 r ≤ B := register_update_le _ rU _ _ hv'B (by omega)
      have r8 : Reach N .edge y B (icL N .S1 0) v' (icL N .S2 0) v6 := by
        have h := ic_run (N := N) (mode := .edge) y B .S1 v' hv'B
          (by rw [icReg_S1, icCount_S1]; omega)
        rwa [icNext_S1, icReg_S1, icCount_S1, ← icL_zero] at h
      have h6U : v6 rU = v' rU + 3 := by rw [hv6, Function.update_self]
      set v7 := Function.update v6 rU (v6 rU + 3) with hv7
      have hv7B : ∀ r, v7 r ≤ B := register_update_le _ rU _ _ hv6B (by omega)
      have r9 : Reach N .edge y B (icL N .S2 0) v6 .eRd1 v7 := by
        have h := ic_run (N := N) (mode := .edge) y B .S2 v6 hv6B
          (by rw [icReg_S2, icCount_S2]; omega)
        rwa [icNext_S2, icReg_S2, icCount_S2] at h
      have h7 := ih (i + 1) v7 (by omega) hv7B
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hS'])
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hT'])
        (by rw [hv7, Function.update_self, h6U, hU', hU]; ring)
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hQ'])
      have hans : decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) =
          decide (∃ i' : Fin N.k, i + 1 ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) := by
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨i', hle, hP'⟩
          refine ⟨i', ?_, hP'⟩
          rcases Nat.lt_or_ge i (i' : ℕ) with h | h
          · omega
          · have hi' : (i' : ℕ) = i := by omega
            rw [hi'] at hP'
            exact absurd hP' hP
        · rintro ⟨i', hle, hP'⟩
          exact ⟨i', by omega, hP'⟩
      rw [hans]
      exact AReach.halt (r.trans (r7.trans (r8.trans r9))) h7

end Edge


/-- **The tail of the edge-code mode**: after the scan, test the scan state and, tape by tape,
the head flags of the first and last cells.

**Proof sketch.** A finite branch on the scan state (`CA_vDone_edge`). Without work tapes the
machine answers `false`. Otherwise it sets `U` to the address `a + 2(hH + 2)` of tape `0`'s flag
in the first cell (a clear, a copy and an increment chain) and the tape counter `Q3` to `k`,
and runs the edge loop (`edge_loop`). -/
theorem edge_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true)) := by
  set B := bnd N y
  have hv0 := hBd.val_le
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B := by
    have : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    omega
  have hsB : s ≤ B := by omega
  have e0 : astep (CA N .edge) orc y (some (.vDone st), R.val, none) =
      (some (if VAcc N st.1 then .eStart else .rej), R.val, none) := by
    rw [astep_jz ((CA_vDone_edge st).trans (goto_eq _)), ite_self]
  have hg0 : GuardLe (CA N .edge) y B (some (.vDone st), R.val, none) :=
    edge_gd hv0 ((CA_vDone_edge st).trans (goto_eq _)) trivial
  by_cases hacc : VAcc N st.1
  swap
  · rw [decide_eq_false (fun h => hacc h.1)]
    refine AHalt.step hg0 ?_
    rw [e0, if_neg hacc]
    exact AHalt.ret (CA_rej .edge) (edge_gd hv0 (CA_rej .edge) trivial)
  have r0 : Reach N .edge y B (.vDone st) R.val .eStart R.val :=
    Reach.single' hg0 (by rw [e0, if_pos hacc])
  by_cases hk : N.k = 0
  · rw [decide_eq_false (fun ⟨_, i, _⟩ => absurd i.isLt (by omega))]
    exact AReach.halt r0 (AHalt.ret (CA_eStart_of_zero .edge hk)
      (edge_gd hv0 (CA_eStart_of_zero .edge hk) trivial))
  -- the address of tape `0`'s flag in the first cell, and the tape counter
  set v1 := Function.update R.val rU 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rU _ _ hv0 (Nat.zero_le _)
  have r1 : Reach N .edge y B .eStart R.val (.cp .Ue) v1 :=
    Reach.single' (edge_gd hv0 (CA_eStart_of_pos .edge hk) trivial)
      (astep_clr (CA_eStart_of_pos .edge hk))
  have h1A : v1 rA = R.A := by rw [hv1, Function.update_of_ne (by decide), Regs.val_A]
  set v2 := Function.update v1 rU R.A with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rU _ _ hv1B (by rw [hA]; omega)
  have r2 : Reach N .edge y B (.cp .Ue) v1 (icL N .Eh 0) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Ue v1 hv1B
      (by rw [cpDst_Ue, cpSrc_Ue, hv1, Function.update_self]; exact Nat.zero_le _)
    rwa [cpNext_Ue, cpDst_Ue, cpSrc_Ue, h1A, ← icL_zero] at h
  have h2U : v2 rU = R.A := by rw [hv2, Function.update_self]
  have hW0 : hH N + 2 < W N := by rw [W_eq]; omega
  have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  set v3 := Function.update v2 rU (R.A + 2 * (hH N + 2)) with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rU _ _ hv2B (by omega)
  have r3 : Reach N .edge y B (icL N .Eh 0) v2 .eK v3 := by
    have h := ic_run (N := N) (mode := .edge) y B .Eh v2 hv2B
      (by rw [icReg_Eh, icCount_Eh, h2U]; omega)
    rwa [icNext_Eh, icReg_Eh, icCount_Eh, h2U] at h
  set v4 := Function.update v3 rQ3 0 with hv4
  have hv4B : ∀ r, v4 r ≤ B := register_update_le _ rQ3 _ _ hv3B (Nat.zero_le _)
  have r4 : Reach N .edge y B .eK v3 (icL N .Ke 0) v4 :=
    Reach.single' (edge_gd hv3B (CA_eK .edge) trivial) (astep_clr (CA_eK .edge))
  have hkB : N.k - 1 + 1 ≤ B := by
    have : N.k ≤ W N := by rw [W_eq]; omega
    omega
  set v5 := Function.update v4 rQ3 (N.k - 1 + 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B := register_update_le _ rQ3 _ _ hv4B hkB
  have r5 : Reach N .edge y B (icL N .Ke 0) v4 .eRd1 v5 := by
    have h := ic_run (N := N) (mode := .edge) y B .Ke v4 hv4B
      (by rw [icReg_Ke, icCount_Ke, hv4, Function.update_self]; omega)
    rwa [icNext_Ke, icReg_Ke, icCount_Ke, hv4, Function.update_self, Nat.zero_add] at h
  have hloop := edge_loop (y := y) (B := B) x w rest hy s hw hB hsB (N.k - 1) 0 v5 (by omega)
    hv5B
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_S, hS])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_T, hT])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_self, hA])
    (by rw [hv5, Function.update_self])
  rw [show decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
      w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true) =
      decide (∃ i' : Fin N.k, 0 ≤ (i' : ℕ) ∧ (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) from
    decide_eq_decide.mpr ⟨fun ⟨_, i, h⟩ => ⟨i, Nat.zero_le _, h⟩,
      fun ⟨i, _, h⟩ => ⟨hacc, i, h⟩⟩]
  exact AReach.halt (r0.trans (r1.trans (r2.trans (r3.trans (r4.trans r5))))) hloop

/-- **Edge codes form a logspace language** (`Complexity.Codec.edgeLang`).

**Proof sketch.** As `validLang_mem`, with the edge-code tail (`edge_tail`) and the edge-code
check (`edgeLang_iff`). -/
theorem edgeLang_mem : edgeLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .edge) (by decide) (mem_edgeLang_iff N)
    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (edgeLang_iff N)
    (fun x s w h => ((edgeChk_def N x s w).mp h).1) ?_
  intro y x w s st R hsh hpre hs hw hst hR hA hS hT _
  refine ⟨_, ?_, edge_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
  rw [decide_eq_true_eq, edgeChk_def, validChk_iff_pre, hst]
  exact ⟨fun ⟨⟨_, hv⟩, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨⟨hpre, hv⟩, h⟩⟩

end Complexity.Codec

## ===== campaign/gates/111-cl1-dedup/evidence/seal/compile-Checks.out =====

exit=0

## ===== campaign/gates/111-cl1-dedup/evidence/seal/compile-Langs.out =====

exit=0

## ===== campaign/gates/111-cl1-dedup/evidence/seal/run.sh.txt =====

#!/usr/bin/env bash
# CL-1 rule-10 seal: copies of Checks and Deciders with the five code languages irreducible.
S=/home/user/tcslib-scratch; . $S/env.sh; export TCSLIB_SCRATCH=$S; D=/home/user/tcslib/devtools/seyoon
T=$S/evidence/g111/seal; W=$S/wt-cl1; OV=$S/ov-cl1
rm -rf $OV; cp -al $S/oleans-lcamp6 $OV
M=$OV/TCSlib/Complexity/SpaceComplexity/Codec
rm -f $M/Langs.olean $M/Langs.ilean $M/Checks.olean $M/Checks.ilean
bash $D/leanelab-o.sh $W $OV TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean $OV > $T/compile-Langs.out 2>&1; echo "exit=$?" >> $T/compile-Langs.out
bash $D/leanelab-o.sh $W $OV TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean $OV > $T/compile-Checks.out 2>&1; echo "exit=$?" >> $T/compile-Checks.out
mkdir -p $W/Scratch
for f in Checks Deciders; do
  python3 -I - "$W/TCSlib/Complexity/SpaceComplexity/Codec/$f.lean" "$W/Scratch/Seal$f.lean" <<'PY'
import sys,re
src=open(sys.argv[1]).read().split('\n')
last=max(i for i,l in enumerate(src) if l.startswith('import '))
ins=['-- unsealed control: the membership destructures',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by',
     '  obtain ⟨x, c, s, -, -⟩ := h',
     '  trivial',
     'attribute [local irreducible] Complexity.Codec.validLang Complexity.Codec.initLang Complexity.Codec.acceptLang Complexity.Codec.stepLang Complexity.Codec.edgeLang',
     '-- sealed controls: the same destructuring fails for each language',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.validLang N) : True := by',
     '  fail_if_success obtain ⟨x, c, s, -, -⟩ := h',
     '  trivial',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.initLang N) : True := by',
     '  fail_if_success obtain ⟨x, c, s, -, -⟩ := h',
     '  trivial',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.acceptLang N) : True := by',
     '  fail_if_success obtain ⟨x, c, s, -, -⟩ := h',
     '  trivial',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.stepLang N) : True := by',
     '  fail_if_success obtain ⟨x, c, -, -⟩ := h',
     '  trivial',
     'example (N : Turing.FinNDTM Bool) (y : List Bool) (h : y ∈ Complexity.Codec.edgeLang N) : True := by',
     '  fail_if_success obtain ⟨x, -⟩ := h',
     '  trivial']
src[last+1:last+1]=ins
open(sys.argv[2],'w').write('\n'.join(src))
PY
  cp $W/Scratch/Seal$f.lean $T/Seal$f.lean.txt
  bash $D/leanelab.sh $W $OV Scratch/Seal$f.lean > $T/seal-$f.out 2>&1; echo "exit=$?" >> $T/seal-$f.out
done
rm -rf $W/Scratch $OV
echo DONE > $T/DONE

## ===== campaign/gates/111-cl1-dedup/evidence/seal/seal-Checks.out =====

Scratch/SealChecks.lean:13:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealChecks.lean:16:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealChecks.lean:19:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealChecks.lean:22:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealChecks.lean:25:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
exit=0

## ===== campaign/gates/111-cl1-dedup/evidence/seal/seal-Deciders.out =====

Scratch/SealDeciders.lean:13:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealDeciders.lean:16:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealDeciders.lean:19:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealDeciders.lean:22:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/SealDeciders.lean:25:51: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
exit=0

## ===== TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Step

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The code languages

The languages a configuration-graph algorithm calls on codes of configurations of a fixed
machine `N` on its real input `x`, at window radius `s` [AB09, §4.1.1]. Each takes the input
`x`, one or two codes and the radius, laid out as the virtual input of a `whole`-mode call
of an abstract register machine whose registers hold the codes and the radius
(`Complexity.LogProg.vword`): `⟨x, ⟨bits c, bits s⟩⟩` or `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`.

* `Complexity.Codec.validLang N` — `c` is the code of a window-bounded configuration;
* `Complexity.Codec.initLang N` — `c` is the code of the initial configuration;
* `Complexity.Codec.acceptLang N` — `c` is the code of a halted window-bounded
  configuration with output `[true]` (acceptance as in `Turing.FinNDTM.AcceptsWithin`);
* `Complexity.Codec.stepLang N` — `c`, `c'` are codes of window-bounded configurations
  with an edge `Turing.NDTM.CfgStep` between them;
* `Complexity.Codec.edgeLang N` — `c` is the code of a window-bounded configuration with a
  work head on the window's boundary.

Besides the membership characterizations, this file reduces membership to the finite
checks on code words that the logspace deciders perform (`ValidChk`, `InitChk`,
`AcceptChk`, `StepChk`).

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.validLang`, `initLang`, `acceptLang`, `stepLang`, `edgeLang`.
* `Complexity.Codec.InitChk`, `AcceptChk`, `StepChk` — the word-level checks.

## Main results

* `Complexity.Codec.mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`,
  `mem_stepLang_iff`, `mem_edgeLang_iff` — the defining equations of the languages.
* `Complexity.Codec.mem_codeLang_iff` — membership in a language of encoded triples.
* `Complexity.Codec.mem_validLang`, `mem_initLang`, `mem_acceptLang`, `mem_stepLang`,
  `mem_edgeLang` —
  membership through the codec.
* `Complexity.Codec.initChk_iff`, `acceptChk_iff`, `stepChk_iff` — the checks recognize
  the code words of the respective configurations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable (N : FinNDTM Bool)

/-! ## The languages -/

/-- **Valid codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x`. -/
def validLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c}

/-- **Initial codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of the
initial configuration of `N` on `x`. -/
def initLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    cfgCode s (N.tm.initCfg x) = c}

/-- **Accepting codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x` that is halted with output exactly `[true]`. -/
def acceptLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
      C.output = [true]}

/-- **Step pairs**: `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩` such that `c` and `c'` are the codes at
radius `s` of window-bounded configurations of `N` on `x` joined by a configuration-graph
edge (one step under some choice bit). -/
def stepLang : Language Bool :=
  {y | ∃ (x : List Bool) (c c' s : ℕ),
    y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
      ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧ cfgCode s C' = c'}

/-- **Edge codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x` with some work head on the window's boundary, at
position `-s` or `s`. A configuration-graph search at radius `s` that reaches no edge code has
seen every reachable configuration. -/
def edgeLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
      ∃ i, |C.workTapePos i| = (s : ℤ)}

/-- A word is in the valid-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the window
of radius `s`. -/
lemma mem_validLang_iff (y : List Bool) :
    y ∈ validLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := Iff.rfl

/-- A word is in the initial-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of the initial configuration of `N` on `x`. -/
lemma mem_initLang_iff (y : List Bool) :
    y ∈ initLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      cfgCode s (N.tm.initCfg x) = c := Iff.rfl

/-- A word is in the accepting-code language exactly when it encodes an input `x`, a code `c` and
a radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
window of radius `s`, is halted and has output exactly `[true]`. -/
lemma mem_acceptLang_iff (y : List Bool) :
    y ∈ acceptLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
        C.output = [true] := Iff.rfl

/-- A word is in the step language exactly when it encodes an input `x`, two codes `c`, `c'` and a
radius `s` such that `c` and `c'` are the radius-`s` codes of configurations `C`, `C'` on `x` that
stay in the window of radius `s`, with a configuration-graph edge from `C` to `C'`. -/
lemma mem_stepLang_iff (y : List Bool) :
    y ∈ stepLang N ↔ ∃ (x : List Bool) (c c' s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := Iff.rfl

/-- A word is in the edge-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
window of radius `s` and has some work head at `-s` or `+s`. -/
lemma mem_edgeLang_iff (y : List Bool) :
    y ∈ edgeLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ i, |C.workTapePos i| = (s : ℤ) := Iff.rfl

/-- The pairing is injective in both components. -/
lemma pairEncode_inj {a b a' b' : List Bool} (h : pairEncode a b = pairEncode a' b') :
    a = a' ∧ b = b' := by
  have := pairEncode_injective (show (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a, b) =
    (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a', b') from h)
  simpa using this

/-- **Membership in a language of encoded triples.** Let `L` be a language whose members are
exactly the encodings `⟨x, ⟨bits c, enc t⟩⟩` with `P x c t`, for an injective encoding `enc` of
the tail. Then for every word `w`, `⟨x, ⟨w, enc t⟩⟩ ∈ L` exactly when `w` is the binary word of
some `c` with `P x c t`. The code languages are of this shape: with tail `bits s` for
`validLang`, `initLang`, `acceptLang` and `edgeLang`, and with tail `⟨w', bits s⟩` for
`stepLang`.

Configuration-graph infrastructure ([AB09, §4.1.1]); not a result of [AB09].

**Proof sketch.** A member `⟨x', ⟨bits c, enc t'⟩⟩` equal to `⟨x, ⟨w, enc t⟩⟩` has `x' = x` and
`bits c = w` by injectivity of the pairing, in both layers, and `t' = t` by injectivity of `enc`.
Conversely `⟨x, ⟨bits c, enc t⟩⟩` is a member when `P x c t` holds. -/
theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
    {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
      y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
    (x w : List Bool) (t : τ) :
    pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t := by
  rw [hL]
  constructor
  · rintro ⟨x', c, t', h, hP⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨hw, ht⟩ := pairEncode_inj h2
    obtain rfl := henc ht
    exact ⟨c, hw.symm, hP⟩
  · rintro ⟨c, rfl, hP⟩
    exact ⟨x, c, t, rfl, hP⟩

/-- **Membership in the valid-code language.** -/
theorem mem_validLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ validLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := by
  rw [mem_codeLang_iff bits_injective (mem_validLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the initial-code language.** -/
theorem mem_initLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ initLang N ↔
      cfgCode s (N.tm.initCfg x) = c := by
  rw [mem_codeLang_iff bits_injective (mem_initLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the accepting-code language.** -/
theorem mem_acceptLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
        C.output = [true] := by
  rw [mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the step language.** -/
theorem mem_stepLang (x : List Bool) (c c' s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∈
        stepLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := by
  -- the tail `⟨bits c', bits s⟩` is the injective image of the pair `(c', s)`
  have henc : Function.Injective fun t : ℕ × ℕ => pairEncode (Nat.bits t.1) (Nat.bits t.2) :=
    fun t t' h => by
      obtain ⟨h1, h2⟩ := pairEncode_inj h
      exact Prod.ext (bits_injective h1) (bits_injective h2)
  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : ℕ × ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits t.1) (Nat.bits t.2))) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧ cfgCode t.2 C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow t.2 C' ∧
          cfgCode t.2 C' = t.1 := fun y => by
    rw [mem_stepLang_iff]
    simp only [Prod.exists]
  rw [mem_codeLang_iff henc hL x (Nat.bits c) (c', s)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the edge-code language.** The encoding of `x`, `bits c` and `bits s` is in
the language exactly when `c` is the radius-`s` code of a configuration on `x` inside the window
of radius `s` with some work head at `-s` or `+s`. -/
theorem mem_edgeLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ edgeLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ i, |C.workTapePos i| = (s : ℤ) := by
  rw [mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

end Complexity.Codec
```

## ===== TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Langs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word-level checks of the code languages

What the logspace deciders of the five code languages actually test, as predicates on the
code words: the validity test `Complexity.Codec.ValidChk` of
`TCSlib.Complexity.SpaceComplexity.Codec.Valid`, plus

* for the initial code: header `(q₀, empty)`, the initial cell shape, input position `1`,
  and the head flag of tape `0` in the middle cell;
* for an accepting code: header `(halted, accept)`;
* for a step: the second word has the right length and final letter, and for one of the two
  choice bits its input position is the moved one and the sliding check of the two chunk
  regions accepts under the local rule of that bit's action;
* for an edge code: the head flag of some tape is set in the first or the last cell
  (`Complexity.Codec.EdgeChk`).

Each check recognizes exactly the code words of the corresponding configurations, and so
decides membership in the code languages on well-shaped inputs.

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.InitChk`, `Complexity.Codec.AcceptChk`, `Complexity.Codec.StepChk`,
  `Complexity.Codec.EdgeChk`.
* `Complexity.Codec.movePos`, `Complexity.Codec.inpOf`, `Complexity.Codec.aI`,
  `Complexity.Codec.Gs` — the arithmetic and finite data of a step check.

## Main results

* `Complexity.Codec.initChk_iff`, `acceptChk_iff`, `stepChk_iff`, `edgeChk_iff`.
* `Complexity.Codec.validLang_iff`, `initLang_iff`, `acceptLang_iff`, `stepLang_iff`,
  `edgeLang_iff` —
  membership of well-shaped inputs in terms of the checks.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## Reading single letters of a code word -/

/-- Letter `t` of block `j` of a concatenation of fixed-width blocks. -/
lemma getD_flatten_block {α : Type} (L : List (List α)) (w : ℕ)
    (hL : ∀ b ∈ L, b.length = w) (j t : ℕ) (hj : j < L.length) (ht : t < w) (d : α) :
    L.flatten.getD (w * j + t) d = L[j].getD t d := by
  have e := take_drop_flatten L w hL j hj
  rw [← e, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos ht, List.getElem?_drop]

/-- Letter `t` of chunk `j` of a code word is bit `t` of the chunk of cell `j`. -/
lemma getD_cfgWord_chunk (s : ℕ) (C : Cfg N.k Bool N.State x) (j t : ℕ) (hj : j < 2 * s + 1)
    (ht : t < W N) :
    (cfgWord s C).getD (W N * j + t) false = chunkBit N (cellOf s C j) t := by
  have hlt : W N * j + t < W N * (2 * s + 1) := by
    calc W N * j + t < W N * j + W N := by omega
      _ = W N * (j + 1) := by ring
      _ ≤ W N * (2 * s + 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [cfgWord, List.append_assoc, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [length_chunksWord]; exact hlt),
    ← List.getD_eq_getElem?_getD]
  unfold chunksWord
  rw [getD_flatten_block _ (W N) (by simp) j t (by simpa using hj) ht]
  simp only [List.getElem_ofFn]
  exact getD_encChunk N _ t ht

/-! ## Initial and accepting codes -/

variable (N) in
/-- **The initial-code check** on a word `w`: valid, header `(q₀, empty)`, every cell of the
initial shape (blank, all heads or none), input position `1`, and (with at least one work
tape) the head of tape `0` flagged in the middle cell `s`. -/
def InitChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (some N.tm.q₀, 0) ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.2.2.2.2 = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) = 1 ∧
    (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)

/-- **The initial-code check recognizes the code of the initial configuration.**

**Proof sketch.** (⇐) Read the header, the initial shape, the position field and the middle
cell off the layout (`vScan_cfgWord`, `cfgWord_pos`, `getD_cfgWord_chunk`). (⇒) The word
is the code of some window-bounded `C` (`validChk_iff`); the header gives the state `q₀` and
the empty output; the initial shape makes every cell blank (and outside the window cells are
blank anyway) and puts all heads in one cell, and the middle-cell flag puts the head of tape
`0`, hence all heads, at position `0`. So `C` has the vertex of the initial configuration,
and codes depend only on the vertex (`cfgWord_congr`). -/
theorem initChk_iff (s : ℕ) (w : List Bool) :
    InitChk N x s w ↔ w = cfgWord s (N.tm.initCfg x) := by
  have hWin : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s
  constructor
  · rintro ⟨hval, hhd, hiok, hpos, hcen⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s C hC
    rw [h1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    obtain ⟨hst, hsum⟩ := hhd
    have hout : C.output = [] := by
      apply (outSummary_eq_empty_iff _).mp
      exact sumIdx_injective (by rw [hsum]; rfl)
    rw [h4, decide_eq_true_eq] at hiok
    rw [cfgWord_pos, bitsVal_padBits] at hpos
    have hblank : ∀ i z, C.workTapes i z = none := by
      intro i z
      by_cases hz : |z| ≤ s
      · have := (hiok (z + s).toNat (by rw [abs_le] at hz; omega)).1 i
        simp only [cellOf] at this
        rwa [show (((z + s).toNat : ℕ) : ℤ) - s = z by rw [abs_le] at hz; omega] at this
      · exact hC.2 i z (not_le.mp hz)
    have hheads : ∀ i, C.workTapePos i = 0 := by
      intro i
      have hk : 0 < N.k := Fin.pos i
      have h0 : C.workTapePos ⟨0, hk⟩ = 0 := by
        rcases hcen with h | h
        · omega
        · have := getD_cfgWord_chunk s C s (hH N + 2) (by omega) (by simp [W]; omega)
          rw [show W N * s + (hH N + 2) = W N * s + (hH N + 2) from rfl, this] at h
          rw [show hH N + 2 = hH N + 3 * (⟨0, hk⟩ : Fin N.k) + 2 by simp,
            chunkBit_tape N _ _ 2 (by omega)] at h
          simpa [cellOf] using h
      have tog := (hiok s (by omega)).2
      simp only [cellOf, sub_self] at tog
      rcases tog with h | h
      · simpa using h i
      · have := h ⟨0, hk⟩
        simp [h0] at this
    have hcore : NDTM.coreSum C = NDTM.coreSum (N.tm.initCfg x) := by
      simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, NDTM.initCfg, Cfg.init, hst, hout,
        Prod.mk.injEq, true_and]
      refine ⟨⟨Fin.ext (by simpa using hpos), funext fun i => funext fun z => hblank i z,
        funext hheads⟩, trivial⟩
    exact cfgWord_congr hcore
  · rintro rfl
    obtain ⟨h1, -, -, h4⟩ := vScan_cfgWord s (N.tm.initCfg x) hWin
    refine ⟨(validChk_iff x s _).mpr ⟨_, hWin, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [h1]; simp [NDTM.initCfg, Cfg.init, outSummary, sumIdx]
    · rw [h4, decide_eq_true_eq]
      intro j hj
      refine ⟨fun i => by simp [cellOf, NDTM.initCfg, Cfg.init], ?_⟩
      by_cases hjs : (j : ℤ) - s = 0
      · left; intro i; simp [cellOf, NDTM.initCfg, Cfg.init, hjs]
      · right; intro i; simp [cellOf, NDTM.initCfg, Cfg.init]; omega
    · rw [cfgWord_pos, bitsVal_padBits]; rfl
    · by_cases hk : N.k = 0
      · exact Or.inl hk
      · right
        have hk' : 0 < N.k := Nat.pos_of_ne_zero hk
        rw [getD_cfgWord_chunk s _ s (hH N + 2) (by omega) (by simp [W]; omega),
          show hH N + 2 = hH N + 3 * (⟨0, hk'⟩ : Fin N.k) + 2 by simp,
          chunkBit_tape N _ _ 2 (by omega)]
        simp [cellOf, NDTM.initCfg, Cfg.init]

variable (N) in
/-- **The accepting-code check** on a word `w`: valid with header `(halted, accept)`. -/
def AcceptChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    (vScan N (w.take (W N * (2 * s + 1)))).2.1 = some (none, 1)

/-- **The accepting-code check recognizes the codes of accepting configurations.**

**Proof sketch.** The header of a code word is the state and the summary index
(`vScan_cfgWord`); summary index `1` is the summary `accept`, i.e. output `[true]`
(`outSummary_eq_accept_iff`). -/
theorem acceptChk_iff (s : ℕ) (w : List Bool) :
    AcceptChk N x s w ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      C.state = none ∧ C.output = [true] := by
  constructor
  · rintro ⟨hval, hhd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    rw [(vScan_cfgWord s C hC).1] at hhd
    simp only [Option.some.injEq, Prod.mk.injEq] at hhd
    refine ⟨C, hC, rfl, hhd.1, (outSummary_eq_accept_iff _).mp ?_⟩
    exact sumIdx_injective (by rw [hhd.2]; rfl)
  · rintro ⟨C, hC, rfl, hst, hout⟩
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, ?_⟩
    rw [(vScan_cfgWord s C hC).1, hst, hout]
    rfl

/-! ## Steps -/

/-- The input position after a move, clamped to `[0, n + 1]`: the arithmetic of
`Turing.moveInputPos`. -/
def movePos (n p : ℕ) : SignType → ℕ
  | .zero => p
  | .pos => if p = n + 1 then p else p + 1
  | .neg => p - 1

/-- `movePos` is the value of the clamped move. -/
lemma val_moveInputPos {n : ℕ} (p : Fin (n + 2)) (mv : SignType) :
    (moveInputPos p mv).val = movePos n p.val mv := by
  have := p.isLt
  cases mv with
  | zero => simp [moveInputPos_zero, movePos]
  | pos =>
    simp only [movePos, moveInputPos, SignType.pos_eq_one, SignType.coe_one]
    split_ifs with h1 h2 h2 <;> simp_all <;> omega
  | neg =>
    simp only [movePos, moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg,
      SignType.coe_one]
    split_ifs with h1 <;> simp_all <;> omega

/-- The input symbol at position `p` (shifted by one; blank at both ends). -/
def inpOf (x : List Bool) (p : ℕ) : Option Bool :=
  if p = 0 ∨ p = x.length + 1 then none else some (x.getD (p - 1) false)

/-- The input symbol of a configuration is `inpOf` of its input position. -/
lemma inputSymbol_eq (C : Cfg N.k Bool N.State x) : C.inputSymbol = inpOf x C.inputPos.val := by
  have := C.inputPos.isLt
  unfold Cfg.inputSymbol inpOf
  by_cases h0 : C.inputPos = 0
  · simp [h0]
  · by_cases h1 : C.inputPos.val = x.length + 1
    · have : C.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h1
      simp [this]
    · have hv : C.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      rw [dif_neg h0, dif_neg h1, if_neg (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show C.inputPos.val - 1 <
        x.length by omega)]

variable (N) in
/-- The finite data a step check needs: the validity-scan state of the first word and the
input symbol under its input head. -/
abbrev SInfo := VSt N × Option Bool

set_option synthInstance.maxSize 1000 in
/-- Step data are finitely many. -/
instance SInfo.instFintype : Fintype (SInfo N) := inferInstance

set_option synthInstance.maxSize 1000 in
/-- Step data have decidable equality. -/
instance SInfo.instDecidableEq : DecidableEq (SInfo N) := inferInstance

/-- The header recorded by a validity scan (a default if none). -/
def hdOfV (st : VSt N) : Hd N := st.2.1.getD (none, 0)

variable (N) in
/-- The action of a step under the choice bit `b`, from the step data. -/
def aI (I : SInfo N) (b : Bool) : Action N.k Bool N.State :=
  effAct N (hdOfV I.1).1 I.2 I.1.2.2.2.1 b

variable (N) in
/-- The local rule of a step under the choice bit `b`, from the step data. -/
def Gs (I : SInfo N) (b : Bool) : SX N → SX N → SX N → SX N :=
  stepG (aI N I b) (newHd (aI N I b) (hdOfV I.1))

variable (N) in
/-- **The step check** on words `w`, `w'`: `w` is valid; `w'` has the code length and final
letter `1`; and for one choice bit `b`, the input position of `w'` is that of `w` moved by
`b`'s action, and the sliding check of the chunk regions under `b`'s local rule accepts. -/
def StepChk (x : List Bool) (s : ℕ) (w w' : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧ w'.length = W N * (2 * s + 1) + wP x.length + 1 ∧
    w'.getD (W N * (2 * s + 1) + wP x.length) false = true ∧
    ∃ b : Bool,
      bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)) =
        movePos x.length (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))
          (aI N (vScan N (w.take (W N * (2 * s + 1))),
            inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b).inputTape ∧
      sDone N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
          inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) b)
        ((if b then Prod.snd else Prod.fst)
          (sScan N (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) false)
            (Gs N (vScan N (w.take (W N * (2 * s + 1))),
              inpOf x (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))) true)
            (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))))) = true

/-- A word of length `a + b + 1` ending with `1` splits into its first `a` letters, the next
`b`, and the final `1`. -/
lemma word_split (w : List Bool) (a b : ℕ) (hlen : w.length = a + b + 1)
    (hlast : w.getD (a + b) false = true) :
    w = w.take a ++ (w.drop a).take b ++ [true] := by
  have htail : w.drop (a + b) = [true] := by
    have hl : (w.drop (a + b)).length = 1 := by simp; omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hl
    rw [hc]
    have h0 := congrArg (fun l : List Bool => l[0]?) hc
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    rw [List.getD_eq_getElem?_getD, h0] at hlast
    simp only [Option.getD_some] at hlast
    rw [hlast]
  rw [← htail, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-- A component of the double sliding scan, by the choice bit. -/
lemma sScan_sel (G : Bool → SX N → SX N → SX N → SX N) (u u' : List Bool) (m : ℕ)
    (hu : u.length = W N * m) (hu' : u'.length = W N * m) (b : Bool) :
    (if b then Prod.snd else Prod.fst) (sScan N (G false) (G true) u u') =
      (List.zip (blocksD N u m) (blocksD N u' m)).foldl (slStep (G b)) (sInit N) := by
  rw [sScan_eq (G false) (G true) u u' m hu hu']
  cases b <;> rfl

/-- The step data of a code word: the action and local rule they determine are those of the
coded configuration. -/
lemma aI_cfgWord (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : Cfg.InWindow s C) (b : Bool) :
    aI N (vScan N ((cfgWord s C).take (W N * (2 * s + 1))),
        inpOf x (bitsVal (((cfgWord s C).drop (W N * (2 * s + 1))).take (wP x.length)))) b =
      effAct N C.state C.inputSymbol C.workTapeSymbols b ∧
    hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
  obtain ⟨h1, -, h3, -⟩ := vScan_cfgWord s C hC
  have hhd : hdOfV (vScan N ((cfgWord s C).take (W N * (2 * s + 1)))) = hdOf C := by
    simp only [hdOfV, h1, Option.getD_some, hdOf]
  refine ⟨?_, hhd⟩
  simp only [aI, hhd, hdOf, cfgWord_pos, bitsVal_padBits, ← inputSymbol_eq]
  congr 1
  funext i
  exact h3 i

/-- **The step check recognizes code words of configuration-graph edges.**

**Proof sketch.** Both directions go through the coded configuration `C` of the first word
(`validChk_iff`), whose scan data determine the action of each choice bit (`aI_cfgWord`).
For a choice bit `b`, with `C' = stepWith b C` (`stepWith_eq_apply`): the sliding check of
`b` accepts iff the chunk region of the second word is that of `C'` and `C'` is
window-bounded (`sScan_sel`, `sDone_step`); the input position of `C'` is the moved one
(`val_moveInputPos`), and a position field is determined by its value (`eq_padBits`); with
the length and the final letter (`word_split`), the second word is the code word of `C'`. -/
theorem stepChk_iff (s : ℕ) (w w' : List Bool) :
    StepChk N x s w w' ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧ cfgWord s C' = w' := by
  constructor
  · rintro ⟨hval, hlen', hlast', b, hpos', hsd⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    have hA' : (w'.take (W N * (2 * s + 1))).length = W N * (2 * s + 1) := by
      simp only [List.length_take]; omega
    rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1) (by simp [length_cfgWord]; omega) hA'] at hsd
    simp only [Gs] at hsd
    rw [ha, hhd, cfgWord_take] at hsd
    obtain ⟨hcells, hwin'⟩ := (sDone_step s C hC a _ hA').mp hsd
    refine ⟨C, hC, rfl, a.apply C, ⟨b, stepWith_eq_apply b C⟩, hwin', ?_⟩
    rw [word_split w' (W N * (2 * s + 1)) (wP x.length) hlen' hlast', hcells]
    simp only [cfgWord]
    congr 2
    have hP : ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length := by
      simp only [List.length_take, List.length_drop]; omega
    rw [eq_padBits ((w'.drop (W N * (2 * s + 1))).take (wP x.length)), hP, hpos', ha]
    simp only [cfgWord_pos, bitsVal_padBits]
    rw [← val_moveInputPos]
    rfl
  · rintro ⟨C, hC, rfl, C', ⟨b, hstep⟩, hC', rfl⟩
    obtain ⟨ha, hhd⟩ := aI_cfgWord s C hC b
    rw [stepWith_eq_apply] at hstep
    subst hstep
    set a := effAct N C.state C.inputSymbol C.workTapeSymbols b
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, length_cfgWord s _, cfgWord_last s _, b, ?_, ?_⟩
    · rw [ha, cfgWord_pos, bitsVal_padBits, cfgWord_pos, bitsVal_padBits]
      exact val_moveInputPos _ _
    · have hA' : ((cfgWord s (a.apply C)).take (W N * (2 * s + 1))).length =
          W N * (2 * s + 1) := by simp only [List.length_take, length_cfgWord]; omega
      rw [sScan_sel (fun b => Gs N _ b) _ _ (2 * s + 1)
        (by simp only [List.length_take, length_cfgWord]; omega) hA']
      simp only [Gs]
      rw [ha, hhd]
      simp only [cfgWord_take]
      exact (sDone_step s C hC a _ (length_chunksWord N _ _)).mpr ⟨rfl, hC'⟩

/-! ## Membership through the checks -/

/-- The code word of a configuration is the binary word of its code; a word equal to a code
word is the binary word of a number. -/
lemma cfgWord_eq_bits_iff (s : ℕ) (C : Cfg N.k Bool N.State x) (c : ℕ) :
    cfgCode s C = c ↔ cfgWord s C = Nat.bits c := by
  rw [← bits_cfgCode]
  exact ⟨fun h => h ▸ rfl, fun h => bits_injective h⟩

variable (N) in
/-- **Valid codes through the check**: on `⟨x, ⟨w, bits s⟩⟩` with any word `w`, membership in
`validLang` is the validity test of `w`. -/
theorem validLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ validLang N ↔ ValidChk (N := N) x.length s w := by
  rw [validChk_iff, mem_codeLang_iff bits_injective (mem_validLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl⟩

variable (N) in
/-- **Initial codes through the check.** -/
theorem initLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ initLang N ↔ InitChk N x s w := by
  rw [initChk_iff, mem_codeLang_iff bits_injective (mem_initLang_iff N)]
  constructor
  · rintro ⟨c, rfl, rfl⟩
    exact bits_cfgCode s _
  · rintro rfl
    exact ⟨cfgCode s (N.tm.initCfg x), bits_cfgCode s _, rfl⟩

variable (N) in
/-- **Accepting codes through the check.** -/
theorem acceptLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ acceptLang N ↔ AcceptChk N x s w := by
  rw [acceptChk_iff, mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl, hst, hout⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, hst, hout⟩
  · rintro ⟨C, hC, rfl, hst, hout⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hst, hout⟩

variable (N) in
/-- **Step pairs through the check.** -/
theorem stepLang_iff (x w w' : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (pairEncode w' (Nat.bits s))) ∈ stepLang N ↔
      StepChk N x s w w' := by
  -- the tail `⟨w', bits s⟩` is the injective image of the pair `(w', s)`
  have henc : Function.Injective fun t : List Bool × ℕ => pairEncode t.1 (Nat.bits t.2) :=
    fun _ _ h => Prod.ext (pairEncode_inj h).1 (bits_injective (pairEncode_inj h).2)
  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : List Bool × ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode t.1 (Nat.bits t.2))) ∧
      ∃ c', Nat.bits c' = t.1 ∧ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧
        cfgCode t.2 C = c ∧ ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧
          Cfg.InWindow t.2 C' ∧ cfgCode t.2 C' = c' := fun y => (mem_stepLang_iff N y).trans
    ⟨fun ⟨x, c, c', s, h, hP⟩ => ⟨x, c, (Nat.bits c', s), h, c', rfl, hP⟩,
      fun ⟨x, c, t, h, c', hc', hP⟩ => ⟨x, c, c', t.2, by rw [hc']; exact h, hP⟩⟩
  rw [stepChk_iff, mem_codeLang_iff henc hL x w (w', s)]
  dsimp only
  constructor
  · rintro ⟨c, rfl, c', rfl, C, hC, rfl, C', hstep, hC', rfl⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, C', hstep, hC', (bits_cfgCode s C').symm⟩
  · rintro ⟨C, hC, rfl, C', hstep, hC', rfl⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, cfgCode s C', bits_cfgCode s C', C, hC, rfl, C',
      hstep, hC', rfl⟩

/-! ## Edge codes -/

variable (N) in
/-- **The edge-code check** on a word `w`: valid, and some tape `i` has its head flag set in the
first cell (work position `-s`) or in the last (work position `s`). -/
def EdgeChk (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ValidChk (N := N) x.length s w ∧
    ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
      w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true

variable (N) in
/-- The edge-code check holds of a word `w` exactly when `w` passes the validity check at radius
`s` for inputs of length `|x|` and, for some work tape `i`, tape `i`'s head flag is set in chunk
`0` or in chunk `2s` of `w`, the cells at `-s` and `+s`. -/
lemma edgeChk_def (x : List Bool) (s : ℕ) (w : List Bool) :
    EdgeChk N x s w ↔ ValidChk (N := N) x.length s w ∧
      ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true := Iff.rfl

/-- The head flag of tape `i` in cell `j` of a code word: letter `hH + 3i + 2` of chunk `j` is
set exactly when the head of tape `i` is at work position `j - s`. -/
lemma getD_cfgWord_head (s : ℕ) (C : Cfg N.k Bool N.State x) (j : ℕ) (hj : j < 2 * s + 1)
    (i : Fin N.k) :
    (cfgWord s C).getD (W N * j + (hH N + 3 * (i : ℕ) + 2)) false =
      decide (C.workTapePos i = (j : ℤ) - s) := by
  have hi : hH N + 3 * (i : ℕ) + 2 < W N := by have := i.isLt; rw [W_eq]; omega
  rw [getD_cfgWord_chunk s C j _ hj hi, chunkBit_tape N _ i 2 (by omega), if_neg (by omega),
    if_neg (by omega), cellOf_head]

/-- **The edge-code check recognizes the codes with a head on the window's boundary.**

**Proof sketch.** A valid word is the code word of a window-bounded `C` (`validChk_iff`). Its
letter `hH + 3i + 2` of chunk `j` is the head flag of tape `i` at work position `j - s`
(`getD_cfgWord_head`). Chunk `0` is position `-s`, chunk `2s` is position `s`, and `|p| = s`
exactly when `p = -s` or `p = s`. -/
theorem edgeChk_iff (s : ℕ) (w : List Bool) :
    EdgeChk N x s w ↔ ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgWord s C = w ∧
      ∃ i, |C.workTapePos i| = (s : ℤ) := by
  have h0 : ∀ (C : Cfg N.k Bool N.State x) (i : Fin N.k),
      (cfgWord s C).getD (hH N + 3 * (i : ℕ) + 2) false =
        decide (C.workTapePos i = -(s : ℤ)) := by
    intro C i
    have := getD_cfgWord_head s C 0 (by omega) i
    rw [Nat.mul_zero, Nat.zero_add] at this
    rw [this]; congr 1; simp
  have h2 : ∀ (C : Cfg N.k Bool N.State x) (i : Fin N.k),
      (cfgWord s C).getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false =
        decide (C.workTapePos i = (s : ℤ)) := by
    intro C i
    rw [getD_cfgWord_head s C (2 * s) (by omega) i]; congr 1; push_cast; ring_nf
  constructor
  · rintro ⟨hval, i, hi⟩
    obtain ⟨C, hC, rfl⟩ := (validChk_iff x s w).mp hval
    refine ⟨C, hC, rfl, i, ?_⟩
    rw [h0, h2, decide_eq_true_eq, decide_eq_true_eq] at hi
    rcases hi with h | h <;> rw [h] <;> simp
  · rintro ⟨C, hC, rfl, i, hi⟩
    refine ⟨(validChk_iff x s _).mpr ⟨C, hC, rfl⟩, i, ?_⟩
    rw [h0, h2, decide_eq_true_eq, decide_eq_true_eq]
    rcases (abs_eq (by positivity)).mp hi with h | h
    · exact Or.inr h
    · exact Or.inl h

variable (N) in
/-- **Edge codes through the check.** For every word `w`, not only for codes, the encoding of
`x`, `w` and `bits s` is in the edge-code language exactly when `w` passes the edge-code check. -/
theorem edgeLang_iff (x w : List Bool) (s : ℕ) :
    pairEncode x (pairEncode w (Nat.bits s)) ∈ edgeLang N ↔ EdgeChk N x s w := by
  rw [edgeChk_iff, mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
  constructor
  · rintro ⟨c, rfl, C, hC, rfl, hi⟩
    exact ⟨C, hC, (bits_cfgCode s C).symm, hi⟩
  · rintro ⟨C, hC, rfl, hi⟩
    exact ⟨cfgCode s C, bits_cfgCode s C, C, hC, rfl, hi⟩

end Complexity.Codec
```

## ===== TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Layout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The one-code languages are logspace

The codec machine `Complexity.Codec.CA` in the modes `valid`, `accept`, `init`, `edge` decides
the languages `Complexity.Codec.validLang N`, `acceptLang N`, `initLang N`, `edgeLang N`: it
parses (`parse_run`), lays out the code word (`layout_run`), compares the input position
(`le_phase`), scans the chunk region (`vscan_run`), and answers from the scan state — for
the initial code after testing the input position and the head flag of the middle cell, for an
edge code after testing, tape by tape, the head flags of the first and last cells.
`Complexity.LogProg.arm_decides_poly` turns this into membership in `L`, once for all four
modes in the wrapper `Complexity.Codec.oneCode_mem`, which takes the mode's tail as a hypothesis.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.PreChk` — the checks done before the scan.
* `Complexity.Codec.InitScan` — the scan-state part of the initial-code test.

## Main results

* `Complexity.Codec.one_run` — the common run of the one-code modes.
* `Complexity.Codec.oneCode_mem` — the decider wrapper of the one-code modes.
* `Complexity.Codec.init_tail` — the tail of the initial-code mode.
* `Complexity.Codec.edge_round`, `Complexity.Codec.edge_loop`, `Complexity.Codec.edge_tail` —
  the tail of the edge-code mode.
* `Complexity.Codec.validLang_mem`, `Complexity.Codec.acceptLang_mem`,
  `Complexity.Codec.initLang_mem`, `Complexity.Codec.edgeLang_mem` — the four languages are in
  `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {mode : CMode}

/-! ## Members are well shaped -/

/-- A code at radius `s` is longer than `s`, so a well-formed input `⟨x, ⟨bits c, bits s⟩⟩`
with `c` a code passes the width check of its radius field. -/
lemma width_of_code {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (y : List Bool)
    (hy : (cfgWord s C).length ≤ y.length) :
    (Nat.bits s).length ≤ (Nat.bits y.length).length := by
  apply length_bits_mono
  have := length_cfgWord s C
  have hW : 1 ≤ W N := by simp [W]
  have : 2 * s + 1 ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_left _ hW
  omega

/-- The input length is at least the code word's. -/
lemma cfgWord_le_length {x : List Bool} (s : ℕ) (C : Cfg N.k Bool N.State x) (rest : List Bool) :
    (cfgWord s C).length ≤ (pairEncode x (pairEncode (cfgWord s C) rest)).length := by
  simp [length_pairEncode]; omega

/-- The register bound in the form of `arm_decides_poly`. -/
lemma gd_mono {y : List Bool} (a : AConf 21 (Lab N)) (h : GuardLe (CA N mode) y (bnd N y) a) :
    PreS (CA N mode) y a ∧ ∀ r, a.2.1 r ≤ (8 * W N + 8) * (y.length + 1) ^ 1 := by
  simpa [bnd] using h

/-- The empty register file is the zero valuation. -/
lemma val_empty : ({} : Regs).val = fun _ => 0 := by
  funext r; fin_cases r <;> rfl

/-- The radius of a well-shaped input is at most twice the input length. -/
lemma s_le_of_width (y : List Bool) (s : ℕ) (hy : 1 ≤ y.length)
    (h : (Nat.bits s).length ≤ (Nat.bits y.length).length) : s ≤ 2 * y.length := by
  have h1 := bitsVal_le_of_width (Nat.bits s) y.length hy h 0
  simpa [bitsVal_bits] using h1

/-! ## The common run of the one-code modes -/

variable (N) in
/-- The checks done before the scan: the length, the final letter, and the input position. -/
def PreChk (n s : ℕ) (w : List Bool) : Prop :=
  w.length = W N * (2 * s + 1) + wP n + 1 ∧ w.getD (W N * (2 * s + 1) + wP n) false = true ∧
    bitsVal ((w.drop (W N * (2 * s + 1))).take (wP n)) ≤ n + 1

/-- The validity test is the pre-scan checks and the scan verdict. -/
lemma validChk_iff_pre (n s : ℕ) (w : List Bool) :
    ValidChk (N := N) n s w ↔ PreChk N n s w ∧ VAcc N (vScan N (w.take (W N * (2 * s + 1)))) := by
  unfold ValidChk PreChk
  tauto

/-- **The common run of the one-code modes**: on a well-shaped input passing the pre-scan
checks the machine reaches the end of the validity scan, with the scan state of the chunk
region and the layout in its registers; otherwise it rejects, and then no decomposition of
the input passes the pre-scan checks.

**Proof sketch.** `parse_run`, `layout_run`, `le_phase`, `vscan_run` in sequence; each
rejection is matched with the failed shape or check. -/
theorem one_run (hm : mode ≠ .step) (y : List Bool) :
    (∃ (x w : List Bool) (s : ℕ), Shape1 y x w s ∧ PreChk N x.length s w ∧
      ∃ (st : VAd N) (R : Regs), st.1 = vScan N (w.take (W N * (2 * s + 1))) ∧
        R.Bd (bnd N y) ∧ R.A = 2 * x.length + 2 ∧ R.S = s ∧ R.T = 0 ∧
        R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) ∧
        Reach N mode y (bnd N y) .lenScan ({} : Regs).val (.vDone st) R.val) ∨
    ((∀ x w s, Shape1 y x w s → ¬ PreChk N x.length s w) ∧
      AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
        (some .lenScan, ({} : Regs).val, none)
        false) := by
  set B := bnd N y
  rcases parse_run (N := N) hm y with ⟨x, w, s, q1, cap, hsh, hq1, hcap, r1⟩ | ⟨hno, hhalt⟩
  · obtain ⟨hy, hwid⟩ := hsh
    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hy, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hwid
    have hbig := bnd_ge (N := N) y s hs
    have hlink : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
    have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    set R1 : Regs := { L := y.length, P := 2 * x.length + 2 * w.length + 4, A := 2 * x.length + 2,
                       Q1 := q1, Cap := cap, Q2 := 2 * x.length + 2 * w.length + 4, S := s }
    have hR1 : R1.Bd B := by simp only [R1, Regs.Bd]; omega
    -- uniqueness of the decomposition
    have huniq : ∀ x' w' s', Shape1 y x' w' s' → x' = x ∧ w' = w ∧ s' = s := by
      rintro x' w' s' ⟨hy', -⟩
      rw [hy] at hy'
      obtain ⟨h1, h2⟩ := pairEncode_inj hy'
      obtain ⟨h3, h4⟩ := pairEncode_inj h2
      exact ⟨h1.symm, h3.symm, (bits_injective h4).symm⟩
    rcases layout_run (N := N) (mode := mode) y x w (Nat.bits s) hy R1 s hR1 rfl rfl rfl hs rfl
      rfl rfl rfl rfl rfl rfl (by simp [R1, hm]) with ⟨hlen, hterm, r2⟩ | ⟨hbad, hhalt⟩
    · set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
      set R2 := layR N R1 x.length s pos
      have hpos_lt : pos < 2 * (x.length + 1) := by
        have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
        have h2 : 2 ^ ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
            2 * (x.length + 1) := by
          rw [show ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
            simp; omega]
          exact two_pow_bits_le _ (by omega)
        omega
      have hwP := wP_le x.length
      have hR2 : R2.Bd B := by simp only [R2, R1, layR, Regs.Bd]; omega
      obtain ⟨hle, hgt⟩ := le_phase (N := N) (mode := mode) y R2 hR2 (by simp [R2, R1, layR])
      by_cases hp : pos ≤ x.length + 1
      · left
        have r3 := hle (by simpa [R2, R1, layR] using hp)
        rw [if_neg hm] at r3
        obtain ⟨st, hst, r4⟩ := vscan_run (N := N) (mode := mode) y x w (Nat.bits s) hy R2 s hR2
          (by simp [R2, R1, layR]) (by simp [R2, layR]) (by omega)
        refine ⟨x, w, s, ⟨hy, hwid⟩, ⟨hlen, hterm, hp⟩, st, _, hst, ?_, ?_, ?_, ?_, ?_,
          r1.trans (r2.trans (r3.trans r4))⟩
        · simp only [R2, R1, layR, Regs.Bd]; omega
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, R1, layR]
        · simp [R2, layR, pos]
      · right
        refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt (r1.trans r2) (hgt (by
          simpa [R2, R1, layR] using hp))⟩
        obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
        exact hp hpre.2.2
    · right
      refine ⟨fun x' w' s' hsh' hpre => ?_, AReach.halt r1 hhalt⟩
      obtain ⟨rfl, rfl, rfl⟩ := huniq x' w' s' hsh'
      exact hbad ⟨hpre.1, hpre.2.1⟩
  · right
    exact ⟨fun x w s h => absurd ⟨x, w, s, h⟩ hno, hhalt⟩

/-! ## Valid and accepting codes -/

/-- An indicator through a decidable characterization. -/
lemma indicator_eq_of_iff {L : Language Bool} {y : List Bool} {P : Prop} [Decidable P]
    (h : y ∈ L ↔ P) : MultiTapeTM.indicator (L : Set (List Bool)) y = decide P := by
  rw [indicator_eq_decide]
  exact decide_eq_decide.mpr h

/-- Members of the one-code languages are well shaped. -/
lemma shape_of_code {y x : List Bool} {c s : ℕ}
    (hy : y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)))
    (C : Cfg N.k Bool N.State x) (hc : cfgCode s C = c) : Shape1 y x (Nat.bits c) s := by
  refine ⟨hy, width_of_code s C y ?_⟩
  rw [hy, ← hc, bits_cfgCode]
  exact cfgWord_le_length s C _

/-- **The decider wrapper of the one-code modes.** Let `L` be a language of encoded triples
`⟨x, ⟨bits c, bits s⟩⟩` with `P x c s`, where `P x c s` makes `c` the code of some
configuration, and let `Chk` be a word-level check that is membership at `⟨x, ⟨w, bits s⟩⟩` and
implies the validity test. If, in the one-code mode `mode`, the tail of the codec machine after
the validity scan answers `Chk x s w` from the registers the common run leaves, on every
well-shaped input passing the pre-scan checks, then `L` is in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a result of
[AB09] by itself.

**Proof sketch.** `arm_decides_poly` with the codec machine in mode `mode` and the register bound
`bnd`. By the common run (`one_run`), either the machine reaches the end of the scan, where the
tail answers the check, which is membership; or it rejects, and then no decomposition of the input
passes the pre-scan checks, so the input is no member: a member is well shaped
(`shape_of_code`) and passes the check, hence the validity test and so the pre-scan checks
(`validChk_iff_pre`). -/
theorem oneCode_mem (hm : mode ≠ .step) {L : Language Bool} {P : List Bool → ℕ → ℕ → Prop}
    {Chk : List Bool → ℕ → List Bool → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧ P x c s)
    (hP : ∀ x c s, P x c s → ∃ C : Cfg N.k Bool N.State x, cfgCode s C = c)
    (hchk : ∀ x w s, pairEncode x (pairEncode w (Nat.bits s)) ∈ L ↔ Chk x s w)
    (hval : ∀ x s w, Chk x s w → ValidChk (N := N) x.length s w)
    (htail : ∀ (y x w : List Bool) (s : ℕ) (st : VAd N) (R : Regs), Shape1 y x w s →
      PreChk N x.length s w → s ≤ 2 * y.length → W N * (2 * s + 1) ≤ w.length →
      st.1 = vScan N (w.take (W N * (2 * s + 1))) → R.Bd (bnd N y) →
      R.A = 2 * x.length + 2 → R.S = s → R.T = 0 →
      R.Pos = bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)) →
      ∃ b : Bool, (Chk x s w ↔ b = true) ∧
        AHalt (CA N mode) orc y (GuardLe (CA N mode) y (bnd N y))
          (some (.vDone st), R.val, none) b) :
    L ∈ LOGSPACE := by
  refine arm_decides_poly (CA N mode) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  rw [← orc_eq]
  rcases one_run (N := N) (mode := mode) hm y with
    ⟨x, w, s, hsh, hpre, st, R, hst, hR, hA, hS, hT, hPos, run⟩ | ⟨hfail, hhalt⟩
  · -- the end of the scan: the tail answers the check
    have hyl : y.length = 2 * x.length + 2 * w.length + 4 + (Nat.bits s).length := by
      rw [hsh.eq, length_pairEncode, length_pairEncode]; ring
    have hs := s_le_of_width y s (by omega) hsh.width
    obtain ⟨b, hb, tail⟩ := htail y x w s st R hsh hpre hs (by have := hpre.1; omega) hst hR hA
      hS hT hPos
    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = b := by
      rw [indicator_eq_of_iff (P := b = true) (by rw [hsh.eq, hchk, hb])]
      cases b <;> rfl
    rw [hind]
    exact AReach.halt run tail
  · -- a rejection: members are well shaped and pass the pre-scan checks
    have hind : MultiTapeTM.indicator (L : Set (List Bool)) y = false := by
      rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
      · rfl
      obtain ⟨x, c, s, hy, hPc⟩ := (hL y).mp h
      obtain ⟨C, hc⟩ := hP x c s hPc
      have hsh := shape_of_code hy C hc
      have hv := hval x s _ ((hchk x (Nat.bits c) s).mp (hy ▸ h))
      exact hfail x _ s hsh ((validChk_iff_pre _ _ _).mp hv).1
    rw [hind]
    exact hhalt

/-- **Valid codes form a logspace language** (`Complexity.Codec.validLang`).

**Proof sketch.** The one-code wrapper (`oneCode_mem`) in mode `valid`: the tail answers the
scan verdict at once, which on inputs passing the pre-scan checks is the validity test
(`validChk_iff_pre`), i.e. membership (`validLang_iff`). -/
theorem validLang_mem : validLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .valid) (by decide) (mem_validLang_iff N)
    (fun _ _ _ ⟨C, _, hc⟩ => ⟨C, hc⟩) (validLang_iff N) (fun _ _ _ h => h) ?_
  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
  refine ⟨decide (VAcc N st.1), ?_, AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
  rw [decide_eq_true_eq, validChk_iff_pre, hst]
  exact ⟨fun h => h.2, fun h => ⟨hpre, h⟩⟩

/-- **Accepting codes form a logspace language** (`Complexity.Codec.acceptLang`).

**Proof sketch.** As `validLang_mem`, answering the scan verdict together with the header
`(halted, accept)` (`acceptLang_iff`). -/
theorem acceptLang_mem : acceptLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .accept) (by decide) (mem_acceptLang_iff N)
    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (acceptLang_iff N) (fun _ _ _ h => h.1) ?_
  intro _ x w s st R _ hpre _ _ hst hR _ _ _ _
  refine ⟨decide (VAcc N st.1 ∧ st.1.2.1 = some (none, 1)), ?_,
    AHalt.ret rfl ⟨by simp [PreS, CA], hR.val_le⟩⟩
  rw [decide_eq_true_eq, AcceptChk, validChk_iff_pre, hst]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hpre, h.1⟩, h.2⟩⟩

/-! ## The initial code -/

variable (N) in
/-- The scan-state part of the initial-code test. -/
def InitScan (st : VSt N) : Prop :=
  VAcc N st ∧ st.2.1 = some (some N.tm.q₀, 0) ∧ st.2.2.2.2.2 = true

instance (st : VSt N) : Decidable (InitScan N st) := by unfold InitScan; infer_instance

/-- **The tail of the initial-code mode**: after the scan, test the scan state, the input
position (`= 1`) and, with work tapes, the head flag of tape `0` in the middle cell.

**Proof sketch.** A finite branch on the scan state; two zero tests around one decrement for
the position; for the middle cell, the address `a + 2(W s + hH + 2)` is computed by a copy, a
scale and an increment chain, and read through the bit oracle (`getD_w`). -/
theorem init_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .init) orc y (GuardLe (CA N .init) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true))) := by
  set B := bnd N y
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
  -- answering from a label whose instruction is `ret`
  have hret : ∀ (l : Lab N) (v : Fin 21 → ℕ) (b : Bool), (∀ r, v r ≤ B) →
      CA N .init l = .ret b →
        AHalt (CA N .init) orc y (GuardLe (CA N .init) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  have hv0 := hBd.val_le
  by_cases hscan : InitScan N st.1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hscan]]
    have r1 : Reach N .init y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
        (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
    exact AReach.halt r1 (hret _ _ _ hv0 rfl)
  have r1 : Reach N .init y B (.vDone st) R.val .iz1 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA, goto]))
      (by simp only [InitScan] at hscan; simp [astep, CA, goto, hscan])
  by_cases hp0 : R.Pos = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp0]]
    have r2 : Reach N .init y B .iz1 R.val .rej R.val :=
      Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
    exact AReach.halt (r1.trans r2) (hret _ _ _ hv0 rfl)
  have r2 : Reach N .init y B .iz1 R.val .iz2 R.val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA, hp0])
  have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
  have r3 : Reach N .init y B .iz2 R.val .iz3 ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv0 (by simp [PreS, CA])) (by simp [astep, CA])
  by_cases hp1 : R.Pos = 1
  swap
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = false by simp [hp1]]
    have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .rej
        ({R with Pos := R.Pos - 1} : Regs).val :=
      Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
        (by simp [astep, CA]; omega)
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le rfl)
  have r4 : Reach N .init y B .iz3 ({R with Pos := R.Pos - 1} : Regs).val .icen
      ({R with Pos := R.Pos - 1} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA]; omega)
  set R1 : Regs := {R with Pos := R.Pos - 1}
  by_cases hk : N.k = 0
  · rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
        (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) = true by simp [hscan, hp1, hk]]
    exact AReach.halt (r1.trans (r2.trans (r3.trans r4))) (hret _ _ _ hv1.val_le (by simp [CA, hk]))
  -- the middle cell
  have hkpos : 1 ≤ N.k := Nat.one_le_iff_ne_zero.mpr hk
  have hWh : hH N + 3 ≤ W N := by simp [W]; omega
  have hidx : W N * s + (hH N + 2) < W N * (2 * s + 1) := by
    have : W N * (2 * s + 1) = W N * s + W N * s + W N := by ring
    have : 0 ≤ W N * s := Nat.zero_le _
    omega
  have hAB : R.A ≤ y.length := by rw [hA]; omega
  have r5 : Reach N .init y B .icen R1.val .clrUc R1.val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA, hk, goto])) (by simp [astep, CA, hk, goto])
  have r6 : Reach N .init y B .clrUc R1.val (.cp .Uc) ({R1 with U := 0} : Regs).val :=
    Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA])
  have r7 : Reach N .init y B (.cp .Uc) ({R1 with U := 0} : Regs).val (.cp .Tsc)
      ({R1 with U := R.A} : Regs).val :=
    Reach.cast (cp_run y B .Uc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc])) (by simp [cpDst, cpSrc, R1])
  have r8 : Reach N .init y B (.cp .Tsc) ({R1 with U := R.A} : Regs).val (.sc .C)
      ({R1 with U := R.A, T := s} : Regs).val :=
    Reach.cast (cp_run y B .Tsc _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [cpDst, cpSrc, R1, hT])) (by simp [cpDst, cpSrc, R1, hS])
  have hscl : R.A + 2 * W N * s + 2 * (hH N + 2) ≤ B := by
    have : 2 * W N * s + 2 * (hH N + 2) ≤ 2 * (W N * (2 * s + 1)) := by
      have : 2 * W N * s = 2 * (W N * s) := by ring
      omega
    omega
  have r9 : Reach N .init y B (.sc .C) ({R1 with U := R.A, T := s} : Regs).val (icL N .C 0)
      ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val :=
    Reach.cast (sc_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [scDst, scSrc, scFactor, R1]; omega)) (by simp [scDst, scSrc, scFactor, R1])
  have r10 : Reach N .init y B (icL N .C 0) ({R1 with U := R.A + 2 * W N * s, T := 0} : Regs).val
      .cenRead ({R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0} : Regs).val :=
    Reach.cast (ic_run y B .C _ (by apply Regs.Bd.val_le; simp only [R1, Regs.Bd]; omega)
      (by simp [icReg, icCount, R1]; omega)) (by simp [icReg, icCount, R1])
  set R2 : Regs := {R1 with U := R.A + 2 * W N * s + 2 * (hH N + 2), T := 0}
  have hR2 : R2.Bd B := by simp only [R2, R1, Regs.Bd]; omega
  have hbit : y.getD (R.A + 2 * W N * s + 2 * (hH N + 2)) false =
      w.getD (W N * s + (hH N + 2)) false := by
    rw [hA, show 2 * x.length + 2 + 2 * W N * s + 2 * (hH N + 2) =
      2 * x.length + 2 + 2 * (W N * s + (hH N + 2)) by ring, hy, getD_w _ _ _ _ (by omega)]
  rw [List.getD_eq_getElem?_getD] at hbit
  rw [show decide (InitScan N st.1 ∧ R.Pos = 1 ∧
      (N.k = 0 ∨ w.getD (W N * s + (hH N + 2)) false = true)) =
      w.getD (W N * s + (hH N + 2)) false by
    rw [List.getD_eq_getElem?_getD]; simp [hscan, hp1, hk]]
  rw [List.getD_eq_getElem?_getD]
  cases hb : (w[W N * s + (hH N + 2)]?).getD false
  · have r11 : Reach N .init y B .cenRead R2.val .rej R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)
  · have r11 : Reach N .init y B .cenRead R2.val .acc R2.val :=
      Reach.single' (gd_of hR2.val_le (by simp [PreS, CA]))
        (by simp [astep, CA, vword_whole₁, orc_bit, R2, hbit, hb])
    exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans
      (r8.trans (r9.trans (r10.trans r11)))))))))) (hret _ _ _ hR2.val_le rfl)

/-- **The initial code forms a logspace language** (`Complexity.Codec.initLang`).

**Proof sketch.** As `validLang_mem`, with the initial-code tail (`init_tail`) and the
initial-code check (`initLang_iff`). -/
theorem initLang_mem : initLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .init) (by decide) (mem_initLang_iff N)
    (fun x _ _ hc => ⟨N.tm.initCfg x, hc⟩) (initLang_iff N) (fun _ _ _ h => h.1) ?_
  intro y x w s st R hsh hpre hs hw hst hR hA hS hT hPos
  refine ⟨_, ?_, init_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
  rw [decide_eq_true_eq, InitChk, validChk_iff_pre, hst, InitScan, hPos]
  constructor
  · rintro ⟨⟨-, hv⟩, h2, h3, h4, h5⟩
    exact ⟨⟨hv, h2, h3⟩, h4, h5⟩
  · rintro ⟨⟨hv, h2, h3⟩, h4, h5⟩
    exact ⟨⟨hpre, hv⟩, h2, h3, h4, h5⟩


/-! ## Edge codes

The edge-code mode reads, tape by tape, the head flags of the first and last cells of the chunk
region. Its run is proved from the table equations of `CA` at its labels (`CA_eRd1`, …), the
step equations of `astep` and the published loop runs, without unfolding `CA` or `astep`. -/

section Edge

variable (N) in
/-- The syntactic preconditions an instruction of the edge tail meets: distinct registers in an
equality test, distinct call arguments, and no input comparison. -/
private def EdgeOK : Ins 21 2 (Lab N) → Prop
  | .jeq r s _ _ => r ≠ s
  | .call _ _ args _ _ => args.Nodup
  | .jeqIn _ _ _ => False
  | .jeqFst _ _ _ => False
  | .jeqSnd _ _ _ => False
  | _ => True

variable {y : List Bool} {B : ℕ}

/-- The guard at a label of the edge tail, from its instruction's table equation. -/
private lemma edge_gd {l : Lab N} {v : Fin 21 → ℕ} (hv : ∀ r, v r ≤ B) {i : Ins 21 2 (Lab N)}
    (hl : CA N .edge l = i) (hi : EdgeOK N i) : GuardLe (CA N .edge) y B (some l, v, none) := by
  subst hl
  refine gd_of hv (preS_of_ins ?_ ?_ ?_ ?_ ?_)
  · intro r s l₁ l₀ h; rw [h] at hi; exact hi
  · intro j md args l₁ l₀ h; rw [h] at hi; exact hi
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim
  · intro r l₁ l₀ h; rw [h] at hi; exact hi.elim

/-- **One round of the edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape
`i` in the first cell, `Q3 = q + 1` and `T = 0`, the machine answers `true` if tape `i`'s flag is
set in the first or the last cell, and otherwise reaches `eTest` with `Q3 = q` and the other
registers it reads unchanged.

**Proof sketch.** Read the flag at `U` (`orc_bit`, `getD_w`); on `1` answer `true`. Otherwise copy
`U` to `Q1`, add `4W · s` (copy `S` to `T`, then the scale loop) and read the flag of the last cell;
on `1` answer `true`. Otherwise count `Q3` down. -/
theorem edge_round (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B)
    (i : ℕ) (hi : i < N.k) (q : ℕ) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hS : v rS = s) (hT : v rT = 0)
    (hU : v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2)) (hQ : v rQ3 = q + 1) :
    ((w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none) true) ∧
    (¬ (w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true) →
      ∃ v', Reach N .edge y B .eRd1 v .eTest v' ∧ (∀ r, v' r ≤ B) ∧
        v' rS = s ∧ v' rT = 0 ∧ v' rU = v rU ∧ v' rQ3 = q) := by
  have hW0 : hH N + 3 * i + 2 < W N := by rw [W_eq]; omega
  have hWs : W N * (2 * s + 1) = W N * (2 * s) + W N := by ring
  -- the flag of tape `i` in the first cell
  have hidx0 : hH N + 3 * i + 2 < w.length := by
    have : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hbit0 : y.getD (v rU) false = w.getD (hH N + 3 * i + 2) false := by
    rw [hU, hy]; exact getD_w x w rest _ hidx0
  have e1 : astep (CA N .edge) orc y (some .eRd1, v, none) =
      (some (if w.getD (hH N + 3 * i + 2) false = true then .acc else .eFar), v, none) := by
    rw [astep_call (CA_eRd1 .edge)]; simp only [vword_whole₁, orc_bit, hbit0]
  have hg1 : GuardLe (CA N .edge) y B (some .eRd1, v, none) :=
    edge_gd hv (CA_eRd1 .edge) (by simp [EdgeOK])
  have r1 : ¬ w.getD (hH N + 3 * i + 2) false = true → Reach N .edge y B .eRd1 v .eFar v :=
    fun h => Reach.single' hg1 (by rw [e1, if_neg h])
  -- the address of the flag in the last cell: `Q1 := U + 4W · s`
  set v1 := Function.update v rQ1 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rQ1 _ _ hv (Nat.zero_le _)
  have r2 : Reach N .edge y B .eFar v (.cp .Qe) v1 :=
    Reach.single' (edge_gd hv (CA_eFar .edge) trivial) (astep_clr (CA_eFar .edge))
  have h1U : v1 rU = v rU := by rw [hv1, Function.update_of_ne (by decide)]
  have h1Q : v1 rQ1 = 0 := by rw [hv1, Function.update_self]
  set v2 := Function.update v1 rQ1 (v rU) with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rQ1 _ _ hv1B (hv rU)
  have r3 : Reach N .edge y B (.cp .Qe) v1 (.cp .Te) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Qe v1 hv1B
      (by rw [cpDst_Qe, cpSrc_Qe, h1Q]; exact Nat.zero_le _)
    rwa [cpNext_Qe, cpDst_Qe, cpSrc_Qe, h1U] at h
  have h2T : v2 rT = 0 := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hT]
  have h2S : v2 rS = s := by
    rw [hv2, Function.update_of_ne (by decide), hv1, Function.update_of_ne (by decide), hS]
  set v3 := Function.update v2 rT s with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rT _ _ hv2B hsB
  have r4 : Reach N .edge y B (.cp .Te) v2 (.sc .Ee) v3 := by
    have h := cp_run (N := N) (mode := .edge) y B .Te v2 hv2B
      (by rw [cpDst_Te, cpSrc_Te, h2T]; exact Nat.zero_le _)
    rwa [cpNext_Te, cpDst_Te, cpSrc_Te, h2S] at h
  have h3T : v3 rT = s := by rw [hv3, Function.update_self]
  have h3Q : v3 rQ1 = v rU := by
    rw [hv3, Function.update_of_ne (by decide), hv2, Function.update_self]
  have hfar : v rU + 4 * W N * s ≤ B := by
    have : 4 * W N * s = 2 * (W N * (2 * s)) := by ring
    omega
  set v4 := Function.update (Function.update v3 rT 0) rQ1 (v rU + 4 * W N * s) with hv4
  have hv4B : ∀ r, v4 r ≤ B :=
    register_update_le _ rQ1 _ _ (register_update_le _ rT _ _ hv3B (Nat.zero_le _)) hfar
  have r5 : Reach N .edge y B (.sc .Ee) v3 .eRd2 v4 := by
    have h := sc_run (N := N) (mode := .edge) y B .Ee v3 hv3B
      (by rw [scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T]; exact hfar)
    rwa [scNext_Ee, scDst_Ee, scSrc_Ee, scFactor_Ee, h3Q, h3T] at h
  -- the flag of tape `i` in the last cell
  have h4Q : v4 rQ1 = v rU + 4 * W N * s := by rw [hv4, Function.update_self]
  have hidx1 : W N * (2 * s) + (hH N + 3 * i + 2) < w.length := by omega
  have hbit1 : y.getD (v4 rQ1) false =
      w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false := by
    rw [h4Q, hU, hy, show 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) + 4 * W N * s =
      2 * x.length + 2 + 2 * (W N * (2 * s) + (hH N + 3 * i + 2)) by ring]
    exact getD_w x w rest _ hidx1
  have e2 : astep (CA N .edge) orc y (some .eRd2, v4, none) =
      (some (if w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true then .acc else .eNext),
        v4, none) := by
    rw [astep_call (CA_eRd2 .edge)]; simp only [vword_whole₁, orc_bit, hbit1]
  have hg2 : GuardLe (CA N .edge) y B (some .eRd2, v4, none) :=
    edge_gd hv4B (CA_eRd2 .edge) (by simp [EdgeOK])
  -- count the tape down
  set v5 := Function.update v4 rQ3 (v4 rQ3 - 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B :=
    register_update_le _ rQ3 _ _ hv4B (le_trans (Nat.sub_le _ _) (hv4B rQ3))
  have r6 : Reach N .edge y B .eNext v4 .eTest v5 :=
    Reach.single' (edge_gd hv4B (CA_eNext .edge) trivial) (astep_dec (CA_eNext .edge))
  constructor
  · intro hP
    by_cases hb0 : w.getD (hH N + 3 * i + 2) false = true
    · refine AHalt.step hg1 ?_
      rw [e1, if_pos hb0]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv (CA_acc .edge) trivial)
    · have hb1 := hP.resolve_left hb0
      refine AReach.halt ((r1 hb0).trans (r2.trans (r3.trans (r4.trans r5)))) (AHalt.step hg2 ?_)
      rw [e2, if_pos hb1]
      exact AHalt.ret (CA_acc .edge) (edge_gd hv4B (CA_acc .edge) trivial)
  · intro hP
    rw [not_or] at hP
    refine ⟨v5, (r1 hP.1).trans (r2.trans (r3.trans (r4.trans (r5.trans
      ((Reach.single' hg2 (by rw [e2, if_neg hP.2])).trans r6))))), hv5B, ?_, ?_, ?_, ?_⟩
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), h2S]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_self]
    · rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hv3, Function.update_of_ne (by decide), hv2,
        Function.update_of_ne (by decide), h1U]
    · have h4Q3 : v4 rQ3 = q + 1 := by
        rw [hv4, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hv3,
          Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
          Function.update_of_ne (by decide), hQ]
      rw [hv5, Function.update_self, h4Q3, Nat.add_sub_cancel]

/-- **The edge loop**: from `eRd1` at tape `i`, with `U` at the head flag of tape `i` in the
first cell, `Q3 = k - i` and `T = 0`, the machine answers whether some tape `i' ≥ i` has its head
flag set in the first or the last cell of the chunk region.

**Proof sketch.** Induction on `k - i`, one tape per round (`edge_round`). After a round without
a set flag, `Q3` is tested: at `0` there is no further tape and the machine answers `false`;
otherwise `U` advances by `6` (two increment chains of `3`) to the next tape. -/
theorem edge_loop (x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest)) (s : ℕ)
    (hw : W N * (2 * s + 1) ≤ w.length)
    (hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B) (hsB : s ≤ B) :
    ∀ m (i : ℕ) (v : Fin 21 → ℕ), i + (m + 1) = N.k → (∀ r, v r ≤ B) →
      v rS = s → v rT = 0 → v rU = 2 * x.length + 2 + 2 * (hH N + 3 * i + 2) →
      v rQ3 = m + 1 →
      AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y B) (some .eRd1, v, none)
        (decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true))) := by
  intro m
  induction m with
  | zero =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ := edge_round x w rest hy s hw hB hsB i (by omega) 0 v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, -, -, -, hQ'⟩ := hno hP
      rw [decide_eq_false (by
        rintro ⟨i', hle, hP'⟩
        have hi' : (i' : ℕ) = i := by have := i'.isLt; omega
        rw [hi'] at hP'
        exact hP hP')]
      refine AReach.halt r (AHalt.step (edge_gd hv'B (CA_eTest .edge) trivial) ?_)
      rw [astep_jz (CA_eTest .edge), if_pos hQ']
      exact AHalt.ret (CA_rej .edge) (edge_gd hv'B (CA_rej .edge) trivial)
  | succ m ih =>
    intro i v hik hv hS hT hU hQ
    obtain ⟨hyes, hno⟩ :=
      edge_round x w rest hy s hw hB hsB i (by omega) (m + 1) v hv hS hT hU hQ
    by_cases hP : w.getD (hH N + 3 * i + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * i + 2)) false = true
    · rw [decide_eq_true ⟨⟨i, by omega⟩, le_rfl, hP⟩]; exact hyes hP
    · obtain ⟨v', r, hv'B, hS', hT', hU', hQ'⟩ := hno hP
      have r7 : Reach N .edge y B .eTest v' (icL N .S1 0) v' :=
        Reach.single' (edge_gd hv'B (CA_eTest .edge) trivial)
          (by rw [astep_jz (CA_eTest .edge), if_neg (by omega)])
      have hW1 : hH N + 3 * (i + 1) + 2 < W N := by rw [W_eq]; omega
      have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have hU6 : v' rU + 6 ≤ B := by omega
      set v6 := Function.update v' rU (v' rU + 3) with hv6
      have hv6B : ∀ r, v6 r ≤ B := register_update_le _ rU _ _ hv'B (by omega)
      have r8 : Reach N .edge y B (icL N .S1 0) v' (icL N .S2 0) v6 := by
        have h := ic_run (N := N) (mode := .edge) y B .S1 v' hv'B
          (by rw [icReg_S1, icCount_S1]; omega)
        rwa [icNext_S1, icReg_S1, icCount_S1, ← icL_zero] at h
      have h6U : v6 rU = v' rU + 3 := by rw [hv6, Function.update_self]
      set v7 := Function.update v6 rU (v6 rU + 3) with hv7
      have hv7B : ∀ r, v7 r ≤ B := register_update_le _ rU _ _ hv6B (by omega)
      have r9 : Reach N .edge y B (icL N .S2 0) v6 .eRd1 v7 := by
        have h := ic_run (N := N) (mode := .edge) y B .S2 v6 hv6B
          (by rw [icReg_S2, icCount_S2]; omega)
        rwa [icNext_S2, icReg_S2, icCount_S2] at h
      have h7 := ih (i + 1) v7 (by omega) hv7B
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hS'])
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hT'])
        (by rw [hv7, Function.update_self, h6U, hU', hU]; ring)
        (by rw [hv7, Function.update_of_ne (by decide), hv6, Function.update_of_ne (by decide),
          hQ'])
      have hans : decide (∃ i' : Fin N.k, i ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) =
          decide (∃ i' : Fin N.k, i + 1 ≤ (i' : ℕ) ∧
          (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
            w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) := by
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨i', hle, hP'⟩
          refine ⟨i', ?_, hP'⟩
          rcases Nat.lt_or_ge i (i' : ℕ) with h | h
          · omega
          · have hi' : (i' : ℕ) = i := by omega
            rw [hi'] at hP'
            exact absurd hP' hP
        · rintro ⟨i', hle, hP'⟩
          exact ⟨i', by omega, hP'⟩
      rw [hans]
      exact AReach.halt (r.trans (r7.trans (r8.trans r9))) h7

end Edge


/-- **The tail of the edge-code mode**: after the scan, test the scan state and, tape by tape,
the head flags of the first and last cells.

**Proof sketch.** A finite branch on the scan state (`CA_vDone_edge`). Without work tapes the
machine answers `false`. Otherwise it sets `U` to the address `a + 2(hH + 2)` of tape `0`'s flag
in the first cell (a clear, a copy and an increment chain) and the tape counter `Q3` to `k`,
and runs the edge loop (`edge_loop`). -/
theorem edge_tail (y x w rest : List Bool) (hy : y = pairEncode x (pairEncode w rest))
    (R : Regs) (s : ℕ) (st : VAd N) (hBd : R.Bd (bnd N y)) (hA : R.A = 2 * x.length + 2)
    (hS : R.S = s) (hT : R.T = 0) (hs : s ≤ 2 * y.length)
    (hw : W N * (2 * s + 1) ≤ w.length) :
    AHalt (CA N .edge) orc y (GuardLe (CA N .edge) y (bnd N y)) (some (.vDone st), R.val, none)
      (decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true)) := by
  set B := bnd N y
  have hv0 := hBd.val_le
  have hyl : y.length = 2 * x.length + 2 * w.length + 4 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hB : 2 * x.length + 2 + 2 * (W N * (2 * s + 1)) ≤ B := by
    have : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
    omega
  have hsB : s ≤ B := by omega
  have e0 : astep (CA N .edge) orc y (some (.vDone st), R.val, none) =
      (some (if VAcc N st.1 then .eStart else .rej), R.val, none) := by
    rw [astep_jz ((CA_vDone_edge st).trans (goto_eq _)), ite_self]
  have hg0 : GuardLe (CA N .edge) y B (some (.vDone st), R.val, none) :=
    edge_gd hv0 ((CA_vDone_edge st).trans (goto_eq _)) trivial
  by_cases hacc : VAcc N st.1
  swap
  · rw [decide_eq_false (fun h => hacc h.1)]
    refine AHalt.step hg0 ?_
    rw [e0, if_neg hacc]
    exact AHalt.ret (CA_rej .edge) (edge_gd hv0 (CA_rej .edge) trivial)
  have r0 : Reach N .edge y B (.vDone st) R.val .eStart R.val :=
    Reach.single' hg0 (by rw [e0, if_pos hacc])
  by_cases hk : N.k = 0
  · rw [decide_eq_false (fun ⟨_, i, _⟩ => absurd i.isLt (by omega))]
    exact AReach.halt r0 (AHalt.ret (CA_eStart_of_zero .edge hk)
      (edge_gd hv0 (CA_eStart_of_zero .edge hk) trivial))
  -- the address of tape `0`'s flag in the first cell, and the tape counter
  set v1 := Function.update R.val rU 0 with hv1
  have hv1B : ∀ r, v1 r ≤ B := register_update_le _ rU _ _ hv0 (Nat.zero_le _)
  have r1 : Reach N .edge y B .eStart R.val (.cp .Ue) v1 :=
    Reach.single' (edge_gd hv0 (CA_eStart_of_pos .edge hk) trivial)
      (astep_clr (CA_eStart_of_pos .edge hk))
  have h1A : v1 rA = R.A := by rw [hv1, Function.update_of_ne (by decide), Regs.val_A]
  set v2 := Function.update v1 rU R.A with hv2
  have hv2B : ∀ r, v2 r ≤ B := register_update_le _ rU _ _ hv1B (by rw [hA]; omega)
  have r2 : Reach N .edge y B (.cp .Ue) v1 (icL N .Eh 0) v2 := by
    have h := cp_run (N := N) (mode := .edge) y B .Ue v1 hv1B
      (by rw [cpDst_Ue, cpSrc_Ue, hv1, Function.update_self]; exact Nat.zero_le _)
    rwa [cpNext_Ue, cpDst_Ue, cpSrc_Ue, h1A, ← icL_zero] at h
  have h2U : v2 rU = R.A := by rw [hv2, Function.update_self]
  have hW0 : hH N + 2 < W N := by rw [W_eq]; omega
  have hWs : W N ≤ W N * (2 * s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  set v3 := Function.update v2 rU (R.A + 2 * (hH N + 2)) with hv3
  have hv3B : ∀ r, v3 r ≤ B := register_update_le _ rU _ _ hv2B (by omega)
  have r3 : Reach N .edge y B (icL N .Eh 0) v2 .eK v3 := by
    have h := ic_run (N := N) (mode := .edge) y B .Eh v2 hv2B
      (by rw [icReg_Eh, icCount_Eh, h2U]; omega)
    rwa [icNext_Eh, icReg_Eh, icCount_Eh, h2U] at h
  set v4 := Function.update v3 rQ3 0 with hv4
  have hv4B : ∀ r, v4 r ≤ B := register_update_le _ rQ3 _ _ hv3B (Nat.zero_le _)
  have r4 : Reach N .edge y B .eK v3 (icL N .Ke 0) v4 :=
    Reach.single' (edge_gd hv3B (CA_eK .edge) trivial) (astep_clr (CA_eK .edge))
  have hkB : N.k - 1 + 1 ≤ B := by
    have : N.k ≤ W N := by rw [W_eq]; omega
    omega
  set v5 := Function.update v4 rQ3 (N.k - 1 + 1) with hv5
  have hv5B : ∀ r, v5 r ≤ B := register_update_le _ rQ3 _ _ hv4B hkB
  have r5 : Reach N .edge y B (icL N .Ke 0) v4 .eRd1 v5 := by
    have h := ic_run (N := N) (mode := .edge) y B .Ke v4 hv4B
      (by rw [icReg_Ke, icCount_Ke, hv4, Function.update_self]; omega)
    rwa [icNext_Ke, icReg_Ke, icCount_Ke, hv4, Function.update_self, Nat.zero_add] at h
  have hloop := edge_loop (y := y) (B := B) x w rest hy s hw hB hsB (N.k - 1) 0 v5 (by omega)
    hv5B
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_S, hS])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_of_ne (by decide), hv2, Function.update_of_ne (by decide), hv1,
      Function.update_of_ne (by decide), Regs.val_T, hT])
    (by rw [hv5, Function.update_of_ne (by decide), hv4, Function.update_of_ne (by decide), hv3,
      Function.update_self, hA])
    (by rw [hv5, Function.update_self])
  rw [show decide (VAcc N st.1 ∧ ∃ i : Fin N.k, w.getD (hH N + 3 * (i : ℕ) + 2) false = true ∨
      w.getD (W N * (2 * s) + (hH N + 3 * (i : ℕ) + 2)) false = true) =
      decide (∃ i' : Fin N.k, 0 ≤ (i' : ℕ) ∧ (w.getD (hH N + 3 * (i' : ℕ) + 2) false = true ∨
        w.getD (W N * (2 * s) + (hH N + 3 * (i' : ℕ) + 2)) false = true)) from
    decide_eq_decide.mpr ⟨fun ⟨_, i, h⟩ => ⟨i, Nat.zero_le _, h⟩,
      fun ⟨i, _, h⟩ => ⟨hacc, i, h⟩⟩]
  exact AReach.halt (r0.trans (r1.trans (r2.trans (r3.trans (r4.trans r5))))) hloop

/-- **Edge codes form a logspace language** (`Complexity.Codec.edgeLang`).

**Proof sketch.** As `validLang_mem`, with the edge-code tail (`edge_tail`) and the edge-code
check (`edgeLang_iff`). -/
theorem edgeLang_mem : edgeLang N ∈ LOGSPACE := by
  refine oneCode_mem (mode := .edge) (by decide) (mem_edgeLang_iff N)
    (fun _ _ _ ⟨C, _, hc, _⟩ => ⟨C, hc⟩) (edgeLang_iff N)
    (fun x s w h => ((edgeChk_def N x s w).mp h).1) ?_
  intro y x w s st R hsh hpre hs hw hst hR hA hS hT _
  refine ⟨_, ?_, edge_tail y x w (Nat.bits s) hsh.eq R s st hR hA hS hT hs hw⟩
  rw [decide_eq_true_eq, edgeChk_def, validChk_iff_pre, hst]
  exact ⟨fun ⟨⟨_, hv⟩, h⟩ => ⟨hv, h⟩, fun ⟨hv, h⟩ => ⟨⟨hpre, hv⟩, h⟩⟩

end Complexity.Codec
```

## ===== TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Layout2
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The step language is logspace

The codec machine `Complexity.Codec.CA` in mode `step` decides
`Complexity.Codec.stepLang N`: after the parse (`parse_run₂`), the layout of both code words
(`layout_run`, `layout2_run`), the position comparison (`le_phase`), the input-symbol read
(`insym_run`) and the validity scan of the first word (`vscan_run`), it reads the step data
into its control, moves the first word's input position by the action of each choice bit
and compares it with the second word's (`pm_run`), and runs the double sliding scan of the
two chunk regions (`s_run`). `Complexity.LogProg.arm_decides_poly` turns this into
membership in `L`.

Configuration-graph infrastructure for logspace algorithms ([AB09, §4.1.1, §4.3]); not a
result of [AB09] by itself.

## Main definitions

* `Complexity.Codec.stepAns` — the answer of the step machine after the scan.

## Main results

* `Complexity.Codec.z_run`, `Complexity.Codec.step_tail` — the step tail.
* `Complexity.Codec.pm_run` — the position move and comparison of one choice bit.
* `Complexity.Codec.stepLang_mem` — the step language is in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, §4.3.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool}

/-- A Boolean branch is the branch at the decision. -/
lemma ite_bool {α : Type} (p : Prop) [Decidable p] (f : Bool → α) :
    (if p then f true else f false) = f (decide p) := by
  by_cases h : p <;> simp [h]

/-- **The position move of one choice bit**: from `.pm I b f .start`, the machine compares
`rPos` moved by the action of `b` (clamped to `[0, rN1]`) with `rPos2`, restores `rPos`, and
continues with the verdict.

**Proof sketch.** By the move: no move compares directly; a right move compares directly at
the right end and otherwise increments, compares and decrements; a left move compares
directly at `0` and otherwise decrements, compares and increments. -/
theorem pm_run (y : List Bool) (I : SInfo N) (b f : Bool) (R : Regs) (hBd : R.Bd (bnd N y))
    (hN1 : 1 ≤ R.N1) (hle : R.Pos ≤ R.N1) (hbig : R.N1 + 1 ≤ bnd N y) :
    Reach N .step y (bnd N y) (.pm I b f .start) R.val
      (pmNext N I b f (decide (movePos (R.N1 - 1) R.Pos (aI N I b).inputTape = R.Pos2))) R.val := by
  set B := bnd N y
  have hv := hBd.val_le
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  cases hm : (aI N I b).inputTape with
  | zero =>
    refine Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) ?_
    simp only [astep, CA, hm, Regs.val_Pos, Regs.val_Pos2]
    rw [ite_bool]; rfl
  | pos =>
    by_cases hp : R.Pos = R.N1
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .eq) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) (by simp [astep, CA, hm, hp])
      refine r1.trans (Reach.single' (gd_of hv (by simp [PreS, CA]; decide)) ?_)
      simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
      rw [ite_bool]
      simp [movePos, show R.N1 - 1 + 1 = R.N1 by omega, hp]
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .inc) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm]; decide)) (by simp [astep, CA, hm, hp])
      have hv1 : ({R with Pos := R.Pos + 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
      have r2 : Reach N .step y B (.pm I b f .inc) R.val (.pm I b f .eq2)
          ({R with Pos := R.Pos + 1} : Regs).val :=
        Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
      have r3 : Reach N .step y B (.pm I b f .eq2) ({R with Pos := R.Pos + 1} : Regs).val
          (.pm I b f (.decR (decide (R.Pos + 1 = R.Pos2))))
          ({R with Pos := R.Pos + 1} : Regs).val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]; decide))
          (by simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
              by_cases h : R.Pos + 1 = R.Pos2 <;> simp [h])
      have r4 : Reach N .step y B (.pm I b f (.decR (decide (R.Pos + 1 = R.Pos2))))
          ({R with Pos := R.Pos + 1} : Regs).val (pmNext N I b f (decide (R.Pos + 1 = R.Pos2)))
          R.val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA])) (by simp [astep, CA])
      refine (r1.trans (r2.trans (r3.trans r4))).cast rfl |> fun h => ?_
      have : movePos (R.N1 - 1) R.Pos .pos = R.Pos + 1 := by
        simp [movePos, show R.N1 - 1 + 1 = R.N1 by omega, hp]
      rw [this]
      exact h
  | neg =>
    by_cases hp : R.Pos = 0
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .eq) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm])) (by simp [astep, CA, hm, hp])
      refine r1.trans (Reach.single' (gd_of hv (by simp [PreS, CA]; decide)) ?_)
      simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
      rw [ite_bool]
      simp [movePos, hp]
    · have r1 : Reach N .step y B (.pm I b f .start) R.val (.pm I b f .decN) R.val :=
        Reach.single' (gd_of hv (by simp [PreS, CA, hm])) (by simp [astep, CA, hm, hp])
      have hv1 : ({R with Pos := R.Pos - 1} : Regs).Bd B := by simp only [Regs.Bd]; omega
      have r2 : Reach N .step y B (.pm I b f .decN) R.val (.pm I b f .eq3)
          ({R with Pos := R.Pos - 1} : Regs).val :=
        Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
      have r3 : Reach N .step y B (.pm I b f .eq3) ({R with Pos := R.Pos - 1} : Regs).val
          (.pm I b f (.incR (decide (R.Pos - 1 = R.Pos2))))
          ({R with Pos := R.Pos - 1} : Regs).val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]; decide))
          (by simp only [astep, CA, Regs.val_Pos, Regs.val_Pos2]
              by_cases h : R.Pos - 1 = R.Pos2 <;> simp [h])
      have r4 : Reach N .step y B (.pm I b f (.incR (decide (R.Pos - 1 = R.Pos2))))
          ({R with Pos := R.Pos - 1} : Regs).val (pmNext N I b f (decide (R.Pos - 1 = R.Pos2)))
          R.val :=
        Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
          (by simp [astep, CA, show R.Pos - 1 + 1 = R.Pos by omega])
      have : movePos (R.N1 - 1) R.Pos .neg = R.Pos - 1 := rfl
      rw [this]
      exact r1.trans (r2.trans (r3.trans r4))

/-- **Reading the step data into the control**: the code of the input symbol in `rZ` becomes
the second component of the step data.

**Proof sketch.** A zero test, a decrement and a second zero test on `rZ` distinguish the
three codes. -/
theorem z_run (y x : List Bool) (σ : VSt N) (R : Regs) (hBd : R.Bd (bnd N y)) (p : ℕ)
    (hZ : R.Z = zcode (inpOf x p)) :
    ∃ z, z ≤ 2 ∧ Reach N .step y (bnd N y) (.zA σ) R.val (.pm (σ, inpOf x p) false false .start)
      ({R with Z := z} : Regs).val := by
  have hv := hBd.val_le
  cases hin : inpOf x p with
  | none =>
    rw [hin] at hZ
    simp only [zcode] at hZ
    have hR : ({R with Z := 0} : Regs) = R := by cases R; simp_all
    refine ⟨0, by omega, ?_⟩
    rw [hR]
    exact Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA, hZ])
  | some c =>
    rw [hin] at hZ
    have r1 : Reach N .step y (bnd N y) (.zA σ) R.val (.zB σ) R.val :=
      Reach.single' (gd_of hv (by simp [PreS, CA]))
        (by cases c <;> simp [astep, CA, hZ, zcode])
    have hv1 : ({R with Z := R.Z - 1} : Regs).Bd (bnd N y) := by
      have := hBd; simp only [Regs.Bd] at this ⊢; omega
    have r2 : Reach N .step y (bnd N y) (.zB σ) R.val (.zC σ) ({R with Z := R.Z - 1} : Regs).val :=
      Reach.single' (gd_of hv (by simp [PreS, CA])) (by simp [astep, CA])
    refine ⟨R.Z - 1, by cases c <;> simp [zcode] at hZ <;> omega, r1.trans (r2.trans ?_)⟩
    exact Reach.single' (gd_of hv1.val_le (by simp [PreS, CA]))
      (by cases c <;> simp [astep, CA, hZ, zcode])

/-- The answer of the step machine after the validity scan, from the scan state `st`, the
input positions `p`, `p'`, and the two chunk regions `u`, `u'`. -/
noncomputable def stepAns (x : List Bool) (st : VSt N) (p p' : ℕ) (u u' : List Bool) : Bool :=
  decide (VAcc N st) &&
    ((decide (movePos x.length p (aI N (st, inpOf x p) false).inputTape = p') &&
        sDone N (Gs N (st, inpOf x p) false)
          (sScan N (Gs N (st, inpOf x p) false) (Gs N (st, inpOf x p) true) u u').1) ||
      (decide (movePos x.length p (aI N (st, inpOf x p) true).inputTape = p') &&
        sDone N (Gs N (st, inpOf x p) true)
          (sScan N (Gs N (st, inpOf x p) false) (Gs N (st, inpOf x p) true) u u').2))

/-- **The tail of the step mode**: after the validity scan of the first word, read the step
data, compare the positions for both choice bits (`pm_run`), run the double sliding scan of
the two chunk regions (`s_run`), and answer `stepAns`.

**Proof sketch.** A branch on the scan verdict, `z_run`, two `pm_run`s, `s_run` with the
letters of both words at stride two (`getD_w`, `getD_w2`), and the final `ret`. -/
theorem step_tail (y x w w' rest : List Bool)
    (hy : y = pairEncode x (pairEncode w (pairEncode w' rest))) (s : ℕ) (st : VAd N) (R : Regs)
    (hBd : R.Bd (bnd N y)) (hN1 : R.N1 = x.length + 1) (hPos : R.Pos ≤ x.length + 1)
    (hZ : R.Z = zcode (inpOf x R.Pos)) (hQ3 : R.Q3 = 2 * x.length + 2)
    (hQ4 : R.Q4 = 2 * x.length + 2 * w.length + 4)
    (hE : R.E = 2 * x.length + 2 + 4 * W N * s + 2 * W N)
    (hw : W N * (2 * s + 1) ≤ w.length) (hw' : W N * (2 * s + 1) ≤ w'.length)
    (hs : s ≤ 2 * y.length) :
    AHalt (CA N .step) orc y (GuardLe (CA N .step) y (bnd N y)) (some (.vDone st), R.val, none)
      (stepAns x st.1 R.Pos R.Pos2 (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))) := by
  set B := bnd N y
  have hv := hBd.val_le
  have hB0 := hBd
  simp only [Regs.Bd] at hB0
  have hyl : y.length = 2 * x.length + 2 * w.length + 2 * w'.length + 6 + rest.length := by
    rw [hy, length_pairEncode, length_pairEncode, length_pairEncode]; ring
  have hbig := bnd_ge (N := N) y s hs
  have hret : ∀ (l : Lab N) (v : Fin 21 → ℕ) (b : Bool), (∀ r, v r ≤ B) →
      CA N .step l = .ret b →
        AHalt (CA N .step) orc y (GuardLe (CA N .step) y B) (some l, v, none) b :=
    fun l v b hv h => AHalt.ret h ⟨by simp [PreS, h], hv⟩
  by_cases hacc : VAcc N st.1
  swap
  · have : stepAns x st.1 R.Pos R.Pos2 (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))
        = false := by simp [stepAns, hacc]
    rw [this]
    have r1 : Reach N .step y B (.vDone st) R.val .rej R.val :=
      Reach.single' (gd_of hv (by simp [PreS, CA, goto])) (by simp [astep, CA, goto, hacc])
    exact AReach.halt r1 (hret _ _ _ hv rfl)
  have r1 : Reach N .step y B (.vDone st) R.val (.zA st.1) R.val :=
    Reach.single' (gd_of hv (by simp [PreS, CA, goto])) (by simp [astep, CA, goto, hacc])
  obtain ⟨z, hz, r2⟩ := z_run (N := N) y x st.1 R hBd R.Pos hZ
  set I : SInfo N := (st.1, inpOf x R.Pos)
  set R2 : Regs := {R with Z := z}
  have hR2 : R2.Bd B := by simp only [R2, Regs.Bd]; omega
  have r3 := pm_run (N := N) y I false false R2 hR2 (by simp [R2, hN1]) (by simp [R2, hN1, hPos])
    (by simp [R2, hN1]; omega)
  set f₀ := decide (movePos (R2.N1 - 1) R2.Pos (aI N I false).inputTape = R2.Pos2)
  have r4 := pm_run (N := N) y I true f₀ R2 hR2 (by simp [R2, hN1]) (by simp [R2, hN1, hPos])
    (by simp [R2, hN1]; omega)
  set f₁ := decide (movePos (R2.N1 - 1) R2.Pos (aI N I true).inputTape = R2.Pos2)
  simp only [pmNext, Bool.false_eq_true, ↓reduceIte] at r3 r4
  set u := w.take (W N * (2 * s + 1))
  set u' := w'.take (W N * (2 * s + 1))
  have hu : u.length = W N * (2 * s + 1) := by simp only [u, List.length_take]; omega
  have hu' : u'.length = W N * (2 * s + 1) := by simp only [u', List.length_take]; omega
  have r5 := s_run (N := N) (mode := .step) y B I f₀ f₁ u u' (by rw [hu, hu']) (sAd0 N) R2.val
    hR2.val_le (by simp [R2, hu, hE, hQ3]; ring)
    (by simp [R2, hu, hQ4]; have : 2 * (W N * (2 * s + 1)) = 4 * W N * s + 2 * W N := by ring
        omega)
    (fun i hi => by
      rw [hu] at hi
      simp only [R2, Regs.val_Q3, hQ3]
      rw [hy, getD_w _ _ _ _ (by omega)]
      simp only [u, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi])
    (fun i hi => by
      rw [hu] at hi
      simp only [R2, Regs.val_Q4, hQ4]
      rw [hy, getD_w2 _ _ _ _ _ (by omega)]
      simp only [u', List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi])
  set R5 : Regs := {R2 with Q3 := R2.Q3 + 2 * u.length, Q4 := R2.Q4 + 2 * u.length}
  have hR5 : R5.Bd B := by
    simp only [R5, R2, Regs.Bd, hu]
    have : 2 * (W N * (2 * s + 1)) = 4 * W N * s + 2 * W N := by ring
    omega
  have r5' : Reach N .step y B (.sTest I f₀ f₁ (sAd0 N)) R2.val
      (.sFin I f₀ f₁ ((List.zip u u').foldl (δS N I) (sAd0 N))) R5.val :=
    Reach.cast r5 (by simp [R5])
  have hans : stepAns x st.1 R.Pos R.Pos2 u u' =
      ((f₀ && sDone N (Gs N I false) ((List.zip u u').foldl (δS N I) (sAd0 N)).1.1) ||
        (f₁ && sDone N (Gs N I true) ((List.zip u u').foldl (δS N I) (sAd0 N)).1.2)) := by
    simp only [stepAns, hacc, decide_true, Bool.true_and, f₀, f₁, R2, hN1,
      Nat.add_sub_cancel, I]
    rfl
  rw [hans]
  exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans r5')))) (hret _ _ _ hR5.val_le rfl)

/-- The answer of the step machine is the step check, on inputs passing the pre-scan
checks of both words. -/
lemma stepAns_iff (x w w' : List Bool) (s : ℕ) (hpre : PreChk N x.length s w)
    (hlen' : w'.length = W N * (2 * s + 1) + wP x.length + 1)
    (hterm' : w'.getD (W N * (2 * s + 1) + wP x.length) false = true) :
    stepAns x (vScan N (w.take (W N * (2 * s + 1))))
        (bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length)))
        (bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length)))
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))) = true ↔
      StepChk N x s w w' := by
  unfold StepChk stepAns
  rw [validChk_iff_pre]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hacc, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨⟨hpre, hacc⟩, hlen', hterm', false, h1.symm, h2⟩
    · exact ⟨⟨hpre, hacc⟩, hlen', hterm', true, h1.symm, h2⟩
  · rintro ⟨⟨-, hacc⟩, -, -, b, h1, h2⟩
    refine ⟨hacc, ?_⟩
    cases b
    · exact Or.inl ⟨h1.symm, h2⟩
    · exact Or.inr ⟨h1.symm, h2⟩

/-- Members of the step language are well shaped. -/
lemma shape2_of_code {y x : List Bool} {c c' s : ℕ}
    (hy : y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))))
    (C : Cfg N.k Bool N.State x) (hc : cfgCode s C = c) :
    Shape2 y x (Nat.bits c) (Nat.bits c') s := by
  refine ⟨hy, width_of_code s C y ?_⟩
  rw [hy, ← hc, bits_cfgCode]
  simp [length_pairEncode]; omega

/-- **The step language is logspace** (`Complexity.Codec.stepLang`).

**Proof sketch.** `arm_decides_poly` with the codec machine in mode `step`: the phases
`parse_run₂`, `layout_run`, `le_phase`, `layout2_run`, `insym_run`, `vscan_run`,
`step_tail` answer `stepAns`, which on well-shaped inputs passing the pre-scan checks is the
step check (`stepAns_iff`), i.e. membership (`stepLang_iff`); every rejection on the way
falsifies the step check or the shape (`shape2_of_code`). -/
theorem stepLang_mem : stepLang N ∈ LOGSPACE := by
  refine arm_decides_poly (CA N .step) .lenScan codecAs codecAs_mem (8 * W N + 8) 1
    fun y => ?_
  rw [← val_empty]
  refine AHalt.mono ?_ (fun a h => gd_mono a h)
  set B := bnd N y
  -- non-members: no shape, or a failed check
  have hnon : (∀ x w w' s, Shape2 y x w w' s → ¬ StepChk N x s w w') →
      MultiTapeTM.indicator (stepLang N : Set (List Bool)) y = false := by
    intro hfail
    rw [indicator_eq_of_iff (P := False) (Iff.intro (fun h => ?_) False.elim)]
    · rfl
    obtain ⟨x, c, c', s, hy, C, hC, hc, C', hstep, hC', hc'⟩ := h
    have hsh := shape2_of_code (c' := c') hy C hc
    exact hfail x _ _ s hsh ((stepLang_iff N x (Nat.bits c) (Nat.bits c') s).mp
      ⟨x, c, c', s, rfl, C, hC, hc, C', hstep, hC', hc'⟩)
  rcases parse_run₂ (N := N) y with ⟨x, w, w', s, q1, cap, ⟨hy, hwid⟩, hq1, hcap, r1⟩ |
      ⟨hno, hhalt⟩
  swap
  · rw [hnon (fun x w w' s h => absurd ⟨x, w, w', s, h⟩ hno)]
    exact hhalt
  have hyl : y.length = 2 * x.length + 2 * w.length + 2 * w'.length + 6 + (Nat.bits s).length := by
    rw [hy, length_pairEncode, length_pairEncode, length_pairEncode]; ring
  have hs := s_le_of_width y s (by omega) hwid
  have hbig := bnd_ge (N := N) y s hs
  have hlink : 4 * W N * s + 2 * W N = 2 * (W N * (2 * s + 1)) := by ring
  have hlink2 : 2 * W N * (2 * s + 1) = 2 * (W N * (2 * s + 1)) := by ring
  have huniq : ∀ x₁ w₁ w₁' s₁, Shape2 y x₁ w₁ w₁' s₁ → x₁ = x ∧ w₁ = w ∧ w₁' = w' ∧ s₁ = s := by
    rintro x₁ w₁ w₁' s₁ ⟨hy₁, -⟩
    rw [hy] at hy₁
    obtain ⟨h1, h2⟩ := pairEncode_inj hy₁
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    obtain ⟨h5, h6⟩ := pairEncode_inj h4
    exact ⟨h1.symm, h3.symm, h5.symm, (bits_injective h6).symm⟩
  set R1 : Regs := { L := y.length, P := 2 * x.length + 2 * w.length + 2 * w'.length + 6,
                     A := 2 * x.length + 2, B := 2 * x.length + 2 * w.length + 4, Q1 := q1,
                     Cap := cap, Q2 := 2 * x.length + 2 * w.length + 2 * w'.length + 6, S := s }
  have hR1 : R1.Bd B := by simp only [R1, Regs.Bd]; omega
  rcases layout_run (N := N) (mode := .step) y x w (pairEncode w' (Nat.bits s)) hy R1 s hR1 rfl rfl
    rfl hs rfl rfl rfl rfl rfl rfl rfl (by simp [R1]) with ⟨hlen, hterm, r2⟩ | ⟨hbad, hhalt⟩
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hbad ⟨hchk.1.1, hchk.1.2.2.2⟩)]
    exact AReach.halt r1 hhalt
  set pos := bitsVal ((w.drop (W N * (2 * s + 1))).take (wP x.length))
  set R2 := layR N R1 x.length s pos
  have hwP := wP_le x.length
  have hpos_lt : pos < 2 * (x.length + 1) := by
    have h1 := bitsVal_lt_two_pow ((w.drop (W N * (2 * s + 1))).take (wP x.length))
    have h2 : 2 ^ ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
        2 * (x.length + 1) := by
      rw [show ((w.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
        simp; omega]
      exact two_pow_bits_le _ (by omega)
    omega
  have hR2 : R2.Bd B := by simp only [R2, R1, layR, Regs.Bd]; omega
  obtain ⟨hle, hgt⟩ := le_phase (N := N) (mode := .step) y R2 hR2 (by simp [R2, R1, layR])
  by_cases hp : pos ≤ x.length + 1
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hp hchk.1.2.2.1)]
    exact AReach.halt (r1.trans r2) (hgt (by simpa [R2, R1, layR] using hp))
  have r3 := hle (by simpa [R2, R1, layR] using hp)
  simp only [↓reduceIte] at r3
  rcases layout2_run (N := N) y x w w' (Nat.bits s) hy R2 s hR2 (by simp [R2, R1, layR])
    (by simp [R2, R1, layR]) (by simp [R2, R1, layR]) hs (by simp [R2, layR])
    (by simp [R2, R1, layR]) (by simp [R2, R1, layR]) (by simp [R2, R1, layR])
    (by simp [R2, R1, layR]) with ⟨hlen', hterm', r4⟩ | ⟨hbad', hhalt'⟩
  swap
  · rw [hnon (fun x₁ w₁ w₁' s₁ hsh hchk => by
      obtain ⟨rfl, rfl, rfl, rfl⟩ := huniq x₁ w₁ w₁' s₁ hsh
      exact hbad' ⟨hchk.2.1, hchk.2.2.1⟩)]
    exact AReach.halt (r1.trans (r2.trans r3)) hhalt'
  set pos' := bitsVal ((w'.drop (W N * (2 * s + 1))).take (wP x.length))
  set R3 := lay2R N R2 (2 * x.length + 2 * w.length + 4) s (wP x.length) pos'
  have hpos'_lt : pos' < 2 * (x.length + 1) := by
    have h1 := bitsVal_lt_two_pow ((w'.drop (W N * (2 * s + 1))).take (wP x.length))
    have h2 : 2 ^ ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length ≤
        2 * (x.length + 1) := by
      rw [show ((w'.drop (W N * (2 * s + 1))).take (wP x.length)).length = wP x.length by
        simp; omega]
      exact two_pow_bits_le _ (by omega)
    omega
  have hR3 : R3.Bd B := by simp only [R3, R2, R1, lay2R, layR, Regs.Bd]; omega
  obtain ⟨u, hu, r5⟩ := insym_run (N := N) y x (pairEncode w (pairEncode w' (Nat.bits s))) hy R3 hR3
    (by simp [R3, R2, R1, lay2R, layR]; omega) (by simp [R3, R2, R1, lay2R, layR])
    (by simp [R3, lay2R]) (by simp [R3, R2, R1, lay2R, layR]) (by simp [R3, R2, R1, lay2R, layR])
    (by simp [R3, R2, R1, lay2R, layR])
  set R4 : Regs := {R3 with Z := zcode (inpOf x R3.Pos), U := u, Q3 := R3.A, Q4 := R3.B}
  have hR4 : R4.Bd B := by
    simp only [R4, R3, R2, R1, lay2R, layR, Regs.Bd]
    have : zcode (inpOf x pos) ≤ 2 := by
      unfold zcode; split <;> omega
    omega
  obtain ⟨st, hst, r6⟩ := vscan_run (N := N) (mode := .step) y x w (pairEncode w' (Nat.bits s)) hy
    R4 s hR4 (by simp [R4, R3, R2, R1, lay2R, layR]) (by simp [R4, R3, R2, lay2R, layR])
    (by omega)
  set R5 : Regs := {R4 with Q1 := R4.E, Q2 := R4.E}
  have hR5 : R5.Bd B := by
    simp only [R5, R4, R3, R2, R1, lay2R, layR, Regs.Bd]
    have : zcode (inpOf x pos) ≤ 2 := by
      unfold zcode; split <;> omega
    omega
  have tail := step_tail (N := N) y x w w' (Nat.bits s) hy s st R5 hR5
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, R1, lay2R, layR]; omega)
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, R1, lay2R, layR])
    (by simp [R5, R4, R3, R2, R1, lay2R, layR]) (by simp [R5, R4, R3, R2, lay2R, layR])
    (by omega) (by omega) hs
  have hPosR5 : R5.Pos = pos := by simp [R5, R4, R3, R2, R1, lay2R, layR]
  have hPos2R5 : R5.Pos2 = pos' := by simp [R5, R4, R3, R2, R1, lay2R, layR]
  rw [hst, hPosR5, hPos2R5] at tail
  have hind : MultiTapeTM.indicator (stepLang N : Set (List Bool)) y =
      stepAns x (vScan N (w.take (W N * (2 * s + 1)))) pos pos'
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1))) := by
    rw [indicator_eq_decide]
    have key := stepAns_iff (N := N) x w w' s ⟨hlen, hterm, hp⟩ hlen' hterm'
    rw [hy, stepLang_iff]
    cases h : stepAns x (vScan N (w.take (W N * (2 * s + 1)))) pos pos'
        (w.take (W N * (2 * s + 1))) (w'.take (W N * (2 * s + 1)))
    · simp only [decide_eq_false_iff_not]
      intro hc; rw [← key] at hc; rw [hc] at h; exact Bool.noConfusion h
    · simp only [decide_eq_true_eq]
      exact key.mp h
  rw [hind]
  exact AReach.halt (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))) tail

end Complexity.Codec
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
