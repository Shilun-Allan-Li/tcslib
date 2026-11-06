## ===== campaign/gates/109-h-landing-fill/pack.md =====

# External audit pack: B6's H landing, `Complexity.space_hierarchy` (PR #218, a fill gate)

## Why this PR

`Complexity.space_hierarchy` (`SpaceComplexity/Hierarchy`; [AB09, Theorem 4.8]) and its corollary
`Complexity.LOGSPACE_ssubset_PSPACE` ([AB09, §4.3.2]) were `sorry` in the campaign. The fill H
(brief `campaign/fills/b6/briefs/b6-fill-hierarchy.md`, agent Codex; REPORT
`campaign/fills/b6/reports/hierarchy-REPORT.md`) proves both, with the frozen statements, by the
window route. One fixed self-universal machine `U₀` is run in a radius-`a · g(n)` window, using
the configuration-count runner, and the verdict is flipped.

The third target, `SPACE_linear_ne_NP` ([AB09, Exercise 3.2]), ends in the brief's allowed named
escalation, **E-PAD**: the library has no host for the padded-language space decider. The private
`sph_linear_ne_NP_of_padding` proves the target from `space_hierarchy` and E-PAD's exact
statement. The user ruled on 2026-11-06:
- E-PAD is published as a general `mem_SPACE_padLang` in a new `SpaceComplexity/Padding` module.
  Its statement PR is #219, with its own gate.
- E-PAD comes before F6 in this file.
- `Hierarchy` may import the new module, and the maintainer closes the target afterwards in a
  small PR.

`space_universal` (F6) is outside H and unchanged.

**The PR:** #218 on `lean/b6h-landing`, head `65d72947` (full hash in the bundle header). It
consists of:
- the delivery `fill/b6-hierarchy` at `30222bbd` (base `e6bc1968`, kept as delivered;
  `campaign/fills/b6/`), merged at `14ee2e46`;
- the maintainer's landing edits `2d65a899` and `66fc5327`, made after a review of the delivery
  (`campaign/fills/b6/review/hierarchy-REVIEW.md`) and a library sweep
  (`campaign/fills/b6/sweep/`);
- merges of the campaign, the last at `65d72947` (after #216).

It changes one file, `Hierarchy.lean`: 317 → 2,507 lines, with 4 public declarations (statements
unchanged) and 43 private `sph_` declarations.

## What changed (verify)

| Declaration | What |
|---|---|
| `Complexity.space_hierarchy` (frozen statement) | proved; its sketch is corrected at landing (below) |
| `Complexity.LOGSPACE_ssubset_PSPACE` (frozen statement) | proved |
| `Complexity.SPACE_linear_ne_NP` (frozen statement) | still `sorry` (E-PAD); its sketch is corrected at landing |
| `Complexity.space_universal` (F6) | unchanged, `sorry` |
| 43 private `sph_` declarations | the diagonalizer pipeline (radius, record, runner, test, verdict), the window containment, the normal-form arithmetic, and `sph_linear_ne_NP_of_padding` |
| the imports | the brief's four (`SelfUniversal`, `Build/WindowRun`, `WindowClock`, `ClassNP/PClosure`) |

**The landing edits** (`2d65a899`, `66fc5327`) make no public statement changes:
- **The sweep's items** (`campaign/fills/b6/sweep/README.md`, copy C, clear and borderline as
  in #208's and #211's sweeps; no import): **17 of its 18 items, 30 sites**. The items are:
  - `Nat.le_mul_of_pos_right` (two sites), `Fin.val_ne_zero_iff`, `Fin.zero_ne_one` (three
    sites), `length_bits_le_self`, `Bool.eq_iff_iff`;
  - `Function.Embedding.ofIsEmpty`, `Finset.sum_le_card_nsmul`, `Fin.castLEEmb`;
  - four `Cfg.ext` skeletons replaced by `Cfg.mapState_mapState` and
    `Cfg.mapState_eq_of_fields`;
  - the borderline `Nat`/`Int`/`Option` lemmas M1–M4 and M6–M8.

  **M5 was applied, then reverted (`66fc5327`).** It rewrote five `1 ≤ g n` floors as
  `Nat.one_le_of_lt (… : logSpace n ≤ g n)`, which typechecks only by unfolding
  `Complexity.logSpace`. The seal at the landed head caught it (five errors, `sorryAx` in both
  headlines). The delivered text (`rw [logSpace_eq]; omega`) is restored at all five sites. The
  sweep's README had flagged M5 as depending on definitional unfolding.
- **The review's minor 3 and note 5:**
  - `space_hierarchy`'s sketch now describes the configuration-count runner
    (`exists_configWindowRunnerTM`) with its own clock. It cites `exists_codeTM_spaceUsed`, not
    a re-derived space clause through `relabelState`.
  - The module docstring no longer mentions "the clock width".
  - `SPACE_linear_ne_NP`'s sketch uses the `(|x|+1)²` pad and `m = (n+1)² + 2n + 2`, cites
    `preimage_mem_NP`, and drops two internal phrases.

## Known deviations and dispositions (for the audit)

- **E-PAD** (above): the brief's allowed escalation, ruled by the user.
- **Size:** 2,507 lines. The brief waives the size limit (its rule 8). It produces the style
  lint's one new WARN and the policy linter's one new finding. About 2,200 lines are the
  diagonalizer pipeline. A later split or harvest is optional (review note 9).
- **The review's minors 1, 2 and 4** concern the REPORT, not the code:
  - checkpoint 7's "admission-free" row was premature;
  - the checkpoint zips were not shipped, though the final zip, patch chain and bundle cover
    them;
  - the REPORT's proposed Implementation paragraph ends with process text. It was not
    inserted.
- **Promotion candidates** (review note 7): `Cfg.select` has no published field equations, so
  `sph_select_fields` is an API gap. `sph_seam_heads` and `sph_halt_contract` are general consumer
  lemmas. These are recorded for a later shared-file window.
- **The unused private** `sph_linear_ne_NP_of_padding` (review note 8) is kept. It becomes the
  target's body once E-PAD lands.

## Brief for the auditor

1. **Soundness and pins:**
   - Are the four statements frozen?
   - Is the proof of `space_hierarchy` correct, including the window containment, the clock
     sufficiency, `n` below the hypothesis' threshold, and the payload padding of the code?
   - Is `LOGSPACE_ssubset_PSPACE` correct?
2. **Rule 10:** do the proofs read other files' definitions only through published equations?
   The seal and its controls are below.
3. **Duplication:** does any proof still re-derive a published lemma (a typed or untyped `have`,
   a `simp` set, a rewrite chain, a conjunct), or another file's private? The review, the sweep
   and the delivery's screen classification list every candidate with a disposition. Challenge
   any of them.
4. **Public text:** are the module docstring and the three targets' docstrings accurate, free of
   campaign labels, and attributed? Does `sph_linear_ne_NP_of_padding`'s hypothesis match #219's
   statement at `S n = n² + 1`, `T n = n + 1`, `C = 1`, `d = 2`?

## Repository-side attestations (verify or challenge)

- **The delivery** (`campaign/fills/b6/`):
  - the REPORT and the delivery's `SHA256SUMS`;
  - the bundle checked against the source, and the patch chain from blob `287acce8` to
    `40d62c36`;
  - the review's freeze, seal (71 definitions, plus `[-simp]` on four), controls (**75 pass
    unsealed, 75 fail sealed**) and axioms, all on the delivered source.
- **Rule 10 at the head** (`evidence/seal/`): the delivered seal block, with the 71 definitions
  and the four `[-simp]` removals, inserted after `space_universal` in the head's `Hierarchy.lean`
  (`66fc5327`). It elaborates against the campaign snapshot with **0 errors**. The only messages
  are the two `sorry` warnings (`space_universal` and `SPACE_linear_ne_NP`).
  `#print axioms` at its end gives `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` on
  `[propext, Classical.choice, Quot.sound]`. At `2d65a899`, before M5 was reverted, the same
  seal gave 5 errors; that output is kept (`seal-head-before-M5-revert.out`). The controls are
  the delivery's, unchanged, because the seal block is the delivered one. Their sources are
  `evidence/seal/HSealControl_*.lean.txt`, and their raw logs are in the delivery zip
  (`arora-barak-ch3-4/archive/deliveries/fill-b6-hierarchy.zip` on the exchange branch,
  `evidence/logs/`). The sealed head source is `evidence/seal/HSealHead.lean.txt`.
- **Freeze** (`evidence/freeze/`):
  - Against the campaign's Lean (`a28b8c42`): 4 → 4 public with statements unchanged, and
    0 → 43 private. The authorized changes are `space_hierarchy`'s and
    `LOGSPACE_ssubset_PSPACE`'s bodies, and `SPACE_linear_ne_NP`'s docstring.
  - Against the delivery: 43 → 43 private. 17 private bodies changed (the sweep), plus the two
    public docstrings.
- **Screen** (`evidence/screen/`): the brief's 43-file population on a `git archive` of the
  head: **1,894 declarations, 1,699 pairs, 539,014 characters**.
  - Against the delivery's after-screen (1,701 pairs): 0 new and 2 gone. The gone pairs are
    `sphWitnessSel` against `sphInitSel`, and `sph_record_suffix` against
    `Cfg.mapState_mapState`; the sweep removed both.
  - Against the brief's screen base (1,689 pairs): 10 new, each with a `Hierarchy` declaration
    on one side. The largest is 84%. They include four against `InputRewind`'s
    `Cfg.mapState_mapState` (84%, 82%, 61%, 58%), which the delivery's classification
    (`screen-final-classification.txt`) disposes of as concrete field readings, not the
    composition equation. The other six are between two `Hierarchy` declarations.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 82 WARN over 112 files at the head,
    against 81 at the base. The new WARN is `Hierarchy`'s size.
  - The policy linter gives 2 findings: the size (new, waived) and a missing
    `## Main definitions` heading (pre-existing).
- **Replay** (`evidence/merged-tree/`):
  - `replay-lh2` at `65d72947` covers the downstream closure of `Hierarchy` (`Hierarchy` and the
    `SpaceComplexity` facade), chained from the campaign snapshot `oleans-lcamp3` (after #216).
  - **2 modules, 0 failed.** The static check finds 0 mismatches. The 2 `sorry` warnings are
    `space_universal` and `SPACE_linear_ne_NP`.
  - #217 (NZ-1) merged after this replay. It changes proof bodies in modules upstream of
    `Hierarchy` and adds one theorem. Before merge, the maintainer re-runs this 2-module replay
    on the campaign after #217.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/109-h-landing-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `h-landing-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/109-h-landing-fill/STATUS.md =====

# Gate 109 (#218, B6's H landing, a fill gate)

- 2026-11-06: delivery reviewed (0/0/4/5); sweep applied (`2d65a899`); M5 reverted after the head
  seal caught a `logSpace` unfolding (`66fc5327`); seal, freeze, lint and screen at the head;
  `replay-lh2` (2/0, after #216). Pack written; staged.

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

## ===== campaign/fills/b6/briefs/b6-fill-hierarchy.md =====

# Ch3–4 fill campaign — B6's H, the space hierarchy and its corollaries (`Hierarchy.lean`)

Targets: `Complexity.space_hierarchy`, `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP`, in
`TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`.

> **Issued** (maintainer, 2026-11-06; drafted 2026-10-27, revised after the brief review
> `campaign/fills/b6/drafts/b6-fill-hierarchy/review-2026-11-06/`: 1 blocker, 5 majors, all
> folded in). PRs #175, #177, #181, #191, #196, #202, #207 and #209 have merged; the pre-ship ran
> on the merged tree (`campaign/fills/b6/logs/b6-fill-hierarchy-preship.log`), and your base is
> `e6bc1968`. **Ruled (user,
> 2026-11-06):** `SPACE_linear_ne_NP` stays H's last checkpoint and may end in a named escalation
> (see the route). **Agent: Codex** (user, 2026-10-27).

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor e6bc196838b4e2675e4214306c730e7404624ab8 HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your targets as gated statements**: the P4.3 statement gate (`campaign/gates/ch4-p43/`),
    the space hierarchy's statement re-gated on the window route (2026-10-13);
  - **every host the route names, proved** on the standard axioms or fewer. The route's original
    hosts have 17 axiom prints (`campaign/status/2026-10-27-headlines/HHosts.*`): the universal
    machine `Turing.exists_selfUniversal` (`TuringMachine/SelfUniversal`); the record rows
    `Turing.exists_recordInitTM` (`Build/RecordTable`) and `Turing.exists_recordTestTM`
    (`Build/CfgRecord`); the configuration-count runner `Turing.exists_configWindowRunnerTM`
    (`SpaceComplexity/WindowClock`, **its clock inside it**); the window run's facts; the normal
    forms; the space facts and readings. The hosts this revision adds (the returning capture
    embedding and R1 in `Build/Embed`, the seam's general-configuration forms, the contract
    layer, the rewinds, the summary update, the published space clause of the coding step) are
    walked, with the main original hosts, by the extended import probe's 86 axiom prints, every
    one within `[propext, Classical.choice, Quot.sound]` (no `sorryAx`);
  - **`Complexity.spaceConstructible_poly` in `SpaceComplexity/Constructible`** (PR #175, gate 86),
    which your file already imports; `SPACE_linear_ne_NP` needs it at degree two;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**), and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b6/inputs/b6-fill-hierarchy/`): the import probe
    (`HImportProbe.lean.txt`, 72 names) and its extension (`HImportProbe2.lean.txt`, 171 checks:
    the 72 and every name this revision newly cites, with the 86 axiom prints), the route probe
    (`HRouteProbe.lean.txt`) with its seal controls, the semantic-duplication probe, the import
    overlay (`HierarchyOverlay.lean.txt`) and the screen population; the order list
    `campaign/fills/b6/orders/b6-fill-hierarchy.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/b6/logs/b6-fill-hierarchy-*`). The route's design note is
    `campaign/items/b6hosts/H/H-route-design.md`; where it and this brief differ (the capture
    wrapper, the seam's `Bool` space lemmas, its line numbers), this brief governs.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule (E-RES).
  Fetch the cache for your roots only (63 Mathlib roots, in the pre-ship log); never run the
  unfiltered `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never
  runs, do not draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-hierarchy e6bc196838b4e2675e4214306c730e7404624ab8
  git rev-parse HEAD        # must print e6bc196838b4e2675e4214306c730e7404624ab8
  git rev-parse HEAD:TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
  # must print 287acce8326a1de271dfa6be2cc3776f3a2caa32
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-hierarchy.zip`, attached in
  your reply, with
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle whose only prerequisite is your base, the environment logs (`evidence/logs/`), the
  bootstrap and final sweep logs with **each module's time and maximum memory**, the axiom log, the
  seal test's source, its controls and both outputs, both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-b6-hierarchy-cp<N>.zip` (`N` 1 to 8) with the same contents as of that commit. Deliver the
  latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after PRs #175, #177, #181, #191, #196, #202
  and #207** (the pre-ship's `d43a1374`). Lines in this brief are those of your base's tree, where
  `Hierarchy.lean` is 317 lines (4 public declarations, no private).
- **The overlay is your first edit** (region (a)): add, after line 10, exactly
  `import TCSlib.Complexity.TuringMachine.SelfUniversal`,
  `import TCSlib.Complexity.TuringMachine.Build.WindowRun`,
  `import TCSlib.Complexity.SpaceComplexity.WindowClock` and
  `import TCSlib.Complexity.ClassNP.PClosure` (for `preimage_mem_NP`; it brings
  `Mathlib.Tactic.Linarith` into the file's environment)
  (`HierarchyOverlay.lean.txt` is the file after it). The pre-ship elaborated it: exactly the four
  sorry warnings, at the overlay's lines 154, 271, 288 and 318 (the base's 150, 267, 284 and 314),
  nothing else. Every host this brief cites is in the overlay's import closure (the extended
  probe imports nothing else).
- **In flight:** #208, the deepening fill's landing: `SavitchARM/Deepen` (new, not in your order
  list) and, in your order list, `Savitch`, `Machines/Bin` (one new lemma,
  `length_bits_succ_le`) and proof-only re-points in `Machines/ARMWidth`,
  `Machines/ARMWidthExample`, `ExpBFS/Main`, `SavitchARM/Correct`, `Logspace/PathHardRegs` and
  `Logspace/ISCountGenCorrect` (no statement changes). It is replayed on the merged tree before it
  merges; cite nothing it adds, and name no private `length_bits_succ_le`. If #208 merges first,
  `savitch` leaves the base sorry set; that is not a difference you need to explain. #211
  (`Robustness/TwoTapes`, G5) is outside your order list. Your base contains #209
  (`NTimeHierarchy`'s docstring, outside your order list); nothing in your closure changes.

## Parallel batches this round

None in `Hierarchy.lean`: **F6** (`Complexity.space_universal`, line 150, the same file) is out of
scope and waits for a later round; leave its statement, docstring and body untouched.

## What this is

**The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through [AB09]). For
space-constructible `f` and `g` with `∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n`: `SPACE f ⊂ SPACE g`. Then
two corollaries in the same file:
- `LOGSPACE_ssubset_PSPACE` ([AB09, §4.3.2]): `space_hierarchy` at `logSpace` and `n + 1`;
- `SPACE_linear_ne_NP` ([AB09, Exercise 3.2], at the normalization `n + 1`).

**Where it stands.** The three bodies are `sorry`. Every host of `space_hierarchy` and
`LOGSPACE_ssubset_PSPACE` is proved; the route probe proves the inclusion half and
`LOGSPACE ⊂ PSPACE` from the hierarchy's statement. **Proved modulo, exactly:** none.
`SPACE_linear_ne_NP` has published hosts for its reduction and its extraction but **none for the
padded language's decider** (see the route): it may end in a named escalation. **A complete
delivery has no `sorryAx` in the three targets**; a delivery whose last checkpoint ends in that
escalation has none in the first two.

**Read first:** the route note `campaign/items/b6hosts/H/H-route-design.md` (it maps the
docstring's sketch onto the published hosts and says where this brief supersedes the sketch); the
three targets' docstrings (lines 163–313); `exists_configWindowRunnerTM`'s statement
(`WindowClock.lean:1503`); `exists_selfUniversal` (`SelfUniversal.lean:143`);
`exists_recordInitTM` (`RecordTable.lean:5805`); `embedSilentRetTM_run` (`Build/Embed.lean:828`)
and the transport's field lemmas after it (`Embed.lean:983–1051`).

**Pre-ship check** (the maintainer, against the replay snapshot of your base's tree; log
`campaign/fills/b6/logs/b6-fill-hierarchy-preship.log`): the overlay as above; the import probe
72 checks of 72 names, 0 errors; the route probe's four lemmas (`hr_inclusion`,
`hr_sq_le_two_pow`, `hr_logSpace_dom`, `hr_logspace_ssubset`) through published readings only,
sealed (5 definitions) with 9 controls (9 pass unsealed, 9 fail sealed), and three axiom prints
on the standard axioms (not `hr_sq_le_two_pow`'s); the duplication probe: of its six `exact?`
calls, only `logSpace_le_succ` (which the route does not need) and `LOGSPACE_subset_PSPACE`
(cited below) close; the order list 220 modules, 63 roots, 26 base sorries in 10 modules; the
screen base (over the 43 files) 1,854 declarations, 1,689 pairs, none on `Hierarchy`; lint 0 FAIL, 80 WARN over 111
files. **This revision** (2026-11-06): the extended import probe, 171 checks, 0 errors, and 86
axiom prints, none outside the standard three, against the campaign's snapshot after #209
(the same closure); the review's probe (`review-2026-11-06/HRevProbe.*`) showed the seam's
`Bool` space lemmas reject a record-alphabet machine and `captureCfg` has no reading under the
seal.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`:
- **(a)** the imports, lines 6–10: add exactly the overlay's four;
- **(b)** new private declarations after `space_universal`'s body (line 161) and before
  `space_hierarchy`'s docstring (line 163), in sections of your own if you like;
- **(c)** the three bodies: lines 271 (`space_hierarchy`), 285 (`LOGSPACE_ssubset_PSPACE`) and 315
  (`SPACE_linear_ne_NP`);
- **(d)** the status text and internal labels, rewritten as public-facing text, keeping the
  mathematics and the references:
  - the module docstring (lines 16–80): the intro's "per the P0 convention —
    `AroraBarakChapters3-4Plan.md` §2.4", "Phase P4.3" and the dated restatement and gate history
    (lines 22–28); "design §16b item 3" (line 48) and "(Finding B, recorded in the sketches)"
    (line 58); "(round-1 confirmed, recorded in the sketch)" (lines 61–62) and "while the P4.1
    gate was live; … since that gate closed" (lines 63–65); "(all sorried; phase-P4.3
    statements)" (line 67); **except** `space_universal`'s entry (lines 69–70), which is F6's;
  - `space_hierarchy`'s docstring (lines 163–266): "spec, fill pending — phase P4.3, … RD-3
    statement gate passed 2026-10-13" (lines 164–165), "(recorded here, seeded to the audit)"
    (line 173), "the P0 zero-bound convention" (lines 174–175), the registry names "H2", "H3"
    and "H5" (lines 187, 189, 206, 255–258), "R8.5d; decision O6" (line 198), "design §12.8a
    decision O4" (line 211), "(W1)" (line 212), "§12.7 and R8.0b" (line 213), "(round-1 finding
    5)" (line 227), "design §14" (line 255) and "record-table row 18; row 17" (line 259);
  - `LOGSPACE_ssubset_PSPACE`'s (lines 273–283): "spec, fill pending" (line 274) and "of phase
    P4.1" (line 279);
  - `SPACE_linear_ne_NP`'s (lines 287–313): "per the P0 convention" (line 288), "spec, fill
    pending" (line 289) and "(round-2 finding 5)" (line 298).

  No phase, gate, round, finding, decision, design-section, registry-row or fill names, no
  `audits/` or `campaign/` paths, no dated rulings. `space_universal`'s docstring (lines 86–149)
  is F6's: leave it as it is. Propose an `**Implementation.**` paragraph for each target's
  docstring in `REPORT.md` (the clock is the runner's, not the sketch's step (iii); the capture
  is `embedSilentRetTM`); the maintainer lands them.

**Targets:** `Complexity.space_hierarchy` (line 267), `Complexity.LOGSPACE_ssubset_PSPACE` (line
284), `Complexity.SPACE_linear_ne_NP` (line 314); statements frozen.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

Write `e := RecSym.digitEmb Q₀ (Fin 3)` for the digit embedding into the record alphabet.

- **The universal machine** is `Turing.exists_selfUniversal`: one `U₀` for the scheme
  `Complexity.TimeHierarchy.code`, with, per code `α`, a `C > 0` such that a halting run of
  `decode α` on `pairEncode α w` within space `s` is reproduced by `U₀` with the same output within
  space `C · (s + 1)`. Never build a second universal machine.
- **The run** is `Turing.exists_configWindowRunnerTM` at `U₀` with **`T := Fin 3`,
  `upd := Turing.summaryTag` and `hupd := Turing.summaryTag_none`**: the only update
  `windowRun_summary_of_halts` is stated for, with the initial tag `0`. Write no summary update of
  your own. From a radius-`r` record of a configuration in its window on tape 0, **every other tape
  of its bank blank** (`WindowClock.lean:1512`), it reaches an exit `out` within
  `C · 2^(C (L + 1))` steps in space `(K + 1)(2C(L + 1) + 1)`, silently, with `out` the window
  run's verdict at every non-exhausted round count up to `configBound + 1`, and, unless
  `out = exhausted`, the record of the window run's endpoint left on tape 0 for **some** round
  count `N`. **The clock is inside it: build no clock, counter loop or round driver of your own.**
- **The initial record** is `Turing.exists_recordInitTM` (`RecordTable.lean:5805`) at radius
  `s = g n`, `ws = (g n).bits` (its `Nat.ofDigits` premise by `counterValue_eq` and
  `counterValue_bits`) and `τ₀ = 0`, the empty-output tag (`outSummaryCode_nil`). Its premises:
  input head at `1`; `ws.map RecSym.digit` readable from tape 1's head over `[-1, |ws|]`; tape 0
  blank over the record's span; tapes `≥ 2` blank. Its record is of `Cfg.init q₀ x`;
  `MultiTapeTM.initCfg_eq` turns that into `U₀.tm.initCfg x`. Its endpoint changes only tape 0.
- **The radius** is `g`'s constructibility witness `M_g` (`spaceConstructible_iff`), lifted and
  run under the **returning capture embedding**
  `Turing.embedSilentRetTM ι cap (M_g.tm.liftSymbols e)` (`Build/Embed`), the selection `ι` the
  witness bank and `cap` the radius tape:
  - the run: `embedSilentRetTM_run` (lockstep, then the live return anchor `Sum.inr ()` exactly
    at the witness's first halt, its final emission recorded);
  - the readings: `embedSilentCfg_cap` (the captured word `bufferTape (pre ++ c.output)`, the head
    just after it), `embedSilentCfg_unselected`, `embedSilentCfg_selected_tape`/`_pos`, and the
    `simps` equations `embedSilentCfg_state`/`_inputPos`/`_output`;
  - the space: `embedSilentRetTM_visitedByTapeHead` (the returning flavor visits what the closed
    one does), then `embedSilentTM_visitedByTapeHead` (the bank: the witness's own cells),
    `embedSilentTM_visitedByTapeHead_frame` (each other tape: one cell) and
    `embedSilentTM_spaceUsedByTape_cap` (the radius tape: the output's growth plus one);
  - the lift: `MultiTapeTM.liftSymbols_runFrom`, `liftSymbols_initCfg`, `liftSymbols_spaceUsed`
    and the field equations `Cfg.liftSymbols_state`, `_workTapePos`, `_inputPos`, `_workTapes`,
    `_output`.

  With `pre = []` the radius tape starts blank (`FinTM.bufferTape_nil`) and ends holding
  `bufferTape ((g n).bits.map e)`, which is `bufferTape ((g n).bits.map RecSym.digit)` by
  `RecSym.digitEmb_apply`: the form `exists_recordInitTM` reads. **Do not use**
  `Turing.capture_run` or `capture_visitedByTapeHead`: they are `Bool`-only and conclude about
  `captureCfg`, which has no published reading (rule 10). `Contract.liftSymbols` needs an
  input-blind machine and does not apply to the witness.
- **The input validation** is `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`: entry and exit with
  the input head at `1`, no work head moved): reject at once a rich input that is not an embedded
  word, so `D`'s space is bounded on every input of the rich alphabet.
- **The rewinds** (after the witness):
  - **the input head**, anywhere in `[0, |x| + 1]` at the witness's halt, must be at `1` for
    `exists_recordInitTM`. `inputRewindTM_run` is `Bool`-only and needs `1 ≤ inputPos`: run
    `(inputRewindTM 0).liftSymbols e` (no work tapes; `liftSymbols_runFrom`) on `D`'s tapes by
    R1 along `Fin 0 ↪ Fin K_D` (below), after a **one-step leaf of your own** that moves the input
    head right (`MultiTapeTM.step_of_some`, `moveInputPos_pos_of_ne_right`,
    `moveInputPos_rightBoundary`): from `0` it reaches `1`, from `p ≥ 1` it stays `≥ 1`;
  - **the radius tape**, whose head the capture leaves at `|ws|`: `Turing.rewindTM_run_ofCfg` at
    `n = |ws|` puts it on the word's first cell, as `exists_recordInitTM` reads it.
- **The verdict's test** is `Turing.exists_recordTestTM` (`CfgRecord.lean:5396`) at
  `k := U₀.k` and `P q τ := decide (q = none ∧ τ = 1)`, a one-tape machine run on the record tape
  by R1. The record it reads is the runner's endpoint for some `N`; identify it with
  `windowRun_summary_of_halts`'s at `N = configBound + 1` by `windowRun_stop_unique`. On
  `exhausted` tape 0 is unspecified: answer `true` without the test (and on `left`, either way).
  The answer is written by a **one-step emitter leaf of your own** (`[e b]`, then halt).
- **The composition**, on general configurations over any alphabet (the seam's `Bool`
  corollaries `seamCompTM_spaceUsed_le_add`, `seamCompTM_spaceUsedByTape_le_add` and `_le_max`
  are stated over `MultiTapeTM k Bool _` and `Cfg.ofWords` and **do not apply** to `D`):
  - the seam: `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
    `seamCompTM_visitedByTapeHead_ofCfg`, and `seamCompTM₂_run_ofCfg` for the fold's two verdicts
    and the runner's exits;
  - R1, to host a phase with fewer tapes on `D`'s: `embedEmitTM`, `embedEmitTM_runFrom`,
    `embedEmitTM_frame`, the reconstruction `embedEmitCfg_eq`/`embedEmitCfg_select`,
    `embedEmitCfg_selected_tape`/`_pos`, `embedEmitCfg_unselected`, `Cfg.select`;
  - or the contract layer `Turing.Contract` (`Build/Contract/{Basic,Seam,Embed}`: `Contract.seq`,
    `Contract.embed`, `Contract.within`, `Contract.spaceUsedByTape_le`); `Contract.embed`
    transports output-normalized preconditions only.
- **The space route:** per tape, the union of the phases' visited sets
  (`seamCompTM_visitedByTapeHead_ofCfg`, then the embeddings' visited lemmas above), or head
  envelopes (`Contract.spaceUsedByTape_le`, `MultiTapeTM.spaceUsedByTape_le_card_Icc`,
  `MultiTapeTM.spaceUsed_le_of_abs_le` for the record rows' and runner's displacement bounds),
  summed over the tapes by `MultiTapeTM.spaceUsed_eq_sum`.
- **The packaging** is `Turing.FinTM.decidesInSpace_of_alphabetReduction` (`ConfigCount:568`) at
  `e`: a `Bool` decider of `L_D` in space `c_D · (g n + 1)`, in `SPACE g` by `g`'s floor
  (`SPACE.mono_const`). Define `L_D` through `D`'s output (`MultiTapeTM.indicator` in `hD`), not
  through `windowRun`: the runner pins its exit only for non-exhausted `N ≤ configBound + 1`.
- **The normalization** (for `L_D ∉ SPACE f`):
  `FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` (a time bound and the space
  bound at every time), `Turing.FinTM.one_work_tape_binary_spaceUsed` (one work tape, constant
  `c₁`), and **`Turing.exists_codeTM_spaceUsed`** (`Encoding.lean:741`: a coded machine with the
  same halting runs and the same space at every time), with `MachineCode.decode_encode` for
  `code.decode (code.encode N) = N`. Never re-derive the space clause through
  `relabelState_runFrom_init` and the `M.k = 1` cast (rule 5).
- **The window facts:** `FinTM.inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts`,
  `windowRun_stop_unique`, `FinTM.configBound_le_two_pow`, `outSummary_append_congr`,
  `outSummary_eq_accept_iff`, `outSummaryCode_eq_one_iff` (the tag `1` is exactly the output
  `[true]`), `Cfg.inWindow_init` (the runner's `InWindow` premise at the start, at every radius),
  `FinTM.ComputesInTime.of_spaceUsed_le`, `FinTM.ComputesInTime.spaceUsed_le_of_halt` (the space
  at time `configBound`; `MultiTapeTM.spaceUsed_mono` points the wrong way past the halt),
  `MultiTapeTM.abs_pos_lt_card_visited`, `mem_visited_of_ne_none`; the records' readings
  `recordAt_iff`, `recordLength_eq`, `joinFields_cfgRecord_length`, `posWidth_eq` and
  `Complexity.LogProg.length_bits_le_log` (`posWidth n = O(logSpace n)`, which `g`'s floor
  absorbs); `length_pairEncode` (`n ≥ N₀`) and `length_bits_le_self`.

### The route (binding where it names a row; the rest is the recommended shape)

**The inclusion** (`SPACE f ⊆ SPACE g`): the route probe's `hr_inclusion` (`hfg` at `A = 1` from
some `N` on, `g`'s floor below `N`, `SPACE.mono_const`). Copy it as a private, **renamed
`sph_inclusion`**.

**The diagonalizer `D`**, over the record alphabet `RecSym Q₀ (Fin 3)` (`Q₀` the states of `U₀`),
on the embedded input `x.map e`, as phases composed by the seam host:
1. validate the input (`inputFoldTM`); on a foreign input, halt;
2. the radius: `M_g`, lifted, under `embedSilentRetTM` on the witness bank, writes
   `bits (g n)` on the radius tape (`r = g n`);
3. the rewinds: the radius tape (`rewindTM`), then the input head (the one-step right move, then
   the lifted `inputRewindTM 0` by R1);
4. the initial record of `U₀`'s start on `x` at radius `r`, with the empty-output tag, by R1;
5. the run: `exists_configWindowRunnerTM` at `U₀` with `summaryTag`, by R1;
6. the verdict: on `halted`, the record test, then `false` if it says yes and `true` otherwise; on
   `left` or `exhausted`, `true`; the emitter leaf writes it.

**The tape plan** (recommended; its constraints are binding): tape 0, the record (the record
rows', the runner's and the test's tape 0); tape 1, the radius (the capture tape `cap`,
`exists_recordInitTM`'s tape 1); a blank bank for `exists_recordInitTM`'s tapes `≥ 2` and the
runner's tapes `≠ 0` (one bank of `max(K_I, K_R)` tapes may serve both, since the record
initializer changes only tape 0); the witness bank, `M_g.k` tapes, dirty after the radius phase.
**The runner's bank must not contain the radius tape or the witness bank.** The fold and
`rewindTM` run on `D`'s tapes directly; the input rewind is embedded on no tape.

**`D`'s space**: the witness's `c_g · g n` (its bank), the radius tape's `|bits (g n)| + 2`, the
record's `L = recordLength U₀.k n (g n) = O(g n + log n)`, the record rows' and runner's
displacements `O(L + g n)`, the test's `O(L)`: all `O(g n)` by `g`'s floor, **uniformly in the code
part of `x`**: the window, not `U₀`'s constant, bounds the simulation (the runner's constants
depend only on `U₀` and `Fin 3`).

**`L_D ∉ SPACE f`.** If `M` decides `L_D` in space `c₀ · f`, normalize it (the normal form's
constant `c₁`), take its code `α`, and pad the payload, never the code: on
`x = pairEncode α (List.replicate N₀ true)` with `N₀` from `hfg` at `A := C_α (c₁ · c₀ + c₁ + 1)`
(`C_α` from `exists_selfUniversal`, using `1 ≤ f n`), `U₀`'s run stays in the radius-`g n` window
and halts within `configBound` rounds, so the runner exits `halted` with the summary of `U₀`'s
output, which is `[x ∈ L_D]`; `D` answers the opposite.

**`LOGSPACE ⊂ PSPACE`**: the route probe's `hr_logspace_ssubset` applied to `space_hierarchy`, with
`hr_logSpace_dom` and `hr_sq_le_two_pow`. Copy the three as privates, **renamed
`sph_logspace_ssubset`, `sph_logSpace_dom` and `sph_sq_le_two_pow`**; the inclusion is the
published `Complexity.LOGSPACE_subset_PSPACE` (`SpaceClasses`, after #181), which the probe
already cites: never re-prove it (the ledger's LS-1).

**`SPACE (n + 1) ≠ NP`** (checkpoint 8): by padding and `NP`'s closure under `≤ₚ` (the
docstring's sketch). **It may end in a named escalation** (the user's ruling, 2026-11-06): no
host is published for the **padded language's decider**, that is, for validating the pad's length
and running `L`'s decider on the input's first component within space linear in the padded
length. If you cannot build it from named hosts, **stop on that item only**, leave
`SPACE_linear_ne_NP`'s body `sorry` with a literal "Proof sketch", and state the missing lemma
(its statement, in `REPORT.md`'s escalations). `space_hierarchy` and `LOGSPACE_ssubset_PSPACE`
do not depend on it. What is published:
- **`NP`'s closure**: `Complexity.preimage_mem_NP` (`ClassNP/PClosure`, PR #177: `NP` is closed
  under polynomial-time preimages; with `L ≤ₚ L'` by `p`, `L = p ⁻¹' L'`): cite it, never re-prove
  it; `NP`'s reading is `mem_NP_iff_exists_length_le`, `≤ₚ` is `Complexity.PolyTimeReducible`;
- **the padding map's polynomial time**, if the pad has length `(|x| + 1) ^ 2`, that is
  `p x := pairEncode x (List.replicate (1 * (|x| + 1) ^ 2) true)`:
  `polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary 1 2)`
  (`PolyTimeComputable.pairEncode`, `ClassNP/PolyTimePairing`); `p ⁻¹' L' = L` by
  `pairEncode_injective` or `pairFstD_pairEncode`/`pairSndD_pairEncode`;
- **parts of the decider**: the first component computed on the native input and installed on
  a work tape, `FinTM.exists_inputCallTM` at `FinTM.computesFunInTime_pairFst` (time only; its
  space by `MultiTapeTM.spaceUsed_le_mul_succ`); a machine run on a buffered word, Z1's
  `vhostEmitTM` (`vhostEmitTM_runFrom`, `vhostEmitTM_spaceUsed_le`: the source's space plus
  `|y| + 2`; the layout `vhostCfg` and its field equations, `vhostCfg_workTapes` and the like).
  **Unhosted:** the pad-length test in space `O(|y|)`, and the assembly of these into a `Bool`
  decider of `L'` in `SPACE (m + 1)`;
- **the strictness extraction**, through `space_hierarchy` at `n + 1` and `n ^ 2 + 1`
  (`spaceConstructible_linear`, `spaceConstructible_poly 2 (by norm_num)`;
  `A · (n + 1) ≤ n ^ 2 + 1` for `n ≥ A + 1`).

**Edge cases that must stay true:** the empty input; an input of the rich alphabet that is not an
embedded word (rejected by the fold, in bounded space); the witness's input head at `0` at its
halt (the one-step right move); `U₀` halting with an output other than `[true]` (`true` from
`D`); the window exit and the clock's exhaustion (`true` from `D`, the latter without the test);
`n` below `N₀` (the padding chooses `n ≥ N₀`); `f`'s floor `1 ≤ f n` (the arithmetic of `A`).

## Gate guidance (binding)

- **The P4.3 statement gate** froze the statements; the hierarchy's constant-factor hypothesis has
  no square and no logarithmic term; both constructibility hypotheses are the book's, and the proof
  uses `g`'s witness and floor but, of `f`'s, only the floor.
- **The route note's rulings:** H first, the corollaries as later checkpoints of the same fill; F6
  after U2's harvest. **The user's ruling (2026-11-06):** `SPACE_linear_ne_NP` stays H's last
  checkpoint and may end in the named escalation above.

## Cited infrastructure (public and proved at the issue commit; all in `HImportProbe2.lean.txt`)

The import probe's 72 names: the targets and the space classes with their readings
(`mem_SPACE_iff`, `SPACE.mono`, `SPACE.mono_const`, `decidesInSpace_iff`, `computesInSpace_iff`,
`spaceConstructible_iff`, `LOGSPACE_eq`, `space_poly_subset_PSPACE`, the three constructible
rows); the universal machine and its code scheme; the runner and the window run with its records,
widths, alphabet and facts; the record rows; the output summary; the alphabet reduction and its
space clause; the input fold; the symbol lift; the seam's `Bool` space lemmas and the `Bool`
capture wrapper (cited there; not used by the route); the space and visited-interval facts; the
normal forms; the counter value's readings; the API of #175, #177 and #181. **The extension's
99 more:** the returning capture embedding and its readings; the lift's field equations; the
seam's general-configuration forms, R1 and the contract layer; the space-from-envelope lemmas;
the rewinds and the one-step leaf's lemmas; the record test; the small readings; the summary
update; `exists_codeTM_spaceUsed`; `NP`'s bounded-certificate reading, `≤ₚ` and the padding's
hosts.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Hierarchy.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the three targets and `space_universal`.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The corollaries depend on `space_hierarchy`'s statement only, so they may be proved
   before it; nothing depends on `SPACE_linear_ne_NP`.
5. **No touching other sorries**, `space_universal`'s among them. Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the base's five and the overlay's four; add none.
7. **One proof per shared argument.** Never write a second universal machine, clock, counter loop,
   record row, window runner, seam, symbol lift, tape embedding or capture transformer: the
   radius phase runs under the published `embedSilentRetTM`, and your only leaves are the
   one-step input move and the one-step emitter. Never re-walk `TimeHierarchy/Diagonal`'s or
   `TimeHierarchy/Separation`'s privates (a colleague's diagonalization), `WindowClock`'s or
   `RecordTable`'s privates: models to read, not to copy.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 317 lines; 4 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and each target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own definitions and privates.
    - **Never unfold a definition of another file**, and no definitional closure either:
      `SPACE` through `mem_SPACE_iff`; `FinTM.DecidesInSpace` and `FinTM.ComputesInSpace` through
      `decidesInSpace_iff` and `computesInSpace_iff`; `SpaceConstructible` through
      `spaceConstructible_iff`; `logSpace` through `logSpace_eq`; `LOGSPACE` through
      `LOGSPACE_eq`; `PSPACE` only through `space_poly_subset_PSPACE`; `NP` through
      `mem_NP_iff_exists_length_le`; the window run, records and summaries through their lemmas;
      the transports `embedSilentCfg`, `embedEmitCfg`, `Cfg.select` and `Cfg.liftSymbols` through
      the field lemmas the hosts list names.
    - **Scope (user, 2026-10-23):** TCSlib's own definitions. Core and Mathlib definitions may
      reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`, `rw` or `unfold`.
    - **The machine model's primitives** are read through their lemmas; unfold `step` and
      `Action.apply` only for a leaf of your own file, preferring `MultiTapeTM.step_of_some` and
      the `Action.apply_*` field equations.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate**, naming the lemma you need.
    - **Self-check by both methods:** a **seal test** (a scratch copy of your module with
      `attribute [local irreducible]` on every other-file TCSlib definition your proofs mention,
      from your first private on: at least the route probe's five (`SpaceConstructible`,
      `SPACE`, `logSpace`, `LOGSPACE`, `PSPACE`) and the transports and record definitions you
      reach (`embedSilentCfg`, `embedEmitCfg`, `Cfg.select`, `Cfg.liftSymbols`, `summaryTag`,
      `outSummaryCode`, `windowRun`, `cfgRecord`, `RecordAt`, `recordLength`, `posWidth`,
      `FinTM.bufferTape`); `attribute [-simp]` on the four `@[simp]` TCSlib definitions
      `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`; **with controls**: for
      each sealed definition, a goal that closes by `rfl` with nothing sealed and fails under the
      seal, recursive definitions with usage controls); and an **inspection table** of every
      `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change` argument in your diff. **Ship the raw
      outputs.** A seal not run, or without controls, is a checklist failure.
    - List every declaration you cite outside your file; if more than `HImportProbe2`'s, extend a
      copy of it and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep **every** new private under the `sph_` prefix, the route probe's copied
    `hr_*` lemmas included (`Sph`/`sph` for types and definitions; `sph_` is unused in the tree at
    the issue commit, while `sh_` is not: `ExpBFS/Run`'s `sh_run`).

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and the inclusion** (`sph_inclusion`).
2. **`D`'s first phases**, each a framed run on the tape plan (a `Turing.Contract` or the
   `_ofCfg` run lemmas): the validation, the radius under `embedSilentRetTM`, the two rewinds,
   the initial record.
3. **`D`'s run and verdict**: the runner at `U₀` by R1, its exits read through the window run,
   the record test and the emitter.
4. **`D`'s space and the packaging**: `L_D ∈ SPACE g`.
5. **The normalization and the window**: `U₀`'s run on the padded code stays in the window and
   halts within `configBound`.
6. **`space_hierarchy`.**
7. **`LOGSPACE_ssubset_PSPACE`.**
8. **`SPACE_linear_ne_NP`**, or its named escalation (the padded decider's missing lemma).

Each may land alone. **Add no new admission.** **One checkpoint, one commit, one zip, delivered at
once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**, each on a
frozen copy of its commit (`git worktree add <dir> HEAD`). **Semantic duplication (required):** for
every private lemma you add, search for a published declaration that states it or a
generalization, in the tree and on every open PR branch, by name and by statement (`git grep`), and
by an `exact?` or `apply?` probe; `REPORT.md` lists the search and result per private. **The
population** is 43 files, all listed in `screen-population.txt`: the pre-ship's 27 (your file;
the 22 other modules declaring the import probe's names, `TimeHierarchy/Diagonal` among them; `ClassNP/NP`; the known
hazards `TimeHierarchy/Separation`, `SpaceComplexity/Savitch`, `ClassNP/Nondeterminism` for the
padding precedent) **plus the 16 modules this revision newly cites**:
`TuringMachine/Build/Embed`, `Build/Contract/Basic`, `Build/Contract/Seam`,
`Build/Contract/Embed`, `Build/InputRewind`, `Build/Rewind`, `Build/InputCall`,
`Build/Primitives`, `Build/VirtualInput`, `TuringMachine/Configuration`,
`TuringMachine/Deterministic`, `TuringMachine/Finite`, `TuringMachine/Simulation`,
`SpaceComplexity/Machines/Bin`, `ClassNP/PolyTime`, `ClassNP/PolyTimePairing`. **The pre-ship
base** is `campaign/fills/b6/logs/b6-fill-hierarchy-screen-base.txt`, over the 43
(`campaign/fills/b6/inputs/b6-fill-hierarchy/screen-population.txt`): 1,854 declarations, 1,689
pairs, 534,736 characters, none on `Hierarchy`. Your before-screen over the 43 files must
reproduce it and is your base for new pairs; `REPORT.md` states both counts. A new cross-file pair with an
owned-file declaration on one side is listed with one disposition (idiom; re-derivation of a
published lemma: cite it instead; re-derivation of another file's private: keep yours and request
a promotion); a pair at 90% or more is a copy. `REPORT.md` carries **"new copies: none"** or lists
each pair, and ships both full outputs.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only**; **never `lake build`**, never
  the unfiltered `lake exe cache get`; `scripts/lean_check_tree.sh` for every check, one Lean
  process at a time (a screen may run beside one). The cache tool's own compilation inside
  `lake exe cache get` is outside the one-Lean rule. **A process deviation never ends the item.**
- **Bootstrap** from `campaign/fills/b6/orders/b6-fill-hierarchy.txt` (220 modules), right after
  branching, logging each module's time and maximum memory. **The base sorry-warning set** has
  26 entries in 10 modules; yours are `Hierarchy`'s four. Record the base list by name first.
- **Final checks:** `Hierarchy`: zero errors, exactly one sorry warning (`space_universal`'s; for a
  partial or the escalation, also the open targets'); every other module: zero errors and the
  base's sorry warnings; `HImportProbe2` re-run, 0 errors. **After every proof edit**, check
  `Hierarchy` and its only importer, the facade `TCSlib/Complexity/SpaceComplexity`; the final
  sweep runs the order list's tail from your module on (52 modules).
- **Axiom prints** for the three targets and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL
  (base: 0 FAIL, 80 WARN over 111 files), and `scripts/style_lint.py` on your file (base: one
  finding, the module docstring's missing `## Main definitions`); no new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your three targets: `space_universal` (F6, your file),
`Complexity.savitch` (`SpaceComplexity/Savitch`), and the rest of the list in
`campaign/fills/b6/logs/b6-fill-hierarchy-base-sorries.txt`.

## REPORT.md checklist

- [ ] The preflight, the roots and the cache fetch (with the logs), the bootstrap with per-module
      time and memory, the base blob check.
- [ ] The overlay only; nothing outside regions (a)–(d); `space_universal` untouched.
- [ ] The checkpoints reached (1–8), one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `D`'s phases and its tape plan; the radius under
      `embedSilentRetTM`; the rewinds; the runner's call and the test's.
- [ ] `D`'s space bound, term by term, and its uniformity in the code part of `x`; the constant
      `A` of the contradiction, with `c₁` and `C_α` named.
- [ ] The base sorry list by name; each edge case with the lemma that covers it.
- [ ] Promotion candidates and escalations (for checkpoint 8, the missing lemma's statement), or
      "none"; the proposed `**Implementation.**` paragraphs.
- [ ] Rule 10: the citations outside your file (an elaborated-constant walk), the probe re-run,
      **the seal test with its controls and both raw outputs**, the inspection table. Rule 11: a
      grep of your diff for the six R3 rows and other files' private names; every private `sph_`.
- [ ] Duplication: both v3 screens on the 43-file population, every new pair justified, the
      semantic search per private, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise**: `funext` before `rw`, or the step closes by
  unfolding and the seal rejects it.
- **`logSpace` is not `Nat.log 2`**: `logSpace n = Nat.log 2 n + 1` (`logSpace_eq`), so it is at
  least `1` everywhere; the floors come from `spaceConstructible_iff`'s first conjunct.
- **`SPACE` absorbs constants** (`SPACE.mono_const`): prove the bound `c · (g n + 1)` and absorb
  it by `g`'s floor, not by unfolding `SPACE`.
- **`PSPACE` has no reading of its own here**: reach it through `space_poly_subset_PSPACE`.
- **The window lemma fixes the update**: `windowRun_summary_of_halts` holds only at
  `upd := summaryTag` and the initial tag `0`; the runner's endpoint clause gives some `N`
  (`windowRun_stop_unique` aligns it).
- **The `Bool`-only rows**: `capture_run`, `inputRewindTM_run` and the seam's space corollaries
  are stated over `Bool`; on `D` use `embedSilentRetTM`, the lifted rewind by R1 and the
  `_ofCfg` forms.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** `omega` with
  products as atoms (`ring` first). The linter needs a literal "Proof sketch" before every
  `sorry` (partial only).

## ===== campaign/fills/b6/reports/hierarchy-REPORT.md =====

# B6 hierarchy fill — final report

**Outcome:** `Complexity.space_hierarchy` and `Complexity.LOGSPACE_ssubset_PSPACE` are
proved on `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. All 43 new private
declarations are also admission-free. Checkpoint 8, reached last, proves the padding implication
and ends in the specifically permitted escalation **E-PAD**: the exact padded-language
linear-space decider. `SPACE_linear_ne_NP` keeps its original `sorry` and literal “Proof sketch”.
F6 is byte-preserved. No new admission, push or PR.

The full 52-module downstream sweep passes with the two expected Hierarchy sorry warnings
and two unchanged baseline style warnings in `Randomized/Classes`
(1,274.870 seconds summed wall time; peak RSS 2,528,956 KiB).
The 71-definition seal passes, all 75 controls pass unsealed and fail sealed, and the final
321-name import probe passes. Campaign lint: 0 FAIL, 81 WARN. The final text screen has 12 new pairs, all below 90%; **new copies: none**.

## Identity and authorized scope

- Exact base: `e6bc196838b4e2675e4214306c730e7404624ab8`.
- Base source blob: `287acce8326a1de271dfa6be2cc3776f3a2caa32`.
- Local branch: `fill/b6-hierarchy`, created at exactly the base after the ancestor check passed.
- Final commit: `30222bbd264a75057ae0779535a32e1a30dd2394`.
- No rebase, merge, cherry-pick, push or PR.
- Only tracked change: `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`, in regions (a)–(d).
  All four public statements are byte-identical to the base. The complete `space_universal`
  docstring/body and its module main-results entry are byte-identical. Imports are exactly the
  five base imports plus the four required overlay imports.
- Source: 2,563 physical lines, four public declarations and 43 private declarations.
  The standalone linter counts the trailing empty split segment as line 2,564. No new admission,
  no forbidden R3 row, no directly cited foreign private, and no added line over 100 characters.

The dispatch files were verified against the supplied manifest before reading:

| File | SHA-256 |
|---|---|
| `b6-fill-hierarchy.md` | `3c92e156529b5a7f1f061e3b1d5beaf0918fe3b11355e34362441b56c36bd357` |
| `fill-environment-addendum.md` | `9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28` |

The first local serialization appended a newline; writing the fetched bytes exactly corrected
that local serialization before verification/read. Neither remote artifact mismatched.

## Checkpoints and declarations

| Checkpoint | Status |
|---|---|
| 1 | Overlay, inclusion and permitted documentation cleanup committed and checked |
| 2 | Validation, returning radius capture, both rewinds and framed initializer committed and checked |
| 3 | Complete simulation suffix: runner, test, all three exits, opposite answer and head envelope |
| 4 | Full validation/capture/rewind/record/suffix composition; all-input space bound; binary language in SPACE g |
| 5 | Normalization and universal-machine window lemma committed and checked |
| 6 | Complete public hierarchy proof, admission-free |
| 7 | Complete public logarithmic-space strictness corollary, admission-free |
| 8 | Last checkpoint: conditional padding proof complete; named decider escalation E-PAD |

| Private declaration | Role |
|---|---|
| `sph_inclusion` | Mandatory inclusion proof via the finite exceptional prefix and SPACE.mono_const |
| `sph_code_window` | Normalize a smaller-space decider, pad only its payload, and obtain the universal halted window summary |
| `sph_sq_le_two_pow` | Mandatory square-versus-exponential arithmetic |
| `sph_logSpace_dom` | Mandatory eventual logarithmic domination |
| `sph_logspace_ssubset` | Mandatory corollary from an explicit hierarchy hypothesis |
| `sphRightTM` | Permitted one-step input-head move leaf |
| `sph_right_run` | Framed run, positive input position, first return and unchanged work heads |
| `sphEmitTM` | Permitted one-step verdict emitter leaf |
| `sph_emit_run` | One-symbol emission and halt, with unchanged work heads |
| `sphDigit` | Finite validator predicate on the rich alphabet |
| `sph_fold_valid` | The fold accepts exactly digit-embedded binary words, including empty input |
| `sph_validation_run` | Framed validation with first-exit cut and unchanged work heads |
| `sphWitnessSel` | Witness bank after record, radius and both scratch banks |
| `sph_witness_cap` | Radius tape is outside the witness selection |
| `sph_radius_run` | Returning capture, complete output buffer, framed endpoint, silence and per-run space bound |
| `sphEmptySel` | Empty selection for the zero-work-tape input rewind |
| `sph_input_rewind_run` | Lifted input rewind via R1 on an arbitrary positive input position |
| `sphRewindsTM` | Published seams joining the right move, input rewind and radius rewind |
| `sph_rewinds_run` | Framed composed rewind endpoint and first return, with radius head at zero |
| `sphInitSel` | Initializer selection preserving the runner and witness banks |
| `sph_initial_record` | Framed initial record on the full tape plan, with first return and head envelope |
| `sph_select_fields` | Shared R1 selected-configuration readings via reconstruction; also used by the initializer |
| `sphRunnerSel` | Runner bank: record zero plus its separate scratch bank |
| `sph_runner_run` | Published runner by R1, including cuts, all exits, record endpoint and displacement bound |
| `sphRecordSel` | Single record-tape selection for the test |
| `sph_test_run` | Published record test by R1 with complete physical frame |
| `sphEmitContract` | Existing one-step emitter packaged as a stationary-head contract |
| `sphVerdictTM` | Published two-exit seam from record test to opposite-bit emitters |
| `sph_verdict_run` | Tested bit complement and shared head envelope |
| `sph_summary` | Returned stopped record aligned with a certified halting summary by stop uniqueness |
| `sph_seam_heads` | Common absolute interval transported through a published single-exit seam |
| `sph_seam_avoids` | A dispatched seam cannot revisit a different left-hand exit |
| `sph_written_record` | Shared record-boundary argument after an interior layout write |
| `sphRunnerTailTM` | Three published seams route halted, left and exhausted runner exits |
| `sph_runner_tail_run` | Complete three-exit suffix run and absolute head bound |
| `sph_suffix` | Uniform initial-record-to-halt suffix with opposite acceptance and displacement bound |
| `sph_record_suffix` | Initializer and complete runner suffix joined on the disjoint tape plan |
| `sph_record_size` | Record, radius digits and fixed overhead bounded by `(4*k+9)*g(n)` |
| `sph_valid_machine` | Complete post-validation machine and absolute head envelope on embedded words |
| `sph_halt_contract` | Public first-halt theorem packages a known bounded run as a branch contract |
| `sph_validated_machine` | Published two-exit validation branch, total on all rich inputs, with a summed space bound |
| `sph_linear_ne_NP_of_padding` | Separation from NP given the exact padded-language decider, using only published padding and preimage hosts |
| `sph_diagonal_language` | Total Boolean language, alphabet reduction and membership in SPACE g |

Every new private lemma has a literal Proof sketch; the small selection/leaf definitions have
public-facing descriptions. The only open target is `SPACE_linear_ne_NP`, with literal **Proof sketch** text. The
untouched F6 body `space_universal` remains `sorry` with its original docstring. Both completed
public target bodies and all 43 private declarations are admission-free. No other source file
or admission was changed.

## Tape plan and first phases

The physical tape count is `KI + KR + M.k + 2`: record 0, radius 1, initializer scratch
2 through `KI + 1`, runner scratch `KI + 2` through `KI + KR + 1`, then the witness bank.
The initializer selects only its own bank plus record/radius. The witness selection starts
strictly after both scratch banks, so its dirty endpoint cannot enter the future runner bank.

The validator uses `inputFoldTM_run_ofCfg` and recognizes exactly the image of `digitEmb`.
The returning radius phase chooses a first halting time of the constructibility witness,
lifts its binary run, and calls `embedSilentRetTM_run`. Its last emitted bit is included.
The radius tape ends at the buffer's length; outside the witness selection and radius tape,
all tape contents and heads are the supplied arbitrary frame. The physical output is unchanged.
Its proved per-run space bound is

```text
(KI + KR + M.k + 2) * (c * g |x| + |bits (g |x|)| + 1).
```

Here `KI` and `KR` are the initializer and runner scratch counts, `M` is the constructibility
witness, `c` its space coefficient, `g` the target bound, and `x` the binary input. This bound
is for the radius phase only, not yet a full-machine space claim.

The one-step right move handles a witness stopped at input position zero, and also handles the
right boundary. The lifted zero-tape input rewind runs by `embedEmitTM` on an empty selection.
`sphRewindsTM` joins it and `rewindTM` by two published general-configuration seams.
`sph_rewinds_run` restores input position one and radius-head position zero, preserves every
work-tape cell and the accumulated output, and proves the first-return cut. Empty captured
words are admitted. The initializer then calls `exists_recordInitTM` by R1, reading the selected
configuration through reconstruction and public field equations. Only its scratch bank must be
blank; the endpoint changes record tape zero only, with the published time and head bounds.

## Simulation suffix

`sph_suffix` applies `exists_configWindowRunnerTM` at the fixed finite machine with `Fin 3`,
`summaryTag` and initial tag zero. The tape-zero record and separate runner scratch bank are
selected by R1. On a halted exit, the returned record for an unspecified stopped round count
is matched to the certified halting summary by `windowRun_stop_unique`. The published record
test checks state `none` and tag one; the emitter writes the complementary bit. Left and
exhausted exits emit true. Exhaustion does not inspect the unspecified record.

Three existing single-exit seams handle the runner's three anchors. This is a composition of
published hosts, not a new seam transformer. The two verdict-test anchors use the published
two-exit seam and its branch contract. Every head stays within

```text
(CR + CT) * (recordLength M.k |x| s + 1)
```

of its initial physical position throughout the suffix. `CR` is the runner coefficient,
`CT` the record-test coefficient, `M` the fixed simulated machine, `x` its binary input and
`s` the radius. These constants do not depend on the input's code part. The suffix halts with
one output symbol on every valid initial record. Whenever `M` halts within the radius at its
configuration-count bound, that symbol is the opposite of its singleton-true acceptance.

## Full-machine space and binary packaging

The strengthened `sph_radius_run` additionally bounds every intermediate physical head by the
absolute ambient frame position plus `c*g(n) + |bits(g(n))|`. Selected heads use the public
space-to-window bound; the capture head uses output-prefix monotonicity; frame heads do not
move. `sph_rewinds_run` retains the published rewind envelope: displacement at most
`|bits(g(n))|+1`, with all cells preserved. The generic seam head lemma is moved earlier solely
so both compositions can share it.

Let `K = KI + KR + G.k + 2` be the physical tape count, `G` the constructibility witness,
`c` its space coefficient, `M` the fixed simulated machine, `n` the binary input length,
`s = g(n)`, and `L = recordLength M.k n s`. Put `C = CI + CR + CT`, the sum of the
initializer, runner and record-test head coefficients. The proof establishes, term by term:

```text
radius capture:       rR = c*s + |bits(s)|
through both rewinds: rW = rR + |bits(s)| + 1
record/suffix motion: rS = C*(L + |bits(s)| + s + 1)
combined radius:      rW + rS
                    <= (c + 3 + C*(4*M.k + 9))*s = B*s.
```

The arithmetic uses `|bits(s)| <= s`, `posWidth n <= 2*logSpace n <= 2*s`, the public formula
`L = M.k*(2*s+1) + posWidth n + M.k + 4`, and `1 <= s`. It does not cite the pending #208
bit-length lemma. Constants are chosen from fixed machines before the input and its code are
known. The record and both scratch banks are initially blank because the radius capture frames
them, and the initializer changes only record zero.

The actual `FinTM` starts the published input fold and uses `seamCompTM₂`/`Contract.branch`.
On a valid embedded word it enters the above machine; on a foreign symbol it emits false.
The branch contract uses a first halt of the valid run without changing its completed output.
Every work head is in `[-B*g(n), B*g(n)]` through the final halt, including on invalid rich
inputs. The public interval theorem gives

```text
D.spaceUsed(init ys, haltTime ys) <= K*(2*B*g(|ys|)+1).
```

The public halted-run space theorem extends this to every time. Applying
`decidesInSpace_of_alphabetReduction` yields a binary decider within
`c'*(K*(2*B*g(n)+1)+1)`. `SPACE.mono_const` absorbs this into `SPACE g`, since

```text
K*(2*B*g(n)+1)+1 <= (K*(2*B+1)+1)*g(n).
```

The language is the set of binary inputs on which the chosen total output of `D` is true.
The indicator equation is obtained through the already imported
`FinTM.toFinNDTM_haltsWithin_and_accepts_iff`: the permitted one-symbol emitter, instantiated
at that indicator bit, identifies acceptance using the public ND embedding/acceptance
readings. No indicator definition is unfolded. The shorter published
`LogProg.indicator_eq_decide` is outside the frozen nine-import closure, so no import was added
and no duplicate generic indicator lemma was introduced. Moving that convenience reading into
a lower imported module would simplify this local consumer calculation.

New notation in these displayed bounds: `rR`, `rW`, `rS` are the three intermediate radii;
`B` is their fixed combined coefficient; `c'` is alphabet reduction's coefficient. Other
symbols are defined immediately above the calculation. The construction proves the actual
existence of the diagonal language in `SPACE g`, not only a conditional packaging statement.

## Normalization and contradiction arithmetic already proved

The second private is `sph_code_window`. It normalizes an arbitrary smaller-space decider by
`one_work_tape_binary_spaceUsed` and `exists_codeTM_spaceUsed`, then uses the supplied universal
machine's per-code simulation contract. It returns a padded input and the exact time
`U₀.configBound x.length (g x.length)`, together with the correct one-bit output, space at most
`g x.length`, and the exact halted window-run summary at the next round.

The constant is chosen after the code and its universal constant:

```text
A = C * (c₁ * c₀ + c₁ + 1)
C * (c₁ * (c₀ * f n + 1) + 1)
  ≤ C * (c₁ * (c₀ * f n + f n) + f n)
  = A * f n ≤ g n.
```

Here the first inequality uses `1 ≤ f n`, and the final inequality uses the domination
threshold. The payload is `List.replicate N₀ true`, so the paired input's length is at least
`N₀`; the code itself is unchanged. The published halting-space theorem supplies the
configuration-bound time, and `windowRun_summary_of_halts` supplies the window conclusion.
No statement of `space_hierarchy` is used in this private proof.

The new symbols in this calculation are the existing proof parameters: `c₀` is the original
decider's coefficient, `c₁` the normal-form coefficient, `C` the fixed code's universal
simulation coefficient, `A` their domination coefficient, and `N₀` the resulting threshold. This `C` is the route's
`C_α`, fixed for the normalized decider's code `α` before its payload is padded.


## Public hierarchy contradiction

Choose the published self-universal machine and the diagonal language already proved in
`SPACE g`. Assuming the reverse inclusion puts that language in `SPACE f`. The normalization
lemma supplies a payload-padded input at which the universal machine computes the language's
indicator within the radius and configuration-count bound. The diagonal language then gives
that same indicator as the negation of whether its singleton output is `[true]`. The two
Boolean cases are contradictory. The forward inclusion is the required finite-prefix lemma.
The logarithmic-space corollary now inherits the resulting admission-free theorem.

## Required edge cases

| Case | Checked lemma or public reading |
|---|---|
| Empty binary input | `sph_fold_valid` proves the empty-list case; `sph_valid_machine` and `sph_diagonal_language` quantify over every `List Bool` with no nonempty premise; the floors give a positive radius |
| Rich input containing a foreign symbol | `sph_fold_valid` characterizes the valid image; `sph_validated_machine` sends the false branch directly to the stationary-head false emitter |
| Witness halts with input head at zero | `sph_right_run` uses `moveInputPos_pos_of_ne_right` and `moveInputPos_rightBoundary` to obtain positivity, then `sph_input_rewind_run` restores position one |
| Witness's final transition emits | `sph_radius_run` uses `embedSilentRetTM_run` at the first halt; `embedSilentCfg_cap` reads the complete captured output |
| Universal output is not `[true]` | `sph_summary` uses `outSummaryCode_eq_one_iff`; `sph_verdict_run` emits the complement of the test, hence true |
| Window exit is `left` | The `left` branch of `sph_runner_tail_run` dispatches directly to the true emitter |
| Clock exit is `exhausted` | The `exhausted` branch of `sph_runner_tail_run` dispatches directly to the true emitter without reading or testing the unspecified record |
| Run clock is beyond an earlier halt | `sph_code_window` uses `FinTM.ComputesInTime.spaceUsed_le_of_halt`; `sph_summary` uses `windowRun_stop_unique` to align endpoint round counts |
| Input length below the domination threshold | `sph_inclusion` absorbs the finite prefix; the diagonal contradiction's `sph_code_window` chooses a payload whose paired length is at least the threshold by `length_pairEncode` |
| The lower bound needs `1 ≤ f n` | `sph_code_window` derives it from `spaceConstructible_iff` and `logSpace_eq` before bounding the universal simulation coefficient |

## Environment and verification

Part 1 preflight passed before bootstrap: 57.747 GiB free on the work filesystem and 9.075 GiB
MemAvailable. No cgroup controller was exposed. The first attempt to read a cgroup limit failed;
the logged fallback used `/proc/meminfo`. `/tmp` is tmpfs; all compilation/cache temporary files
used the disk-backed task `TMPDIR` instead. A later resource check still found over 51 GiB free
and 8.6 GiB MemAvailable.

Lean 4.25.0 was installed from the official release archive into a fresh task directory. It
starts normally (commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`); no loader shim or borrowed
compiled artifact was used. Every present package matched both its manifest revision and URL;
absent optional packages were not named by the module order. The cache was fetched for exactly
the 63 derived Mathlib roots, never unfiltered.

The first narrowed cache fetch succeeded. A subsequent probe was rejected because its source
resolved through a symlink outside the repository root. Conservatively, the single cleaned
retry was taken: package/build configuration artifacts were removed, preflight and pin checks
repeated, and the same roots fetched again using the freshly obtained 1,057 archives. A physical
`FillProbes/CacheProbe.lean` then passed. No empty `.olean` was found. This was a path-validation
error, not evidence of corrupt cached proofs.

The fresh **220-module bootstrap passed**, with exactly the supplied 26 sorry warnings in ten
modules. Per-module wall time and peak RSS are recorded using `os.wait4` in
`evidence/logs/bootstrap/`; summed module time was 2,834.864 seconds, maximum RSS 2,994,428 KiB.
The cache probe and every other Lean invocation also have separate resource logs. Only one
agent-started Lean invocation ran at a time; the permitted low-priority text screen ran beside it.
No `lake build`, unfiltered cache fetch or module timeout was used.


The draft checks build each composition before landing it. `cp4-edit` and the final
`cp4-seal-final` and `cp4-controls-final` series check the owned module and facade after every landed proof edit.
The owned source, full-seal, controls, extended-host and axiom checks pass. A first seal attempt
caught a repeated ND embedding field occurrence that `rw` had left to definitional reduction;
explicit public simplification of both transport occurrences fixed it. All diagnostic failures
and repairs remain in the evidence.

The 71-definition seal includes every reached other-file TCSlib `def`, including the extra
ND acceptance/embedding operations, `posWidth`, `counterValue` and finite-state instances.
The four primitive simp attributes are removed. There are 75 effective controls: 67 delta
controls, cardinality usage controls for the two enumerated rewind-state instances, recursive equation usage controls for `windowRun` and `NDTM.runWith`, and four
primitive simp controls. All pass unsealed and fail sealed. The generic whole-instance delta goal was initially ineffective for two enumerated Fintype structures (eta contraction); their cardinality goals replace it and detect the seal. Both raw runs are retained. Reducible abbreviations are excluded by the pinned `policy.md:72–79` and
`campaign/standards/TEMPLATE.md:43–49`: they are notation and Lean's default reducibility
validation rejects sealing them. In particular, `Cfg.Halted` is read as its state equation in
the two first-halt consumers, exactly the policy's explicit example; it is never an argument to
`simp`, `rw` or `unfold`. Generated structure projections and recursors are also recorded as
abbreviations. No unsafe reducibility override is used. The exact policy excerpt is shipped.

The final citation inventory combines elaborated proof references with explicit source
identifier resolution: 900 outside constants, 272 from TCSlib, with no directly cited foreign
`_private` constant. The elaborated walk alone records 882 constants, 269 from TCSlib; explicit
source resolution contributes three further TCSlib readings that simplification removed from
proof terms. The final import probe has 321 checks, adding 150 to the supplied 171. Its source
is `FinalImportProbe.lean`; the complete citation list is `evidence/citations/final.md`.
The bundled ND field readings' source modules are correctly recorded as
`TuringMachine/Nondeterministic`. No additional definition needed sealing.

The source-identifier diagnostic initially used two incompatible metaprogramming calls;
`final-source-citations-v2` is the successful run on the corrected source, with the earlier
errors retained. The inspection table `evidence/inspection/final_v2.md` enumerates all 443
rewriting/reduction tactic sites, including complete multiline arguments and public target
bodies. The final extraction also includes `simp_all` and complete multiline `change` targets,
which were not fully displayed by the earlier 442-site checkpoint table. The accompanying
`final-rewrite-heads.json` checks explicit bracket heads against Lean-resolved declaration
kinds; no foreign definition or abbreviation is supplied as a reduction rule. Own lets/leaves
and public equations are the only explicit reduction arguments.

| Axiom walk | Result |
|---|---|
| All 43 private declarations, including the complete diagonal-language construction | Subsets of `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `space_hierarchy` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `LOGSPACE_ssubset_PSPACE` | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `SPACE_linear_ne_NP` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

The two source sorry warnings remain the untouched F6 and `SPACE_linear_ne_NP`.
The public hierarchy theorem uses the private construction, normalization and inclusion. Neither completed public target depends on any admission.

## Baseline admissions by name

The bootstrap has exactly 26 warnings in the following ten modules. The only removals are
`space_hierarchy` and `LOGSPACE_ssubset_PSPACE`; the remaining 24 admissions are unchanged.
The complete original list is also in `evidence/logs/base-sorries.txt`.

| Module under `TCSlib/Complexity` | Baseline declarations |
|---|---|
| `TuringMachine/Simulation` | `branchTM_spaceUsed` |
| `TuringMachine/Encoding` | `pairDiagTM_computes` |
| `TuringMachine/Composition` | `idTM_computes`, `ifEqTM_computes`, `condTM_computes_iff` |
| `ClassP/TimeConstructible` | `_root_.Turing.FinTM.lengthBitsTM_computes`, `_root_.Turing.FinTM.lengthBitsTM_spaceUsed` |
| `TuringMachine/Build/Wrappers` | `timedCondTM_computes`, `timedCondTM_spaceUsed` |
| `TuringMachine/Build/Loop` | `loopHostTM_contracts`, `loopHostTM_decides`, `loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes` |
| `TuringMachine/Build/Primitives` | `polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes` |
| `TuringMachine/Build/RecordTable` | `exists_tableFindTM`, `exists_tableAppendTM`, `exists_recordValidTM`, `exists_recordNextTM` |
| `SpaceComplexity/Savitch` | `savitch` |
| `SpaceComplexity/Hierarchy` | `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP` |

## Duplication and lint

The before-screen is byte-identical to the supplied base: 1,854 declarations, 1,689 pairs and
534,736 reproduced characters, no pair on Hierarchy. The frozen-checkpoint-1 screen has exactly
the same pair lines. The frozen-checkpoint-2 screen completed with 1,871 declarations,
1,693 pairs and 536,116 reproduced characters: four added pairs, none at 90% or higher.
Its only added cross-file pair is the five-field `Cfg.ext`/public-map-state-reading idiom in
`sph_rewinds_run`, 82% against `Cfg.mapState_mapState`. The framed endpoint also changes input
and radius head, so it does not restate that public pure relabeling lemma. The other three
pairs are between this file's distinct leaves/bank selections. Full dispositions are in
`screen-cp2-classification.txt`. For completed screens, **new copies: none**.

The frozen-checkpoint-3 screen completed: 1,885 declarations, 1,697 pairs and 538,487
reproduced characters. Its eight added pairs are all below 90%; full dispositions are in
`screen-cp3-classification.txt`. The second cross-file pair is `sph_verdict_run` against the
same public configuration-field idiom (84%), not a reproof of mapState composition. 

The first frozen-final screen, at `bf4d026a7bea613fa9649bc8fe9ca05dbe6632d1`, found
12 new pairs, all below 90%, with 1,893 declarations, 1,701 pairs and 539,440 reproduced
characters. Inspection identified two pure `mapState` composition calculations inside
`sph_valid_machine`. They now directly cite the public `Cfg.mapState_mapState`, removing
13 lines. This is a re-derivation repaired by citation, not merely an idiom disposition.
Only the unpublished checkpoint-8 commit was amended; its refreshed archive supersedes its
first version. All raw first-screen evidence is retained as history. The final screen and
sweep below concern the amended commit.

The amended commit's final screen completes with 1,893 declarations,
1,701 pairs and 539,326 reproduced characters. There are 12 new pairs
and no removed baseline pairs. It ran under `nice -n 10` in 2,789.130 seconds
(peak RSS 486,544 KiB), with the unmodified pinned v3 script. Each new pair is
classified below; the complete raw outputs and `screen-final-classification.txt` are included.

| Target in `Hierarchy.lean` | Source | Match | Disposition |
|---|---|---:|---|
| `sph_verdict_run` | `InputRewind.lean::Cfg.mapState_mapState` | 339/402 (84%) | idiom: Public field readings establish a branch precondition using its live-state hypothesis and emitted endpoints with changed state/output; this is not the generic composition equation. |
| `sph_right_run` | `Hierarchy.lean::sph_emit_run` | 490/588 (83%) | same-file leaf idiom: The two explicitly permitted one-step leaves have different effects and share public action-field readings. |
| `sph_rewinds_run` | `InputRewind.lean::Cfg.mapState_mapState` | 330/402 (82%) | idiom: Public field readings for a framed endpoint that changes input position and the radius head; not pure state-map composition. |
| `sphWitnessSel` | `Hierarchy.lean::sphInitSel` | 70/88 (80%) | same-file arithmetic idiom: Distinct bank selections share elementary embedding-injectivity arithmetic. |
| `sph_record_suffix` | `InputRewind.lean::Cfg.mapState_mapState` | 293/402 (73%) | idiom: Restore the original live entry configuration using its state hypothesis and unchanged physical fields; the conclusion is not the generic composition equation. |
| `sph_valid_machine` | `Hierarchy.lean::sph_witness_cap` | 69/111 (62%) | same-file arithmetic idiom: This excludes the entire initializer/runner bank from the witness bank; sph_witness_cap is already cited for the distinct claim excluding radius tape one. |
| `sph_runner_run` | `Hierarchy.lean::sph_initial_record` | 1059/1728 (61%) | same-file R1 consumer idiom: Distinct published clocked-runner and initializer hosts, both embedded through R1; shared field transport already factors through sph_select_fields. |
| `sph_valid_machine` | `InputRewind.lean::Cfg.mapState_mapState` | 245/402 (61%) | idiom; earlier pure re-derivations repaired: The remaining match is the concrete initial-configuration comparison through capture, lift, blank-frame and initialization fields. Both pure composition calculations now cite Cfg.mapState_mapState directly. |
| `sph_runner_run` | `Hierarchy.lean::sph_test_run` | 836/1424 (59%) | same-file R1 consumer idiom: Distinct published clocked-runner and Boolean record-test hosts, with shared R1 field transport through sph_select_fields. |
| `sph_validated_machine` | `InputRewind.lean::Cfg.mapState_mapState` | 232/402 (58%) | idiom: Concrete initialization and branch-precondition identities through Cfg.init and mapState field readings. |
| `sph_seam_avoids` | `Hierarchy.lean::sph_seam_heads` | 137/241 (57%) | same-file public-trajectory idiom: The same public seam case split supports different conclusions: exit-state avoidance and a physical head envelope. |
| `sph_emit_run` | `Hierarchy.lean::sph_right_run` | 490/915 (54%) | same-file leaf idiom: Reverse direction of the same permitted-leaf comparison. |

**New copies: none.** No new pair rederives a foreign private declaration; no promotion is
required by the text screen. Optional general-consumer promotions are listed below.

Every new private lemma has name and statement-family searches against the exact base and all
four open PR heads observed during this task:

| PR | Read-only fetched head |
|---|---|
| 211 | `f239dafd09f060ec87ca0992103ae8eb48bce31e` |
| 210 | `fff0430c7c9db136e60ed14b069e972c2ea56fc8` |
| 208 | `d01c56a4ed9487fa2c84c7d62470cee2c6bef960` |
| 195 | `40553944417ba519d736985a300e61fbd13eaffc` |


The initial route searches and probes cover `sph_inclusion`, the square, logarithmic domination,
and strictness helper. The mandated route copies are renamed exactly as required. The separate
normalization/window exact? probe fails to find a published replacement. The corollary probe
finds the owned admitted public target, which is not a usable proved external lemma.

For checkpoint 2, nine exact? goals run against the base overlay imports and own definitions
only, deliberately excluding the new lemma proofs: right move, emitter, fold characterization,
validation run, witness-cap disjointness, radius capture, input rewind, paired rewinds and
initial record. All nine fail to find an exact proof. The companion per-lemma git-grep logs
record the named hosts that are cited in the implementation. The diagnostic probe's nonzero
exit is expected and is not an owned-source failure. The nine probes are in `CP2Semantic.lean`.

For checkpoint 3, ten further apply? probes run against the base overlay plus the checked
checkpoint-2 declarations and new machine definitions, excluding all ten checkpoint-3 lemma
proofs. The per-lemma name/statement searches cover all four observed open PR heads. Hosts
found by those searches are cited, rather than copied. The apply? results are recorded in
`CP3Semantic.lean` and its raw diagnostic log. No complete published replacement was found. Generic logical candidates and partial proofs are not replacements. The initial unrestricted exact? and apply? diagnostics were interrupted after failing to return promptly; the final apply? run used Lean's standard 200,000-heartbeat per-declaration search budget and completed in 55.129 seconds. Its expected nonzero exit, partial suggestions and any search-budget failures are retained. This diagnostic does not certify absence of equivalents; the base/open-PR statement searches were also reviewed. No wall-clock timeout was imposed on an owned module check, and no item was stopped.

The two checkpoint-3 goals that reached the search budget, `sph_verdict_run` and
`sph_seam_heads`, were additionally isolated and rerun with `exact?` and a
1,000,000-heartbeat per-declaration budget in `FinalSemanticRetry.lean`, again excluding their
proofs and all other checkpoint-3 lemma proofs. Both again reached the heartbeat budget (159.306 seconds total), so this diagnostic
still does not certify absence of a replacement. A final interface-only version applies the
same 71-definition seal immediately before the two goals; both searches also reached the 1,000,000-heartbeat budget (156.367 seconds total). The raw errors remain in `final-semantic-sealed`; no complete published replacement was certified by these diagnostics.

Checkpoint 4 has six further per-lemma searches and exact? probes, using the base overlay
and earlier checkpoint proofs while excluding all six new lemma proofs. All six fail to find an exact published replacement (15.833 seconds total); there are no heartbeat failures. The expected diagnostic exit is nonzero.
The two strengthened earlier lemmas still consume their already searched capture/rewind hosts.
The generic first-halt contract cites `exists_first_halt`; it does not reimplement first-halt
selection. The six searches also cover `Contract.ofSegment`, record/suffix compositions,
validation hosts and the indicator-reading alternative. Raw searches/probes are shipped.

Campaign lint: **0 FAIL, 81 WARN over 111 files**. The sole additional campaign warning is
file length above 1,000 lines. Justification: the brief explicitly imposes no size cap and
restricts ownership to this one file's private region; splitting into another source file would
violate that ownership. The standalone linter reports the same size threshold and the baseline
missing Main definitions heading. No new proof-sketch or long-line finding remains.

## Per-private semantic duplication ledger

Each search covers the exact base and the four observed open PR heads listed above, by name
and statement family. Paths in this table are under `evidence/logs/`; diagnostic probe sources
are under `evidence/probes/`. Expected failed-search errors are not source-check failures.
The twelve remaining private declarations are definitions of permitted leaves, bank selections
or compositions of named hosts; their roles are listed in the complete declaration table.

| Private lemma | Name/statement search | Search tactic and result | Disposition |
|---|---|---|---|
| `sph_inclusion` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_code_window` | `semantic-sph_code_window.log` | `cp5-dup`: exact? found no replacement | Consumer of normalization, coding, universal and window hosts |
| `sph_sq_le_two_pow` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_logSpace_dom` | `semantic-search-initial.log` | `baseline-dup`: exact? found no replacement | Required renamed route-probe copy; public supporting lemmas cited |
| `sph_logspace_ssubset` | `semantic-search-initial.log` | `cp7-dup`: finds the admitted public target, unusable as an external proved replacement | Required renamed route-probe copy, with explicit hierarchy hypothesis |
| `sph_right_run` | `semantic-sph_right_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_emit_run` | `semantic-sph_emit_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_fold_valid` | `semantic-sph_fold_valid.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_validation_run` | `semantic-sph_validation_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_witness_cap` | `semantic-sph_witness_cap.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_radius_run` | `semantic-sph_radius_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_input_rewind_run` | `semantic-sph_input_rewind_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_seam_heads` | `semantic-sph_seam_heads.log` | `cp3-semantic-bounded`: apply? search reached its 200,000-heartbeat budget | Public-host composition/reading; no complete replacement certified by this diagnostic; name/statement search reviewed |
| `sph_rewinds_run` | `semantic-sph_rewinds_run.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_select_fields` | `semantic-sph_select_fields.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_initial_record` | `semantic-sph_initial_record.log` | `cp2-dup`: exact? found no replacement | Distinct framed consumer of the named host, or permitted leaf |
| `sph_runner_run` | `semantic-sph_runner_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_test_run` | `semantic-sph_test_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_verdict_run` | `semantic-sph_verdict_run.log` | `cp3-semantic-bounded`: apply? search reached its 200,000-heartbeat budget | Public-host composition/reading; no complete replacement certified by this diagnostic; name/statement search reviewed |
| `sph_summary` | `semantic-sph_summary.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_seam_avoids` | `semantic-sph_seam_avoids.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_written_record` | `semantic-sph_written_record.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_runner_tail_run` | `semantic-sph_runner_tail_run.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_suffix` | `semantic-sph_suffix.log` | `cp3-semantic-bounded`: apply? found no complete replacement | Public-host composition/reading; only partial generic logical candidates |
| `sph_record_suffix` | `semantic-sph_record_suffix.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_record_size` | `semantic-sph_record_size.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_valid_machine` | `semantic-sph_valid_machine.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_halt_contract` | `semantic-sph_halt_contract.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_validated_machine` | `semantic-sph_validated_machine.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_diagonal_language` | `semantic-sph_diagonal_language.log` | `cp4-seal-final`: exact? found no replacement | Public-host composition/space packaging; no search-budget error |
| `sph_linear_ne_NP_of_padding` | `semantic-sph_linear_ne_NP_of_padding.log` | `cp8-semantic-final`: exact? found no replacement | Conditional consequence of the exact missing padding interface |

## Escalation E-PAD — exact padded-language space decider

The only unresolved target is `SPACE_linear_ne_NP`. No hierarchy obstruction remains.
The missing public interface, in namespace `Complexity` with `open Turing`, is:

```lean
∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
  ({y | ∃ x ∈ L,
    y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
      SPACE (fun n => n + 1)
```

This is a scoped API gap, not a claim that the statement is false or mathematically
unprovable. It must validate the exact paired syntax, all-true pad and its quadratic length
on **every** input, then run the original decider on the first component, with a linear
space bound measured in the padded input's length. Malformed or short-pad inputs must reject
without first allocating the potentially larger quadratic workspace.

The brief explicitly permits this named escalation at the last checkpoint. Name and
statement-family searches against the exact base and all four observed open PR heads found
no proved public replacement. The two exact? goals (the conditional corollary and this
missing interface) found none; raw diagnostic output is supplied. The search excludes the
admitted public target from the probe environment. The final diagnostic takes 14.326 seconds and has exactly two expected failed-search errors, with no heartbeat failures. Its initial version had a doc-comment/command parse error; that draft is retained and the corrected probe was rerun.

The published `FinTM.exists_inputCallTM` at `computesFunInTime_pairFst` supplies first-component
extraction/installation. Its time bound can be charged to space by the published general
space-from-time inequality. `vhostEmitTM_runFrom` and `vhostEmitTM_spaceUsed_le` supply a
buffered-input simulation with the original space plus buffer length and two. These are
pieces of a consumer assembly, not the exact all-input pad validator or its final decider
contract. The private padding implementation in `ClassNP/Nondeterminism` proves different
time/NP statements and cannot be cited or copied under the ownership and host rules.

Everything downstream of that interface is proved in `sph_linear_ne_NP_of_padding`:
the prescribed polynomial-time padding map, its exact preimage by `pairFstD_pairEncode`,
NP closure by `preimage_mem_NP`, and the contradiction with the linear/quadratic instance
of the hierarchy (domination threshold `A + 1`). The helper takes the hierarchy statement
and missing interface as explicit hypotheses; its axiom print has no `sorryAx`.

No unproved helper is introduced, and the last public body remains literally `sorry`.
Potential promotions of the checked general consumers are `sph_select_fields`, the seam
head/avoidance consumers, and `sph_written_record`; these are public-reading consequences,
not copies of foreign private implementations. Drafts are continuation material; the
committed source and patch series are the landed code.

Proposed implementation paragraphs for the maintainer (not inserted into the frozen target docstrings):

- `space_hierarchy`: **Implementation.** Absorb the finite exceptional prefix for inclusion.
  For strictness, compute the radius under `embedSilentRetTM`, rewind the radius and input,
  initialize the fixed self-universal machine's record, and use the configuration-count runner
  with `summaryTag`. The clock belongs to the runner. Test a halted endpoint and emit the
  opposite verdict, with foreign inputs rejected before the radius computation. Normalize a
  putative smaller-space decider through the published space-preserving normal form and coding
  clauses, fix its per-code universal constant, then pad only the payload.
- `LOGSPACE_ssubset_PSPACE`: **Implementation.** Apply the space hierarchy to `logSpace` and
  `n + 1`, using the integer-logarithm domination lemma, and transport strictness through the
  published linear-space inclusion into `PSPACE`.
- `SPACE_linear_ne_NP`: **Implementation.** Use the polynomial-time quadratic-padding map and
  `preimage_mem_NP`. A linear-space decider for the precisely padded language would turn an
  assumed equality of linear space and `NP` into the reverse of the linear/quadratic hierarchy.
  If that padded decider cannot be assembled from the named hosts, retain the admission and
  escalate its exact missing statement.

The supplied base sorry inventory is included verbatim in `evidence/logs/base-sorries.txt`.
Only the two completed target warnings disappear: the 220-module closure has 24 remaining
admissions versus 26 at baseline, all unchanged except those removals. The final tail has the two expected Hierarchy sorry warnings and two unchanged baseline
style warnings in `Randomized/Classes.lean` (unnecessary `<;>` at line 499 and unused simp
argument `hp` at line 1215). These also occur in the bootstrap and first final sweep; the
earlier summary recorded only admission warnings. The affected source is byte-identical
to the pinned base. Every other final-tail module has exactly its baseline warning list. Use the committed source and patches, not unchecked drafts.


Current checkpoint-8 validation is `final-v2-edit`: the corrected owned module and facade,
the elaborated walk, all 43-private/three-public axiom prints, and the complete 71-definition
seal all pass. `final-v2-import` passes all 321 checks (12.247 seconds; peak RSS 2,080,164 KiB).
The unchanged 71-definition seal has the same 75 effective controls as `cp8-final`, all passing
unsealed and failing sealed. The inspection has 443 sites, including the `simp_all` site. The final lint logs are
`final-v2-campaign-lint.txt` (0 FAIL, 81 WARN) and `final-v2-style-lint.txt` (only the baseline
heading finding and permitted file-length finding).

## Current evidence index

All paths below are inside this ZIP. The sources in `evidence/probes/final_v2/` match the
final source exactly, apart from the seal's inserted attributes and the axiom-print suffix;
`final-proof-snapshot-integrity.json` records that comparison and the unchanged control set.
The earlier `cp*`, `final-sweep/` and first-screen records are preserved diagnostic history.

| Verification | Current evidence |
|---|---|
| Preflight, official toolchain, manifest pins, narrowed cache, base identity | Original environment logs and runtime scripts under `evidence/logs/` and `evidence/runtime/` |
| Fresh 220-module bootstrap, each module's wall time and peak RSS | `evidence/logs/bootstrap/`, including `summary.jsonl` |
| Corrected source and facade | `evidence/logs/final-v2-edit/001-TCSlib_Complexity_SpaceComplexity_Hierarchy.log` and `002-TCSlib_Complexity_SpaceComplexity.log` |
| Full 71-definition seal | `evidence/probes/final_v2/Seal.lean`; `evidence/logs/final-v2-edit/005-FillProbes_final_v2_Seal.log` |
| All 75 effective controls, both flavors | `evidence/probes/cp8/HSealControl_unsealed.lean` and `HSealControl_sealed.lean`; corresponding `002` and `003` raw logs in `evidence/logs/cp8-final/` |
| All 43-private/three-target axiom prints | `evidence/logs/final-v2-edit/004-FillProbes_final_v2_Axioms.log`; `evidence/logs/final-axiom-accounting.json` |
| Complete citation inventory and extended import probe | `evidence/citations/final.md`, `evidence/citations/final.json`, `evidence/probes/FinalImportProbe.lean`, `evidence/logs/final-v2-import/` |
| Explicit rewrite/reduction inspection | `evidence/inspection/final_v2.md`, `evidence/logs/final-rewrite-heads.json` |
| Corrected commit's 52-module final sweep | `evidence/logs/final-sweep-v2/`, `evidence/logs/final-sweep-summary.md`, `evidence/logs/final-sweep-v2-accounting.json` |
| Full before/after text screens | `evidence/logs/screen-before.txt`, `evidence/logs/screen-after-final-v2.txt`, their resource logs, and `evidence/logs/screen-final-classification.txt` |
| Lint | `evidence/logs/final-v2-campaign-lint.txt`, `evidence/logs/final-v2-style-lint.txt` |
| Scope, patches and archive integrity | `evidence/logs/final_v2-source-audit.json`, `evidence/logs/delivery-integrity.json`, `evidence/logs/final-delivery-identity.json`, root `SHA256SUMS` and `bundle-verify.log` |

## Delivery integrity

All eight checkpoint archives pass every entry of their `SHA256SUMS` manifests and ZIP CRC
validation; each source matches its recorded commit. The eight format-patches were applied,
in order, to an isolated Git index at the pinned base. The reconstructed tree exactly equals
`e7b54ea9ddf1cda851f0d31838a4f4b43c8bf5d5`, the final commit's tree. This did not change any branch.
The bundle has only the pinned base as a prerequisite; its verification log is included.
The tracked working tree is clean and the only tracked change against base is Hierarchy.
The final manifest covers every ZIP entry except itself, including the embedded dispatch
manifest. The archive verification checks both that complete coverage and each digest.

| Checkpoint | Commit | ZIP SHA-256 |
|---|---|---|
| cp1 | `fd925fa2ee9de1509a74300ae7ea5202f7461605` | `daf114b1f1438a0d5aee549328a20273fb49623cebacea5f14cb07629370851b` |
| cp5 | `eec4e0a5e9dd3533340250f845369e04b1a07535` | `2dc340326d43bdc5bc8572dc941cbee9f610b109f2c33753eefcf1ab635e4383` |
| cp7 | `a55f653ddd191a33fb5adeda7f9d6dac3ed09567` | `b8d29e843ba76638847a4b06be0f6b89cf8b3948226b8190a003247d416dc9b4` |
| cp2 | `aae09bb9510e75b7760bdd1ac7ce190749c086be` | `69334d4e065d45dfffa377d463cacc871c2a39fbb4eb09db1fcb6d47430174c8` |
| cp3 | `80b00fe9c1c9be8155b48152615b904621cb0706` | `85ff547f1f129c920871b6dc4dcb8ce1570e64532136d48629dafa63cfc262aa` |
| cp4 | `f32dc1709aca0c6c24ca08c9492f5269b4a8ccf8` | `d71fd7bebe12f58a9cb82a2721ef6055c93fea939f0974f1b583c8ce0dbd1fd0` |
| cp6 | `37a041bc4053ca1e6d6b7272eeaeaddab7407839` | `2e16739d2a58c73d81eb2485d8b0ddda57533c5e1993db61f233433f44b06799` |
| cp8 | `30222bbd264a75057ae0779535a32e1a30dd2394` | `6dda89966bf6dc2306c14f3bb6a984d96dd2c27c3aa24a736e805edbfd918dfa` |

Final citation verification: `final-v2-import` checks the 321-name union; all checks pass
(12.247 seconds; peak RSS 2,080,164 KiB).

## ===== campaign/fills/b6/review/hierarchy-REVIEW.md =====

# Pre-gate review: B6's H fill (Codex), commit `30222bbd`

Scope: `deliver/fill-b6-hierarchy-in` at `30222bbd` (base `e6bc1968`), merged into `lean/b6h-landing` at
`14ee2e46` (worktree `wt-h`). The delivery, extracted at `deliveries/h-final/x/`, was read as data.
The brief is `campaign/fills/b6/briefs/b6-fill-hierarchy.md`. No tracked file was modified.

**Verdict: no blocker, no major.** Four minors are in the REPORT and the public text, and none touches
soundness. The two completed targets are proved on the standard axioms; I checked this with my own
sealed elaboration of the delivered source. E-PAD is within the brief's permitted escalation. Its
statement is true as written, precise, and absent from the library and from the open PR branches.

Elaborations used: 3 of 3, run one at a time with `leanelab.sh` against `oleans-lnth`. The olean set
is the base's Lean content; `git diff e6bc1968 14ee2e46 -- TCSlib` shows `Hierarchy.lean` as the only
Lean change. Probe sources and raw outputs are in `wt-hk/rvprobe/hdreview/`:

- `HDSeal.lean`/`.out`: the delivered source with the delivered 71-definition seal and four
  `[-simp]` removals inserted before the first private. A constant walk and the axiom prints are
  appended before `end Complexity`.
- `HDDup.lean`/`.out`: eleven `exact?` duplication goals against the base closure.
- `HDDup2.lean`/`.out`: three goals against the overlay closure.

## Findings

| # | Severity | Where | Finding | Fix |
|---|---|---|---|---|
| 1 | minor | REPORT §"Checkpoints and declarations", row 7 | Row 7 says "Complete public logarithmic-space strictness corollary, admission-free". At checkpoint 7's commit `a55f653d`, committed before checkpoints 2–6, `LOGSPACE_ssubset_PSPACE` still depended on `sorryAx` through `space_hierarchy`'s `sorry`. The agent's own log `evidence/logs/cp7-verify` prints `[propext, sorryAx, Classical.choice, Quot.sound]`. The rule-4 ordering itself is allowed. Only the wording is wrong, and nothing is unsound at the final commit. | Reword row 7: "proved from `space_hierarchy`'s statement; admission-free from checkpoint 6 (`37a041bc`) on". Mention that the commit order is cp1, cp5, cp7, cp2, cp3, cp4, cp6, cp8. |
| 2 | minor | Delivery; REPORT §"Delivery integrity" | The brief asks for one zip per checkpoint, delivered at once. Only `fill-b6-hierarchy.zip` reached `deliveries/h-final/`. The REPORT lists SHA-256s for eight checkpoint archives that the maintainer does not hold. Checkpoint 8 was amended after its first archive (`bf4d026a` became `30222bbd`). The final zip does carry the per-checkpoint evidence (`evidence/{citations,inspection,logs}/cp1…cp8`), the eight-patch series and the bundle. The patch chain checks out: blob `287acce8` → … → `40d62c36` = `30222bbd:Hierarchy.lean`. | Ask Codex for the seven intermediate zips, or record a waiver: the final zip, the patch series and the bundle make them redundant for the gate. |
| 3 | minor | `Hierarchy.lean:2533–2559`, `SPACE_linear_ne_NP`'s docstring | The sketch pads with `List.replicate (\|x\|²) true` and gives the padded length as `m = n² + 2n + 2`. The route, `sph_linear_ne_NP_of_padding` and E-PAD all use the brief's `(\|x\|+1)²` pad (`polyUnary 1 2`), which gives `m = n² + 4n + 3`. Both pads are mathematically valid, but the public sketch and the escalated interface disagree. The sketch also keeps internal phrasing ("a derived obligation from…", "the chapter-2 padding-cluster discipline"). `NP`'s closure is now published as `preimage_mem_NP` and is not cited. | At landing, or when E-PAD lands: state the `(\|x\|+1)²` pad and `m = (n+1)² + 2n + 2`, cite `Complexity.preimage_mem_NP`, and drop the two internal phrases. |
| 4 | minor | REPORT §"Escalation E-PAD", proposed `**Implementation.**` for `SPACE_linear_ne_NP` | The paragraph ends with process text: "If that padded decider cannot be assembled from the named hosts, retain the admission and escalate its exact missing statement." It is not public text, and it omits the pad. | Land it as: "Use the polynomial-time padding map `x ↦ pairEncode x (replicate ((\|x\|+1)²) true)` and `preimage_mem_NP`; a linear-space decider of the padded language turns `SPACE (n+1) = NP` into `SPACE (n²+1) ⊆ SPACE (n+1)`, against the hierarchy at `n + 1` and `n² + 1`." |
| 5 | note | `space_hierarchy`'s docstring (2402–2501); module docstring (60) | This is base text kept under region (d), as the brief prescribes. The sketch still describes a `counterLoopTMVia` clock, `exists_recordStepTM` rounds and a clock width. The normalization is given as `exists_codeTM` plus a re-derived space clause through `relabelState_runFrom_init`. The proof uses the runner's internal clock and `exists_codeTM_spaceUsed`, which rule 5 requires. The module docstring says "`g`'s witness drives the window radius and the clock width". The REPORT's proposed Implementation paragraph corrects the clock but not the relabel sentence. | When landing the Implementation paragraph, also rewrite the "Relabel it… (`Turing.exists_codeTM`, plus the space clause it does not state…)" sentence to cite `exists_codeTM_spaceUsed`, and drop "and the clock width". |
| 6 | note | REPORT §"Escalation E-PAD" | The search for E-PAD did not consider the nearest published host. `Complexity.LogProg.OIS.compile_decides` and `Complexity.mem_LOGSPACE_preimage` (`SpaceComplexity/Logspace/PreimageHost`) run an arbitrary decider `M` on a virtual input `f x`, never written. The space is `M.k(2S+1) + O(log) + bank`, with `S` the space `M` uses on the virtual input. This module is outside H's frozen nine-import closure, so it does not invalidate the escalation, but it bears on the API PR (see the assessment below). | Record it in the E-PAD ticket. |
| 7 | note | `sph_select_fields` (838), `sph_seam_heads` (700), `sph_halt_contract` (2067), `sph_written_record` (1361) | These are general consumer lemmas, not copies. **`sph_select_fields`:** `Cfg.select` has no published field equations; my `exact?` on its state and work-tape conjuncts returns only `exact rfl`, which is definitional and which rule 10 forbids. The private is therefore a genuine API gap, and the REPORT lists it as a promotion candidate. **`sph_seam_heads`:** a seam head-envelope lemma, parallel to the env clause of `Contract.seq`/`Traj.seq`. `exact?` timed out at 400k and 2M heartbeats, matching the agent's result. **`sph_halt_contract`:** builds a `Contract` by structure literal where `Contract.ofSegment` with `exists_first_halt` would also serve. **`sph_written_record`:** mirrors an inline step of `CfgRecord`'s private `recordStep_apply_run`. It is not a declaration copy, and the screen shows no pair against it. | Promote `Cfg.select_{state,inputPos,output,workTapes,workTapePos}` next to `embedEmitCfg_select` in `Build/Embed` at the next shared-file window, and re-point `sph_select_fields`. The others need no action. |
| 8 | note | `sph_linear_ne_NP_of_padding` (2364–2398) | A 35-line private with no consumer in the file. It takes `space_hierarchy`'s statement and E-PAD as hypotheses and is admission-free. It is beyond the escalation's minimum, but it does no harm: once E-PAD lands, the target's body becomes `sph_linear_ne_NP_of_padding space_hierarchy <E-PAD>`. | The maintainer can accept or drop it. Keeping it is reasonable. |
| 9 | note | File size | 2,563 lines, 4 public and 43 private declarations. `style_lint` reports "2564 lines (> 1000, must split)" and campaign lint has one new WARN (81 against the base's 80). The brief's rule 8 waives the size limit. About 2,200 lines are the diagonalizer pipeline (`sph_suffix`, `sph_record_suffix`, `sph_valid_machine`, `sph_validated_machine`), generic in the simulated `FinTM Bool`. | Optional later split or harvest, for example a public diagonalizer row; it is not needed for this gate. |

## Checks that passed

**1. Soundness and freeze**

- **Statements frozen.** The four public statements, `theorem … :` up to `:= by`, are byte-identical
  to the base: `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP`.
- **F6 untouched.** `space_universal`'s docstring and body (4,826 bytes) are byte-identical, and so is
  its module "Main results" entry, which keeps its dated text as the brief requires.
- **Regions.** Every diff hunk is in an allowed region: (a) the imports after line 10; (b) the 2,241
  lines inserted after base line 162; (c) the bodies at base 271 and 285, with `SPACE_linear_ne_NP`'s
  body still `sorry`; (d) the docstrings. There are no `set_option`, `attribute`, `instance`,
  notation or new `open` lines.
- **Imports.** Exactly the base's five plus the overlay's four, in the order the brief gives.
- **Identity.** The delivered source equals the zip's source and the landing worktree's file.
- **Proofs and axioms**, from `HDSeal.out`, my own sealed copy:
  - 0 errors; two `sorry` warnings, at `space_universal` and `SPACE_linear_ne_NP`.
  - `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` print `[propext, Classical.choice, Quot.sound]`.
    `SPACE_linear_ne_NP` adds `sorryAx`.
  - A walk over all 149 constants local to the file (theorems among them) finds `sorryAx` only in
    `space_universal` and `SPACE_linear_ne_NP`, and no non-standard axiom anywhere. All 43 privates
    are admission-free.

**2. Rule 10**

- **Seal coverage, my walk.** The used constants (type and value) of every local declaration,
  auxiliaries included, reference 104 other-file TCSlib definitions:
  - 71 are irreducible under the seal, which is exactly the delivered 71.
  - The other 33 are all `reducible`: structure projections, the abbrev `Cfg.Halted`, and the
    generated `casesOn`/`noConfusion`/`ctorIdx`. These are exempt under `TEMPLATE.md`'s abbreviation
    rule.
  - No semireducible other-file definition is left unsealed. No further definitions sit in the
    statements of the 135 cited TCSlib theorems.
- **Agent's walk.** `evidence/citations/final.md` classifies the same 71 as `def`.
- **`[-simp]`.** All four (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`) are
  removed. No other `@[simp]` definition is among the 71.
- **Controls.** The raw logs show `cp8-final/002` with 75 PASS and 0 FAIL unsealed, and `003` with
  0 PASS and 75 FAIL sealed. The controls are 67 delta `rfl` controls, 2 `Fintype.card` usage
  controls, 2 equation controls (`windowRun`, `NDTM.runWith`) and 4 simp controls. The
  final_v2 seal is identical to cp8's.
- **Rewrite arguments, my scan.** No `rw`/`simp`/`simpa`/`dsimp`/`simp_all`/`norm_num` argument
  names an other-file definition; the only match was the local hypothesis `hi`. There is no
  `unfold` or `delta` anywhere. The 10 `show`/`change` sites reduce only structure-update
  projections, own definitions or core definitions, and all of them pass the seal.
- **Rule 11.** No R3 row, no `_private`, no `capture_run`/`capture_visitedByTapeHead`, no Bool
  seam-space corollary, no `length_bits_succ_le`, no `Contract.liftSymbols`.
  `inputRewindTM_run` is used only on the binary source `inputRewindTM 0` before the lift, which is
  the brief's route. `exists_codeTM_spaceUsed` is used, not `relabelState`. All 43 privates carry
  the `sph_`/`Sph` prefix.

**3. Duplication**

- **Probes.** `exact?` finds no replacement for `sph_seam_avoids`, `sph_written_record`,
  `sph_halt_contract`, `sph_fold_valid`, `sph_sq_le_two_pow`, `sph_inclusion`, `sph_summary`,
  `sph_record_size` or the E-PAD interface. For `sph_seam_heads` the search was inconclusive
  (heartbeat timeout). For `sph_select_fields` the only proof found is `rfl`.
- **Screens.**
  - The before-screen is byte-identical to `b6-fill-hierarchy-screen-base.txt`.
  - The after-screen (`screen-after-final-v2.txt`) has exactly 12 lines on `Hierarchy.lean`, all
    below 90%. The dispositions are sound: 4 are against `Cfg.mapState_mapState`, as an `Cfg.ext`
    field idiom, and 8 are same-file.
  - The first-final screen's two genuine `mapState_mapState` re-derivations were repaired by
    citation.
  - No pair is against another file's private. "New copies: none" holds.

**4. Public text**

- No campaign labels remain in the owned docstrings. The phase, gate, round, finding, design,
  registry and row names the brief lists are all removed. F6's docstring, lines 84–145, is
  untouched by mandate.
- No line exceeds 100 characters, measured in characters.
- Every private lemma over about 20 lines has a literal "Proof sketch", 35 in all.
- The public targets keep their `[AB09]` attributions and sketches.
- The module docstring keeps its `## References` and is free of status text.

**5. REPORT figures and evidence**

- **Counts.** Line count, 43 privates, the 71/75 seal and controls, the 321-check import probe
  (`final-v2-import`, 0 errors), lint 0 FAIL / 81 WARN, the 26-entry base sorry list by name, and the
  12-pair table are all accurate.
- **Patches and bundle.** The bundle requires only `e6bc1968`, and its verification log is
  included.
- **Implementation paragraphs.** They are proposed in the REPORT, not inserted, as the brief requires.

## E-PAD assessment

**Within the brief's terms: yes.** The user's 2026-11-06 ruling lets checkpoint 8 end in a named
escalation for "the padded language's decider". The brief itself lists the pad-length test and the
assembly as unhosted. The body is still `sorry`, preceded by a literal "Proof sketch". The missing
statement is in the REPORT, and nothing else depends on it.

**Stated precisely and true.** For `L ∈ SPACE (n²+1)` with decider space `c·(n²+1)`, the padded word
is `y = pairEncode x (replicate ((n+1)²) true)`. Its length is `|y| = 2n + 2 + (n+1)² = n² + 4n + 3`,
from `length_pairEncode`, so `c·(n²+1) ≤ c·|y|`.

A decider of `L'` works as follows:

1. Check the doubled-code syntax, the `[false, true]` separator, the all-`true` pad and the pad length
   `(n+1)²`, in O(|y|) space (in fact logarithmic).
2. Install `x`, which costs `≤ |y|` cells.
3. Run `L`'s decider in `c·|y|` cells.

The total is `O(|y| + 1)`, so the statement holds for every `L`.

The REPORT rightly stresses validate-first. On a malformed `y`, `|pairFstD y|` can be about `|y|/2`,
and running the decider there would cost about `c·|y|²/4`, which is not linear.

The pad matches `polyTimeComputable_polyUnary 1 2`, and the interface is exactly the hypothesis
`hpad` that the machine-checked `sph_linear_ne_NP_of_padding` consumes. Supplying it closes the
target.

**Absent: confirmed.**

- **`ClassNP/Nondeterminism`'s padding.** The A3 checks and `a3n_pad_eq` are private and
  polynomial-*time* only, with an exponential pad and no space clause.
- **`SpaceComplexity`.** It has no padding lemma (the hits are codec and bank padding). Its only
  closure lemmas are `SPACE.mono` and `mono_const`, with no intersection or preimage closure.
- **Branches.** No padding theorem exists on any `origin/lean/*` branch. The open PRs (#211, #214,
  #215, #216, #210, #195) add none.

**What an API PR would take.** I recommend publishing a more general row than the specific
interface, for example `Complexity.mem_SPACE_pad` in a new `SpaceComplexity/Padding` module. For
`L ∈ SPACE s` and a pad `q n = C·(n+1)^d`, with `s n ≤ a·(q n + 2n + 2)`, the padded language would be
in `SPACE (m + 1)`. E-PAD is then the instance at `C = 1`, `d = 2`. There are two routes:

- **(i) The machine route, from H's hosts.** This is roughly the size of one of H's phases, a few
  hundred lines:
  - A new pad validator: syntax by an `inputFoldTM`-style scan, and the length by a binary counter
    compared against `(n+1)²`. This is the real gap: a leaf or host row with a space clause.
  - `seamCompTM₂` or `Contract.branch` for reject-first.
  - `FinTM.exists_inputCallTM` at `computesFunInTime_pairFst` to install `x`, with its space by
    `spaceUsed_le_mul_succ`.
  - `vhostEmitTM_runFrom` and `vhostEmitTM_spaceUsed_le` to run the decider, for space `S + |y| + 2`.
  - Packaging through `decidesInSpace_iff` and `SPACE.mono_const`.
- **(ii) The preimage route.** Generalize `mem_LOGSPACE_preimage` to a `mem_SPACE_preimage`: from
  `LogProg.OIS.compile_decides`, `f` implicitly logspace computable and `C ∈ SPACE s` with
  `s (|f x|) ≤ a·t (|x|)` and `t ≥ logSpace`, conclude `f⁻¹ C ∈ SPACE t`. Then take
  `f y = if valid y then pairFstD y else w₀`. This needs:
  - logspace bit deciders for that conditional projection, with the pad-length arithmetic from
    `Logspace/Mult`;
  - a small case split for when `w₀ ∈ L` cannot be avoided (`L = univ`, where `L'` is the validity
    language).

  Route (ii) gives a reusable space analogue of `preimage_mem_NP`. Route (i) stays inside H's host
  family. Either way the consumer change in `Hierarchy.lean` is a one-line body plus one import,
  which needs the user's import ruling under rule 6.

## ===== campaign/fills/b6/sweep/README.md =====

# Library re-derivation sweep of `Hierarchy.lean`

Target: `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean` at the landing branch `lean/b6h-landing`
(worktree `wt-h`, head `14ee2e46`, "Merge B6's H fill delivery"). The file has 2,563 lines and
43 private declarations, all `sph_`/`sph…`. All line numbers below are lines of that source. It is
copied here as `Hierarchy.src.lean` (`cmp`-identical to the worktree file and to `git show`).

Method: the G5 sweep's (`agents/g5sweep/README.md`), followed step for step. Copy A runs `exact?`
in place. File B runs generalised `example`s. B2 runs name checks, term checks and `apply?`. Then
one tested replacement copy C.

Nothing tracked was edited, committed or pushed. `git status --short` is empty in `wt-h` and
`wt-hk`. In `/home/user/tcslib` it shows only one untracked file,
`campaign/items/dedup/as1-SCOPE.md`, which this sweep did not create. Scratch Lean files are in `wt-hk/rvprobe/hsweep/`, which is git-excluded
through `rvprobe/`.

Lean was run only as
`bash /home/user/tcslib/devtools/seyoon/leanelab.sh /home/user/tcslib-scratch/wt-hk /home/user/tcslib-scratch/oleans-lnth rvprobe/hsweep/<File>.lean`.
Each command was prefixed by `. /home/user/tcslib-scratch/env.sh`. Elaborations ran one at a time,
and Python only as `python3 -I`. Each log ends with `-- exit=N, T s (snapshot oleans-lnth)`. Every
probe copy, and every replacement copy, replaces the file-level `set_option maxHeartbeats 0` by
`400000`. Every `exact?`/`apply?` also carries `set_option maxHeartbeats 400000 in`. The
unmodified file elaborates under 400000 (`base4.log`), so no proof needs the unbounded setting.

## Result

| class | items | sites |
|---|---|---|
| clear hits | **G1–G9, K1** | 20 |
| borderline (M class) | **M1–M8** | 15 |
| needs an import | none | 0 |
| optional cosmetic | O1–O8 | 8 |

* **Clear hits: G1–G9 and K1 (10 items, 20 sites).** K1 is a field-by-field `Cfg.ext` skeleton
  that re-proves two published TCSlib lemmas.
* **Borderline: M1–M8 (8 items, 15 sites).**
* **Needs an import: none.** Every replacement lemma is in the file's import closure (106 TCSlib
  modules, `closure.txt`). Unlike G5's closure, this one has `smul_eq_mul`, `Fin.sum_const` and
  `Finset.card_fin`.
* **Optional cosmetic: O1–O8.** These are not hits.

`copyC.diff` applies G, K and M together (27 hunks, +41 −80; the file goes from 2,563 to 2,524
lines). **Copy C elaborates with exit 0, and its only messages are the two expected `sorry`
warnings**: `space_universal` at 147:8 (F6's) and `SPACE_linear_ne_NP` at 2521:8. This matches the
unmodified baseline, which has the same two warnings at 147:8 and 2560:8.

Two variants also elaborate with exit 0 and only those two warnings:

* **copy CG** (`copyCG.diff`, 17 hunks, +24 −62): clear hits only, G1–G9 and K1, without the M
  items;
* **copy D** (`copyD.diff`, 34 hunks, +51 −107): copy C plus O1–O8.

All three diffs are against the target path (`a/…`, `b/…`). Each one applies with `patch -p1` to
`git show 14ee2e46:<path>` and reproduces the tested copy byte for byte. `git apply --check` also
passes on `wt-h`. None touches line 16 (`maxHeartbeats 0`). Every hunk keeps its
`have`/`lemma`/`def` statement unchanged, so the hunks are independent. No added line is over 100
characters.

| id | line(s) | declaration: step | inline proof | published lemma (replacement) |
|---|---|---|---|---|
| **G1** | 177–179 | `sph_inclusion`: second `by_cases` branch | `calc … _ = (F+1)*1 := (Nat.mul_one _).symm; _ ≤ (F+1)*g n := Nat.mul_le_mul_left _ (hfloor n)` | `_ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)` (core). Its proof is the same two steps. |
| **G2** | 1027, 1042 | `sph_runner_run`: `hz`, `0 < i.val` | `fun h => hi (Fin.ext h)` (×2) | `Fin.val_ne_zero_iff.mpr hi`. Same class as G5's G5 (`Fin.val_ne_of_ne`). |
| **G3** | 1775–1777, 1790–1792, 1793–1795 | `sph_record_suffix`: `(0 : Fin (KI+KR+m+2)) ≠ 1` (×3) | `intro h; have hh := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_one] at hh; omega` | `Fin.zero_ne_one` |
| **G4** | 1865 | `sph_record_size`: `hk : k ≤ k * g n` | `simpa only [mul_one] using Nat.mul_le_mul_left k hfloor` | `Nat.le_mul_of_pos_right k hfloor` |
| **G5** | 1854, 2048 | `sph_record_size` `hb`, `sph_valid_machine` `hbits`: `m.bits.length ≤ m` | `LogProg.length_bits_le Nat.lt_two_pow_self` (×2) | `length_bits_le_self _` (`Turing.`, `Encoding.lean:290`). See the note below. |
| **G6** | 2332–2333 | `sph_diagonal_language` `hind`: `bit = answer …` from `htest` | `cases hb : bit <;> cases ha : … <;> simp_all only […]` (a 4-way case bash) | `exact Bool.eq_iff_iff.mpr htest.symm` (= `Bool.coe_iff_coe.mp`) |
| **G7** | 621–623 | private `sphEmptySel : Fin 0 ↪ Fin k` | `toFun := Fin.elim0; inj' := fun i => Fin.elim0 i` | `Function.Embedding.ofIsEmpty` (`⟨isEmptyElim, isEmptyElim⟩`). The name is kept, so its 8 uses are untouched. |
| **G8** | 560–589 | `sph_radius_run`: space bound, `∑ j ≤ (KI+KR+M.k+2) * r` | `apply Finset.sum_le_sum` to a constant sum, then `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl` | `apply Finset.sum_le_card_nsmul` (the per-tape body is unchanged), then `rw [Finset.card_fin, smul_eq_mul]`. Same pattern as G5's G4 + K1. |
| **G9** | 863–866 | private `sphInitSel : Fin (KI+2) ↪ Fin (KI+KR+m+2)` | `toFun i := ⟨i.val, _⟩`, injectivity by `Fin.ext ∘ congrArg val` | `Fin.castLEEmb (by omega)`. Mathlib's definition is `toFun := castLE h`, which is `⟨i.val, _⟩`. The name is kept, and `h0`/`h1 := Fin.ext rfl` still hold. |
| **K1** | 1252–1260, 1610–1618, 1668–1676, 1756–1761 | `sph_verdict_run` `hp`; `sph_suffix` `hstart`, `hmaps`; `sph_record_suffix` `hstart` | `apply Cfg.ext` plus five field rewrites through two or three `mapState` layers. The goal is `c.mapState F = c` (or `= c.mapState G`). | `simp only [_, Cfg.mapState_mapState]`, then `exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl`, or `rfl` for `hmaps`. The lemmas are `InputRewind.lean:49` and `CfgFacts.lean:69`. Both proofs are this skeleton verbatim. The file already uses `rw [Cfg.mapState_mapState]; rfl` at 1959 and 1994. |
| M1 | 342, 1180 | `sph_right_run`; `sphEmitContract.cut` | `have : u = 0 := by omega` (from `hu : u < 1`) | `Nat.lt_one_iff.mp hu` |
| M2 | 347, 384 | `sph_right_run`; `sph_emit_run` | `have : u = 0 ∨ u = 1 := by omega` | `Nat.le_one_iff_eq_zero_or_eq_one.mp hu` |
| M3 | 616, 2136 | `sph_radius_run` `hn`; `sph_validated_machine` `hrad` | `(0 : ℤ) ≤ ↑n := by omega` | `Int.natCast_nonneg _` |
| M4 | 462–464 | `sphWitnessSel.inj'` | `omega` from `h' : a + i = a + j` | `exact Nat.add_left_cancel h'` |
| M5 | 168–169, 234–235, 1853, 2049, 2346 | five floors `1 ≤ g n` from `logSpace n ≤ g n` | `rw [logSpace_eq] (at h); omega`, inside `le_trans` at 168/234 | `Nat.one_le_of_lt h`. This is definitional: `logSpace_eq` is `rfl`, so `logSpace n ≤ g n` is `Nat.log 2 n < g n`. No published `1 ≤ logSpace n` lemma exists. |
| M6 | 1349 | `sph_seam_avoids` `obtain` | `⟨u - (t + 1), by omega⟩` | `Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)`. Same class as G5's M3. |
| M7 | 1823–1825 | `sph_record_suffix` `hSB` | `(Nat.mul_le_mul_left _ (by omega)).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))` | `Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)`. Its proof is this `trans`. |
| M8 | 1351–1353 | `sph_seam_avoids`: right segment | `cases hq : … with \| none => … \| some q => …` | `obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad; exact Sum.inr_ne_inl hq`. Two lemmas, as in G5's G8. It is ranked borderline because no single lemma states the fact (B34 ✗). |

**Taking only part of the result.** The maintainer can take the clear hits alone, which means
copy CG's diff. That copy also elaborates cleanly.

**Note on G5.** By the G5 taxonomy, two chained citations that make one lemma are M class. I
counted G5 as clear anyway, for three reasons:

* the lemma is TCSlib-published;
* the module's own `space_universal` docstring cites it (line 141, `Turing.length_bits_le_self`);
* the H review's M2 and the reworked brief bind it among the readings to name.

Demote it to M if strict consistency with G5's M1 is preferred.

**Note on M5.** M5 depends on unfolding `logSpace` definitionally. It is accepted, as copy C
shows, but it relies on a definitional fact. A maintainer who prefers the published equation can
keep the five sites, or write `Nat.one_le_of_lt (logSpace_eq n ▸ h)`.

## Optional (copy D = copy C + these; not hits)

| id | line | change | why optional |
|---|---|---|---|
| O1 | 1268 | `ht : t + 2 = t + 1 + 1 := by omega` → `rfl` | definitional (A20 `exact rfl`) |
| O2 | 2159–2164 | `hstart₁` `Cfg.ext` skeleton → `rfl` | definitional through `Cfg.init`/`Cfg.mapState` (A36 `exact rfl`). The field args of `mapState_eq_of_fields` would not be `rfl` here without unfolding. |
| O3 | 2216–2221 | `hpre` `Cfg.ext` skeleton → `rfl` | same (A39 `exact rfl`) |
| O4 | 538–540 | `hout'`: `List.map_congr_left … RecSym.digitEmb_apply` → `rfl` | definitional (A11 `exact rfl`). `digitEmb_apply` is the published reading, so keep it under the "readings, not unfolding" discipline. |
| O5 | 921 | `(by have := j.isLt; exact this)` → `j.isLt` | cosmetic. The goal is `(ι j).val < KI + 2` by defeq, so A15 `exact?` ✗. |
| O6 | 220–221 | `hx`: residual `omega` after `simp only` → `exact Nat.le_add_left _ _` | residual-goal `omega` (idiom class; A04 found it) |
| O7 | 335–340 | positive endpoint of the right move: `by_cases` over two published moves → `LogProg.moveInputPos_val` + `simp only [Fin.eta]` + `omega` | an alternative route through the published clamp formula, not a re-derivation of one lemma (A07/B11 ✗, `apply?` none) |
| O8 | 1096–1098 | private `sphRecordSel : Fin 1 ↪ Fin (k+1)` → `Fin.castLEEmb (by omega)` | agrees with `toFun _ := 0` only extensionally (`Fin 1` is a singleton). `h0 : ι 0 = 0 := rfl` still holds. |

## Method

1. **Enumeration.** I read the whole file.
   * `all_sites.txt` (from `grep -nE`, 769 lines) lists every `have`/`obtain` (289), private
     declaration (43), `calc` step, anonymous `have :=`, and `rw`/`simp only`/`simpa only`/`omega`/
     `nlinarith` line.
   * For TCSlib facts I computed the import closure (`closure.py` → `closure.txt`, 106 modules)
     and searched it at `14ee2e46` with `git grep`. I searched for:
     * a `1 ≤ logSpace` floor (none; only `logSpace_le_succ`, `_mono`, `_le_size_succ`, `_le_of_le_mul_two_pow`);
     * `length_bits_le_self` (found);
     * every `mapState` declaration (`Cfg.mapState_mapState`, `Cfg.mapState_eq_of_fields`, `_const_eq_mapState_sigma`, `_sigma_state_ne`);
     * `moveInputPos_*` (`LogProg.moveInputPos_val` found);
     * the `PSPACE` inclusions (`space_poly_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE`);
     * the `pairEncode` lemmas;
     * the `SPACE` monotonicity lemmas;
     * the seam, select, emitter, contract, record and window names.
   * The published one-step emitters are `Bool`-only: `Turing.FinTM.emit_run`, `emitCfg`, `rightCfg_run`.
   * `framedContract` exits at `some done`, not at the halt, so it does not cover `sphEmitContract`.
   * No `Cfg.select_*` field lemmas exist, and no absolute-envelope seam lemma exists (only the
     visited-set `seamCompTM_visitedByTapeHead_ofCfg`). So the private seam, select, emit, halt,
     record and summary helpers are not library facts.
2. **In-context probe (copy A).** `mk_copyA.py` puts `exact?` in place of each of 47 candidates
   (`copyA_tags.tsv`). The run finished in 152 s (`copyA.log`).
   * The lean CLI prints a successful `exact?`'s `Try this` info without a position. I matched
     those infos to probes in message order.
   * Two probes hit the 400000 cap: A27 and A32a. Each timeout aborts its whole declaration, so
     three later probes in the same declarations gave no message (A28, A33, A34).
   * The timeout in `sph_valid_machine` also produces the kernel "unknown constant" at 2225. That
     is a cascade, not a finding.
   * I reran A28, A33 and A34 alone (`HA2.lean`, `copyA2.log`, 151 s).
3. **Generalised probe (file B).** `HB.lean` has 46 standalone `example`s under the file's nine
   imports (`copyB.log`, 86 s, `copyB_tags.tsv`).
4. **Name checks, term checks, `apply?` (file B2).** `HB2.lean` (`copyB2.log`, 72 s, exit 0; 0.35 MB
   because of the `apply?` listings) contains:
   * 31 `#check`s, all resolved;
   * 20 term checks of the proposed replacements, all accepted;
   * `apply?` on the six open statements. None of them gives a closing suggestion: the square
     below `2^L`, the `|a| ≤ |a - b| + |b|` triangle step, the preimage form, the `foldl`/`all`
     fold, the right-move endpoint, and the `logSpace` domination.
5. **Judgement.** I used the G5 rule.
   * A **hit** is a site whose inline proof re-establishes one published lemma, where the lemma
     states the fact or a direct specialisation, and its arguments are hypotheses or at most one
     further lemma.
   * The **M class** covers an `omega` witness, or two chained citations, that make exactly one
     published lemma.
   * An **idiom** is a site that already cites the lemma and only adapts its shape, or a decision
     procedure closing a residual goal.
   * **Not a library fact** means no lemma states it.
6. **Replacement test.** `mk_copyC.py` applies the replacements. Each old text must occur the
   stated number of times, and added lines over 100 characters are flagged (none). The modes are:
   * default → copy C;
   * `--no-M` → copy CG;
   * `--optional` → copy D;
   * `--heartbeats` → the probe-copy option, used for the elaborated copies.

## Candidate table

A = copy A (in context), B = file B (generalised), B2 = name/term checks. ✓ = closed by the lemma
named; ✗ = `exact?` could not close; "cap" = hit the 400000 heartbeat cap.

| line | declaration | step | candidate lemma | how found | verdict |
|---|---|---|---|---|---|
| 167–175 | `sph_inclusion` | the whole statement | – | B08 ✗ (also the pre-ship `HDupProbe`) | not a library fact |
| **168–169** | `sph_inclusion` | `hfloor : ∀ n, 1 ≤ g n` | `Nat.one_le_of_lt` | A01 ✗ (the `∀` binder); A41/B06 ✓ on the pointwise form | **M5** |
| 174 | `sph_inclusion` | `simpa using this` (`1 * f n ≤ g n`) | – | A02 ✗, B43 ✗ | idiom (`one_mul`) |
| 175 | `sph_inclusion` | `Nat.le_mul_of_pos_left _ (Nat.succ_pos _)` | – | – | citation |
| **177–179** | `sph_inclusion` | calc steps 2–3 | `Nat.le_mul_of_pos_right` | **A03 ✓**; B42 ✗ on the whole branch (the `omega` side) | **hit G1** |
| 207–250 | `sph_code_window` | normal form, coding, simulation, window | `exists_codeTM_spaceUsed`, `decode_encode`, … | reading | citations (the review's M4 route) |
| 219–221 | `sph_code_window` | `hx`, residual goal | `Nat.le_add_left` | A04 ✓ (residual); B46 ✗ (whole) | idiom; **O6** |
| **234–235** | `sph_code_window` | `hfloor` for `f` | `Nat.one_le_of_lt` | as 168 | **M5** |
| 236–241 | `sph_code_window` | `hsmall` | – | – | idiom (`calc` + `ring`) |
| 255–261 | `sph_sq_le_two_pow` | `4 ≤ L → L * L ≤ 2 ^ L` | – | A05 ✗, B01/B02 ✗, B2 `apply?` none | not a library fact |
| 267–278 | `sph_logSpace_dom` | `A * logSpace n ≤ n + 1` eventually | – | B03 ✗, B2 `apply?` none | not a library fact |
| 288–290 | `sph_logspace_ssubset` | `hlin : SPACE (n+1) ⊆ PSPACE` | – | A06 ✗, B04 ✗; B2 T13 `SPACE_succ_pow_subset_PSPACE 1` (same length) | citation (`space_poly_subset_PSPACE 1` + `pow_one`) |
| 303–333 | `sphRightTM`, `sph_right_run` | one-step leaf, field reading | – | grep: the published leaves are `Bool`-only | not a library fact |
| 335–340 | `sph_right_run` | `1 ≤ (moveInputPos p .pos).val` | `LogProg.moveInputPos_val` | A07 ✗, B11 ✗, `apply?` none; B2 T07 ✓ (+ `omega`) | alternative route; **O7** |
| **342** | `sph_right_run` | `u = 0` | `Nat.lt_one_iff` | **A08a ✓**, B09 ✓ | **M1** |
| 345 | `sph_right_run` | `decide` | – | – | idiom |
| **347** | `sph_right_run` | `u = 0 ∨ u = 1` | `Nat.le_one_iff_eq_zero_or_eq_one` | **A09a ✓**, B10 ✓ | **M2** |
| 354–381 | `sphEmitTM`, `sph_emit_run` | emitter leaf | – | grep (no non-`Bool` emitter) | not a library fact |
| **384** | `sph_emit_run` | `u = 0 ∨ u = 1` | as 347 | **A09b ✓** | **M2** |
| 389–429 | `sphDigit`, `sph_fold_valid` | the fold accepts exactly digit images | – | B40 ✗, B45 ✗, B2 `apply?` none | not a library fact |
| 412, 426 | `sph_fold_valid` | `Bool.and_eq_true_iff`, `List.cons.inj` | – | – | citations |
| 437–453 | `sph_validation_run` | wraps `inputFoldTM_run_ofCfg` | – | – | citation |
| 457–461 | `sphWitnessSel` | `⟨KI+KR+2+i, _⟩` | `Fin.natAddEmb` + a cast | reading | no hit (needs a cast; 471/1990 unfold the def) |
| **462–464** | `sphWitnessSel.inj'` | `omega` from `a + i = a + j` | `Nat.add_left_cancel` | **A10 ✓**, B12 ✓ | **M4** |
| 467–472 | `sph_witness_cap` | – | – | – | TCSlib |
| 516–531 | `sph_radius_run` | `hs`, `ho`, `hc`, `hh`, `hl` | – | – | citations |
| 535–540 | `sph_radius_run` | `hout'` map congruence | `rfl` | A11 `rfl`; B36 `rfl` | definitional; **O4** |
| 555, 594 | `sph_radius_run` | `lt_or_eq_of_le` | – | – | citation |
| **560–589** | `sph_radius_run` | per-tape sum ≤ card · r | `Finset.sum_le_card_nsmul`, `Finset.card_fin`, `smul_eq_mul` | A12 ✗ (constant step); B13/B14 ✗; **B38 ✓**; B2 T03/T04 ✓ | **hit G8** |
| 577, 583, 586, 604, 614, 617 | `sph_radius_run` | residual `omega`/`push_cast` | – | – | idiom |
| **616** | `sph_radius_run` | `hn : (0:ℤ) ≤ ↑n` | `Int.natCast_nonneg` | **A13 ✓**, B15 ✓ | **M3** |
| **621–623** | `sphEmptySel` | `Fin 0 ↪ Fin k` | `Function.Embedding.ofIsEmpty` | **B28 ✓** (A n/a: a `def`) | **hit G7** |
| 631–683 | `sph_input_rewind_run` | R1 reconstruction | – | – | citations (`embedEmitCfg_eq`, `inputRewindTM_run`, …) |
| 641, 646, 653, 654 / 670, 672, 673 | `sph_input_rewind_run` | `simpa [length_map]`, `Fin.ext rfl`, `List.append_nil`, `Fin.elim0` | – | – | idiom / citation |
| 700–717 | `sph_seam_heads` | absolute envelope through a seam | – | grep (visited-set versions only) | not a library fact |
| 715 | `sph_seam_heads` | `∃ w ≤ v, u = t+1+w` | – | A14 ✗, B19 ✗ | not a library fact (bounded witness) |
| 725–831 | `sph_rewinds_run` | seams and rewinds | – | – | citations |
| 783–801 | `sph_rewinds_run` | `hend` (`Cfg.ext` on `d₃.mapState`, nontrivial fields) | – | – | idiom (not the K1 shape) |
| 811, 817, 830 | `sph_rewinds_run` | `rw [_, sub_self, abs_zero]; omega` | – | – | idiom (residual `0 ≤ ↑n`) |
| 839–860 | `sph_select_fields` | `Cfg.select` field readings | – | grep (no `Cfg.select_*`) | not a library fact |
| **863–866** | `sphInitSel` | `⟨i.val, _⟩` embedding | `Fin.castLEEmb` | reading; Mathlib source; copy C ✓ | **hit G9** |
| 907–908, 1132 | `sph_initial_record`, `sph_test_run` | `h0`/`h1` | – | – | definitional |
| 921 | `sph_initial_record` | `(by have := j.isLt; exact this)` | `j.isLt` | A15 ✗ (the goal is `(ι j).val < _`) | cosmetic; **O5** |
| 938, 1064, 1157 | three runners | `simp only [sub_self, abs_zero, Nat.cast_nonneg]` | – | – | idiom |
| 948, 1080 | `sph_initial_record`, `sph_runner_run` | `hz` via `ι.injective.eq_iff` | – | – | citation |
| 963–972 | `sphRunnerSel` | piecewise embedding | – | – | not a library fact |
| **1027** | `sph_runner_run` | `hz : i.val ≠ 0` | `Fin.val_ne_zero_iff` | **A16 ✓**, B16 ✓ | **hit G2** |
| **1042** | `sph_runner_run` | `0 < i.val` (inner lambda) | `Fin.val_ne_zero_iff` | A17 ✗ (whole), B17 ✗; B2 T06 ✓ (also `Fin.pos_iff_ne_zero.mpr hi`) | **hit G2** |
| 1096–1098 | `sphRecordSel` | `Fin 1 ↪ Fin (k+1)`, `toFun _ := 0` | `Fin.castLEEmb` | reading; copy D ✓ | extensional only; **O8** |
| **1180** | `sphEmitContract.cut` | `u = 0` | `Nat.lt_one_iff` | **A08b ✓** | **M1** |
| 1187 | `sphEmitContract.env` | `Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩` | (`Finset.left_mem_Icc.mpr le_rfl`) | A18 ✗, B35 ✗; B2 T09 (same length) | idiom (published `framedContract` uses the same) |
| 1223–1243, 1264 | `sph_verdict_run` | contract fields, `ite_self` | – | – | citations |
| **1252–1260** | `sph_verdict_run` | `hp` `Cfg.ext` skeleton | `Cfg.mapState_mapState`, `Cfg.mapState_eq_of_fields` | A19 ✗; **B32/B44 ✓** | **hit K1** |
| 1268 | `sph_verdict_run` | `ht : t+2 = t+1+1` | `rfl` | A20 `rfl`; B37 `rfl` | definitional; **O1** |
| 1275–1296 | `sph_verdict_run` | `Cfg.ext` on a record update | – | – | idiom (not the K1 shape) |
| 1303, 2231 | two envelopes | `min_eq_left`/`max_eq_left` | – | – | idiom |
| 1313–1324 | `sph_summary` | stop-uniqueness reading | – | – | citations |
| 1322, 1711, 1467, 1499 | various | `WindowExit.noConfusion` | – | – | idiom |
| 1344, 1453, 1462, 1478 | various | `Option.map_injective Sum.inl_injective` | – | – | citation |
| **1349** | `sph_seam_avoids` | `∃ w, u = t + 1 + w` | `Nat.exists_eq_add_of_le` | A21 ✗, B18 ✗; **B2 T05 ✓** | **M6** |
| **1351–1353** | `sph_seam_avoids` | right-segment state is not left | `Option.map_eq_some_iff`, `Sum.inr_ne_inl` | A22 ✗, B34 ✗; **B2 T08 ✓** | **M8** |
| 1361–1390 | `sph_written_record` | layout boundary argument | – | – | not a library fact (`recordAt_iff` cited); 1385 `omega` split idiom |
| 1412–1551 | `sph_runner_tail_run` | three-exit seams | – | – | citations |
| 1583–1608, 1619–1663 | `sph_suffix` | runner, test, record readings | – | – | citations |
| **1610–1618** | `sph_suffix` | `hstart` `Cfg.ext` skeleton | as K1 | A23 ✗; B32 ✓ | **hit K1** |
| 1625–1626, 1821–1822 | `sph_suffix`, `sph_record_suffix` | `hRB`, `hTB`, `hIB` | – | – | citations |
| **1668–1676** | `sph_suffix` | `hmaps` `Cfg.ext` skeleton | `Cfg.mapState_mapState` + `rfl` | A24 ✗; in-file precedent 1959/1994 | **hit K1** |
| 1683–1686 | `sph_suffix` | `decide_eq_decide` | – | – | citation |
| **1756–1761** | `sph_record_suffix` | `hstart` `Cfg.ext` skeleton | as K1 | A25 ✗; B32 ✓ | **hit K1** |
| **1775–1777, 1790–1795** | `sph_record_suffix` | `(0 : Fin _) ≠ 1` ×3 | `Fin.zero_ne_one` | **A26a–c ✓**, B20 ✓ | **hit G3** |
| 1781, 1815 | `sph_record_suffix` | `j ≠ 1` from a bound | – | – | idiom |
| 1813 | `sph_record_suffix` | `hj0 : j ≠ 0` from `KI + 2 ≤ j.val` | – | A27 cap, B41 ✗ | not a library fact |
| **1823–1825** | `sph_record_suffix` | `hSB` two-step `trans` | `Nat.mul_le_mul` | A28 ✗ (`B` is a `let`, A2); **B29 ✓** | **M7** |
| **1853** | `sph_record_size` | `hfloor` | `Nat.one_le_of_lt` | B06 ✓ | **M5** |
| **1854** | `sph_record_size` | `hb : (g n).bits.length ≤ g n` | `length_bits_le_self` | **A29 ✓**, B22 ✓ | **hit G5** |
| 1855–1863 | `sph_record_size` | `posWidth n ≤ 2 * g n` | – | B30 ✗ | not a library fact |
| 1857–1859 | `sph_record_size` | `hpow : n+1 < 2^(log n + 2)` | – | A30 ✗, B31 ✗ | idiom (two citations, no single lemma) |
| **1865** | `sph_record_size` | `hk : k ≤ k * g n` | `Nat.le_mul_of_pos_right` | **A31 ✓**, B21 ✓ | **hit G4** |
| 1866, 2052, 2398 | three arithmetic closes | `nlinarith` | – | – | idiom |
| 1913–1947 | `sph_valid_machine` | `hstart` (`embedSilentCfg` readings) | – | – | idiom |
| 1957–1960, 1993–1995 | `sph_valid_machine` | `hwi`, `hai` | – | – | already cite `Cfg.mapState_mapState` |
| 2014–2020, 2025–2030 | `sph_valid_machine` | `\|a\| ≤ \|a - b\| + \|b\|` via `abs_sub_le` | – | A32a cap, A33 ✗ (A2), B23 ✗, B2 `apply?` none | idiom |
| **2048** | `sph_valid_machine` | `hbits` | `length_bits_le_self` | **A34 ✓** (A2) | **hit G5** |
| **2049** | `sph_valid_machine` | `hfloor` | `Nat.one_le_of_lt` | B06 ✓ | **M5** |
| 2067–2092 | `sph_halt_contract` | first-halt contract | – | grep | not a library fact |
| **2136** | `sph_validated_machine` | `hrad : (0:ℤ) ≤ ↑radius` | `Int.natCast_nonneg` | **A35 ✓** | **M3** |
| 2159–2164 | `sph_validated_machine` | `hstart₁` `Cfg.ext` skeleton | `rfl` | A36 `rfl`; B33 `rfl` (`Cfg.init`) | definitional; **O2** |
| 2184 | `sph_validated_machine` | `heq` from mapped words | – | A37 ✗, B39 ✗ | citation (`List.map_injective_iff`) |
| 2200–2201 | `sph_validated_machine` | `ScanPhase.done true ≠ .done false` | – | A38 `not_eq_of_beq_eq_false rfl` | idiom |
| 2216–2221 | `sph_validated_machine` | `hpre` `Cfg.ext` skeleton | `rfl` | A39 `rfl` | definitional; **O3** |
| 2304–2329 | `sph_diagonal_language` | leaf and acceptance readings | – | – | citations |
| **2332–2333** | `sph_diagonal_language` | `hind` 4-way case bash | `Bool.eq_iff_iff` / `Bool.coe_iff_coe` | **A40 ✓**, B24/B25 ✓ | **hit G6** |
| **2346** | `sph_diagonal_language` | `hn : 1 ≤ g n` | `Nat.one_le_of_lt` | **A41 ✓** | **M5** |
| 2347–2350 | `sph_diagonal_language` | `hb` `calc` | – | – | idiom (`ring`) |
| 2381–2391 | `sph_linear_ne_NP_of_padding` | `hpull : p ⁻¹' L' = L` | (`Set.preimage_image_eq`) | A43 ✗, B27 ✗, B2 `apply?` none | no hit (`L'` is `{y \| ∃ x ∈ L, y = p x}`, not `p '' L`) |
| 2387–2388 | `sph_linear_ne_NP_of_padding` | `he : x = y` | – | A42 ✗, B26 ✗; B2 T11 via `pairEncode_injective` (not shorter) | citation (`pairFstD_pairEncode`) |
| 2515–2517 | `space_hierarchy` | final `simp only` | – | – | idiom |

**Repetition within the file** (out of scope; not library re-derivations):

* the R1 `hrun` reconstruction (`embedEmitTM_runFrom` + `embedEmitCfg_select`, 4 copies);
* the selected-envelope block with `simp only [sub_self, abs_zero, Nat.cast_nonneg]` (3 copies);
* the `RecordAt` transport through `mapState` (`recordAt_iff` + `mapState_workTapes`/`_workTapePos`,
  5 copies);
* the logarithmic floor (5 copies, M5);
* the `(0 : Fin _) ≠ 1` proof (3 copies, G3).

## Elaboration outputs

| file | content | result |
|---|---|---|
| `base.log` | `HBase.lean`, unmodified copy (`cmp`-identical) | exit 0; `sorry` at 147:8 and 2560:8 only; 7 s |
| `base4.log` | `HBase4.lean`, unmodified except `maxHeartbeats 400000` | exit 0; the same two warnings; 6 s |
| `copyA.log` | `HA.lean`, 47 in-context probes | exit 1 (probe messages only, plus the cascade at 2225); 152 s |
| `copyA2.log` | `HA2.lean`, A28/A33/A34 alone | exit 1 (probe messages only); 151 s |
| `copyB.log` | `HB.lean`, 46 generalised probes | exit 1 (probe messages only); 86 s |
| `copyB2.log` | `HB2.lean`, names, term checks, `apply?` | exit 0 (`apply?` leaves `sorry` warnings); 72 s |
| `copyC.log` | **`HC.lean`: G1–G9, K1, M1–M8** | **exit 0; `sorry` at 147:8 (`space_universal`) and 2521:8 (`SPACE_linear_ne_NP`) only; 8 s** |
| `copyCG.log` | `HCG.lean`: G1–G9, K1 only | exit 0; the same two warnings (147:8, 2522:8); 8 s |
| `copyD.log` | `HD.lean`: copy C + O1–O8 | exit 0; the same two warnings (147:8, 2504:8); 7 s |

The elaborated copies `HC`/`HCG`/`HD` carry the probe option `maxHeartbeats 400000` at line 16.
The diffs and `HierarchyC/CG/D.lean` here keep the file's `maxHeartbeats 0`. Otherwise they are
identical to the elaborated copies (`diff` shows only line 16). Passing at 400000 implies passing
at the file's unbounded setting.

## Files

* `README.md` (this file); `copyC.diff` (the deliverable), `copyCG.diff`, `copyD.diff`.
* `HierarchyC.lean`, `HierarchyCG.lean`, `HierarchyD.lean`: the patched files, with line 16 as in
  the source.
* `mk_copyA.py` (an optional third argument selects probes), `mk_copyC.py` (`--no-M`,
  `--optional`, `--heartbeats`), `closure.py`.
* `Hierarchy.src.lean` (the target at `14ee2e46`), `all_sites.txt`, `closure.txt`,
  `copyA_tags.tsv`, `copyA2_tags.tsv`, `copyB_tags.tsv`.
* Logs: `base.log`, `base4.log`, `copyA.log`, `copyA2.log`, `copyB.log`, `copyB2.log`, `copyC.log`,
  `copyCG.log`, `copyD.log`.
* Scratch Lean (git-excluded), in `wt-hk/rvprobe/hsweep/`: `HBase.lean`, `HBase4.lean`, `HA.lean`,
  `HA2.lean`, `HB.lean`, `HB2.lean`, `HC.lean`, `HCG.lean`, `HD.lean`.

## ===== campaign/fills/b6/sweep/copyC.diff =====

--- a/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
@@ -166,7 +166,7 @@
     (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) : SPACE f ⊆ SPACE g := by
   obtain ⟨N, hN⟩ := hfg 1
   have hfloor : ∀ n, 1 ≤ g n := fun n =>
-    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff g).mp hg).1 n)
+    Nat.one_le_of_lt (((spaceConstructible_iff g).mp hg).1 n)
   set F := (Finset.range N).sup f with hF
   refine SPACE.mono_const (a := F + 1) fun n => ?_
   by_cases hn : N ≤ n
@@ -175,8 +175,7 @@
       _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
   · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
     calc f n ≤ F + 1 := by omega
-      _ = (F + 1) * 1 := (Nat.mul_one _).symm
-      _ ≤ (F + 1) * g n := Nat.mul_le_mul_left _ (hfloor n)
+      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)
 
 /-- A decider in the smaller space class has a padded code on which the fixed universal
 machine halts inside the larger window, before its configuration-count clock expires.
@@ -232,7 +231,7 @@
   obtain ⟨u, hu, hsu⟩ := hsim (List.replicate N₀ true)
     [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ (c₁ * (c₀ * f x.length + 1)) hn hs
   have hfloor : 1 ≤ f x.length :=
-    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff f).mp hf).1 x.length)
+    Nat.one_le_of_lt (((spaceConstructible_iff f).mp hf).1 x.length)
   have hsmall : C * (c₁ * (c₀ * f x.length + 1) + 1) ≤ A * f x.length := by
     calc
       _ ≤ C * (c₁ * (c₀ * f x.length + f x.length) + f x.length) :=
@@ -339,12 +338,12 @@
     · rw [moveInputPos_pos_of_ne_right _ h]
       exact Nat.succ_pos _
   · intro u hu
-    have : u = 0 := by omega
+    have : u = 0 := Nat.lt_one_iff.mp hu
     subst u
     rw [MultiTapeTM.runFrom_zero, hd]
     decide
   · intro u hu
-    have : u = 0 ∨ u = 1 := by omega
+    have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
     rcases this with rfl | rfl
     · rw [MultiTapeTM.runFrom_zero]
     · rw [hstep]
@@ -381,7 +380,7 @@
       rfl
   refine ⟨hstep, ?_⟩
   intro u hu
-  have : u = 0 ∨ u = 1 := by omega
+  have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
   rcases this with rfl | rfl
   · rw [MultiTapeTM.runFrom_zero]
   · rw [hstep]
@@ -461,7 +460,7 @@
     apply Fin.ext
     have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
       congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
-    omega
+    exact Nat.add_left_cancel h'
 
 /-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
 private lemma sph_witness_cap (KI KR m : ℕ) :
@@ -557,9 +556,9 @@
     · rw [hr, embedSilentCfg_output]
   · rw [MultiTapeTM.spaceUsed_eq_sum]
     calc
-      _ ≤ ∑ _j : Fin (KI + KR + M.k + 2),
+      _ ≤ (Finset.univ : Finset (Fin (KI + KR + M.k + 2))).card •
           (c * g x.length + (g x.length).bits.length + 1) := by
-        apply Finset.sum_le_sum
+        apply Finset.sum_le_card_nsmul
         intro j _
         rw [MultiTapeTM.spaceUsedByTape_eq_card,
           embedSilentRetTM_visitedByTapeHead,
@@ -584,9 +583,7 @@
           · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
               tapes heads [] out a t j hj hjc).2]
             omega
-      _ = _ := by
-        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
-        rfl
+      _ = _ := by rw [Finset.card_fin, smul_eq_mul]
   · intro u hu j
     have hpos : (R.runFrom start u).workTapePos j =
         (embedSilentCfg ι 1 tapes heads [] out
@@ -613,14 +610,13 @@
         push_cast
         omega
       · rw [(embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc).2]
-        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) := by omega
+        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) :=
+          Int.natCast_nonneg _
         omega
 
 
 /-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
-private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k where
-  toFun := Fin.elim0
-  inj' := fun i => Fin.elim0 i
+private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k := Function.Embedding.ofIsEmpty
 
 /-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
 input position of an embedded binary word, with the entire physical work bank framed.
@@ -860,10 +856,8 @@
     rwa [embedEmitCfg_selected_pos] at h
 
 /-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
-private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) where
-  toFun i := ⟨i.val, by have := i.isLt; omega⟩
-  inj' := fun _ _ h => Fin.ext
-    (congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h)
+private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) :=
+  Fin.castLEEmb (by omega)
 
 /-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
 bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]
@@ -1024,7 +1018,7 @@
     apply Fin.ext
     simp only [ι, sphRunnerSel, Function.Embedding.coeFn_mk, Fin.val_zero, if_pos]
   have hv (i : Fin (KR + 1)) (hi : i ≠ 0) : (ι i).val = KI + 1 + i.val := by
-    have hz : i.val ≠ 0 := fun h => hi (Fin.ext h)
+    have hz : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
     exact if_neg hz
   let a := d.select ι
   obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
@@ -1039,7 +1033,7 @@
       rw [htapes]
       apply hblank (ι i)
       · rw [hv i hi]
-        have : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
+        have : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
         omega
       · rw [hv i hi]
         have := i.isLt
@@ -1177,7 +1171,7 @@
   exit_mem := fun _ _ _ _ => Set.mem_singleton _
   cut := by
     intro _ d hd _ u hu
-    have : u = 0 := by omega
+    have : u = 0 := Nat.lt_one_iff.mp hu
     subst u
     rw [MultiTapeTM.runFrom_zero, hd]
     exact Option.some_ne_none _
@@ -1250,14 +1244,8 @@
   have hp : C.pre () d₀ := by
     rw [Contract.branch_pre]
     change (d₀.mapState fun _ => entry) = d
-    apply Cfg.ext
-    · rw [Cfg.mapState_state, hd₀, hd]; rfl
-    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
-    · funext j p
-      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
-    · funext j
-      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
-    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
+    simp only [d₀, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   have htime : C.time () d₀ = t + 2 := by
     rw [Contract.branch_time]
     dsimp only [C₀, sphEmitContract]
@@ -1346,11 +1334,10 @@
     · exact ho u h hh
     · rw [hr, he] at hh
       exact hne (Option.some.inj hh)
-  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := ⟨u - (t + 1), by omega⟩
+  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)
     rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_state] at hbad
-    cases hq : (B.runFrom (d'.mapState fun _ => entry) w).state with
-    | none => rw [hq, Option.map_none] at hbad; cases hbad
-    | some q => rw [hq, Option.map_some] at hbad; cases hbad
+    obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad
+    exact Sum.inr_ne_inl hq
 
 /-- Writing a layout's interior between its two blank boundary cells installs that record.
 This is the shared boundary argument for the initializer and the stopped runner.
@@ -1607,15 +1594,8 @@
     rw [Cfg.mapState_workTapes]
     exact hblank j hj hj' p
   have hstart : (((a.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) = d := by
-    apply Cfg.ext
-    · simp only [a, Cfg.mapState_state, hd, Option.map_some]
-      rfl
-    · simp only [a, Cfg.mapState_inputPos]
-    · funext j p
-      simp only [a, Cfg.mapState_workTapes]
-    · funext j
-      simp only [a, Cfg.mapState_workTapePos]
-    · simp only [a, Cfg.mapState_output]
+    simp only [a, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   obtain ⟨t, out, _, he, hc, hh, ho, hword, hend⟩ := hR KI m s (M.tm.initCfg x) 0
     (by rw [MultiTapeTM.initCfg_eq]; exact Cfg.inWindow_init _ _ s) a ha har hab
   let a' := (H KI m).runFrom a t
@@ -1665,15 +1645,8 @@
     obtain ⟨hvr, hvh⟩ := sph_verdict_run (J KI m) ten yes no hne z hz b v (CT * (L + 1))
       (by simpa only [b, decide_eq_true_eq] using hrunT) hcutT hheadsT
     have hmaps : ((z.mapState Sum.inl).mapState Sum.inl) = a'.mapState (fun _ => ven) := by
-      apply Cfg.ext
-      · simp only [z, Cfg.mapState_state, ha', Option.map_some]
-        rfl
-      · simp only [z, Cfg.mapState_inputPos]
-      · funext j p
-        simp only [z, Cfg.mapState_workTapes]
-      · funext j
-        simp only [z, Cfg.mapState_workTapePos]
-      · simp only [z, Cfg.mapState_output]
+      simp only [z, Cfg.mapState_mapState]
+      rfl
     rw [hmaps] at hvr hvh
     refine ⟨v + 2, !b, ?_, ?_, ?_, ?_⟩
     · rw [hvr]
@@ -1753,12 +1726,8 @@
   let a := d.mapState (fun _ => ien)
   have ha : a.state = some ien := by rw [Cfg.mapState_state, hd]; rfl
   have hstart : a.mapState Sum.inl = d := by
-    apply Cfg.ext
-    · rw [Cfg.mapState_state, Cfg.mapState_state, hd]; rfl
-    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
-    · funext j p; rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
-    · funext j; rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
-    · rw [Cfg.mapState_output, Cfg.mapState_output]
+    simp only [a, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   let L := recordLength M.k x.length s
   have hblank' (j : Fin (KI + KR + m + 2)) (hj : j.val < KI + KR + 2) (hj1 : j ≠ 1)
       (p : ℤ) : a.workTapes j p = none := by
@@ -1772,9 +1741,7 @@
       exact hrad p hp hp')
     (by
       intro p _ _
-      exact hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
+      exact hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
     (by
       intro j hj hj' p
       exact hblank' j (by omega) (by
@@ -1787,12 +1754,8 @@
   have har : RecordAt a' 0 (cfgRecord s (M.tm.initCfg x) 0) := by
     have hwritten := sph_written_record a (some iex) (cfgRecord s (M.tm.initCfg x) 0) L
       (joinFields_cfgRecord_length _ _ _)
-      (hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
-      (hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
+      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
+      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
     dsimp only [a']
     rw [recordAt_iff] at hwritten ⊢
     intro p hp hp'
@@ -1821,8 +1784,7 @@
   have hIB : CI * (L + ws.length + s + 1) ≤ B :=
     Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
   have hSB : CS * (L + 1) ≤ B :=
-    (Nat.mul_le_mul_left _ (by omega)).trans
-      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
+    Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)
   refine ⟨t + 1 + v, b, ?_, ?_, ?_, hpred⟩
   · rw [hrun, Cfg.mapState_state, hvs, Option.map_none]
   · rw [hrun, Cfg.mapState_output, hvo, Cfg.mapState_output, hao]
@@ -1850,8 +1812,8 @@
 formula and absorb the additive constants using the logarithmic floor. -/
 private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n) (k n : ℕ) :
     recordLength k n (g n) + (g n).bits.length + g n + 1 ≤ (4 * k + 9) * g n := by
-  have hfloor : 1 ≤ g n := by have h := hg n; rw [logSpace_eq] at h; omega
-  have hb : (g n).bits.length ≤ g n := LogProg.length_bits_le Nat.lt_two_pow_self
+  have hfloor : 1 ≤ g n := Nat.one_le_of_lt (hg n)
+  have hb : (g n).bits.length ≤ g n := length_bits_le_self _
   have hp : posWidth n ≤ 2 * g n := by
     rw [posWidth_eq]
     have hpow : n + 1 < 2 ^ (Nat.log 2 n + 2) :=
@@ -1862,7 +1824,7 @@
     rw [logSpace_eq] at hg'
     omega
   rw [recordLength_eq]
-  have hk : k ≤ k * g n := by simpa only [mul_one] using Nat.mul_le_mul_left k hfloor
+  have hk : k ≤ k * g n := Nat.le_mul_of_pos_right k hfloor
   nlinarith
 
 
@@ -2045,8 +2007,8 @@
   rw [hstart] at hDH
   have hsize : radius ≤ B * g x.length := by
     have hrecord := sph_record_size g hg M.k x.length
-    have hbits : ws.length ≤ g x.length := LogProg.length_bits_le Nat.lt_two_pow_self
-    have hfloor : 1 ≤ g x.length := by have h := hg x.length; rw [logSpace_eq] at h; omega
+    have hbits : ws.length ≤ g x.length := length_bits_le_self _
+    have hfloor : 1 ≤ g x.length := Nat.one_le_of_lt (hg x.length)
     have h := Nat.mul_le_mul_left C hrecord
     dsimp only [radius, rW, rR, rS, B]
     nlinarith
@@ -2133,7 +2095,7 @@
     (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
   let a' := {a with state := some (ScanPhase.done b)}
   let radius := S ys.length
-  have hrad : (0 : ℤ) ≤ radius := by omega
+  have hrad : (0 : ℤ) ≤ radius := Int.natCast_nonneg _
   let C₀ : Contract F (.fwd true) {some (.done true), some (.done false)} Unit ys :=
     { pre := fun _ d => d = a
       time := fun _ _ => 2 * ys.length + 2
@@ -2329,8 +2291,7 @@
           rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append, hb]
     have htest : answer (x.map e) = true ↔ bit = true := hlang.trans hacc
     change bit = answer (x.map e)
-    cases hb : bit <;> cases ha : answer (x.map e) <;>
-      simp_all only [Bool.false_eq_true, iff_false, iff_true, not_true_eq_false]
+    exact Bool.eq_iff_iff.mpr htest.symm
   let S (n : ℕ) := k * (2 * (B * g n) + 1)
   obtain ⟨c', N, hN⟩ := FinTM.decidesInSpace_of_alphabetReduction e D L S
     (by
@@ -2343,7 +2304,7 @@
       exact (ht ys).spaceUsed_le_of_halt (hs ys) u)
   have hL : L ∈ SPACE (fun n => S n + 1) := mem_SPACE_iff.mpr ⟨c', N, hN⟩
   have hb (n : ℕ) : S n + 1 ≤ (k * (2 * B + 1) + 1) * g n := by
-    have hn : 1 ≤ g n := by have h := hfloor n; rw [logSpace_eq] at h; omega
+    have hn : 1 ≤ g n := Nat.one_le_of_lt (hfloor n)
     calc
       _ ≤ k * (2 * (B * g n) + g n) + g n :=
         Nat.add_le_add (Nat.mul_le_mul_left k (Nat.add_le_add_left hn _)) hn

## ===== campaign/fills/b6/inputs/b6-fill-hierarchy/screen-population.txt =====

TCSlib/Complexity/ClassNP/PClosure.lean
TCSlib/Complexity/SpaceComplexity/Basic.lean
TCSlib/Complexity/SpaceComplexity/ConfigCount.lean
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean
TCSlib/Complexity/SpaceComplexity/Constructible.lean
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean
TCSlib/Complexity/SpaceComplexity/WindowClock.lean
TCSlib/Complexity/TimeHierarchy/Diagonal.lean
TCSlib/Complexity/TuringMachine/Build/Catalog.lean
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean
TCSlib/Complexity/TuringMachine/Build/Scan.lean
TCSlib/Complexity/TuringMachine/Build/Seam.lean
TCSlib/Complexity/TuringMachine/Build/WindowRun.lean
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean
TCSlib/Complexity/TuringMachine/Encoding.lean
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean
TCSlib/Complexity/TuringMachine/SelfUniversal.lean
TCSlib/Complexity/TuringMachine/StateRenaming.lean
TCSlib/Complexity/TuringMachine/SymbolLift.lean
TCSlib/Complexity/ClassNP/NP.lean
TCSlib/Complexity/TimeHierarchy/Separation.lean
TCSlib/Complexity/SpaceComplexity/Savitch.lean
TCSlib/Complexity/ClassNP/Nondeterminism.lean
TCSlib/Complexity/TuringMachine/Build/Embed.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean
TCSlib/Complexity/TuringMachine/Build/InputRewind.lean
TCSlib/Complexity/TuringMachine/Build/Rewind.lean
TCSlib/Complexity/TuringMachine/Build/InputCall.lean
TCSlib/Complexity/TuringMachine/Build/Primitives.lean
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean
TCSlib/Complexity/TuringMachine/Configuration.lean
TCSlib/Complexity/TuringMachine/Deterministic.lean
TCSlib/Complexity/TuringMachine/Finite.lean
TCSlib/Complexity/TuringMachine/Simulation.lean
TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean
TCSlib/Complexity/ClassNP/PolyTime.lean
TCSlib/Complexity/ClassNP/PolyTimePairing.lean

## ===== campaign/gates/109-h-landing-fill/evidence/freeze/declfreeze-Hierarchy-base.txt =====

public before/after: 4 4 private before/after: 0 43
public added: []
public removed: []
authorized body change: Complexity.LOGSPACE_ssubset_PSPACE
authorized body change: Complexity.SPACE_linear_ne_NP
authorized body change: Complexity.space_hierarchy
private removed: []
private added: ['Complexity.sphDigit', 'Complexity.sphEmitContract', 'Complexity.sphEmitTM', 'Complexity.sphEmptySel', 'Complexity.sphInitSel', 'Complexity.sphRecordSel', 'Complexity.sphRewindsTM', 'Complexity.sphRightTM', 'Complexity.sphRunnerSel', 'Complexity.sphRunnerTailTM', 'Complexity.sphVerdictTM', 'Complexity.sphWitnessSel', 'Complexity.sph_code_window', 'Complexity.sph_diagonal_language', 'Complexity.sph_emit_run', 'Complexity.sph_fold_valid', 'Complexity.sph_halt_contract', 'Complexity.sph_inclusion', 'Complexity.sph_initial_record', 'Complexity.sph_input_rewind_run', 'Complexity.sph_linear_ne_NP_of_padding', 'Complexity.sph_logSpace_dom', 'Complexity.sph_logspace_ssubset', 'Complexity.sph_radius_run', 'Complexity.sph_record_size', 'Complexity.sph_record_suffix', 'Complexity.sph_rewinds_run', 'Complexity.sph_right_run', 'Complexity.sph_runner_run', 'Complexity.sph_runner_tail_run', 'Complexity.sph_seam_avoids', 'Complexity.sph_seam_heads', 'Complexity.sph_select_fields', 'Complexity.sph_sq_le_two_pow', 'Complexity.sph_suffix', 'Complexity.sph_summary', 'Complexity.sph_test_run', 'Complexity.sph_valid_machine', 'Complexity.sph_validated_machine', 'Complexity.sph_validation_run', 'Complexity.sph_verdict_run', 'Complexity.sph_witness_cap', 'Complexity.sph_written_record']
private changed: []

## ===== campaign/gates/109-h-landing-fill/evidence/freeze/declfreeze-Hierarchy-delivery.txt =====

public before/after: 4 4 private before/after: 43 43
public added: []
public removed: []
authorized body change: Complexity.SPACE_linear_ne_NP
authorized body change: Complexity.space_hierarchy
private removed: []
private added: []
private changed: ['Complexity.sphEmitContract', 'Complexity.sphEmptySel', 'Complexity.sphInitSel', 'Complexity.sphWitnessSel', 'Complexity.sph_diagonal_language', 'Complexity.sph_emit_run', 'Complexity.sph_inclusion', 'Complexity.sph_radius_run', 'Complexity.sph_record_size', 'Complexity.sph_record_suffix', 'Complexity.sph_right_run', 'Complexity.sph_runner_run', 'Complexity.sph_seam_avoids', 'Complexity.sph_suffix', 'Complexity.sph_valid_machine', 'Complexity.sph_validated_machine', 'Complexity.sph_verdict_run']

## ===== campaign/gates/109-h-landing-fill/evidence/landing/landing.diff =====

diff --git a/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean b/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
index 40d62c36..301b9847 100644
--- a/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
@@ -57,7 +57,7 @@ space-bounded configuration window.
   full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
   `S`.
 * **Both bounds space-constructible**, as in the book; `g`'s witness drives
-  the window radius and the clock width, and of `f` the proof uses only the
+  the window radius, and of `f` the proof uses only the
   bundled floor `1 ≤ logSpace n ≤ f n`.
 * The `SpaceComplexity.lean` facade imports this module.
 
@@ -175,8 +175,7 @@ private lemma sph_inclusion {f g : ℕ → ℕ} (hg : SpaceConstructible g)
       _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
   · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
     calc f n ≤ F + 1 := by omega
-      _ = (F + 1) * 1 := (Nat.mul_one _).symm
-      _ ≤ (F + 1) * g n := Nat.mul_le_mul_left _ (hfloor n)
+      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)
 
 /-- A decider in the smaller space class has a padded code on which the fixed universal
 machine halts inside the larger window, before its configuration-count clock expires.
@@ -339,12 +338,12 @@ private lemma sph_right_run {k : ℕ} {Γ : Type} {x : List Γ}
     · rw [moveInputPos_pos_of_ne_right _ h]
       exact Nat.succ_pos _
   · intro u hu
-    have : u = 0 := by omega
+    have : u = 0 := Nat.lt_one_iff.mp hu
     subst u
     rw [MultiTapeTM.runFrom_zero, hd]
     decide
   · intro u hu
-    have : u = 0 ∨ u = 1 := by omega
+    have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
     rcases this with rfl | rfl
     · rw [MultiTapeTM.runFrom_zero]
     · rw [hstep]
@@ -381,7 +380,7 @@ private lemma sph_emit_run {k : ℕ} {Γ : Type} {x : List Γ} (b : Γ)
       rfl
   refine ⟨hstep, ?_⟩
   intro u hu
-  have : u = 0 ∨ u = 1 := by omega
+  have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
   rcases this with rfl | rfl
   · rw [MultiTapeTM.runFrom_zero]
   · rw [hstep]
@@ -461,7 +460,7 @@ private def sphWitnessSel (KI KR m : ℕ) : Fin m ↪ Fin (KI + KR + m + 2) wher
     apply Fin.ext
     have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
       congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
-    omega
+    exact Nat.add_left_cancel h'
 
 /-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
 private lemma sph_witness_cap (KI KR m : ℕ) :
@@ -557,9 +556,9 @@ private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
     · rw [hr, embedSilentCfg_output]
   · rw [MultiTapeTM.spaceUsed_eq_sum]
     calc
-      _ ≤ ∑ _j : Fin (KI + KR + M.k + 2),
+      _ ≤ (Finset.univ : Finset (Fin (KI + KR + M.k + 2))).card •
           (c * g x.length + (g x.length).bits.length + 1) := by
-        apply Finset.sum_le_sum
+        apply Finset.sum_le_card_nsmul
         intro j _
         rw [MultiTapeTM.spaceUsedByTape_eq_card,
           embedSilentRetTM_visitedByTapeHead,
@@ -584,9 +583,7 @@ private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
           · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
               tapes heads [] out a t j hj hjc).2]
             omega
-      _ = _ := by
-        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
-        rfl
+      _ = _ := by rw [Finset.card_fin, smul_eq_mul]
   · intro u hu j
     have hpos : (R.runFrom start u).workTapePos j =
         (embedSilentCfg ι 1 tapes heads [] out
@@ -613,14 +610,13 @@ private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
         push_cast
         omega
       · rw [(embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc).2]
-        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) := by omega
+        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) :=
+          Int.natCast_nonneg _
         omega
 
 
 /-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
-private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k where
-  toFun := Fin.elim0
-  inj' := fun i => Fin.elim0 i
+private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k := Function.Embedding.ofIsEmpty
 
 /-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
 input position of an embedded binary word, with the entire physical work bank framed.
@@ -860,10 +856,8 @@ private lemma sph_select_fields {m k : ℕ} {Γ S : Type} {x : List Γ}
     rwa [embedEmitCfg_selected_pos] at h
 
 /-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
-private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) where
-  toFun i := ⟨i.val, by have := i.isLt; omega⟩
-  inj' := fun _ _ h => Fin.ext
-    (congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h)
+private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) :=
+  Fin.castLEEmb (by omega)
 
 /-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
 bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]
@@ -1024,7 +1018,7 @@ private lemma sph_runner_run (M : FinTM Bool) :
     apply Fin.ext
     simp only [ι, sphRunnerSel, Function.Embedding.coeFn_mk, Fin.val_zero, if_pos]
   have hv (i : Fin (KR + 1)) (hi : i ≠ 0) : (ι i).val = KI + 1 + i.val := by
-    have hz : i.val ≠ 0 := fun h => hi (Fin.ext h)
+    have hz : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
     exact if_neg hz
   let a := d.select ι
   obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
@@ -1039,7 +1033,7 @@ private lemma sph_runner_run (M : FinTM Bool) :
       rw [htapes]
       apply hblank (ι i)
       · rw [hv i hi]
-        have : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
+        have : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
         omega
       · rw [hv i hi]
         have := i.isLt
@@ -1177,7 +1171,7 @@ private def sphEmitContract {k : ℕ} {Γ : Type} (b : Γ) (x : List Γ) :
   exit_mem := fun _ _ _ _ => Set.mem_singleton _
   cut := by
     intro _ d hd _ u hu
-    have : u = 0 := by omega
+    have : u = 0 := Nat.lt_one_iff.mp hu
     subst u
     rw [MultiTapeTM.runFrom_zero, hd]
     exact Option.some_ne_none _
@@ -1250,14 +1244,8 @@ private lemma sph_verdict_run {k : ℕ} {Q P : Type} [DecidableEq P]
   have hp : C.pre () d₀ := by
     rw [Contract.branch_pre]
     change (d₀.mapState fun _ => entry) = d
-    apply Cfg.ext
-    · rw [Cfg.mapState_state, hd₀, hd]; rfl
-    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
-    · funext j p
-      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
-    · funext j
-      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
-    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
+    simp only [d₀, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   have htime : C.time () d₀ = t + 2 := by
     rw [Contract.branch_time]
     dsimp only [C₀, sphEmitContract]
@@ -1346,11 +1334,10 @@ private lemma sph_seam_avoids {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : Lis
     · exact ho u h hh
     · rw [hr, he] at hh
       exact hne (Option.some.inj hh)
-  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := ⟨u - (t + 1), by omega⟩
+  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)
     rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_state] at hbad
-    cases hq : (B.runFrom (d'.mapState fun _ => entry) w).state with
-    | none => rw [hq, Option.map_none] at hbad; cases hbad
-    | some q => rw [hq, Option.map_some] at hbad; cases hbad
+    obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad
+    exact Sum.inr_ne_inl hq
 
 /-- Writing a layout's interior between its two blank boundary cells installs that record.
 This is the shared boundary argument for the initializer and the stopped runner.
@@ -1607,15 +1594,8 @@ private lemma sph_suffix (M : FinTM Bool) :
     rw [Cfg.mapState_workTapes]
     exact hblank j hj hj' p
   have hstart : (((a.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) = d := by
-    apply Cfg.ext
-    · simp only [a, Cfg.mapState_state, hd, Option.map_some]
-      rfl
-    · simp only [a, Cfg.mapState_inputPos]
-    · funext j p
-      simp only [a, Cfg.mapState_workTapes]
-    · funext j
-      simp only [a, Cfg.mapState_workTapePos]
-    · simp only [a, Cfg.mapState_output]
+    simp only [a, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   obtain ⟨t, out, _, he, hc, hh, ho, hword, hend⟩ := hR KI m s (M.tm.initCfg x) 0
     (by rw [MultiTapeTM.initCfg_eq]; exact Cfg.inWindow_init _ _ s) a ha har hab
   let a' := (H KI m).runFrom a t
@@ -1665,15 +1645,8 @@ private lemma sph_suffix (M : FinTM Bool) :
     obtain ⟨hvr, hvh⟩ := sph_verdict_run (J KI m) ten yes no hne z hz b v (CT * (L + 1))
       (by simpa only [b, decide_eq_true_eq] using hrunT) hcutT hheadsT
     have hmaps : ((z.mapState Sum.inl).mapState Sum.inl) = a'.mapState (fun _ => ven) := by
-      apply Cfg.ext
-      · simp only [z, Cfg.mapState_state, ha', Option.map_some]
-        rfl
-      · simp only [z, Cfg.mapState_inputPos]
-      · funext j p
-        simp only [z, Cfg.mapState_workTapes]
-      · funext j
-        simp only [z, Cfg.mapState_workTapePos]
-      · simp only [z, Cfg.mapState_output]
+      simp only [z, Cfg.mapState_mapState]
+      rfl
     rw [hmaps] at hvr hvh
     refine ⟨v + 2, !b, ?_, ?_, ?_, ?_⟩
     · rw [hvr]
@@ -1753,12 +1726,8 @@ private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
   let a := d.mapState (fun _ => ien)
   have ha : a.state = some ien := by rw [Cfg.mapState_state, hd]; rfl
   have hstart : a.mapState Sum.inl = d := by
-    apply Cfg.ext
-    · rw [Cfg.mapState_state, Cfg.mapState_state, hd]; rfl
-    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
-    · funext j p; rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
-    · funext j; rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
-    · rw [Cfg.mapState_output, Cfg.mapState_output]
+    simp only [a, Cfg.mapState_mapState]
+    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
   let L := recordLength M.k x.length s
   have hblank' (j : Fin (KI + KR + m + 2)) (hj : j.val < KI + KR + 2) (hj1 : j ≠ 1)
       (p : ℤ) : a.workTapes j p = none := by
@@ -1772,9 +1741,7 @@ private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
       exact hrad p hp hp')
     (by
       intro p _ _
-      exact hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
+      exact hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
     (by
       intro j hj hj' p
       exact hblank' j (by omega) (by
@@ -1787,12 +1754,8 @@ private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
   have har : RecordAt a' 0 (cfgRecord s (M.tm.initCfg x) 0) := by
     have hwritten := sph_written_record a (some iex) (cfgRecord s (M.tm.initCfg x) 0) L
       (joinFields_cfgRecord_length _ _ _)
-      (hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
-      (hblank' 0 (by rw [Fin.val_zero]; omega) (by
-        intro h; have hh := congrArg Fin.val h
-        rw [Fin.val_zero, Fin.val_one] at hh; omega) _)
+      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
+      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
     dsimp only [a']
     rw [recordAt_iff] at hwritten ⊢
     intro p hp hp'
@@ -1821,8 +1784,7 @@ private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
   have hIB : CI * (L + ws.length + s + 1) ≤ B :=
     Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
   have hSB : CS * (L + 1) ≤ B :=
-    (Nat.mul_le_mul_left _ (by omega)).trans
-      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
+    Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)
   refine ⟨t + 1 + v, b, ?_, ?_, ?_, hpred⟩
   · rw [hrun, Cfg.mapState_state, hvs, Option.map_none]
   · rw [hrun, Cfg.mapState_output, hvo, Cfg.mapState_output, hao]
@@ -1851,7 +1813,7 @@ formula and absorb the additive constants using the logarithmic floor. -/
 private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n) (k n : ℕ) :
     recordLength k n (g n) + (g n).bits.length + g n + 1 ≤ (4 * k + 9) * g n := by
   have hfloor : 1 ≤ g n := by have h := hg n; rw [logSpace_eq] at h; omega
-  have hb : (g n).bits.length ≤ g n := LogProg.length_bits_le Nat.lt_two_pow_self
+  have hb : (g n).bits.length ≤ g n := length_bits_le_self _
   have hp : posWidth n ≤ 2 * g n := by
     rw [posWidth_eq]
     have hpow : n + 1 < 2 ^ (Nat.log 2 n + 2) :=
@@ -1862,7 +1824,7 @@ private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n)
     rw [logSpace_eq] at hg'
     omega
   rw [recordLength_eq]
-  have hk : k ≤ k * g n := by simpa only [mul_one] using Nat.mul_le_mul_left k hfloor
+  have hk : k ≤ k * g n := Nat.le_mul_of_pos_right k hfloor
   nlinarith
 
 
@@ -2045,7 +2007,7 @@ private lemma sph_valid_machine (M : FinTM Bool) (g : ℕ → ℕ)
   rw [hstart] at hDH
   have hsize : radius ≤ B * g x.length := by
     have hrecord := sph_record_size g hg M.k x.length
-    have hbits : ws.length ≤ g x.length := LogProg.length_bits_le Nat.lt_two_pow_self
+    have hbits : ws.length ≤ g x.length := length_bits_le_self _
     have hfloor : 1 ≤ g x.length := by have h := hg x.length; rw [logSpace_eq] at h; omega
     have h := Nat.mul_le_mul_left C hrecord
     dsimp only [radius, rW, rR, rS, B]
@@ -2133,7 +2095,7 @@ private lemma sph_validated_machine {k : ℕ} {Q P : Type} [Fintype Q] [Decidabl
     (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
   let a' := {a with state := some (ScanPhase.done b)}
   let radius := S ys.length
-  have hrad : (0 : ℤ) ≤ radius := by omega
+  have hrad : (0 : ℤ) ≤ radius := Int.natCast_nonneg _
   let C₀ : Contract F (.fwd true) {some (.done true), some (.done false)} Unit ys :=
     { pre := fun _ d => d = a
       time := fun _ _ => 2 * ys.length + 2
@@ -2329,8 +2291,7 @@ private lemma sph_diagonal_language (M : FinTM Bool) (g : ℕ → ℕ) (hg : Spa
           rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append, hb]
     have htest : answer (x.map e) = true ↔ bit = true := hlang.trans hacc
     change bit = answer (x.map e)
-    cases hb : bit <;> cases ha : answer (x.map e) <;>
-      simp_all only [Bool.false_eq_true, iff_false, iff_true, not_true_eq_false]
+    exact Bool.eq_iff_iff.mpr htest.symm
   let S (n : ℕ) := k * (2 * (B * g n) + 1)
   obtain ⟨c', N, hN⟩ := FinTM.decidesInSpace_of_alphabetReduction e D L S
     (by
@@ -2439,25 +2400,20 @@ ruler is needed; only this direction is used.
 (`a = 1` suffices, the code-dependent constant being paid by the hypothesis
 below; a power of two costs only low zero digits) and write `U₀`'s initial
 record on `x` at radius `r`, tagged with the empty-output summary
-(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner: each round
-tests the record for a halted state (`Turing.exists_recordTestTM`), else
-applies one step of `U₀` (`Turing.exists_recordStepTM`, whose `no` verdict
-is the window exit), the tag updated by the three-valued output summary
-`Turing.outSummary` (append-compatible, `Turing.outSummary_append_congr`;
-coded in `Fin 3`), so the emitted word is never buffered. The rounds are driven by
-the configuration-count clock,
-the rich counter loop (`Turing.counterLoopTMVia`) on an
-all-`true` word of width `W = |Q₀| + posWidth n + 3 · k₀ · (2r + 1) + 1`,
-where `Q₀` and `k₀` are `U₀`'s states and tape count. Its value `2^W - 1`
-exceeds `Turing.FinTM.configBound U₀ n r`, which is at most
-`2^(|Q₀| + posWidth n + 3 · k₀ · (2r + 1))`, each of its four factors being
-at most a power of two. (iv) Answer `false` if the runner stopped at a halted
+(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner at `U₀`
+(`Turing.exists_configWindowRunnerTM`): each round tests the record for a halted state, else
+applies one step of `U₀` (leaving the window is an exit), the tag updated by the three-valued
+output summary `Turing.outSummary` (`summaryTag`; append-compatible,
+`Turing.outSummary_append_congr`; coded in `Fin 3`), so the emitted word is never buffered.
+The runner carries its own configuration-count clock, whose value suffices for every round up
+to `Turing.FinTM.configBound U₀ n r + 1`, in `O(record length)` cells.
+(iv) Answer `false` if the runner stopped at a halted
 record with summary `accept` (output exactly `[true]`,
 `Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
 with another output, window exit, or clock exhaustion. `D` halts on every
 input. Its cells are the witness's `O(g n)`, the record's
 `k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
-rows' `O(record length)` scratch and the clock's `W`: all `O(g n)` with
+runner's `O(record length)` scratch and clock: all `O(g n)` with
 constants depending only on `U₀` and `g`'s witness, **uniformly in the code
 part of `x`**, because the window, not `U₀`'s constant, bounds the
 simulation; the `posWidth n = O(logSpace n)` terms are
@@ -2470,10 +2426,8 @@ that `D` decides lies in `SPACE g`.
 every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
 configuration frozen after it). The space-faithful normal form
 `Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
-`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N`
-(`Turing.exists_codeTM`, plus the space clause it does not state:
-relabelling states leaves tapes and heads untouched,
-`Turing.MultiTapeTM.relabelState_runFrom_init`) and set
+`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N` within the same space
+(`Turing.exists_codeTM_spaceUsed`) and set
 `α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
 never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
 `[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
@@ -2490,13 +2444,11 @@ whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
 opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. The construction uses
 `U₀` with its forward ledger (the step block at one coded work tape, the
 native input device and the chapter-1 startup); the configuration-count
-windowed runner at `U₀` with the output-summary tag, over the record rows
-`exists_recordInitTM` (with `exists_recordTemplateTM` beneath it),
-`exists_recordTestTM` and
-`exists_recordStepTM`, clocked by `counterLoopTMVia`; the radius and
-clock-width phases (`g`'s witness captured, radius digits, width expansion);
-the window-containment lemma from the visited-interval facts; the space
-clause of `exists_codeTM` and the all-times space bound of a decider; the
+windowed runner `exists_configWindowRunnerTM` at `U₀` with the output-summary tag, after
+the record initializer `exists_recordInitTM` and followed by the record test
+`exists_recordTestTM`; the radius phase (`g`'s witness captured, radius digits);
+the window-containment lemma from the visited-interval facts;
+`exists_codeTM_spaceUsed` and the all-times space bound of a decider; the
 contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
 alphabet reduction. -/
 theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
@@ -2535,28 +2487,20 @@ normalization `n + 1` — the literal `SPACE(n)` is the zero-work-tape class).
 Neither inclusion between the
 two classes is claimed, matching the book's remark.
 
-**Proof sketch.** Suppose `SPACE (n + 1) = NP`. `NP` is closed downward
-under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
-obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
-bounded form). Padding transfers space bounds down:
-for `L ∈ SPACE (n² + 1)`, the padded language
-`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate (|x|²) true)}` —
-membership restricted to padded members of `L`; padded
-length exactly `m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
-length (validate, then run the `L`-decider on the first component; the pad
-supplies the room — the chapter-2 padding-cluster discipline,
-`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
-`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
-language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
-`NP` pullback composing the reduction with the bounded-certificate verifier
-at the reduction's polynomial output length. Hence
-`SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
+**Proof sketch.** Suppose `SPACE (n + 1) = NP`. Padding transfers space bounds down: for
+`L ∈ SPACE (n² + 1)`, the padded language
+`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate ((|x| + 1)²) true)}` (padded members of
+`L` only; padded length exactly `m = (n + 1)² + 2n + 2`) lies in `SPACE (m + 1)`: validate the
+padding, then run the `L`-decider on the first component, the pad supplying the room. So
+`L' ∈ NP` by the assumption. The padding map is polynomial-time computable and `L` is the
+preimage of `L'` under it, so `L ∈ NP` (`Complexity.preimage_mem_NP`), that is
+`L ∈ SPACE (n + 1)`. Hence `SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
 `Complexity.space_hierarchy` at the constructible pair
 (`Complexity.spaceConstructible_linear`,
 `Complexity.spaceConstructible_poly` at degree two; domination
-`A · (n + 1) ≤ n² + 1` eventually). The argument uses the `NP`
-`≤ₚ`-closure lemma, the padded-language space decider, the padding
-reduction machine and the strictness extraction. -/
+`A · (n + 1) ≤ n² + 1` eventually). The argument uses the padded-language space decider,
+the padding map's polynomial-time computability, `preimage_mem_NP` and the strictness
+extraction. -/
 theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
   sorry
 

## ===== campaign/gates/109-h-landing-fill/evidence/lint/campaign-SpaceComplexity-base.txt =====

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

## ===== campaign/gates/109-h-landing-fill/evidence/lint/campaign-SpaceComplexity-head.txt =====

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
WARN  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      2507 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
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
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      2507 lines; 4 public / 43 private declarations
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

style_lint: 0 FAIL, 82 WARN over 112 files

## ===== campaign/gates/109-h-landing-fill/evidence/lint/policy-base.txt =====


1 findings in 1 files
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean: module docstring missing `## Main definitions`

## ===== campaign/gates/109-h-landing-fill/evidence/lint/policy-head.txt =====


2 findings in 1 files
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean: module docstring missing `## Main definitions`
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean: 2508 lines (> 1000, must split)

## ===== campaign/gates/109-h-landing-fill/evidence/merged-tree/down-lh2.txt =====

TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity

## ===== campaign/gates/109-h-landing-fill/evidence/merged-tree/replay-lh2-static.txt =====

modules 2, mismatches 0, static total 2

## ===== campaign/gates/109-h-landing-fill/evidence/merged-tree/replay-lh2.log =====

# replay-lh2 at 65d72947: #218, H landing with M5 restored, on the campaign after #216 (2 modules), fresh .oleans into oleans-lh2
TCSlib/Complexity/SpaceComplexity/Hierarchy exit=0 errors=0 sorry=2
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
# modules=2 failed=0

## ===== campaign/gates/109-h-landing-fill/evidence/merged-tree/replay-lh2.sh =====

#!/usr/bin/env bash
# Replay lh2 (#218, H landing with M5 restored, on the campaign after #216; branch lean/b6h-landing, stacked on the campaign after #216 (oleans-lcamp3)): its downstream closure (2 modules),
# fresh .oleans into oleans-lh2, a copy of oleans-lcamp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-h"
LIST="/home/user/tcslib-scratch/fills/replay/down-lh2.txt"
LOG="$S/fills/replay/replay-lh2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:301b9847a1c361943839b8b5d1e103b66c5c9297"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/b6h-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD || { echo "precheck: the head must contain the campaign after #216 (oleans-lcamp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #216 (oleans-lcamp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lh2" ] && { echo "precheck: $S/oleans-lh2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp3" ] || { echo "precheck: oleans-lcamp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp3" "$S/oleans-lh2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lh2 at $(git rev-parse --short HEAD): #218, H landing with M5 restored, on the campaign after #216 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lh2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lh2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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

## ===== campaign/gates/109-h-landing-fill/evidence/screen/delivery-screen-final-classification.txt =====

Final frozen commit: 30222bbd264a75057ae0779535a32e1a30dd2394.
Baseline: 1854 declarations, 1689 pairs, 534736 reproduced characters.
Final: 1893 declarations, 1701 pairs, 539326 reproduced characters.
12 new pairs; 0 removed pairs. No new pair reaches 90%.

   Hierarchy.lean::sph_verdict_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 339/402 = 84%
  Disposition: idiom. Public field readings establish a branch precondition using its live-state hypothesis and emitted endpoints with changed state/output; this is not the generic composition equation.

   Hierarchy.lean::sph_right_run  reproduces  Hierarchy.lean::sph_emit_run: 490/588 = 83%
  Disposition: same-file leaf idiom. The two explicitly permitted one-step leaves have different effects and share public action-field readings.

   Hierarchy.lean::sph_rewinds_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 330/402 = 82%
  Disposition: idiom. Public field readings for a framed endpoint that changes input position and the radius head; not pure state-map composition.

   Hierarchy.lean::sphWitnessSel  reproduces  Hierarchy.lean::sphInitSel: 70/88 = 80%
  Disposition: same-file arithmetic idiom. Distinct bank selections share elementary embedding-injectivity arithmetic.

   Hierarchy.lean::sph_record_suffix  reproduces  InputRewind.lean::Cfg.mapState_mapState: 293/402 = 73%
  Disposition: idiom. Restore the original live entry configuration using its state hypothesis and unchanged physical fields; the conclusion is not the generic composition equation.

   Hierarchy.lean::sph_valid_machine  reproduces  Hierarchy.lean::sph_witness_cap: 69/111 = 62%
  Disposition: same-file arithmetic idiom. This excludes the entire initializer/runner bank from the witness bank; sph_witness_cap is already cited for the distinct claim excluding radius tape one.

   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_initial_record: 1059/1728 = 61%
  Disposition: same-file R1 consumer idiom. Distinct published clocked-runner and initializer hosts, both embedded through R1; shared field transport already factors through sph_select_fields.

   Hierarchy.lean::sph_valid_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 245/402 = 61%
  Disposition: idiom; earlier pure re-derivations repaired. The remaining match is the concrete initial-configuration comparison through capture, lift, blank-frame and initialization fields. Both pure composition calculations now cite Cfg.mapState_mapState directly.

   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_test_run: 836/1424 = 59%
  Disposition: same-file R1 consumer idiom. Distinct published clocked-runner and Boolean record-test hosts, with shared R1 field transport through sph_select_fields.

   Hierarchy.lean::sph_validated_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 232/402 = 58%
  Disposition: idiom. Concrete initialization and branch-precondition identities through Cfg.init and mapState field readings.

   Hierarchy.lean::sph_seam_avoids  reproduces  Hierarchy.lean::sph_seam_heads: 137/241 = 57%
  Disposition: same-file public-trajectory idiom. The same public seam case split supports different conclusions: exit-state avoidance and a physical head envelope.

   Hierarchy.lean::sph_emit_run  reproduces  Hierarchy.lean::sph_right_run: 490/915 = 54%
  Disposition: same-file leaf idiom. Reverse direction of the same permitted-leaf comparison.

New copies: none. No new pair rederives a foreign private declaration.
Historical first-screen finding: two pure mapState-composition calculations in sph_valid_machine were replaced by citations before this final run; see screen-first-final-classification.txt.

## ===== campaign/gates/109-h-landing-fill/evidence/screen/pairdiff-vs-base.txt =====

head pairs 1699; union of earlier 1689; new at head 10; earlier-only 0
  NEW   Hierarchy.lean::sph_verdict_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 339/402 = 84%
  NEW   Hierarchy.lean::sph_right_run  reproduces  Hierarchy.lean::sph_emit_run: 520/618 = 84%
  NEW   Hierarchy.lean::sph_rewinds_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 330/402 = 82%
  NEW   Hierarchy.lean::sph_valid_machine  reproduces  Hierarchy.lean::sph_witness_cap: 69/111 = 62%
  NEW   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_initial_record: 1059/1728 = 61%
  NEW   Hierarchy.lean::sph_valid_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 245/402 = 61%
  NEW   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_test_run: 836/1424 = 59%
  NEW   Hierarchy.lean::sph_validated_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 232/402 = 58%
  NEW   Hierarchy.lean::sph_emit_run  reproduces  Hierarchy.lean::sph_right_run: 520/957 = 54%
  NEW   Hierarchy.lean::sph_seam_avoids  reproduces  Hierarchy.lean::sph_seam_heads: 128/241 = 53%

## ===== campaign/gates/109-h-landing-fill/evidence/screen/pairdiff-vs-delivery.txt =====

head pairs 1699; union of earlier 1701; new at head 0; earlier-only 2
  GONE  Hierarchy.lean::sphWitnessSel  reproduces  Hierarchy.lean::sphInitSel: 70/88 = 80%
  GONE  Hierarchy.lean::sph_record_suffix  reproduces  InputRewind.lean::Cfg.mapState_mapState: 293/402 = 73%

## ===== campaign/gates/109-h-landing-fill/evidence/screen/screen-head.txt =====

declarations screened: 1894; copy pairs (target reproduces >= half of source): 1699; reproduced text: 539,014 chars
   Catalog.lean::f2_timed_branch_run  reproduces  Wrappers.lean::timed_branch_run: 1051/1051 = 100%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_pairCountTM  reproduces  Primitives.lean::pairCountTM: 860/860 = 100%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanCopy_suffix: 850/850 = 100%
   Nondeterminism.lean::a3n_poly_cond  reproduces  PolyTimePairing.lean::polyTimeComputable_ite: 802/802 = 100%
   Catalog.lean::f2_timedCondTM  reproduces  Wrappers.lean::timedCondTM: 802/802 = 100%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_pairExtractTM: 793/793 = 100%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::pairExtractTM: 793/793 = 100%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Catalog.lean::f2_splitPrepare_run  reproduces  Primitives.lean::splitPrepare_run: 632/632 = 100%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanTrues_run: 608/608 = 100%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 537/537 = 100%
   PolyTimePairing.lean::PolyTimeComputable.pairMapSnd  reproduces  Nondeterminism.lean::a3n_poly_map: 512/512 = 100%
   Nondeterminism.lean::a3n_poly_map  reproduces  PolyTimePairing.lean::PolyTimeComputable.pairMapSnd: 512/512 = 100%
   Catalog.lean::f2_catalogPolyCost_le  reproduces  Primitives.lean::catalogPolyCost_le: 485/485 = 100%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanCopy_run: 482/482 = 100%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_incFixedTM: 474/474 = 100%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::incFixedTM: 474/474 = 100%
   Catalog.lean::f2_timed_control_init  reproduces  Wrappers.lean::timed_control_init: 470/470 = 100%
   Primitives.lean::splitBody_envelope  reproduces  Catalog.lean::f2_splitBody_envelope: 466/466 = 100%
   Catalog.lean::f2_splitBody_envelope  reproduces  Primitives.lean::splitBody_envelope: 466/466 = 100%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_rawStripTM: 461/461 = 100%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::rawStripTM: 461/461 = 100%
   Catalog.lean::f2_splitEmit_run  reproduces  Primitives.lean::splitEmit_run: 440/440 = 100%
   Simulation.lean::timed_rewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Primitives.lean::catalogRewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Nondeterminism.lean::a2Buffer_write: 408/408 = 100%
   Primitives.lean::splitPrepareTM  reproduces  Catalog.lean::f2_splitPrepareTM: 399/399 = 100%
   Catalog.lean::f2_splitPrepareTM  reproduces  Primitives.lean::splitPrepareTM: 399/399 = 100%
   Primitives.lean::catalogMarker_cases  reproduces  Catalog.lean::f2_catalogMarker_cases: 396/396 = 100%
   Catalog.lean::f2_catalogMarker_cases  reproduces  Primitives.lean::catalogMarker_cases: 396/396 = 100%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairCount_computes  reproduces  Primitives.lean::pairCount_computes: 383/383 = 100%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::f2_splitPos_succ  reproduces  Primitives.lean::splitPos_succ: 353/353 = 100%
   Primitives.lean::incFixed_cases  reproduces  Catalog.lean::f2_incFixed_cases: 352/352 = 100%
   Catalog.lean::f2_incFixed_cases  reproduces  Primitives.lean::incFixed_cases: 352/352 = 100%
   Primitives.lean::splitEmitTM  reproduces  Catalog.lean::f2_splitEmitTM: 327/327 = 100%
   Catalog.lean::f2_splitEmitTM  reproduces  Primitives.lean::splitEmitTM: 327/327 = 100%
   Primitives.lean::emitter_take_succ_eq  reproduces  Nondeterminism.lean::e3c_take_succ_eq: 291/291 = 100%
   Nondeterminism.lean::e3c_take_succ_eq  reproduces  Primitives.lean::emitter_take_succ_eq: 291/291 = 100%
   Primitives.lean::splitLoop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 276/276 = 100%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::splitLoop_bound: 276/276 = 100%
   Primitives.lean::pairValidTM  reproduces  Catalog.lean::f2_pairValidTM: 249/249 = 100%
   Catalog.lean::f2_pairValidTM  reproduces  Primitives.lean::pairValidTM: 249/249 = 100%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::e3c_bits_injective: 227/227 = 100%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Primitives.lean::emitter_bits_injective: 227/227 = 100%
   InputCall.lean::inputSeekRewind  reproduces  InputRewind.lean::inputRewindTM: 215/215 = 100%
   Catalog.lean::f2_splitPos_read  reproduces  Primitives.lean::splitPos_read: 215/215 = 100%
   Primitives.lean::prependTM  reproduces  Catalog.lean::f2_catalogPrefixTM: 209/209 = 100%
   Catalog.lean::f2_catalogPrefixTM  reproduces  Primitives.lean::prependTM: 209/209 = 100%
   Catalog.lean::f2_splitStep_orbit  reproduces  Primitives.lean::splitStep_orbit: 201/201 = 100%
   Catalog.lean::f2_splitCountCfg  reproduces  Primitives.lean::splitCountCfg: 201/201 = 100%
   Primitives.lean::splitRewindTM  reproduces  Catalog.lean::f2_splitRewindTM: 185/185 = 100%
   Catalog.lean::f2_splitRewindTM  reproduces  Primitives.lean::splitRewindTM: 185/185 = 100%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::lenCfg: 177/177 = 100%
   Primitives.lean::anyTrueTM  reproduces  Catalog.lean::f2_anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_anyTrueTM  reproduces  Primitives.lean::anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_scanCfg_read  reproduces  Primitives.lean::scanCfg_read: 172/172 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Primitives.lean::splitCountAction  reproduces  Catalog.lean::f2_splitCountAction: 166/166 = 100%
   Catalog.lean::f2_splitCountAction  reproduces  Primitives.lean::splitCountAction: 166/166 = 100%
   Catalog.lean::f2_catalogPolyTape_write  reproduces  Primitives.lean::catalogPolyTape_write: 165/165 = 100%
   Finite.lean::runFrom_state_ne_none_of_le  reproduces  Catalog.lean::f2_loop_live_prefix: 156/156 = 100%
   Catalog.lean::f2_loop_live_prefix  reproduces  Finite.lean::runFrom_state_ne_none_of_le: 156/156 = 100%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::catalog_redirect_loop: 140/140 = 100%
   Catalog.lean::catalog_redirect_loop  reproduces  Wrappers.lean::redirect_loop: 140/140 = 100%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  Nondeterminism.lean::choiceVerifier: 136/136 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Primitives.lean::SplitBodyState  reproduces  Catalog.lean::f2_SplitBodyState: 134/134 = 100%
   Catalog.lean::f2_SplitBodyState  reproduces  Primitives.lean::SplitBodyState: 134/134 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Nondeterminism.lean::e3_split_spec  reproduces  Nondeterminism.lean::certificateSplit_spec: 125/125 = 100%
   Nondeterminism.lean::certificateSplit_spec  reproduces  Nondeterminism.lean::e3_split_spec: 125/125 = 100%
   Catalog.lean::f2_splitPrepareReady  reproduces  Primitives.lean::splitPrepareReady: 122/122 = 100%
   Primitives.lean::catalogBuffer_erase  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Primitives.lean::catalogBuffer_erase: 118/118 = 100%
   Primitives.lean::splitSafe_add  reproduces  Catalog.lean::f2_splitSafe_add: 110/110 = 100%
   Catalog.lean::f2_splitSafe_add  reproduces  Primitives.lean::splitSafe_add: 110/110 = 100%
   Primitives.lean::splitSafe_one  reproduces  Catalog.lean::f2_splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitSafe_one  reproduces  Primitives.lean::splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitRestoreScan: 106/106 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitPrepareScan: 97/97 = 100%
   Catalog.lean::f2_splitSafe_join  reproduces  Primitives.lean::splitSafe_join: 95/95 = 100%
   Wrappers.lean::timedBranchCfg  reproduces  Catalog.lean::f2_timedBranchCfg: 92/92 = 100%
   Catalog.lean::f2_timedBranchCfg  reproduces  Wrappers.lean::timedBranchCfg: 92/92 = 100%
   Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairEncodeFixed: 91/91 = 100%
   Wrappers.lean::timedControlCfg  reproduces  Catalog.lean::f2_timedControlCfg: 89/89 = 100%
   Primitives.lean::CatalogPolyControl  reproduces  Catalog.lean::f2_CatalogPolyControl: 89/89 = 100%
   Nondeterminism.lean::a2Buffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_timedControlCfg  reproduces  Wrappers.lean::timedControlCfg: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Nondeterminism.lean::a2Buffer_read: 89/89 = 100%
   Catalog.lean::f2_CatalogPolyControl  reproduces  Primitives.lean::CatalogPolyControl: 89/89 = 100%
   Rewind.lean::rw_cfg  reproduces  Catalog.lean::catalogSeekCfg: 79/79 = 100%
   Catalog.lean::catalogSeekCfg  reproduces  Rewind.lean::rw_cfg: 79/79 = 100%
   Wrappers.lean::redirectState  reproduces  Catalog.lean::catalog_redirectState: 78/78 = 100%
   Catalog.lean::catalog_redirectState  reproduces  Wrappers.lean::redirectState: 78/78 = 100%
   ConfigGraph.lean::outSummary_eq_empty_iff  reproduces  ConfigGraph.lean::outSummary_eq_accept_iff: 77/77 = 100%
   ConfigGraph.lean::outSummary_eq_accept_iff  reproduces  ConfigGraph.lean::outSummary_eq_empty_iff: 77/77 = 100%
   Wrappers.lean::timedPadTM  reproduces  Catalog.lean::f2_timedPadTM: 72/72 = 100%
   Catalog.lean::f2_timedPadTM  reproduces  Wrappers.lean::timedPadTM: 72/72 = 100%
   Catalog.lean::catalog_redirectAction  reproduces  Wrappers.lean::redirectAction: 71/71 = 100%
   CfgRecord.lean::Turing.{k#2  reproduces  CfgRecord.lean::Turing.{k#1: 66/66 = 100%
   CfgRecord.lean::Turing.{k#1  reproduces  CfgRecord.lean::Turing.{k#2: 66/66 = 100%
   PolyTimePairing.lean::polyTimeComputable_of_linear  reproduces  Nondeterminism.lean::a3n_poly_linear: 63/63 = 100%
   Nondeterminism.lean::a3n_poly_linear  reproduces  PolyTimePairing.lean::polyTimeComputable_of_linear: 63/63 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   Primitives.lean::splitRestoreClean  reproduces  Catalog.lean::f2_splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_splitRestoreClean  reproduces  Primitives.lean::splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   PClosure.lean::mem_P_of_blockXorAny  reproduces  PClosure.lean::mem_P_of_blockAny: 312/313 = 100%
   Wrappers.lean::timedCondTM  reproduces  Catalog.lean::f2_timedCondTM: 802/805 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Primitives.lean::emitterSplit_find  reproduces  Primitives.lean::splitFind_eq: 227/228 = 100%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  AlphabetReduction.lean::alphabet_reduction: 184/185 = 99%
   Catalog.lean::f2_timedReadyCfg  reproduces  Wrappers.lean::timedReadyCfg: 136/137 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   PolyTimePairing.lean::polyTimeComputable_ite  reproduces  Nondeterminism.lean::a3n_poly_cond: 802/809 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::emitterToken_separator: 213/215 = 99%
   Catalog.lean::catalog_redirectCfg  reproduces  Wrappers.lean::redirectCfg: 84/85 = 99%
   Catalog.lean::f2_catalogPolyUnaryTM  reproduces  Primitives.lean::catalogPolyUnaryTM: 788/798 = 99%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::extract_run: 1830/1854 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   Nondeterminism.lean::choiceVerifier  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 136/138 = 99%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanTrues_run: 608/617 = 99%
   Primitives.lean::splitStep_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 201/204 = 99%
   Primitives.lean::splitCountCfg  reproduces  Catalog.lean::f2_splitCountCfg: 201/204 = 99%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_suffix: 1125/1142 = 99%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitEmit_double: 1402/1424 = 98%
   Primitives.lean::lenCfg  reproduces  Catalog.lean::f2_lenCfg: 177/180 = 98%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Primitives.lean::catalogPoly_loop: 3777/3842 = 98%
   Catalog.lean::f2_splitBodyTM  reproduces  Primitives.lean::splitBodyTM: 676/688 = 98%
   Primitives.lean::catalogPolyCost_le  reproduces  Catalog.lean::f2_catalogPolyCost_le: 485/494 = 98%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Primitives.lean::catalogPoly_rewind: 1010/1030 = 98%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_copy: 705/719 = 98%
   Primitives.lean::splitEmit_run  reproduces  Catalog.lean::f2_splitEmit_run: 440/449 = 98%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 850/868 = 98%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::splitLoop_result: 226/231 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Nondeterminism.lean::a2BorrowPos_le: 89/91 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_timed_start  reproduces  Wrappers.lean::timed_start: 1025/1049 = 98%
   Primitives.lean::pairCount_computes  reproduces  Catalog.lean::f2_pairCount_computes: 383/392 = 98%
   Primitives.lean::emitterP2SmallIndex  reproduces  Primitives.lean::emitterP2PairIndex: 207/212 = 98%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay: 567/581 = 98%
   Primitives.lean::pairExtractTM_snd  reproduces  Primitives.lean::pairExtractTM_concat: 118/121 = 98%
   Primitives.lean::pairExtractTM_fst  reproduces  Primitives.lean::pairExtractTM_concat: 118/121 = 98%
   Wrappers.lean::timed_control_init  reproduces  Catalog.lean::f2_timed_control_init: 470/482 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::f2_rawStrip_erase  reproduces  Primitives.lean::rawStrip_erase: 345/354 = 97%
   Catalog.lean::f2_splitCount_run  reproduces  Primitives.lean::splitCount_run: 898/922 = 97%
   Catalog.lean::f2_catalogPrefixTM_computes  reproduces  Primitives.lean::prependTM_computes: 369/379 = 97%
   Nondeterminism.lean::choiceVerifier_no_split  reproduces  Nondeterminism.lean::e3_choice_no_split: 145/149 = 97%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::rawStrip_replay: 395/406 = 97%
   Primitives.lean::splitPos_read  reproduces  Catalog.lean::f2_splitPos_read: 215/221 = 97%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   Wrappers.lean::timed_branch_run  reproduces  Catalog.lean::f2_timed_branch_run: 1051/1081 = 97%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Primitives.lean::catalogPoly_unary_computes: 1223/1258 = 97%
   Wrappers.lean::timedReadyCfg  reproduces  Catalog.lean::f2_timedReadyCfg: 136/140 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   SingleTape.lean::sweepPos_move  reproduces  SingleTape.lean::dgPos_move: 67/69 = 97%
   Catalog.lean::f2_splitEmitCfg  reproduces  Primitives.lean::splitEmitCfg: 97/100 = 97%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_run: 482/497 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Primitives.lean::splitSafe_join  reproduces  Catalog.lean::f2_splitSafe_join: 95/98 = 97%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::splitFind_eq: 221/228 = 97%
   Primitives.lean::catalogPolyUnaryTM  reproduces  Catalog.lean::f2_catalogPolyUnaryTM: 788/813 = 97%
   Catalog.lean::f2_scanCopy_finish  reproduces  Primitives.lean::scanCopy_finish: 249/257 = 97%
   Wrappers.lean::computesFunInTime_cond  reproduces  Catalog.lean::f2_cond_time: 621/641 = 97%
   Primitives.lean::scanTrues_run  reproduces  Primitives.lean::scanStep_right: 153/158 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Primitives.lean::emitterP2_right_frame  reproduces  Primitives.lean::emitterP2_left_frame: 273/282 = 97%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::lenStart: 1606/1659 = 97%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_block: 633/654 = 97%
   PClosure.lean::lenLe_preimage_mem_P  reproduces  PClosure.lean::lenEq_preimage_mem_P: 60/62 = 97%
   PClosure.lean::lenEq_preimage_mem_P  reproduces  PClosure.lean::lenLe_preimage_mem_P: 60/62 = 97%
   NP.lean::verifier_poly_reverseBound  reproduces  PolyTimePairing.lean::polyTimeComputable_prepend: 60/62 = 97%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 537/555 = 97%
   Primitives.lean::pairExtractTM_concat  reproduces  Primitives.lean::pairExtractTM_snd: 118/122 = 97%
   Primitives.lean::pairExtractTM_concat  reproduces  Primitives.lean::pairExtractTM_fst: 118/122 = 97%
   Primitives.lean::pairCountTM  reproduces  Catalog.lean::f2_pairCountTM: 860/890 = 97%
   Primitives.lean::scanCfg_read  reproduces  Catalog.lean::f2_scanCfg_read: 172/178 = 97%
   Primitives.lean::splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 227/235 = 97%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay: 567/587 = 97%
   Primitives.lean::catalogPolyTape_write  reproduces  Catalog.lean::f2_catalogPolyTape_write: 165/171 = 96%
   Primitives.lean::emitterP2_left_frame  reproduces  Primitives.lean::emitterP2_right_frame: 273/283 = 96%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Primitives.lean::splitEmit_suffix: 1056/1095 = 96%
   Catalog.lean::f2_splitCount_over  reproduces  Primitives.lean::splitCount_over: 132/137 = 96%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_rewind: 718/746 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitRestore_scan: 799/831 = 96%
   Catalog.lean::f2_extract_first  reproduces  Primitives.lean::extract_first: 274/285 = 96%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 149/155 = 96%
   Catalog.lean::f2_extract_finish  reproduces  Primitives.lean::extract_finish: 595/619 = 96%
   Catalog.lean::f2_rawStrip_finish  reproduces  Primitives.lean::rawStrip_finish: 270/281 = 96%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM: 215/224 = 96%
   Primitives.lean::splitPos_succ  reproduces  Catalog.lean::f2_splitPos_succ: 353/368 = 96%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_extract_run: 1830/1908 = 96%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 395/412 = 96%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::pairDup_double: 1127/1176 = 96%
   Primitives.lean::splitBodyTM  reproduces  Catalog.lean::f2_splitBodyTM: 676/706 = 96%
   Nondeterminism.lean::certificateSplit_none_iff  reproduces  Nondeterminism.lean::e3_split_none_iff: 155/162 = 96%
   Primitives.lean::emitterP2_body_erase_right  reproduces  Primitives.lean::emitterP2_body_erase_left: 1078/1127 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_double: 1402/1466 = 96%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_block: 700/732 = 96%
   Wrappers.lean::timed_start  reproduces  Catalog.lean::f2_timed_start: 1025/1073 = 96%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 827/866 = 95%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 827/866 = 95%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitRestore_rewind: 754/790 = 95%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::splitEmit_separator: 730/765 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Primitives.lean::splitLoop_result  reproduces  Catalog.lean::f2_splitLoop_result: 226/237 = 95%
   Primitives.lean::computesFunInTime_stripLast  reproduces  Catalog.lean::f2_strip_linear: 1616/1695 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Primitives.lean::splitPrepareReady  reproduces  Catalog.lean::f2_splitPrepareReady: 122/128 = 95%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::extract_replay_finish: 284/298 = 95%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 719/755 = 95%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::f2_splitCount_run: 898/943 = 95%
   AlphabetReduction.lean::arTail_update  reproduces  AlphabetReduction.lean::arTape_update: 78/82 = 95%
   Primitives.lean::emitterP2_body_erase_left  reproduces  Primitives.lean::emitterP2_body_erase_right: 1078/1134 = 95%
   Nondeterminism.lean::e3_choice_append  reproduces  Nondeterminism.lean::choiceVerifier_append: 192/202 = 95%
   Primitives.lean::rawStrip_erase  reproduces  Catalog.lean::f2_rawStrip_erase: 345/363 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairFst: 149/157 = 95%
   Catalog.lean::f2_rawStrip_trim  reproduces  Primitives.lean::rawStrip_trim: 575/606 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   PClosure.lean::mem_P_of_blockAny  reproduces  PClosure.lean::mem_P_of_blockXorAny: 312/329 = 95%
   Nondeterminism.lean::a2_compile  reproduces  Nondeterminism.lean::b2_compile: 924/975 = 95%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_scan: 605/639 = 95%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 390/412 = 95%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitRestoreScan: 106/112 = 95%
   Primitives.lean::splitPrepare_run  reproduces  Catalog.lean::f2_splitPrepare_run: 632/668 = 95%
   Catalog.lean::f2_catalogPoly_copy  reproduces  Primitives.lean::catalogPoly_copy: 665/703 = 95%
   Catalog.lean::f2_catalogPoly_start  reproduces  Primitives.lean::catalogPoly_start: 833/881 = 95%
   Primitives.lean::catalogPoly_loop  reproduces  Catalog.lean::f2_catalogPoly_loop: 3777/3995 = 95%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_suffix: 1125/1190 = 95%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Catalog.lean::f2_catalogPoly_unary_computes: 1223/1294 = 95%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::RoundContract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::ReturnContract: 412/436 = 94%
   Primitives.lean::catalogPoly_rewind  reproduces  Catalog.lean::f2_catalogPoly_rewind: 1010/1069 = 94%
   Primitives.lean::lenStart  reproduces  Catalog.lean::f2_lenStart: 1606/1701 = 94%
   Primitives.lean::splitCount_over  reproduces  Catalog.lean::f2_splitCount_over: 132/140 = 94%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::splitSolve_of_body: 886/940 = 94%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_rewind: 663/704 = 94%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitPrepareScan: 97/103 = 94%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::rawStrip_copy: 699/743 = 94%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_extra: 424/451 = 94%
   Catalog.lean::f2_splitRestore_first  reproduces  Primitives.lean::splitRestore_first: 608/647 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   PClosure.lean::preimage_mem_NP  reproduces  PolyTimePairing.lean::polyTimeComputable_pairSwap: 61/65 = 94%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_block: 633/675 = 94%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Catalog.lean::f2_catalogPrefixTM_copy: 705/752 = 94%
   Primitives.lean::incFixedTM_computes  reproduces  Primitives.lean::scanStep_right: 148/158 = 94%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 220/235 = 94%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_rewind: 718/767 = 94%
   Catalog.lean::catalog_redirect_apply  reproduces  Wrappers.lean::redirect_apply: 175/187 = 94%
   Primitives.lean::pairExtractTM_snd  reproduces  Primitives.lean::pairExtractTM_fst: 114/122 = 93%
   Primitives.lean::pairExtractTM_fst  reproduces  Primitives.lean::pairExtractTM_snd: 114/122 = 93%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::pairExtractTM_snd: 114/122 = 93%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::pairExtractTM_fst: 114/122 = 93%
   Catalog.lean::f2_splitSolve_source  reproduces  Primitives.lean::splitSolve_source: 397/425 = 93%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::pairExtractTM_concat: 113/121 = 93%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_setup: 533/571 = 93%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::lenParse_run: 1533/1643 = 93%
   Primitives.lean::splitFind_eq  reproduces  Catalog.lean::f2_splitFind_eq: 221/237 = 93%
   Catalog.lean::f2_lenParse_first  reproduces  Primitives.lean::lenParse_first: 287/308 = 93%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   SingleTape.lean::dgPos_move  reproduces  SingleTape.lean::sweepPos_move: 67/72 = 93%
   Catalog.lean::f2_splitCount_accept  reproduces  Primitives.lean::splitCount_accept: 266/286 = 93%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_pairDup_double: 1127/1212 = 93%
   Primitives.lean::prependTM_computes  reproduces  Catalog.lean::f2_catalogPrefixTM_computes: 369/397 = 93%
   Catalog.lean::f2_timed_capture  reproduces  Wrappers.lean::timed_capture: 314/338 = 93%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_splitEmit_suffix: 1056/1137 = 93%
   Primitives.lean::emitterSplit_find  reproduces  Catalog.lean::f2_splitFind_eq: 220/237 = 93%
   SingleTape.lean::dg_sweep_reverse_prefix  reproduces  SingleTape.lean::dg_sweep_prefix: 232/250 = 93%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 799/861 = 93%
   Nondeterminism.lean::choiceVerifier_append  reproduces  Nondeterminism.lean::e3_choice_append: 192/207 = 93%
   Nondeterminism.lean::a2BorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 89/96 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 719/776 = 93%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 754/814 = 93%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_small_frame: 539/582 = 93%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_block: 700/756 = 93%
   Catalog.lean::f2_rawStrip_computes  reproduces  Primitives.lean::rawStrip_computes: 650/702 = 93%
   Primitives.lean::rawStrip_trim  reproduces  Catalog.lean::f2_rawStrip_trim: 575/621 = 93%
   Primitives.lean::scanCopy_finish  reproduces  Catalog.lean::f2_scanCopy_finish: 249/269 = 93%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_separator: 199/215 = 93%
   Primitives.lean::extract_finish  reproduces  Catalog.lean::f2_extract_finish: 595/643 = 93%
   Primitives.lean::extract_replay_finish  reproduces  Catalog.lean::f2_extract_replay_finish: 284/307 = 93%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_emit: 468/506 = 92%
   Catalog.lean::f2_pairExtract_computes  reproduces  Primitives.lean::pairExtractTM_computes: 443/479 = 92%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_pair_frame: 539/583 = 92%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanStep_right: 146/158 = 92%
   Catalog.lean::f2_timed_read  reproduces  Wrappers.lean::timed_read: 1692/1832 = 92%
   Nondeterminism.lean::e3_choice_no_split  reproduces  Nondeterminism.lean::choiceVerifier_no_split: 145/157 = 92%
   Catalog.lean::f2_cond_time  reproduces  Wrappers.lean::computesFunInTime_cond: 621/673 = 92%
   Primitives.lean::rawStrip_finish  reproduces  Catalog.lean::f2_rawStrip_finish: 270/293 = 92%
   Catalog.lean::f2_pairValid_run  reproduces  Primitives.lean::pairValid_run: 1083/1177 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenSuffix_run: 1436/1566 = 92%
   Primitives.lean::emitterP2PairIndex  reproduces  Primitives.lean::emitterP2SmallIndex: 207/226 = 92%
   Primitives.lean::splitEmitCfg  reproduces  Catalog.lean::f2_splitEmitCfg: 97/106 = 92%
   Primitives.lean::catalogPoly_copy  reproduces  Catalog.lean::f2_catalogPoly_copy: 665/727 = 91%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 663/725 = 91%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Nondeterminism.lean::b2_compile  reproduces  Nondeterminism.lean::a2_compile: 924/1011 = 91%
   Primitives.lean::extract_first  reproduces  Catalog.lean::f2_extract_first: 274/300 = 91%
   Catalog.lean::f2_anyTrue_computes  reproduces  Primitives.lean::anyTrue_computes: 231/253 = 91%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::incFixedTM_computes: 2332/2555 = 91%
   Primitives.lean::rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_copy: 699/767 = 91%
   Primitives.lean::splitCount_accept  reproduces  Catalog.lean::f2_splitCount_accept: 266/292 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::pairExtractTM_concat: 110/121 = 91%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::pairExtractTM_concat: 110/121 = 91%
   Catalog.lean::f2_splitPoly_loop_end  reproduces  Primitives.lean::splitPoly_loop_end: 639/703 = 91%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 605/666 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Primitives.lean::catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Primitives.lean::splitEmit_separator  reproduces  Catalog.lean::f2_splitEmit_separator: 730/804 = 91%
   Nondeterminism.lean::e3_split_none_iff  reproduces  Nondeterminism.lean::certificateSplit_none_iff: 155/171 = 91%
   Primitives.lean::splitRestore_first  reproduces  Catalog.lean::f2_splitRestore_first: 608/671 = 91%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanStep_right: 143/158 = 91%
   Wrappers.lean::timed_capture  reproduces  Catalog.lean::f2_timed_capture: 314/347 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 122/135 = 90%
   Wrappers.lean::redirectCfg  reproduces  Catalog.lean::catalog_redirectCfg: 84/93 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::pairExtractTM_snd: 110/122 = 90%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::pairExtractTM_fst: 110/122 = 90%
   Nondeterminism.lean::contSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   Primitives.lean::computesFunInTime_pairEncodeFixed  reproduces  Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed: 91/101 = 90%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_initial: 263/292 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Primitives.lean::mapParse_block  reproduces  Primitives.lean::mapParse_first: 244/271 = 90%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_lenParse_run: 1533/1703 = 90%
   Primitives.lean::catalogPoly_start  reproduces  Catalog.lean::f2_catalogPoly_start: 833/926 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Wrappers.lean::redirectAction  reproduces  Catalog.lean::catalog_redirectAction: 71/79 = 90%
   Primitives.lean::splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_extra: 424/472 = 90%
   Catalog.lean::f2_splitBody_round  reproduces  Primitives.lean::splitBody_round: 4481/4991 = 90%
   Primitives.lean::lenParse_first  reproduces  Catalog.lean::f2_lenParse_first: 287/320 = 90%
   Catalog.lean::catalog_redirect_step  reproduces  Wrappers.lean::redirect_step: 826/921 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   Catalog.lean::f2_splitScratch_erase  reproduces  Primitives.lean::splitScratch_erase: 139/155 = 90%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::e3_verifier_of_split: 929/1036 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 121/135 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 121/135 = 90%
   Primitives.lean::splitSolve_source  reproduces  Catalog.lean::f2_splitSolve_source: 397/443 = 90%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 276/308 = 90%
   Primitives.lean::splitBody_round  reproduces  Catalog.lean::f2_splitBody_round: 4481/5014 = 89%
   Primitives.lean::pairExtractTM_computes  reproduces  Catalog.lean::f2_pairExtract_computes: 443/497 = 89%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_setup: 533/598 = 89%
   SingleTape.lean::dg_sweep_prefix  reproduces  SingleTape.lean::dg_sweep_reverse_prefix: 232/261 = 89%
   Catalog.lean::catalog_redirect_run  reproduces  Wrappers.lean::redirect_run: 160/180 = 89%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_emit: 468/527 = 89%
   Nondeterminism.lean::cont_parse_double  reproduces  Nondeterminism.lean::cont_parse_separator: 579/652 = 89%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitRestore_append: 1052/1185 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenSuffix_run: 1436/1623 = 88%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::a3n_eq_separator: 1072/1212 = 88%
   Primitives.lean::rawStrip_computes  reproduces  Catalog.lean::f2_rawStrip_computes: 650/735 = 88%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::pairDup_computes: 1321/1494 = 88%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Catalog.lean::f2_splitSource_constant  reproduces  Primitives.lean::splitSource_constant: 398/451 = 88%
   WindowClock.lean::cw_seg_back  reproduces  WindowClock.lean::cw_seg_skipS: 308/350 = 88%
   Primitives.lean::pairValid_run  reproduces  Catalog.lean::f2_pairValid_run: 1083/1231 = 88%
   Catalog.lean::f2_scanStep_right  reproduces  Primitives.lean::scanStep_right: 139/158 = 88%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::choiceCore_finish: 285/324 = 88%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   SingleTape.lean::dgSpan_generate_left  reproduces  SingleTape.lean::dgSpan_generate_right: 359/409 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_timed_read: 1692/1931 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Primitives.lean::incFixedTM_computes  reproduces  Catalog.lean::f2_incFixed_computes: 2332/2675 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Primitives.lean::anyTrue_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 231/265 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::pairExtractTM_fst: 106/122 = 87%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::pairExtractTM_snd: 106/122 = 87%
   Primitives.lean::pairLenCheckTM_computes  reproduces  Catalog.lean::f2_first_length: 137/158 = 87%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 117/135 = 87%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 477/551 = 87%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 661/764 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Nondeterminism.lean::e3SplitWord  reproduces  Nondeterminism.lean::contSplitWord: 64/74 = 86%
   Primitives.lean::splitPoly_loop_end  reproduces  Catalog.lean::f2_splitPoly_loop_end: 639/739 = 86%
   Primitives.lean::splitScratch_erase  reproduces  Catalog.lean::f2_splitScratch_erase: 139/161 = 86%
   Wrappers.lean::redirect_apply  reproduces  Catalog.lean::catalog_redirect_apply: 175/203 = 86%
   Catalog.lean::f2_lenAction_apply  reproduces  Primitives.lean::lenAction_apply: 125/145 = 86%
   Catalog.lean::f2_catalogPrefixTM_emit  reproduces  Primitives.lean::catalogPrefixTM_emit: 295/343 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_strip_linear  reproduces  Primitives.lean::computesFunInTime_stripLast: 1616/1881 = 86%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 477/557 = 86%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_update_left: 542/633 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_control: 71/83 = 86%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 661/773 = 86%
   Primitives.lean::splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   Catalog.lean::f2_splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_ready_step: 539/632 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Cfg.SameOutside.keep_blank  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::endpoint_not_mem: 97/114 = 85%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Nondeterminism.lean::e3_step_orbit  reproduces  Primitives.lean::splitStep_orbit: 171/201 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Primitives.lean::splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 796/938 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::safeSegment_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::segment_iff: 84/99 = 85%
   Primitives.lean::scanStep_right  reproduces  Catalog.lean::f2_scanStep_right: 139/164 = 85%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::splitSolve_of_body: 796/940 = 85%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_run: 408/482 = 85%
   Catalog.lean::f2_splitCount_apply  reproduces  Primitives.lean::splitCount_apply: 725/857 = 85%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_rewind_input: 1256/1488 = 84%
   Catalog.lean::f2_splitRestore_run  reproduces  Primitives.lean::splitRestore_run: 762/903 = 84%
   Primitives.lean::pairDup_computes  reproduces  Catalog.lean::f2_pairDup_computes: 1321/1566 = 84%
   Hierarchy.lean::sph_verdict_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 339/402 = 84%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitRestore_append: 1052/1248 = 84%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::time_box  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::time_envelope: 123/146 = 84%
   Catalog.lean::f2_anyTrue_run  reproduces  Primitives.lean::anyTrue_run: 669/795 = 84%
   Hierarchy.lean::sph_right_run  reproduces  Hierarchy.lean::sph_emit_run: 520/618 = 84%
   CfgRecord.lean::recordStep_contract_clauses  reproduces  CfgRecord.lean::recordStep_contract_clauses_range: 122/145 = 84%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::e3_split_answer: 659/784 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Nondeterminism.lean::e3_step_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 171/204 = 84%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_splitBody_count  reproduces  Primitives.lean::splitBody_count: 483/577 = 84%
   InputRewind.lean::inputRewindTM  reproduces  InputCall.lean::inputSeekRewind: 215/257 = 84%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_update_right: 542/648 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Primitives.lean::emitterSplit_result  reproduces  Primitives.lean::splitLoop_result: 193/231 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 630/755 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_rewind: 447/538 = 83%
   Nondeterminism.lean::cont_parse_separator  reproduces  Nondeterminism.lean::cont_parse_double: 579/697 = 83%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 462/557 = 83%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::splitBody_prepare: 1263/1523 = 83%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 587/708 = 83%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::a3n_eq_double: 1072/1293 = 83%
   WindowRun.lean::wl_Ctrl_decidableEq  reproduces  WindowRun.lean::wr_Ctrl_decidableEq: 63/76 = 83%
   PClosure.lean::mem_P_of_blockAny  reproduces  PClosure.lean::mem_P_of_blockMajority: 120/145 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 599/725 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 253/308 = 82%
   Hierarchy.lean::sph_rewinds_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 330/402 = 82%
   PClosure.lean::mem_P_of_blockXorAny  reproduces  PClosure.lean::mem_P_of_blockMajority: 119/145 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::hullLo  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::hullHi: 114/139 = 82%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::hullHi  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::hullLo: 114/139 = 82%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 127/155 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_catalogPolyMove_apply  reproduces  Primitives.lean::catalogPolyMove_apply: 141/173 = 82%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 615/755 = 81%
   Primitives.lean::emitterSplit_result  reproduces  Catalog.lean::f2_splitLoop_result: 193/237 = 81%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   SingleTape.lean::sweep_init_block  reproduces  SingleTape.lean::sweep_grow_right_block: 428/526 = 81%
   SingleTape.lean::dg_end_with_growth  reproduces  SingleTape.lean::dg_end_without_growth: 371/456 = 81%
   Primitives.lean::splitSource_constant  reproduces  Catalog.lean::f2_splitSource_constant: 398/490 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::splitBody_restore: 405/499 = 81%
   Primitives.lean::catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   SingleTape.lean::sweep_turn_right  reproduces  SingleTape.lean::sweepRevCfg_write: 189/233 = 81%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 557/687 = 81%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::cont_choiceVerifier_mem_P: 929/1146 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_loopValue_bits  reproduces  Nondeterminism.lean::a2Value_bits: 106/131 = 81%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 127/157 = 81%
   Primitives.lean::anyTrue_run  reproduces  Catalog.lean::f2_anyTrue_run: 669/828 = 81%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 353/437 = 81%
   Primitives.lean::splitBody_count  reproduces  Catalog.lean::f2_splitBody_count: 483/598 = 81%
   Primitives.lean::splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_prepare_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_erase_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitSolve_closed  reproduces  Primitives.lean::splitSolve_closed: 310/385 = 81%
   Primitives.lean::catalogPrefixTM_emit  reproduces  Catalog.lean::f2_catalogPrefixTM_emit: 295/367 = 80%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step: 315/393 = 80%
   Primitives.lean::splitCount_apply  reproduces  Catalog.lean::f2_splitCount_apply: 725/905 = 80%
   Catalog.lean::skipBackTM  reproduces  Rewind.lean::rewindTM: 140/175 = 80%
   Primitives.lean::splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_rewind: 447/559 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 630/790 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Primitives.lean::lenAction_apply  reproduces  Catalog.lean::f2_lenAction_apply: 125/157 = 80%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Primitives.lean::emitterP2_control: 66/83 = 80%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_run: 395/497 = 79%
   Wrappers.lean::redirect_step  reproduces  Catalog.lean::catalog_redirect_step: 826/1041 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::extract_first: 226/285 = 79%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 615/776 = 79%
   Primitives.lean::splitRestore_run  reproduces  Catalog.lean::f2_splitRestore_run: 762/963 = 79%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanStep_right: 125/158 = 79%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 253/320 = 79%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 505/639 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   Catalog.lean::f2_pairValid_block  reproduces  Primitives.lean::pairValid_block: 370/470 = 79%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_rewind_choices: 1256/1596 = 79%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 557/708 = 79%
   Primitives.lean::catalogPayload_computes  reproduces  Nondeterminism.lean::a3n_comp_at: 343/436 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   WindowClock.lean::cw_seg_clockBack  reproduces  WindowClock.lean::cw_seg_skipC: 285/363 = 79%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::a2_exp_scheduler  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Wrappers.lean::redirect_run  reproduces  Catalog.lean::catalog_redirect_run: 160/204 = 78%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 408/521 = 78%
   Primitives.lean::splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_prepare: 1263/1613 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 436/557 = 78%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 599/767 = 78%
   Nondeterminism.lean::b2_rewind_step  reproduces  Nondeterminism.lean::b2_copy_done: 303/388 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Nondeterminism.lean::b2_unary_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 117/150 = 78%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopBorrow_step: 328/421 = 78%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 615/790 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::endpoint_not_mem  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::traj_iff: 80/103 = 78%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Frames.trans  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::traj_iff: 80/103 = 78%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Cfg.SameOutside.keep_blank  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::traj_iff: 80/103 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 549/708 = 78%
   Nondeterminism.lean::b2_copy_done  reproduces  Nondeterminism.lean::b2_rewind_step: 303/391 = 77%
   Primitives.lean::splitBody_restore  reproduces  Catalog.lean::f2_splitBody_restore: 405/523 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanStep_right: 122/158 = 77%
   SingleTape.lean::dgSpan_generate_right  reproduces  SingleTape.lean::dgSpan_generate_left: 359/465 = 77%
   Nondeterminism.lean::b2_host_bound  reproduces  Nondeterminism.lean::a2_host_bound: 381/494 = 77%
   Catalog.lean::f2_catalogPoly_advance  reproduces  Primitives.lean::catalogPoly_advance: 131/170 = 77%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_runFrom_one: 73/95 = 77%
   Primitives.lean::splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::splitLoop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 212/276 = 77%
   Catalog.lean::f2_splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Nondeterminism.lean::b2_ready_run  reproduces  Nondeterminism.lean::b2_rewind_run: 196/256 = 77%
   SingleTape.lean::sweepInput_read  reproduces  SingleTape.lean::dgInput_read: 189/247 = 77%
   SingleTape.lean::sweep_grow_left_block  reproduces  SingleTape.lean::sweep_init_block: 446/583 = 77%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 717/938 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Nondeterminism.lean::a2Buffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Primitives.lean::catalogPolyMove_apply  reproduces  Catalog.lean::f2_catalogPolyMove_apply: 141/185 = 76%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 408/537 = 76%
   ConfigCount.lean::visitedByTapeHead_mono  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  Deterministic.lean::mem_visitedByTapeHead_iff: 60/79 = 76%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 587/773 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 395/521 = 76%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairFst: 119/157 = 76%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 119/157 = 76%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::round_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::segment_iff: 75/99 = 76%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Nondeterminism.lean::b2_guess_return  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRet_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 615/814 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Nondeterminism.lean::a2Value_bits  reproduces  Catalog.lean::f2_loopValue_bits: 106/141 = 75%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::extract_replay_finish: 224/298 = 75%
   Primitives.lean::splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 672/896 = 75%
   Catalog.lean::f2_pairValid_computes  reproduces  Primitives.lean::pairValidTM_computes: 216/288 = 75%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 338/451 = 75%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Primitives.lean::pairValid_block  reproduces  Catalog.lean::f2_pairValid_block: 370/494 = 75%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Primitives.lean::splitSolve_closed  reproduces  Catalog.lean::f2_splitSolve_closed: 310/415 = 75%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 236/316 = 75%
   Nondeterminism.lean::e3_split_answer  reproduces  Nondeterminism.lean::cont_split_answer: 659/883 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::f2_loopBorrow_step  reproduces  Nondeterminism.lean::a2Borrow_step: 328/440 = 75%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_ready_done: 539/724 = 74%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 353/476 = 74%
   Primitives.lean::emitterP2_body_length  reproduces  Primitives.lean::emitterP2_body_width: 493/665 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 100/135 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 100/135 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Catalog.lean::f2_splitEmbed_run: 139/188 = 74%
   Primitives.lean::extract_block  reproduces  Primitives.lean::extract_first: 210/285 = 74%
   Primitives.lean::splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::segment_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::round_iff: 75/102 = 74%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::safeSegment_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::round_iff: 75/102 = 74%
   Encoding.lean::exists_codeTM_spaceUsed  reproduces  Encoding.lean::FinTM.toCodeTM_computesInTime_iff: 75/102 = 74%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 408/555 = 74%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::endpoint_not_mem  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_step: 315/429 = 73%
   SingleTape.lean::sweep_grow_right_block  reproduces  SingleTape.lean::sweep_init_block: 428/583 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Primitives.lean::emitterP2_body_width  reproduces  Primitives.lean::emitterP2_body_length: 493/674 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Nondeterminism.lean::a2Buffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Primitives.lean::mapStart  reproduces  Primitives.lean::lenStart: 1210/1659 = 73%
   SingleTape.lean::dgStart  reproduces  SingleTape.lean::sweepStart: 148/203 = 73%
   Primitives.lean::pairExtractTM_concat  reproduces  Primitives.lean::computesFunInTime_pairConcat: 113/155 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::ReturnContract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::RoundContract: 412/566 = 73%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 500/687 = 73%
   WindowClock.lean::cw_seg_skipS  reproduces  WindowClock.lean::cw_seg_back: 308/424 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Primitives.lean::pairExtractTM_snd  reproduces  Primitives.lean::computesFunInTime_pairSnd: 114/157 = 73%
   Primitives.lean::pairExtractTM_fst  reproduces  Primitives.lean::computesFunInTime_pairFst: 114/157 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   AlphabetReduction.lean::arWriteCfg  reproduces  AlphabetReduction.lean::arMoveCfg: 113/156 = 72%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 366/506 = 72%
   Primitives.lean::splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 326/451 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 496/687 = 72%
   SingleTape.lean::sweepStart  reproduces  SingleTape.lean::dgStart: 148/205 = 72%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Primitives.lean::catalogPoly_advance  reproduces  Catalog.lean::f2_catalogPoly_advance: 131/182 = 72%
   Primitives.lean::emitterSplit_find  reproduces  Nondeterminism.lean::e3_find_eq: 123/171 = 72%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_initial: 210/292 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::a2Buffer_read: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_loopBuffer_read: 64/89 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 549/764 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::locate  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::cut: 219/305 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Primitives.lean::emitterSplit_of_body  reproduces  Primitives.lean::splitSolve_of_body: 672/940 = 71%
   Wrappers.lean::emit_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Wrappers.lean::capture_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Primitives.lean::splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Primitives.lean::splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Catalog.lean::f2_splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Nondeterminism.lean::choice_certificate_iff  reproduces  Nondeterminism.lean::e3_choice_certificate: 158/222 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_counterInc_bits  reproduces  Nondeterminism.lean::a2Value_bits: 93/131 = 71%
   Primitives.lean::pairExtractTM_snd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 110/155 = 71%
   Primitives.lean::pairExtractTM_fst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 110/155 = 71%
   Nondeterminism.lean::NP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_eq_iUnion_NTIME: 66/93 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 635/896 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Primitives.lean::pairValidTM_computes  reproduces  Catalog.lean::f2_pairValid_computes: 216/306 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 393/557 = 71%
   Primitives.lean::lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay_finish: 210/298 = 70%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Nondeterminism.lean::NEXP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_eq_iUnion_NTIME: 66/94 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::traj_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Frames.trans  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::endpoint_not_mem: 80/114 = 70%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 209/298 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Primitives.lean::splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Primitives.lean::pairExtractTM_concat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 110/157 = 70%
   Primitives.lean::pairExtractTM_concat  reproduces  Primitives.lean::computesFunInTime_pairFst: 110/157 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Nondeterminism.lean::a3n_scaled_envelope  reproduces  Nondeterminism.lean::a2_envelope: 535/766 = 70%
   Catalog.lean::f2_loopDebit  reproduces  Nondeterminism.lean::a2Debit: 62/89 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipBackTM: 140/202 = 69%
   Primitives.lean::splitSolveWithTM_computes  reproduces  Primitives.lean::emitterP2_closed: 1437/2075 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Nondeterminism.lean::cont_start_core  reproduces  Nondeterminism.lean::cont_write_apply: 221/320 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 380/551 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   CfgRecord.lean::recordStep_contract_clauses_range  reproduces  CfgRecord.lean::recordStep_contract_clauses: 122/177 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Primitives.lean::unaryTokenTM  reproduces  Primitives.lean::pairDupTM: 266/386 = 69%
   Primitives.lean::unaryTokenTM  reproduces  Catalog.lean::f2_pairDupTM: 266/386 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 93/135 = 69%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 1037/1506 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_double: 533/775 = 69%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::emit_run: 430/626 = 69%
   Primitives.lean::emitterP2_erase_run  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   WindowClock.lean::cw_cfg_moveL  reproduces  WindowClock.lean::cw_cfg_move₀: 118/172 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_loopDebit_value  reproduces  Nondeterminism.lean::a2Debit_value: 128/187 = 68%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 210/307 = 68%
   Primitives.lean::rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Nondeterminism.lean::cont_parse_run  reproduces  Nondeterminism.lean::a3n_eq_parse: 350/512 = 68%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 356/521 = 68%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Wrappers.lean::emit_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Wrappers.lean::capture_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Primitives.lean::splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::f2_splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::a2_mapSetup_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   WindowClock.lean::cw_cfg_box  reproduces  WindowClock.lean::cw_cfg_pos_zero: 96/141 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   SingleTape.lean::one_work_tape_binary_spaceUsed  reproduces  SingleTape.lean::one_work_tape_binary: 305/448 = 68%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 306/451 = 68%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_right_frame: 192/283 = 68%
   PolyTimePairing.lean::PolyTimeComputable.pairEncode  reproduces  PolyTimePairing.lean::PolyTimeComputable.append: 97/143 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   Primitives.lean::emitterSplit_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 635/938 = 68%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 432/639 = 68%
   Primitives.lean::mapStart  reproduces  Catalog.lean::f2_lenStart: 1149/1701 = 68%
   Primitives.lean::pairExtractTM_snd  reproduces  Primitives.lean::computesFunInTime_pairFst: 106/157 = 68%
   Primitives.lean::pairExtractTM_fst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 106/157 = 68%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::phaseHostTM_run  reproduces  InputRewind.lean::Cfg.mapState_mapState: 270/402 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanStep_right: 106/158 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_right_frame: 189/283 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Primitives.lean::emitterP2_body_prepare  reproduces  Primitives.lean::emitterP2_body_compare: 566/849 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  WindowClock.lean::FinTM.inWindow_of_spaceUsed_le: 336/505 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Nondeterminism.lean::b2_guess_run  reproduces  Nondeterminism.lean::cont_guess_run: 151/227 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 270/406 = 67%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::unaryTokenTM: 266/400 = 66%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::unaryTokenTM: 266/400 = 66%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Nondeterminism.lean::b2_rewind_run  reproduces  Nondeterminism.lean::b2_ready_run: 196/295 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 390/587 = 66%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilent_apply  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmit_apply: 168/253 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 365/551 = 66%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 593/896 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 203/307 = 66%
   Nondeterminism.lean::e3_choice_certificate  reproduces  Nondeterminism.lean::choice_certificate_iff: 158/239 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 68/103 = 66%
   Primitives.lean::splitSolve_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 886/1343 = 66%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_left_frame: 186/282 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 363/551 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   AlphabetReduction.lean::arWriteCfg_finish  reproduces  AlphabetReduction.lean::arMoveCfg_finish: 166/253 = 66%
   Primitives.lean::extract_run  reproduces  Primitives.lean::lenParse_run: 1077/1643 = 66%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 500/764 = 65%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 195/298 = 65%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   RecordTable.lean::rt_tailState_decidableEq  reproduces  RecordTable.lean::rt_tailState_fintype: 64/98 = 65%
   Catalog.lean::f2_catalogPair_inverse  reproduces  Nondeterminism.lean::a3n_pair_inverse: 220/337 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   SingleTape.lean::sweep_grow_left_block  reproduces  SingleTape.lean::sweep_grow_right_block: 343/526 = 65%
   SingleTape.lean::sweep_init_block  reproduces  SingleTape.lean::sweep_grow_left_block: 446/684 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 88/135 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 88/135 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Primitives.lean::lenStart  reproduces  Primitives.lean::mapStart: 1210/1864 = 65%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_left_frame: 183/282 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 432/666 = 65%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 306/472 = 65%
   Nondeterminism.lean::a2_host_bound  reproduces  Nondeterminism.lean::b2_host_bound: 381/588 = 65%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 106/164 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanStep_right: 102/158 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::lenParse_run: 1057/1643 = 64%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 321/499 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   SingleTape.lean::dgInput_read  reproduces  SingleTape.lean::sweepInput_read: 189/294 = 64%
   Nondeterminism.lean::cont_split_length  reproduces  Nondeterminism.lean::e3_split_length: 90/140 = 64%
   SingleTape.lean::dg_unused_space  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 81/126 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 496/773 = 64%
   Primitives.lean::splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_setup: 366/571 = 64%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 259/406 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 195/307 = 64%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 80/126 = 63%
   Primitives.lean::splitSolve_source  reproduces  Primitives.lean::split_hyps: 266/419 = 63%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Primitives.lean::emitterP2_body_compare  reproduces  Primitives.lean::emitterP2_body_prepare: 566/894 = 63%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::scanStep_right: 100/158 = 63%
   SingleTape.lean::dg_turn_with_growth  reproduces  SingleTape.lean::dg_turn_without_growth: 462/730 = 63%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanCopy_run: 305/482 = 63%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitPrepare_rewind: 477/755 = 63%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 348/551 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Bin.lean::bits_getLast  reproduces  Bin.lean::bitsVal_bits: 251/398 = 63%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitPrepare_rewind: 476/755 = 63%
   Nondeterminism.lean::a3n_eq_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 199/316 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 259/412 = 63%
   SingleTape.lean::dg_unused_space  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 71/113 = 63%
   Primitives.lean::pairLenCheckTM_computes  reproduces  Primitives.lean::catalogPayload_length: 125/199 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Nondeterminism.lean::a2Debit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Primitives.lean::split_hyps  reproduces  Primitives.lean::splitSolve_source: 266/425 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_cond_ledger  reproduces  Wrappers.lean::timed_start: 655/1049 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 272/437 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 102/164 = 62%
   Hierarchy.lean::sph_valid_machine  reproduces  Hierarchy.lean::sph_witness_cap: 69/111 = 62%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1057/1703 = 62%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::RoundContract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Contract: 302/487 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Primitives.lean::pairExtractTM_concat: 75/121 = 62%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Primitives.lean::pairExtractTM_concat: 75/121 = 62%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Primitives.lean::pairExtractTM_concat: 75/121 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_branch_space  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 70/113 = 62%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 91/147 = 62%
   WindowClock.lean::cw_prev  reproduces  WindowClock.lean::cw_next: 65/105 = 62%
   Primitives.lean::lenCfg  reproduces  Primitives.lean::mapCfg: 99/160 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Primitives.lean::pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 447/725 = 62%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 254/412 = 62%
   Primitives.lean::mapStart  reproduces  Nondeterminism.lean::cont_pair_empty: 90/146 = 62%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::mapStart: 1149/1864 = 62%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Deterministic.lean::timed_input_bound  reproduces  Catalog.lean::f2_loop_input_run_le: 224/364 = 62%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Primitives.lean::pairExtractTM_snd: 75/122 = 61%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Primitives.lean::pairExtractTM_fst: 75/122 = 61%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Primitives.lean::pairExtractTM_snd: 75/122 = 61%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Primitives.lean::pairExtractTM_fst: 75/122 = 61%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Primitives.lean::pairExtractTM_snd: 75/122 = 61%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Primitives.lean::pairExtractTM_fst: 75/122 = 61%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitPrepare_rewind: 477/776 = 61%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::a2_copy_step: 325/529 = 61%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_first: 175/285 = 61%
   Primitives.lean::lenParse_block  reproduces  Primitives.lean::lenParse_first: 189/308 = 61%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitPrepare_rewind: 476/776 = 61%
   Wrappers.lean::emit_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Wrappers.lean::capture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Primitives.lean::splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_initial_record: 1059/1728 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 188/307 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 506/828 = 61%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentCfg: 165/270 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   SingleTape.lean::dg_left_span  reproduces  SingleTape.lean::dg_right_span: 312/511 = 61%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 318/521 = 61%
   Primitives.lean::incFixedTM_computes  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   WindowClock.lean::cw_red  reproduces  WindowClock.lean::cw_next: 64/105 = 61%
   Hierarchy.lean::sph_valid_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 245/402 = 61%
   Nondeterminism.lean::a3n_pair_inverse  reproduces  Catalog.lean::f2_catalogPair_inverse: 220/361 = 61%
   SingleTape.lean::tapeZone_length  reproduces  SingleTape.lean::read_zone: 78/128 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Wrappers.lean::captureCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 129/212 = 61%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 505/831 = 61%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::capture_run: 430/708 = 61%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 68/112 = 61%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::traj_iff  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Frames.trans  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_tag: 209/346 = 60%
   Nondeterminism.lean::a2Debit_value  reproduces  Catalog.lean::f2_loopDebit_value: 128/212 = 60%
   RecordTable.lean::rt_tailState_fintype  reproduces  RecordTable.lean::rt_tailState_decidableEq: 64/106 = 60%
   Primitives.lean::mapBuffer_rewind  reproduces  Primitives.lean::mapPayload_replay: 372/617 = 60%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Nondeterminism.lean::cont_core_run: 170/282 = 60%
   Primitives.lean::mapParse_first  reproduces  Primitives.lean::mapParse_block: 244/405 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::rawStrip_erase: 213/354 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 461/767 = 60%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Nondeterminism.lean::cont_mask_count  reproduces  Nondeterminism.lean::b2_unary_run: 81/135 = 60%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanCopy_run: 289/482 = 60%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanCopy_finish: 154/257 = 60%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Primitives.lean::emitter_compare_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 189/316 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 382/639 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::splitBody_rewind: 321/538 = 60%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_first: 170/285 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Primitives.lean::emitter_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_counter_rewind  reproduces  Primitives.lean::emitterToken_separator: 128/215 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 461/776 = 59%
   RecordTable.lean::rt_position_run  reproduces  RecordTable.lean::rt_moveWord_run: 954/1606 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::mapCfg: 95/160 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   RecordTable.lean::rt_initRestTM  reproduces  RecordTable.lean::rt_tailTM: 113/191 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitRestore_rewind: 467/790 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/215 = 59%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/215 = 59%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/215 = 59%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/215 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 889/1506 = 59%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitRestore_rewind: 466/790 = 59%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Hierarchy.lean::sph_runner_run  reproduces  Hierarchy.lean::sph_test_run: 836/1424 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_scan_preserves: 339/578 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 448/764 = 59%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 79/135 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 447/764 = 59%
   Nondeterminism.lean::NP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_subset_iUnion_NTIME: 62/106 = 58%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 448/767 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_first: 175/300 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 289/497 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Primitives.lean::incFixedTM_computes  reproduces  Primitives.lean::emitterToken_separator: 125/215 = 58%
   Encoding.lean::pairDiag_separator  reproduces  Primitives.lean::emitterToken_separator: 125/215 = 58%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/215 = 58%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::extract_run: 1077/1854 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   SingleTape.lean::sweepRevCfg_write  reproduces  SingleTape.lean::sweep_turn_right: 189/326 = 58%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   WindowRun.lean::windowRun_spec  reproduces  WindowRun.lean::windowRun_exhausted_of_live: 313/541 = 58%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Catalog.lean::f2_loopBody_run  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 443/767 = 58%
   Hierarchy.lean::sph_validated_machine  reproduces  InputRewind.lean::Cfg.mapState_mapState: 232/402 = 58%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Nondeterminism.lean::a2_envelope  reproduces  Nondeterminism.lean::a3n_scaled_envelope: 535/929 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 237/412 = 58%
   Primitives.lean::catalogPayload_computes  reproduces  Primitives.lean::pairExtractTM_snd: 70/122 = 57%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitRestore_rewind: 467/814 = 57%
   SingleTape.lean::dg_end_with_growth  reproduces  SingleTape.lean::dg_turn_with_growth: 736/1283 = 57%
   Primitives.lean::splitSolve_closed  reproduces  Primitives.lean::split_sources: 196/342 = 57%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::cont_split_length: 110/192 = 57%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitRestore_rewind: 466/814 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::time_envelope  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::time_box: 123/215 = 57%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::cont_write_apply: 183/320 = 57%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 1037/1814 = 57%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::extract_run: 1057/1854 = 57%
   AlphabetReduction.lean::arCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::runFrom: 94/165 = 57%
   Nondeterminism.lean::b2_initial  reproduces  Simulation.lean::leftCfg_apply: 107/188 = 57%
   Simulation.lean::runFrom_eq_of_agreeOn  reproduces  ConfigCount.lean::core_runFrom: 62/109 = 57%
   Catalog.lean::f2_loopBodyCfg  reproduces  Wrappers.lean::captureCfg: 129/227 = 57%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/215 = 57%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/215 = 57%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_first: 170/300 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   Wrappers.lean::emit_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Wrappers.lean::capture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Catalog.lean::f2_splitSolve_source  reproduces  Primitives.lean::split_hyps: 237/419 = 57%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Primitives.lean::pairExtractTM_fst: 69/122 = 57%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 427/755 = 57%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Nondeterminism.lean::b2_unary_run  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 178/316 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Primitives.lean::catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 76/135 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_control_heads: 95/169 = 56%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Nondeterminism.lean::e3_shift_scan  reproduces  Catalog.lean::f2_idTM_run: 434/773 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   ConfigCount.lean::ComputesInTime.spaceUsed_le_of_halt  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 64/114 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1699/3028 = 56%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   SingleTape.lean::dg_collect  reproduces  SingleTape.lean::dg_read: 120/214 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::seekStartTM  reproduces  Rewind.lean::rewindTM: 98/175 = 56%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Primitives.lean::mapCfg  reproduces  Primitives.lean::lenCfg: 99/177 = 56%
   Nondeterminism.lean::a3n_eq_parse  reproduces  Nondeterminism.lean::cont_parse_run: 350/626 = 56%
   RecordTable.lean::rt_richWindow_run  reproduces  RecordTable.lean::rt_moveWord_run: 897/1606 = 56%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_first: 172/308 = 56%
   Catalog.lean::a2_map_parse  reproduces  Primitives.lean::extract_run: 1035/1854 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_frame: 63/113 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 63/113 = 56%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 63/113 = 56%
   Nondeterminism.lean::b2_initial  reproduces  Simulation.lean::rightCfg_apply: 107/192 = 56%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::scanStep_right: 88/158 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::runFrom  reproduces  AlphabetReduction.lean::arCfg_run: 94/169 = 56%
   SingleTape.lean::dg_init  reproduces  SingleTape.lean::dg_right_span: 284/511 = 56%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::pairDup_double: 653/1176 = 56%
   Catalog.lean::f2_idTM_run  reproduces  Nondeterminism.lean::e3_shift_scan: 434/782 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::pairDup_double: 652/1176 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Primitives.lean::rawStrip_replay: 225/406 = 55%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1057/1908 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 175/316 = 55%
   Primitives.lean::computesFunInTime_stripLast  reproduces  Primitives.lean::stripLastTM_computes: 506/914 = 55%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 93/168 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 479/866 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 479/866 = 55%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanCopy_finish: 142/257 = 55%
   Primitives.lean::splitSolveTM_spaceUsed  reproduces  Primitives.lean::splitSolveTM_computes: 364/659 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipTM: 71/129 = 55%
   Nondeterminism.lean::cont_select_length  reproduces  Nondeterminism.lean::contSelect_eq_maskSelect: 71/129 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 427/776 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::unaryTokenTM: 220/400 = 55%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::unaryTokenTM: 220/400 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Primitives.lean::catalogRewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::splitPrepare_rewind: 414/755 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Nondeterminism.lean::b2_unary_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Primitives.lean::emitter_compare_run  reproduces  Primitives.lean::emitterP2_erase_scan: 173/316 = 55%
   SingleTape.lean::write_zone  reproduces  SingleTape.lean::read_zone: 70/128 = 55%
   SingleTape.lean::dg_right_span  reproduces  SingleTape.lean::dg_left_span: 312/571 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Catalog.lean::f2_rawStrip_replay: 225/412 = 55%
   Primitives.lean::splitRestore_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::splitPrepare_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::scanCopy_run  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::rawStrip_replay  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::rawStrip_copy  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::mapPayload_replay  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Primitives.lean::extract_replay  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_splitRestore_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_splitPrepare_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_scanCopy_run  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_rawStrip_replay  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_rawStrip_copy  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_extract_replay  reproduces  AlphabetReduction.lean::arReadCfg_run: 103/189 = 54%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Primitives.lean::extract_run  reproduces  Primitives.lean::pairValid_run: 641/1177 = 54%
   Primitives.lean::catalogPayload_length  reproduces  Catalog.lean::f2_first_length: 86/158 = 54%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 443/814 = 54%
   Primitives.lean::extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Nondeterminism.lean::NEXP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_subset_iUnion_NTIME: 62/114 = 54%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 275/506 = 54%
   Hierarchy.lean::sph_emit_run  reproduces  Hierarchy.lean::sph_right_run: 520/957 = 54%
   Wrappers.lean::timed_control_init  reproduces  Nondeterminism.lean::cont_guess_initial: 113/208 = 54%
   Catalog.lean::f2_timed_control_init  reproduces  Nondeterminism.lean::cont_guess_initial: 113/208 = 54%
   VirtualInput.lean::vhostCfg  reproduces  Simulation.lean::bufferedSecondCfg: 126/232 = 54%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_ready_done: 393/724 = 54%
   Catalog.lean::a2_map_block  reproduces  Primitives.lean::extract_block: 355/654 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Wrappers.lean::timed_branch_run  reproduces  Nondeterminism.lean::cont_core_run: 153/282 = 54%
   Catalog.lean::f2_timed_branch_run  reproduces  Nondeterminism.lean::cont_core_run: 153/282 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Primitives.lean::catalogBuffer_erase: 64/118 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   SingleTape.lean::read_zone  reproduces  SingleTape.lean::tapeZone_length: 78/144 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 469/866 = 54%
   Primitives.lean::pairValidTM_computes  reproduces  Primitives.lean::anyTrue_computes: 137/253 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::pairValid_run: 637/1177 = 54%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::splitBody_restore: 270/499 = 54%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Primitives.lean::splitPoly_loop_end: 380/703 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 468/866 = 54%
   Nondeterminism.lean::cont_mask_count  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 81/150 = 54%
   Primitives.lean::splitEmbed_cut  reproduces  AlphabetReduction.lean::arReadCfg_run: 102/189 = 54%
   Primitives.lean::emitterAppend_run  reproduces  AlphabetReduction.lean::arReadCfg_run: 102/189 = 54%
   Catalog.lean::f2_splitEmbed_cut  reproduces  AlphabetReduction.lean::arReadCfg_run: 102/189 = 54%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/215 = 54%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/215 = 54%
   Primitives.lean::splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 652/1212 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 172/320 = 54%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitEmit_separator: 411/765 = 54%
   AlphabetReduction.lean::arReadCfg_run  reproduces  AlphabetReduction.lean::arWriteCfg_run: 94/175 = 54%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_copyback_run: 1276/2377 = 54%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 242/451 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_guess_return: 316/590 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::splitFind_eq: 122/228 = 54%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   Primitives.lean::split_hyps  reproduces  Catalog.lean::f2_splitSolve_source: 237/443 = 53%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   Nondeterminism.lean::e3_split_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 717/1343 = 53%
   TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::Contract  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Primitives.lean::splitSolveWithTM_computes  reproduces  Primitives.lean::split_fuel: 104/195 = 53%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_runFrom_pos  reproduces  Nondeterminism.lean::b2_unary_run: 72/135 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_guess_return: 314/590 = 53%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 91/171 = 53%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 340/639 = 53%
   Primitives.lean::emitterP2_frame  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedEmitCfg_eq: 227/427 = 53%
   Hierarchy.lean::sph_seam_avoids  reproduces  Hierarchy.lean::sph_seam_heads: 128/241 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Primitives.lean::emitter_compare_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 100/189 = 53%
   Primitives.lean::emitterP2_prepare_suffix  reproduces  AlphabetReduction.lean::arReadCfg_run: 100/189 = 53%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  AlphabetReduction.lean::arReadCfg_run: 100/189 = 53%
   Primitives.lean::emitterP2_erase_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 100/189 = 53%
   Nondeterminism.lean::a3n_eq_scan  reproduces  AlphabetReduction.lean::arReadCfg_run: 100/189 = 53%
   Primitives.lean::splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_scan: 338/639 = 53%
   SingleTape.lean::dg_turn_without_growth  reproduces  SingleTape.lean::dg_end_without_growth: 241/456 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Primitives.lean::catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Primitives.lean::mapCfg  reproduces  Catalog.lean::f2_lenCfg: 95/180 = 53%
   Primitives.lean::mapValidate  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Deterministic.lean::mem_visitedByTapeHead_iff  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 60/114 = 53%
   TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  TCSlib/Complexity/TuringMachine/Build/Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   WindowRun.lean::windowRun_spec  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   InputRewind.lean::inputRewindTM_run  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Catalog.lean::seekEndTM  reproduces  Rewind.lean::rewindTM: 92/175 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::scanStep_right: 83/158 = 53%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_finish: 135/257 = 53%
   WindowClock.lean::cw_cfg_moveL  reproduces  WindowClock.lean::cw_cfg_pos_zero: 74/141 = 52%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/343 = 52%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/343 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 292/557 = 52%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::emitterSplit_find: 123/235 = 52%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 275/527 = 52%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   RecordTable.lean::rt_tail_run  reproduces  RecordTable.lean::rt_moveWord_run: 836/1606 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Primitives.lean::catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 432/831 = 52%
   Primitives.lean::pairValid_run  reproduces  Primitives.lean::anyTrue_run: 413/795 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Primitives.lean::rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::a2Borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Nondeterminism.lean::b2_rewind_done  reproduces  AlphabetReduction.lean::arCfg_init: 72/139 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_rawStrip_erase: 188/363 = 52%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_pairValid_run: 637/1231 = 52%
   Nondeterminism.lean::b2_verify_step  reproduces  Nondeterminism.lean::b2_ready_step: 327/632 = 52%
   Primitives.lean::splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/215 = 52%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/215 = 52%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/215 = 52%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/215 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Catalog.lean::a2_mapSetup_run: 84/163 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Catalog.lean::f2_splitFind_eq: 122/237 = 51%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Simulation.lean::bufferedScanCfg_run  reproduces  Primitives.lean::rawStrip_rewind: 362/704 = 51%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::scanCopy_suffix: 437/850 = 51%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::b2_rewind_step: 201/391 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::pairValid_run: 605/1177 = 51%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Nondeterminism.lean::a2Borrow_correct: 166/323 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 388/755 = 51%
   AlphabetReduction.lean::arTail_update  reproduces  AlphabetReduction.lean::arBuffer_update: 78/152 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Primitives.lean::catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 242/472 = 51%
   Wrappers.lean::captureCfg  reproduces  Wrappers.lean::emitCfg: 61/119 = 51%
   Primitives.lean::mapPayload_replay  reproduces  Primitives.lean::rawStrip_replay: 208/406 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   InputRewind.lean::inputRewindTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 86/168 = 51%
   Encoding.lean::pairDiag_double  reproduces  Primitives.lean::emitterToken_separator: 110/215 = 51%
   Primitives.lean::splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_counter_increment  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backB  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backA  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_double: 396/775 = 51%
   SingleTape.lean::dg_turn_with_growth  reproduces  SingleTape.lean::dg_end_without_growth: 233/456 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitter_compare_scan: 334/654 = 51%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::pairValid_run: 601/1177 = 51%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 340/666 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 174/341 = 51%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 106/208 = 51%
   Primitives.lean::split_sources  reproduces  Primitives.lean::splitSolve_closed: 196/385 = 51%
   Primitives.lean::splitRestore_scan  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::splitPrepare_scan  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::splitEmbed_cut  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::scanCopy_run  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::rawStrip_replay  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::rawStrip_copy  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::mapPayload_replay  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Primitives.lean::extract_replay  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_splitPrepare_scan  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_splitEmbed_cut  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_scanCopy_run  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_rawStrip_replay  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_rawStrip_copy  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_extract_replay  reproduces  AlphabetReduction.lean::arWriteCfg_run: 89/175 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 156/307 = 51%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Wrappers.lean::redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 400/790 = 51%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_extra: 228/451 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 252/499 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Primitives.lean::mapPayload_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 208/412 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   SingleTape.lean::sweep_prepare  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   SingleTape.lean::sweep_finish  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Simulation.lean::bufferedScanCfg_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::mapBuffer_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitter_compare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Encoding.lean::pairDiag_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_counter_carry  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::a2_mapVirtual_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   PolyTimePairing.lean::polyTimeComputable_pairConcat  reproduces  PolyTimePairing.lean::PolyTimeComputable.append: 72/143 = 50%
   Primitives.lean::pairMap_computes  reproduces  PolyTime.lean::PolyTimeComputable.output_length_le: 77/153 = 50%
   Primitives.lean::emitterAppend_run  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  AlphabetReduction.lean::arWriteCfg_run: 88/175 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::rawStrip_replay: 204/406 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_finish: 135/269 = 50%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 432/861 = 50%
   CfgRecord.lean::recordStep_state_run  reproduces  CfgRecord.lean::recordStep_scan_preserves: 290/578 = 50%
   SingleTape.lean::sweep_grow_right_block  reproduces  SingleTape.lean::sweep_grow_left_block: 343/684 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_map_suffix  reproduces  Primitives.lean::scanCopy_suffix: 426/850 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 272/544 = 50%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Primitives.lean::extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   WindowRun.lean::wl_Ctrl_fintype  reproduces  WindowRun.lean::wl_Ctrl_decidableEq: 82/164 = 50%
   Nondeterminism.lean::e3_loop_result  reproduces  Nondeterminism.lean::e3_split_length: 70/140 = 50%
   StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 63/126 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%

## ===== campaign/gates/109-h-landing-fill/evidence/seal/HSealControl_sealed.lean.txt =====

/-
Seal controls for H's route probe (`HRouteProbe.lean`), with the generic control commands of E-Q
cont1's review: for each of the 5 sealed definitions a delta goal (`#ctl_rfl`), and for the four
erased `@[simp]` definitions a pointwise unfolding goal by `intros; simp` (`#ctl_simp`). Each logs
`CONTROL_PASS` or `CONTROL_FAIL`. Expected: unsealed, every control passes; sealed, every control
fails. A probe record, not library code.
-/
import TCSlib.Complexity.SpaceComplexity.Hierarchy

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

open Lean Elab Command Meta in
elab "#ctl_card " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let ty := ci.type.getAppArgs[0]!
        let c := mkConst n
        let lhs := mkApp2 (mkConst ``Fintype.card [Level.zero]) ty c
        let goal ← mkEq lhs (mkNatLit 3)
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} card {n}"

section Controls

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg
attribute [local irreducible]
  Complexity.SpaceConstructible
  Complexity.SPACE
  Complexity.logSpace
  Complexity.LOGSPACE
  Complexity.PSPACE

attribute [local irreducible]
  Complexity.NP
  Complexity.PolyTimeComputable
  Complexity.TimeHierarchy.code
  Complexity.pairFstD
  Turing.Action.apply
  Turing.Cfg.InWindow
  Turing.Cfg.init
  Turing.Cfg.inputSymbol
  Turing.Cfg.liftSymbols
  Turing.Cfg.mapState
  Turing.Cfg.select
  Turing.Cfg.workTapeSymbols
  Turing.CodeTM.toFinTM
  Turing.Contract.branch
  Turing.FinNDTM.AcceptsWithin
  Turing.FinTM.ComputesFunInTime
  Turing.FinTM.ComputesInSpace
  Turing.FinTM.ComputesInTime
  Turing.FinTM.DecidesInSpace
  Turing.FinTM.bufferTape
  Turing.FinTM.configBound
  Turing.FinTM.toFinNDTM
  Turing.MultiTapeTM.indicator
  Turing.MultiTapeTM.initCfg
  Turing.MultiTapeTM.liftSymbols
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.spaceUsed
  Turing.MultiTapeTM.spaceUsedByTape
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.toNDTM
  Turing.MultiTapeTM.visitedByTapeHead
  Turing.NDTM.HaltsWithin
  Turing.NDTM.initCfg
  Turing.NDTM.runWith
  Turing.RecSym.digitEmb
  Turing.RecordAt
  Turing.cfgRecord
  Turing.counterValue
  Turing.embedEmitCfg
  Turing.embedEmitTM
  Turing.embedSilentCfg
  Turing.embedSilentRetTM
  Turing.embedSilentTM
  Turing.fieldsTape
  Turing.inputFoldTM
  Turing.inputRewindTM
  Turing.instDecidableEqInputRewindPhase
  Turing.instDecidableEqRecSym
  Turing.instDecidableEqRewindPhase
  Turing.instDecidableEqScanPhase
  Turing.instFintypeInputRewindPhase
  Turing.instFintypeRewindPhase
  Turing.instFintypeScanPhase
  Turing.joinFields
  Turing.moveInputPos
  Turing.outSummary
  Turing.outSummaryCode
  Turing.pairEncode
  Turing.posWidth
  Turing.recSymFintype
  Turing.recordLength
  Turing.rewindTM
  Turing.seamCompTM
  Turing.seamCompTM₂
  Turing.summaryTag
  Turing.windowRun

#ctl_rfl Complexity.SpaceConstructible
#ctl_rfl Complexity.SPACE
#ctl_rfl Complexity.logSpace
#ctl_rfl Complexity.LOGSPACE
#ctl_rfl Complexity.PSPACE
#ctl_simp Turing.Action.apply
#ctl_simp Turing.Cfg.init
#ctl_simp Turing.MultiTapeTM.initCfg
#ctl_simp Turing.NDTM.initCfg

#ctl_rfl Complexity.NP
#ctl_rfl Complexity.PolyTimeComputable
#ctl_rfl Complexity.TimeHierarchy.code
#ctl_rfl Complexity.pairFstD
#ctl_rfl Turing.Action.apply
#ctl_rfl Turing.Cfg.InWindow
#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.Cfg.inputSymbol
#ctl_rfl Turing.Cfg.liftSymbols
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.Cfg.select
#ctl_rfl Turing.Cfg.workTapeSymbols
#ctl_rfl Turing.CodeTM.toFinTM
#ctl_rfl Turing.Contract.branch
#ctl_rfl Turing.FinNDTM.AcceptsWithin
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.FinTM.ComputesInSpace
#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.DecidesInSpace
#ctl_rfl Turing.FinTM.bufferTape
#ctl_rfl Turing.FinTM.configBound
#ctl_rfl Turing.FinTM.toFinNDTM
#ctl_rfl Turing.MultiTapeTM.indicator
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.MultiTapeTM.liftSymbols
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.spaceUsed
#ctl_rfl Turing.MultiTapeTM.spaceUsedByTape
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.MultiTapeTM.toNDTM
#ctl_rfl Turing.MultiTapeTM.visitedByTapeHead
#ctl_rfl Turing.NDTM.HaltsWithin
#ctl_rfl Turing.NDTM.initCfg
#ctl_rfl Turing.RecSym.digitEmb
#ctl_rfl Turing.RecordAt
#ctl_rfl Turing.cfgRecord
#ctl_rfl Turing.counterValue
#ctl_rfl Turing.embedEmitCfg
#ctl_rfl Turing.embedEmitTM
#ctl_rfl Turing.embedSilentCfg
#ctl_rfl Turing.embedSilentRetTM
#ctl_rfl Turing.embedSilentTM
#ctl_rfl Turing.fieldsTape
#ctl_rfl Turing.inputFoldTM
#ctl_rfl Turing.inputRewindTM
#ctl_rfl Turing.instDecidableEqInputRewindPhase
#ctl_rfl Turing.instDecidableEqRecSym
#ctl_rfl Turing.instDecidableEqRewindPhase
#ctl_rfl Turing.instDecidableEqScanPhase
#ctl_rfl Turing.instFintypeScanPhase
#ctl_rfl Turing.joinFields
#ctl_rfl Turing.moveInputPos
#ctl_rfl Turing.outSummary
#ctl_rfl Turing.outSummaryCode
#ctl_rfl Turing.pairEncode
#ctl_rfl Turing.posWidth
#ctl_rfl Turing.recSymFintype
#ctl_rfl Turing.recordLength
#ctl_rfl Turing.rewindTM
#ctl_rfl Turing.seamCompTM
#ctl_rfl Turing.seamCompTM₂
#ctl_rfl Turing.summaryTag
#ctl_card Turing.instFintypeInputRewindPhase
#ctl_card Turing.instFintypeRewindPhase
#ctl_eqn Turing.windowRun
#ctl_eqn Turing.NDTM.runWith

end Controls

## ===== campaign/gates/109-h-landing-fill/evidence/seal/HSealControl_unsealed.lean.txt =====

/-
Seal controls for H's route probe (`HRouteProbe.lean`), with the generic control commands of E-Q
cont1's review: for each of the 5 sealed definitions a delta goal (`#ctl_rfl`), and for the four
erased `@[simp]` definitions a pointwise unfolding goal by `intros; simp` (`#ctl_simp`). Each logs
`CONTROL_PASS` or `CONTROL_FAIL`. Expected: unsealed, every control passes; sealed, every control
fails. A probe record, not library code.
-/
import TCSlib.Complexity.SpaceComplexity.Hierarchy

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

open Lean Elab Command Meta in
elab "#ctl_card " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let ty := ci.type.getAppArgs[0]!
        let c := mkConst n
        let lhs := mkApp2 (mkConst ``Fintype.card [Level.zero]) ty c
        let goal ← mkEq lhs (mkNatLit 3)
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} card {n}"

section Controls

#ctl_rfl Complexity.SpaceConstructible
#ctl_rfl Complexity.SPACE
#ctl_rfl Complexity.logSpace
#ctl_rfl Complexity.LOGSPACE
#ctl_rfl Complexity.PSPACE
#ctl_simp Turing.Action.apply
#ctl_simp Turing.Cfg.init
#ctl_simp Turing.MultiTapeTM.initCfg
#ctl_simp Turing.NDTM.initCfg

#ctl_rfl Complexity.NP
#ctl_rfl Complexity.PolyTimeComputable
#ctl_rfl Complexity.TimeHierarchy.code
#ctl_rfl Complexity.pairFstD
#ctl_rfl Turing.Action.apply
#ctl_rfl Turing.Cfg.InWindow
#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.Cfg.inputSymbol
#ctl_rfl Turing.Cfg.liftSymbols
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.Cfg.select
#ctl_rfl Turing.Cfg.workTapeSymbols
#ctl_rfl Turing.CodeTM.toFinTM
#ctl_rfl Turing.Contract.branch
#ctl_rfl Turing.FinNDTM.AcceptsWithin
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.FinTM.ComputesInSpace
#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.DecidesInSpace
#ctl_rfl Turing.FinTM.bufferTape
#ctl_rfl Turing.FinTM.configBound
#ctl_rfl Turing.FinTM.toFinNDTM
#ctl_rfl Turing.MultiTapeTM.indicator
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.MultiTapeTM.liftSymbols
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.spaceUsed
#ctl_rfl Turing.MultiTapeTM.spaceUsedByTape
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.MultiTapeTM.toNDTM
#ctl_rfl Turing.MultiTapeTM.visitedByTapeHead
#ctl_rfl Turing.NDTM.HaltsWithin
#ctl_rfl Turing.NDTM.initCfg
#ctl_rfl Turing.RecSym.digitEmb
#ctl_rfl Turing.RecordAt
#ctl_rfl Turing.cfgRecord
#ctl_rfl Turing.counterValue
#ctl_rfl Turing.embedEmitCfg
#ctl_rfl Turing.embedEmitTM
#ctl_rfl Turing.embedSilentCfg
#ctl_rfl Turing.embedSilentRetTM
#ctl_rfl Turing.embedSilentTM
#ctl_rfl Turing.fieldsTape
#ctl_rfl Turing.inputFoldTM
#ctl_rfl Turing.inputRewindTM
#ctl_rfl Turing.instDecidableEqInputRewindPhase
#ctl_rfl Turing.instDecidableEqRecSym
#ctl_rfl Turing.instDecidableEqRewindPhase
#ctl_rfl Turing.instDecidableEqScanPhase
#ctl_rfl Turing.instFintypeScanPhase
#ctl_rfl Turing.joinFields
#ctl_rfl Turing.moveInputPos
#ctl_rfl Turing.outSummary
#ctl_rfl Turing.outSummaryCode
#ctl_rfl Turing.pairEncode
#ctl_rfl Turing.posWidth
#ctl_rfl Turing.recSymFintype
#ctl_rfl Turing.recordLength
#ctl_rfl Turing.rewindTM
#ctl_rfl Turing.seamCompTM
#ctl_rfl Turing.seamCompTM₂
#ctl_rfl Turing.summaryTag
#ctl_card Turing.instFintypeInputRewindPhase
#ctl_card Turing.instFintypeRewindPhase
#ctl_eqn Turing.windowRun
#ctl_eqn Turing.NDTM.runWith

end Controls

## ===== campaign/gates/109-h-landing-fill/evidence/seal/HSealHead.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with the space-bounded universal machine of
[AB09, Exercise 4.1] (its forward clause, as the book states it), the
strictness corollary `L ⊊ PSPACE` on the p. 92 chain, and `SPACE(n+1) ≠ NP`
([AB09, Exercise 3.2], stated with the positive normalization). The universal
machine statement has a forward clause with the addend-free bound `C · s`;
the hierarchy uses a fixed self-application universal machine inside a
space-bounded configuration window.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and the layout
  `⟨bits s, ⟨α, x⟩⟩`, and keeps only Exercise 4.1's forward clause: a run of
  the coded machine within `s` work cells is reproduced, output included,
  within constant-factor space. Overruns and divergence are unconstrained, so
  the machine tests no budget, runs no clock and replays nothing. Its space
  bound is Exercise 4.1's `C_α · t`, with no addend: the simulated input, a
  suffix of its input, is read through the bounded-prefix ruler device
  (`Turing.exists_rulerHostTM`), a unary ruler of the header's length, which
  the bound absorbs because every qualifying run visits a cell.
* **The hierarchy takes the window route**: the
  diagonalizer runs one fixed self-application universal machine `U₀` in a
  window of radius `a · g(n)` on the configuration-record rows
  (`Build/CfgRecord.lean`, `Build/RecordTable.lean`), stopped by a
  configuration-count clock, and flips its verdict. The window, not `U₀`'s
  code-dependent constant, bounds the diagonalizer's space. The chapter-1
  interpreter (`Turing.universalInterpreter`) serves neither machine: it
  tracks the simulated input head in unary on its fourth tape, which uses one
  plus the largest simulated input position reached, `Θ(n + 1)` cells on a
  full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
  `S`.
* **Both bounds space-constructible**, as in the book; `g`'s witness drives
  the window radius, and of `f` the proof uses only the
  bundled floor `1 ≤ logSpace n ≤ f n`.
* The `SpaceComplexity.lean` facade imports this module.

## Main results

* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12; addend-free `C · s` since 2026-10-13).
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1], p. 93,
forward clause; spec, fill pending — phase P4.3, restated forward-only
2026-10-12 by design §16b item 3, RD-3 statement gate passed 2026-10-13;
strengthened to the addend-free `C · s` 2026-10-13, statement gate passed
2026-10-14):
for the fixed scheme there is a machine `SU` such that for every code `α`
there is a constant `C > 0` with: whenever the coded machine halts on `x`
with `output`, having visited at most `s` work cells by then, `SU` on input
`⟨bits s, ⟨α, x⟩⟩` halts with the same `output`, having visited at most
`C · s` work cells: the book's `C · t`. Nothing is claimed when the coded
machine overruns `s` or does not halt. The time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound. Every
qualifying run has `s ≥ 1` (`Turing.CodeTM.one_le_spaceUsed`), so the bound
is never `0`.

Deviations from the book's `SU(α, t, x) = M_α(x)` within `C · t` cells:
* **`C` depends on the representation `α`**, not only on `M_α`, as in
  `Turing.universal`, whose module docstring records why an arbitrary
  effective scheme forces this.
* "Halts before using `t` cells" is read as "at most `s` visited cells"; the
  budget is an argument of `SU`, as in the book, but is never read.
* The output is the simulated output itself: with no failure clause there is
  no verdict to tag. The former `[false]` clause, and with it the
  visited-interval counters, the core-count clock and the probe/replay of the
  previous statement, went with design §16b item 3.

There is no input-device addend: the gated `+ logSpace |x| + 1` (a binary
position for the simulated input head) is replaced by a unary ruler of the
header's length, whose cells the bound absorbs (the RD-3 gate's minor 1).

**Proof sketch.** A code-first interpreter in three parts. (i) **Startup.**
Parse the header `bits s`, `α` and the two separators by a finite-state pair
scan, writing one ruler cell per header cell, so that the ruler is `true^ℓ`
with `ℓ = 2|bits s| + 2|α| + 4` (`Turing.pairEncode_pairEncode_length`,
`Turing.pairEncode_pairEncode_drop`) and the physical input head ends at
`ℓ + 1`, the virtual position `1`; the budget is never read. Canonize `α`
into the table and state tapes as `U₀`'s startup does
(`Turing.exists_selfStartupTM`'s phases, reading the code where the header
holds it). Its cells are a constant depending only on `α`
(`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's halting time);
the effective scheme supplies no bound linear in `|α|`, and none is claimed.
(ii) **Input device and step block** (H5's bounded-prefix ruler device and
H2). Run `U₀`'s wrapped round loop (`Turing.exists_selfUniversal`'s sketch:
H2's step block on the output-erased source, with the leaf that forwards each
emission before the next round and before the halt) through the ruler host
`Turing.exists_rulerHostTM` on the virtual input `x`. The host is a positive
finite block simulation: it reads a blank and suppresses left moves at the
virtual left boundary, which it tests by restoring sweeps of `ℓ` cells
(`Turing.exists_rulerTestTM`), so `SU` halts exactly when the round loop does,
with its output, the coded machine's. The chapter-1 interpreter's device
cannot serve: its fourth tape holds a unary boundary marker whose head
`applyRecord` moves with the input head (`Turing.universalInterpreter`), so
that tape uses one plus the largest simulated input position reached,
`Θ(|x| + 1)` cells on a full scan, which a budget `s = o(|x|)` does not
cover (Finding B). (iii) **Space.** The host's bank visits exactly the round
loop's cells: the mirrored tape only the coded machine's, at most `s`, and the
table and summary tapes `O(|table| + 1)`, a constant for fixed `α`. Its ruler
visits `ℓ + 2` cells. Every qualifying run has `s ≥ 1`
(`Turing.CodeTM.one_le_spaceUsed`) and `|bits s| ≤ s`
(`Turing.length_bits_le_self`), so `ℓ ≤ 2s + 2|α| + 4 ≤ (2|α| + 6) · s`, and
the total `C_α + s + ℓ + 2` is at most `C · s`. Fill obligations, named: the
header-ruler startup with the buffered canonization; the H5 ruler host;
`U₀`'s wrapped round loop (H2 at one coded work tape, with its head
envelope); the per-code constant ledger. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * s := by
  sorry

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg
attribute [local irreducible]
  Complexity.SpaceConstructible
  Complexity.SPACE
  Complexity.logSpace
  Complexity.LOGSPACE
  Complexity.PSPACE
  Complexity.NP
  Complexity.PolyTimeComputable
  Complexity.TimeHierarchy.code
  Complexity.pairFstD
  Turing.Action.apply
  Turing.Cfg.InWindow
  Turing.Cfg.init
  Turing.Cfg.inputSymbol
  Turing.Cfg.liftSymbols
  Turing.Cfg.mapState
  Turing.Cfg.select
  Turing.Cfg.workTapeSymbols
  Turing.CodeTM.toFinTM
  Turing.Contract.branch
  Turing.FinNDTM.AcceptsWithin
  Turing.FinTM.ComputesFunInTime
  Turing.FinTM.ComputesInSpace
  Turing.FinTM.ComputesInTime
  Turing.FinTM.DecidesInSpace
  Turing.FinTM.bufferTape
  Turing.FinTM.configBound
  Turing.FinTM.toFinNDTM
  Turing.MultiTapeTM.indicator
  Turing.MultiTapeTM.initCfg
  Turing.MultiTapeTM.liftSymbols
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.spaceUsed
  Turing.MultiTapeTM.spaceUsedByTape
  Turing.MultiTapeTM.step
  Turing.MultiTapeTM.toNDTM
  Turing.MultiTapeTM.visitedByTapeHead
  Turing.NDTM.HaltsWithin
  Turing.NDTM.initCfg
  Turing.NDTM.runWith
  Turing.RecSym.digitEmb
  Turing.RecordAt
  Turing.cfgRecord
  Turing.counterValue
  Turing.embedEmitCfg
  Turing.embedEmitTM
  Turing.embedSilentCfg
  Turing.embedSilentRetTM
  Turing.embedSilentTM
  Turing.fieldsTape
  Turing.inputFoldTM
  Turing.inputRewindTM
  Turing.instDecidableEqInputRewindPhase
  Turing.instDecidableEqRecSym
  Turing.instDecidableEqRewindPhase
  Turing.instDecidableEqScanPhase
  Turing.instFintypeInputRewindPhase
  Turing.instFintypeRewindPhase
  Turing.instFintypeScanPhase
  Turing.joinFields
  Turing.moveInputPos
  Turing.outSummary
  Turing.outSummaryCode
  Turing.pairEncode
  Turing.posWidth
  Turing.recSymFintype
  Turing.recordLength
  Turing.rewindTM
  Turing.seamCompTM
  Turing.seamCompTM₂
  Turing.summaryTag
  Turing.windowRun


/-- The inclusion half: `hfg` at `A = 1` from some `N` on, and `g`'s floor below `N`.
[AB09, Theorem 4.8, inclusion]

**Proof sketch.** Bound the finitely many exceptional values by their supremum. The positive
floor of `g` absorbs that supremum into one constant, and `SPACE.mono_const` applies. -/
private lemma sph_inclusion {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) : SPACE f ⊆ SPACE g := by
  obtain ⟨N, hN⟩ := hfg 1
  have hfloor : ∀ n, 1 ≤ g n := fun n =>
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff g).mp hg).1 n)
  set F := (Finset.range N).sup f with hF
  refine SPACE.mono_const (a := F + 1) fun n => ?_
  by_cases hn : N ≤ n
  · have := hN n hn
    calc f n ≤ g n := by simpa using this
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
    calc f n ≤ F + 1 := by omega
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)

/-- A decider in the smaller space class has a padded code on which the fixed universal
machine halts inside the larger window, before its configuration-count clock expires.
[AB09, Theorem 4.8, diagonal contradiction]

**Proof sketch.** Normalize the decider to one binary work tape and then to a coded machine,
using the published space clauses. Choose the domination constant after the code's universal
simulation constant is fixed, and pad the payload to the resulting threshold. The configuration
bound supplies a halting time; the window-summary theorem identifies the run at the next round. -/
private lemma sph_code_window (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) (U₀ : FinTM Bool)
    (hU : ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (TimeHierarchy.code.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
          ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
        ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
          U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1))
    (L : Language Bool) (c₀ : ℕ) (M : FinTM Bool)
    (hM : M.DecidesInSpace L (fun n => c₀ * f n)) :
    ∃ (x : List Bool) (t : ℕ),
      U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t ∧
      U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length ∧
      t = U₀.configBound x.length (g x.length) ∧
      windowRun U₀.tm (g x.length) summaryTag (t + 1) (U₀.tm.initCfg x) 0 =
        (.halted, U₀.tm.runFrom (U₀.tm.initCfg x) t,
          outSummaryCode (outSummary [MultiTapeTM.indicator (L : Set (List Bool)) x])) := by
  have hm := (FinTM.decidesInSpace_iff M L (fun n => c₀ * f n)).mp hM
  have hbounds := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨M₁, c₁, hk, htime, hspace⟩ := FinTM.one_work_tape_binary_spaceUsed M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => M.configBound n (c₀ * f n)) (fun n => c₀ * f n) hbounds.1 hbounds.2
  obtain ⟨N, hrun, hsp⟩ := exists_codeTM_spaceUsed M₁ hk
  let α := TimeHierarchy.code.encode N
  have hα : TimeHierarchy.code.decode α = N := MachineCode.decode_encode _ _
  obtain ⟨C, _hC, hsim⟩ := hU α
  let A := C * (c₁ * c₀ + c₁ + 1)
  obtain ⟨N₀, hN₀⟩ := hfg A
  let x := pairEncode α (List.replicate N₀ true)
  have hx : N₀ ≤ x.length := by
    simp only [x, length_pairEncode, List.length_replicate]
    omega
  let t₀ := c₁ * (M.configBound x.length (c₀ * f x.length) + 1) ^ 2
  have hn : (TimeHierarchy.code.decode α).toFinTM.ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ := by
    rw [hα]
    exact (hrun x _ t₀).mpr ((FinTM.computesFunInTime_iff _ _ _).mp htime x)
  have hs : (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
      ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg x) t₀ ≤
      c₁ * (c₀ * f x.length + 1) := by
    rw [hα, hsp]
    exact hspace x t₀
  obtain ⟨u, hu, hsu⟩ := hsim (List.replicate N₀ true)
    [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ (c₁ * (c₀ * f x.length + 1)) hn hs
  have hfloor : 1 ≤ f x.length :=
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff f).mp hf).1 x.length)
  have hsmall : C * (c₁ * (c₀ * f x.length + 1) + 1) ≤ A * f x.length := by
    calc
      _ ≤ C * (c₁ * (c₀ * f x.length + f x.length) + f x.length) :=
        Nat.mul_le_mul_left C (Nat.add_le_add
          (Nat.mul_le_mul_left c₁ (Nat.add_le_add_left hfloor _)) hfloor)
      _ = A * f x.length := by dsimp only [A]; ring
  have hwindow : U₀.tm.spaceUsed (U₀.tm.initCfg x) u ≤ g x.length :=
    hsu.trans (hsmall.trans (hN₀ x.length hx))
  let t := U₀.configBound x.length (g x.length)
  have hhalt : U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    hu.of_spaceUsed_le hwindow
  have hspace' : U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length :=
    hu.spaceUsed_le_of_halt hwindow t
  exact ⟨x, t, hhalt, hspace', rfl,
    windowRun_summary_of_halts U₀ x hhalt hspace' (Nat.lt_succ_self t)⟩

/-- A square below a power of two, from `4` on.

**Proof sketch.** Induct from `4`; doubling the previous power absorbs the next square. -/
private lemma sph_sq_le_two_pow : ∀ L, 4 ≤ L → L * L ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- The logarithm is dominated by the identity at every constant factor, eventually.

**Proof sketch.** Beyond `2 ^ max 4 (2 * A)`, the integer logarithm is at least both `4` and
`2 * A`. Its square fits below `n`, and dominates `A * (log₂ n + 1)`. -/
private lemma sph_logSpace_dom : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logSpace n ≤ n + 1 := by
  intro A
  refine ⟨2 ^ (max 4 (2 * A)), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := max 4 (2 * A)); omega
  set L := Nat.log 2 n with hL
  have hLge : max 4 (2 * A) ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hsq := sph_sq_le_two_pow L (le_trans (le_max_left _ _) hLge)
  have h2A : 2 * A ≤ L := le_trans (le_max_right _ _) hLge
  rw [logSpace_eq, ← hL]
  nlinarith

/-- **`LOGSPACE ⊂ PSPACE`**, from the space hierarchy's statement. [AB09, §4.3.2]

**Proof sketch.** Apply the hierarchy to logarithmic and linear space, then transport strictness
along the published inclusion of linear space into polynomial space. -/
private lemma sph_logspace_ssubset
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g) :
    LOGSPACE ⊂ PSPACE := by
  have hlin : SPACE (fun n => n + 1) ⊆ PSPACE := by
    have := space_poly_subset_PSPACE 1
    simpa only [pow_one] using this
  obtain ⟨-, hnot⟩ := hH logSpace (fun n => n + 1) spaceConstructible_logSpace
    spaceConstructible_linear sph_logSpace_dom
  refine ⟨LOGSPACE_subset_PSPACE, fun hP => hnot ?_⟩
  rw [← LOGSPACE_eq]
  exact hlin.trans hP

/-- One input-head move before the lifted rewind. The rewind's published contract requires a
positive input position; this leaf supplies it even when the radius witness stops at `0`.
The action changes no work tape or output. [AB09, §1.2]

**Proof sketch.** The transition always moves the input head right and reaches its live anchor.
At the right boundary it stays put; everywhere else its position increases by one. -/
private def sphRightTM (k : ℕ) (Γ : Type) : MultiTapeTM k Γ Bool where
  q₀ := false
  tr := fun _ _ _ => ⟨.pos, fun _ => (none, 0), none, some true⟩

/-- The right-move leaf's framed run and positive endpoint.

**Proof sketch.** Read the one transition field by field, separate the input's right boundary,
and use the zero-step and one-step configurations for the cut and head claim. -/
private lemma sph_right_run {k : ℕ} {Γ : Type} {x : List Γ}
    (d : Cfg k Γ Bool x) (hd : d.state = some false) :
    (sphRightTM k Γ).runFrom d 1 =
        {d with state := some true, inputPos := moveInputPos d.inputPos .pos} ∧
      1 ≤ (moveInputPos d.inputPos .pos).val ∧
      (∀ u < 1, ((sphRightTM k Γ).runFrom d u).state ≠ some true) ∧
      ∀ u ≤ 1, ((sphRightTM k Γ).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphRightTM k Γ).runFrom d 1 =
      {d with state := some true, inputPos := moveInputPos d.inputPos .pos} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]; rfl
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphRightTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphRightTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      simp only [sphRightTM, Option.toList_none, List.append_nil]
  refine ⟨hstep, ?_, ?_, ?_⟩
  · by_cases h : d.inputPos.val = x.length + 1
    · have hp : d.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h
      rw [hp, SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right _ h]
      exact Nat.succ_pos _
  · intro u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    decide
  · intro u hu
    have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
    rcases this with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]

/-- Emit the final verdict and halt, preserving the input and work tapes. The only output
leaf needed after the record test. [AB09, §1.2] -/
private def sphEmitTM (k : ℕ) {Γ : Type} (b : Γ) : MultiTapeTM k Γ Unit where
  q₀ := ()
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The verdict emitter appends exactly one symbol in one step, with no work-head motion.

**Proof sketch.** Read the five fields of its sole action using the public action equations. -/
private lemma sph_emit_run {k : ℕ} {Γ : Type} {x : List Γ} (b : Γ)
    (d : Cfg k Γ Unit x) (hd : d.state = some ()) :
    (sphEmitTM k b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} ∧
      ∀ u ≤ 1, ((sphEmitTM k b).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphEmitTM k b).runFrom d 1 =
      {d with state := none, output := d.output ++ [b]} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]
      exact moveInputPos_zero _
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphEmitTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphEmitTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      rfl
  refine ⟨hstep, ?_⟩
  intro u hu
  have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
  rcases this with rfl | rfl
  · rw [MultiTapeTM.runFrom_zero]
  · rw [hstep]

/-- The input validator's finite-state test: precisely the embedded binary digits. -/
private def sphDigit {Q : Type} : RecSym Q (Fin 3) → Bool
  | .digit _ => true
  | .cell _ _ => false
  | .st _ => false
  | .tag _ => false

/-- The validator accepts precisely embedded binary words, including the empty word.

**Proof sketch.** Induct on the input. A successful fold forces the head symbol to be a digit;
strip that digit and use the induction hypothesis on the tail. Conversely, prepend the
corresponding Boolean to the decoded tail. -/
private lemma sph_fold_valid {Q : Type} (ys : List (RecSym Q (Fin 3))) (a : Bool) :
    ys.foldl (fun b c => b && sphDigit c) a = true ↔
      a = true ∧ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) := by
  induction ys generalizing a with
  | nil =>
    rw [List.foldl_nil]
    exact ⟨fun h => ⟨h, [], rfl⟩, fun h => h.1⟩
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨hay, x, hx⟩
      obtain ⟨ha, hy⟩ := Bool.and_eq_true_iff.mp hay
      refine ⟨ha, ?_⟩
      cases y with
      | digit b =>
        refine ⟨b :: x, ?_⟩
        rw [List.map_cons, RecSym.digitEmb_apply, ← hx]
      | cell c m => cases hy
      | st q => cases hy
      | tag t => cases hy
    · rintro ⟨ha, x, hx⟩
      cases x with
      | nil => cases hx
      | cons b bs =>
        rw [List.map_cons] at hx
        obtain ⟨hy, ht⟩ := List.cons.inj hx
        refine ⟨Bool.and_eq_true_iff.mpr ⟨ha, ?_⟩, bs, ht⟩
        rw [hy, RecSym.digitEmb_apply]
        rfl

/-- The rich-input validation phase, on all of the diagonalizer's work tapes. Its successful
exit supplies a binary input for every subsequent phase; it moves no work head.
[AB09, Theorem 4.8, alphabet reduction]

**Proof sketch.** Use the published framed input fold and identify its final flag with
`sph_fold_valid`. The framed endpoint also restores the input head to its initial position. -/
private lemma sph_validation_run {k : ℕ} {Q : Type}
    {ys : List (RecSym Q (Fin 3))} (d : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys)
    (hd : d.state = some (.fwd true)) (hin : d.inputPos = 1) :
    ∃ b : Bool,
      (inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d (2 * ys.length + 2) =
        {d with state := some (.done b)} ∧
      (b = true ↔ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3))) ∧
      (∀ u < 2 * ys.length + 2, ∀ a,
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).state ≠
          some (.done a)) ∧
      ∀ j u, u ≤ 2 * ys.length + 2 →
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).workTapePos j =
          d.workTapePos j := by
  obtain ⟨hr, hc, hh⟩ := inputFoldTM_run_ofCfg (fun a c => a && sphDigit c) true d hd hin
  refine ⟨ys.foldl (fun a c => a && sphDigit c) true, hr, ?_, hc, hh⟩
  exact ⟨fun h => ((sph_fold_valid ys true).mp h).2,
    fun h => (sph_fold_valid ys true).mpr ⟨rfl, h⟩⟩

/-- Witness tapes are after the record, radius, initializer scratch and runner scratch banks.
Separate scratch banks keep the runner disjoint from both the radius and the dirty witness. -/
private def sphWitnessSel (KI KR m : ℕ) : Fin m ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨KI + KR + 2 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
      congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
    exact Nat.add_left_cancel h'

/-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
private lemma sph_witness_cap (KI KR m : ℕ) :
    (1 : Fin (KI + KR + m + 2)) ∉ Set.range (sphWitnessSel KI KR m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [sphWitnessSel, Function.Embedding.coeFn_mk, Fin.val_one] at this
  omega

/-- The constructibility witness returns with its complete binary radius on tape `1`, preserving
all tapes outside its bank and the radius tape. Its last emission is included in the captured
word. [AB09, Theorem 4.8, radius phase]

**Proof sketch.** Choose the witness's first halting time and lift its run to the record
alphabet. Apply the published returning capture embedding. Its capture and frame equations give
the endpoint. Its selected, capture and frame space equations bound each tape; summing gives a
constant multiple of the witness space and radius length. -/
private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
    (g : ℕ → ℕ) (c : ℕ) (M : FinTM Bool)
    (hM : M.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n))
    (x : List Bool)
    (tapes : Fin (KI + KR + M.k + 2) → ℤ → Option (RecSym Q (Fin 3)))
    (heads : Fin (KI + KR + M.k + 2) → ℤ) (out : List (RecSym Q (Fin 3))) :
    let e := RecSym.digitEmb Q (Fin 3)
    let ι := sphWitnessSel KI KR M.k
    let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
    let start := (embedSilentCfg ι 1 tapes heads [] out
      ((M.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : M.State → M.State ⊕ Unit)
    ∃ t : ℕ,
      (R.runFrom start t).state = some (Sum.inr ()) ∧
      (∀ u < t, (R.runFrom start u).state ≠ some (Sum.inr ())) ∧
      (R.runFrom start t).workTapes 1 =
        FinTM.bufferTape ((g x.length).bits.map RecSym.digit) ∧
      (R.runFrom start t).workTapePos 1 = ((g x.length).bits.length : ℤ) ∧
      (∀ j, j ∉ Set.range ι → j ≠ 1 →
        (R.runFrom start t).workTapes j = tapes j ∧
          (R.runFrom start t).workTapePos j = heads j) ∧
      (∀ u ≤ t, (R.runFrom start u).output = out) ∧
      R.spaceUsed start t ≤ (KI + KR + M.k + 2) *
        (c * g x.length + (g x.length).bits.length + 1) ∧
      ∀ u ≤ t, ∀ j,
        |(R.runFrom start u).workTapePos j| ≤
          |heads j| + (c * g x.length + (g x.length).bits.length : ℕ) := by
  classical
  dsimp only
  let e := RecSym.digitEmb Q (Fin 3)
  let ι := sphWitnessSel KI KR M.k
  let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
  let a := (M.tm.initCfg x).liftSymbols e
  let start := (embedSilentCfg ι 1 tapes heads [] out a).mapState
    (Sum.inl : M.State → M.State ⊕ Unit)
  obtain ⟨v, hv, hsv⟩ := (FinTM.computesInSpace_iff _ _ _).mp hM x
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hv
  obtain ⟨t, htv, hlive, heq⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hhalt
  have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * g x.length :=
    (M.tm.spaceUsed_mono _ htv).trans hsv
  have ho : (M.tm.runFrom (M.tm.initCfg x) t).output = (g x.length).bits :=
    (congrArg Cfg.output heq).trans hout
  have hc : a.state ≠ none := by
    rw [Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hh : ((M.tm.liftSymbols e).runFrom a t).state = none := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state, heq, hhalt]
  have hl : ∀ u < t, ((M.tm.liftSymbols e).runFrom a u).state ≠ none := by
    intro u hu
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state]
    exact hlive u hu
  have hcap := sph_witness_cap KI KR M.k
  obtain ⟨hpre, hr, hcut⟩ := embedSilentRetTM_run ι 1 hcap (M.tm.liftSymbols e)
    tapes heads [] out a t hc hl hh
  have hout' : ((M.tm.liftSymbols e).runFrom a t).output =
      (g x.length).bits.map RecSym.digit := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output, ho]
    apply List.map_congr_left
    intro b _
    exact RecSym.digitEmb_apply _ _ b
  refine ⟨t, ?_, hcut, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).1
    simpa only [List.nil_append, hout'] using h
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).2
    simpa only [List.nil_append, hout', List.length_map] using h
  · intro j hj hjc
    rw [hr]
    exact embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc
  · intro u hu
    rcases lt_or_eq_of_le hu with hu | rfl
    · rw [hpre u hu, Cfg.mapState_output, embedSilentCfg_output]
    · rw [hr, embedSilentCfg_output]
  · rw [MultiTapeTM.spaceUsed_eq_sum]
    calc
      _ ≤ (Finset.univ : Finset (Fin (KI + KR + M.k + 2))).card •
          (c * g x.length + (g x.length).bits.length + 1) := by
        apply Finset.sum_le_card_nsmul
        intro j _
        rw [MultiTapeTM.spaceUsedByTape_eq_card,
          embedSilentRetTM_visitedByTapeHead,
          ← MultiTapeTM.spaceUsedByTape_eq_card]
        by_cases hj : j ∈ Set.range ι
        · obtain ⟨i, rfl⟩ := hj
          rw [(embedSilentTM_visitedByTapeHead ι 1 hcap _ tapes heads [] out a t i).2]
          have h : (M.tm.liftSymbols e).spaceUsedByTape a t i ≤ c * g x.length :=
            calc
              _ ≤ (M.tm.liftSymbols e).spaceUsed a t :=
                (M.tm.liftSymbols e).spaceUsedByTape_le_spaceUsed a t i
              _ = M.tm.spaceUsed (M.tm.initCfg x) t :=
                MultiTapeTM.liftSymbols_spaceUsed M.tm e (M.tm.initCfg x) t
              _ ≤ _ := hs
          omega
        · by_cases hjc : j = 1
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap ι 1 hcap
              (M.tm.liftSymbols e) tapes heads [] out a t
            rw [hout', List.length_map] at h
            exact h.trans (by omega)
          · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
              tapes heads [] out a t j hj hjc).2]
            omega
      _ = _ := by rw [Finset.card_fin, smul_eq_mul]
  · intro u hu j
    have hpos : (R.runFrom start u).workTapePos j =
        (embedSilentCfg ι 1 tapes heads [] out
          ((M.tm.liftSymbols e).runFrom a u)).workTapePos j := by
      rcases lt_or_eq_of_le hu with hlt | rfl
      · rw [hpre u hlt, Cfg.mapState_workTapePos]
      · rw [hr]
    rw [hpos]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_pos, MultiTapeTM.liftSymbols_runFrom,
        Cfg.liftSymbols_workTapePos]
      have h := ((FinTM.inWindow_of_spaceUsed_le M x hs u hu).core_bounds i).1
      have hn := abs_nonneg (heads (ι i))
      exact h.trans (by push_cast; omega)
    · by_cases hjc : j = 1
      · subst j
        rw [(embedSilentCfg_cap ι 1 hcap tapes heads [] out _).2,
          MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output,
          List.nil_append, List.length_map, abs_of_nonneg (by omega)]
        have h := (M.tm.output_prefix (M.tm.initCfg x) hu).length_le
        rw [ho] at h
        have hn := abs_nonneg (heads 1)
        push_cast
        omega
      · rw [(embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc).2]
        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) :=
          Int.natCast_nonneg _
        omega


/-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k := Function.Embedding.ofIsEmpty

/-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
input position of an embedded binary word, with the entire physical work bank framed.

**Proof sketch.** Construct the zero-tape binary configuration at the same input position,
apply the published input rewind, lift its run, and use the R1 reconstruction theorem to
identify its initial and final embeddings with the physical configurations. -/
private lemma sph_input_rewind_run {k : ℕ} {Q : Type} [DecidableEq Q] {x : List Bool}
    (d : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    let R := embedEmitTM (sphEmptySel k)
      ((inputRewindTM 0).liftSymbols (RecSym.digitEmb Q (Fin 3)))
    R.runFrom d (d.inputPos.val + 1) = {d with state := some .done, inputPos := 1} ∧
      (∀ u < d.inputPos.val + 1, (R.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 1, (R.runFrom d u).workTapePos = d.workTapePos := by
  let e := RecSym.digitEmb Q (Fin 3)
  let a : Cfg 0 Bool InputRewindPhase x :=
    ⟨some .start, ⟨d.inputPos.val, by simpa only [List.length_map] using d.inputPos.isLt⟩,
      Fin.elim0, Fin.elim0, []⟩
  have ha : a.inputPos.val = d.inputPos.val := rfl
  have hi : (a.liftSymbols e).inputPos = d.inputPos := by
    rw [Cfg.liftSymbols_inputPos]
    exact Fin.ext rfl
  have hs : embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
      (a.liftSymbols e) = d := by
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]; exact hd.symm
    · exact hi
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  obtain ⟨hr, hc, hh⟩ := inputRewindTM_run a rfl (ha.symm ▸ hp)
  have hrun (u : ℕ) :
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)).runFrom d u =
        embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
          (((inputRewindTM 0).runFrom a u).liftSymbols e) := by
    have h := embedEmitTM_runFrom (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
      d.workTapes d.workTapePos d.output (a.liftSymbols e) u
    rw [hs, MultiTapeTM.liftSymbols_runFrom] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, ← ha, hr]
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]
    · rw [Cfg.liftSymbols_inputPos]
      exact Fin.ext rfl
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state, Cfg.liftSymbols_state]
    exact hc u (ha.symm ▸ hu)
  · intro u _
    rw [hrun]
    funext j
    exact (embedEmitCfg_unselected (sphEmptySel k) d.workTapes d.workTapePos d.output
      (((inputRewindTM 0).runFrom a u).liftSymbols e) j
      (by rintro ⟨i, _⟩; exact Fin.elim0 i)).2

/-- The two rewinds after radius capture: a right move makes the input position positive,
the zero-tape input rewind restores position one, and the radius rewind restores tape one.
Both seams use the published general-configuration composition. -/
private def sphRewindsTM (k : ℕ) (Q : Type) [DecidableEq Q] (cap : Fin k) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) :=
  seamCompTM
    (seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols
        (RecSym.digitEmb Q (Fin 3)))) .start)
    (.inr .done) (rewindTM k cap) .start

/-- A common absolute head interval is preserved by a published general-configuration seam.

**Proof sketch.** Before the dispatch use the public left trajectory; afterwards use the
public right trajectory. State relabelling preserves every work-head position. -/
private lemma sph_seam_heads {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t v : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (p : Fin k → ℤ) (r : ℕ)
    (hA : ∀ u ≤ t, ∀ j, |(A.runFrom d u).workTapePos j - p j| ≤ (r : ℤ))
    (hB : ∀ u ≤ v, ∀ j,
      |(B.runFrom (d'.mapState fun _ => entry) u).workTapePos j - p j| ≤ (r : ℤ)) :
    ∀ u ≤ t + 1 + v, ∀ j,
      |((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).workTapePos j - p j| ≤
        (r : ℤ) := by
  intro u hu j
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_workTapePos]
    exact hA u h j
  · obtain ⟨w, hw, rfl⟩ : ∃ w ≤ v, u = t + 1 + w := ⟨u - (t + 1), by omega, by omega⟩
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_workTapePos]
    exact hB w hw j

/-- The paired rewinds on the tape plan, including an empty captured word and an input head
initially at zero. Every work-tape cell and the accumulated output are preserved.

**Proof sketch.** Compose the one-step right move and the lifted zero-tape rewind at their
first returns. Apply the framed radius rewind at the full captured word's length and compose
again. Read the endpoint through the public state-map equations. -/
private lemma sph_rewinds_run (KI KR m : ℕ) {Q : Type} [DecidableEq Q]
    {x : List Bool} (ws : List Bool)
    (d : Cfg (KI + KR + m + 2) (RecSym Q (Fin 3)) Bool
      (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some false)
    (hcap : d.workTapes 1 = FinTM.bufferTape (ws.map RecSym.digit))
    (hpos : d.workTapePos 1 = (ws.length : ℤ)) :
    ∃ t,
      (sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) t =
        { state := some (Sum.inr RewindPhase.done)
          inputPos := 1
          workTapes := d.workTapes
          workTapePos := Function.update d.workTapePos 1 0
          output := d.output } ∧
      (∀ u < t,
        ((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).state ≠ some (Sum.inr .done)) ∧
      ∀ u ≤ t, ∀ j,
        |((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j - d.workTapePos j| ≤
            ((ws.length + 1 : ℕ) : ℤ) := by
  let k := KI + KR + m + 2
  let e := RecSym.digitEmb Q (Fin 3)
  let I := embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
  let A := seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true I .start
  let d₁ := {d with state := some true, inputPos := moveInputPos d.inputPos .pos}
  let a := d₁.mapState (fun _ => InputRewindPhase.start)
  let d₂ : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map e) :=
    {a with state := some InputRewindPhase.done, inputPos := 1}
  obtain ⟨h₁, hp, hc₁, hh₁⟩ := sph_right_run d hd
  obtain ⟨h₂, hc₂, hh₂⟩ := sph_input_rewind_run a
    (by rw [Cfg.mapState_state]; rfl)
    (by rw [Cfg.mapState_inputPos]; exact hp)
  have hA : A.runFrom (d.mapState Sum.inl) (1 + 1 + (a.inputPos.val + 1)) =
      d₂.mapState Sum.inr :=
    seamCompTM_run_ofCfg (sphRightTM k _) true I .start h₁ rfl hc₁ h₂
  have hAc := seamCompTM_firstReturn_ofCfg (sphRightTM k _) true I .start .done
    h₁ rfl hc₁ h₂ rfl hc₂
  let b := (d₂.mapState (Sum.inr : InputRewindPhase → Bool ⊕ InputRewindPhase)).mapState
    (fun _ => RewindPhase.start)
  have hb : b.state = some .start := by
    rw [Cfg.mapState_state, Cfg.mapState_state]
    rfl
  have hbh : b.workTapePos = d.workTapePos := by
    funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  have hbt : b.workTapes = d.workTapes := by
    funext j p
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  obtain ⟨h₃, hc₃, hh₃⟩ := rewindTM_run_ofCfg (1 : Fin k)
    (ws.map (RecSym.digit : Bool → RecSym Q (Fin 3))) ws.length
    (by rw [List.length_map]) b hb (by
      intro p _ _
      rw [hbt, hbh, hpos, sub_self, zero_add, hcap])
  let d₃ := { b with
    state := some RewindPhase.done
    workTapePos := Function.update b.workTapePos 1 (b.workTapePos 1 - ws.length) }
  have hend : d₃.mapState Sum.inr =
      ({ state := some (Sum.inr RewindPhase.done)
         inputPos := 1
         workTapes := d.workTapes
         workTapePos := Function.update d.workTapePos 1 0
         output := d.output } : Cfg k (RecSym Q (Fin 3))
           ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) (x.map e)) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j p
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun hbt j) p
    · funext j
      rw [Cfg.mapState_workTapePos]
      dsimp only [d₃]
      rw [hbh, hpos, sub_self]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output]
  refine ⟨(1 + 1 + (a.inputPos.val + 1)) + 1 + (ws.length + 2), ?_, ?_, ?_⟩
  · exact (seamCompTM_run_ofCfg A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃).trans hend
  · exact seamCompTM_firstReturn_ofCfg A (.inr .done) (rewindTM k 1) .start .done
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃ rfl hc₃
  · have hAh := sph_seam_heads (sphRightTM k (RecSym Q (Fin 3))) true I .start
      h₁ rfl hc₁ d.workTapePos (ws.length + 1)
      (by
        intro u hu j
        rw [hh₁ u hu, sub_self, abs_zero]
        omega)
      (by
        intro u hu j
        have h := congrFun (hh₂ u hu) j
        rw [Cfg.mapState_workTapePos] at h
        rw [h, sub_self, abs_zero]
        omega)
    exact sph_seam_heads A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc d.workTapePos (ws.length + 1) hAh
      (by
        intro u hu j
        change |((rewindTM k 1).runFrom b u).workTapePos j - d.workTapePos j| ≤
          ((ws.length + 1 : ℕ) : ℤ)
        have h := hh₃ j u hu
        by_cases hj : j = 1
        · rw [if_pos hj, hbh, Finset.mem_Icc] at h
          exact abs_le.mpr ⟨by push_cast; omega, by push_cast; omega⟩
        · rw [if_neg hj, hbh] at h
          rw [h, sub_self, abs_zero]
          omega)


/-- Read a selected configuration through R1 reconstruction, without unfolding the selector.
This common field calculation is used by the runner and final record test.

**Proof sketch.** Project the public reconstruction identity and use the public equations for
the forwarding transport's selected tapes, positions, state, input and output. -/
private lemma sph_select_fields {m k : ℕ} {Γ S : Type} {x : List Γ}
    (ι : Fin m ↪ Fin k) (d : Cfg k Γ S x) :
    (d.select ι).state = d.state ∧ (d.select ι).inputPos = d.inputPos ∧
      d.output ++ (d.select ι).output = d.output ∧
      (∀ i, (d.select ι).workTapes i = d.workTapes (ι i)) ∧
      (∀ i, (d.select ι).workTapePos i = d.workTapePos (ι i)) := by
  have hr := embedEmitCfg_select ι d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg Cfg.state hr
    rwa [embedEmitCfg_state] at h
  · have h := congrArg Cfg.inputPos hr
    rwa [embedEmitCfg_inputPos] at h
  · have h := congrArg Cfg.output hr
    rwa [embedEmitCfg_output] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapes
        (ι i) = d.workTapes (ι i) := congrArg (fun c => c.workTapes (ι i)) hr
    rwa [embedEmitCfg_selected_tape] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapePos
        (ι i) = d.workTapePos (ι i) := congrArg (fun c => c.workTapePos (ι i)) hr
    rwa [embedEmitCfg_selected_pos] at h

/-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) :=
  Fin.castLEEmb (by omega)

/-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]

**Proof sketch.** Select the record, radius and initializer scratch tapes. Read the selected
configuration through the R1 reconstruction equation and its field equations. Apply the
published initial-record row, transport its run by R1 and reconstruct the framed endpoint. -/
private lemma sph_initial_record (M : FinTM Bool) (KR m : ℕ) :
    ∃ (KI : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength M.k x.length s : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (KI + KR + m + 2), 2 ≤ j.val → j.val < KI + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (recordLength M.k x.length s + ws.length + s + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + (recordLength M.k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (M.tm.initCfg x) 0) (q - d.workTapePos j)
                else d.workTapes j q} := by
  classical
  obtain ⟨KI, P, hF, hD, I, entry, exit, C, hI⟩ :=
    exists_recordInitTM M.k M.tm.q₀ (0 : Fin 3)
  letI := hF
  letI := hD
  let ι := sphInitSel KI KR m
  have h0 : ι 0 = 0 := Fin.ext rfl
  have h1 : ι 1 = 1 := Fin.ext rfl
  refine ⟨KI, P, hF, hD, embedEmitTM ι I, entry, exit, C, ?_⟩
  intro x s ws hws d hd hin hrad hslot hblank
  let a := d.select ι
  have hrecon : embedEmitCfg ι d.workTapes d.workTapePos d.output a = d :=
    embedEmitCfg_select ι d
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  obtain ⟨t, htime, hcut, henv, hr⟩ := hI s ws hws a (hstate.trans hd) (hinput.trans hin)
    (by intro p hp hp'; rw [htapes, hheads, h1]; exact hrad p hp hp')
    (by intro p hp hp'; rw [htapes, hheads, h0]; exact hslot p hp hp')
    (by
      intro j hj p
      rw [htapes]
      exact hblank (ι j) hj (by have := j.isLt; exact this) p)
  have hrun (u : ℕ) :
      (embedEmitTM ι I).runFrom d u =
        embedEmitCfg ι d.workTapes d.workTapePos d.output (I.runFrom a u) := by
    have h := embedEmitTM_runFrom ι I d.workTapes d.workTapePos d.output a u
    rwa [hrecon] at h
  refine ⟨t, htime, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput

/-- The runner uses record tape zero and its scratch bank, never the radius or witness bank. -/
private def sphRunnerSel (KI KR m : ℕ) : Fin (KR + 1) ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨if i.val = 0 then 0 else KI + 1 + i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : (if i.val = 0 then 0 else KI + 1 + i.val) =
        (if j.val = 0 then 0 else KI + 1 + j.val) := congrArg Fin.val h
    split_ifs at h' <;> omega

/-- The published clocked runner on the diagonalizer's full tape plan. Its blank scratch
condition excludes both the radius tape and the dirty witness bank. [AB09, Theorem 4.8]

**Proof sketch.** Select record tape zero and the runner scratch bank. Apply the published
configuration-count runner with `summaryTag`, and transport its run, head envelope, silence
and nonexhausted record endpoint by R1. No new clock or simulation is constructed. -/
private lemma sph_runner_run (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KR + 1) (RecSym M.State (Fin 3)) P)
      (entry : P) (exit : WindowExit → P) (C : ℕ),
      (∀ e, exit e ≠ entry) ∧ Function.Injective exit ∧
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3),
      c.InWindow s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        let H := embedEmitTM (sphRunnerSel KI KR m) R
        ∃ (t : ℕ) (out : WindowExit),
          t ≤ C * 2 ^ (C * (recordLength M.k x.length s + 1)) ∧
          (H.runFrom d t).state = some (exit out) ∧
          (∀ u < t, ∀ e, (H.runFrom d u).state ≠ some (exit e)) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ u ≤ t, (H.runFrom d u).output = d.output) ∧
          (∀ N ≤ M.configBound x.length s + 1,
            (windowRun M.tm s summaryTag N c τ).1 ≠ .exhausted →
            out = (windowRun M.tm s summaryTag N c τ).1) ∧
          (out ≠ .exhausted → ∃ N,
            (windowRun M.tm s summaryTag N c τ).1 = out ∧
            H.runFrom d t =
              { d with
                state := some (exit out)
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                      q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                    then fieldsTape (cfgRecord s (windowRun M.tm s summaryTag N c τ).2.1
                      (windowRun M.tm s summaryTag N c τ).2.2) (q - d.workTapePos 0)
                  else d.workTapes j q }) := by
  classical
  obtain ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, hR⟩ :=
    exists_configWindowRunnerTM M summaryTag summaryTag_none
  letI := hF
  letI := hD
  refine ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, ?_⟩
  intro KI m x s c τ hc d hd hrec hblank
  dsimp only
  let ι := sphRunnerSel KI KR m
  have h0 : ι 0 = 0 := by
    apply Fin.ext
    simp only [ι, sphRunnerSel, Function.Embedding.coeFn_mk, Fin.val_zero, if_pos]
  have hv (i : Fin (KR + 1)) (hi : i ≠ 0) : (ι i).val = KI + 1 + i.val := by
    have hz : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    exact if_neg hz
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, out, ht, he, hcut, henv, hs, _, hvote, hend⟩ := hR s c τ hc a
    (hstate.trans hd) hrec' (by
      intro i hi p
      rw [htapes]
      apply hblank (ι i)
      · rw [hv i hi]
        have : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
        omega
      · rw [hv i hi]
        have := i.isLt
        omega)
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, out, ht, ?_, ?_, ?_, ?_, hvote, ?_⟩
  · rw [hrun, embedEmitCfg_state]
    exact he
  · intro u hu e
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu e
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · intro u hu
    rw [hrun, embedEmitCfg_output, hs u hu]
    exact houtput
  · intro hn
    obtain ⟨N, hN, hr⟩ := hend hn
    refine ⟨N, hN, ?_⟩
    rw [hrun, hr]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, h0, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput


/-- A one-tape record test selects the physical record tape alone. -/
private def sphRecordSel (k : ℕ) : Fin 1 ↪ Fin (k + 1) where
  toFun _ := 0
  inj' := fun _ _ _ => Subsingleton.elim _ _

/-- The final record test, on the full work bank, asks whether the encoded configuration is
halted and its output summary is the singleton-true summary. It preserves every physical field
except its finite verdict state. [AB09, Theorem 4.8]

**Proof sketch.** Apply the published one-tape record test to the selected record tape and
transport the framed endpoint and head envelope by R1. -/
private lemma sph_test_run (M : FinTM Bool) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM 1 (RecSym M.State (Fin 3)) P) (entry yes no : P) (C : ℕ),
      yes ≠ no ∧
      ∀ (k : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3)
        {ys : List (RecSym M.State (Fin 3))}
        (d : Cfg (k + 1) (RecSym M.State (Fin 3)) P ys),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        let H := embedEmitTM (sphRecordSel k) R
        ∃ t ≤ C * (recordLength M.k x.length s + 1),
          (∀ u < t, (H.runFrom d u).state ≠ some yes ∧
            (H.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          H.runFrom d t =
            {d with state := some (if c.state = none ∧ τ = 1 then yes else no)} := by
  classical
  obtain ⟨P, hF, hD, R, entry, yes, no, C, hne, hR⟩ :=
    exists_recordTestTM (k := M.k)
      (fun (q : Option M.State) (τ : Fin 3) => decide (q = none ∧ τ = 1))
  letI := hF
  letI := hD
  refine ⟨P, hF, hD, R, entry, yes, no, C, hne, ?_⟩
  intro k x s c τ ys d hd hrec
  dsimp only
  let ι := sphRecordSel k
  have h0 : ι 0 = 0 := rfl
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, ht, hcut, henv, hr⟩ := hR s c τ a (hstate.trans hd) hrec'
  rw [joinFields_cfgRecord_length] at ht henv
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr]
    apply embedEmitCfg_eq
    · simp only [decide_eq_true_eq]
    · exact hinput
    · exact houtput
    · intro i
      exact ⟨htapes i, hheads i⟩
    · exact fun _ _ => ⟨rfl, rfl⟩


/-- The emitter leaf as a framed contract, with a singleton head interval on every tape. -/
private def sphEmitContract {k : ℕ} {Γ : Type} (b : Γ) (x : List Γ) :
    Contract (sphEmitTM k b) () {none} Unit x where
  pre := fun _ _ => True
  time := fun _ _ => 1
  post := fun _ d => {d with state := none, output := d.output ++ [b]}
  lo := fun _ d => d.workTapePos
  hi := fun _ d => d.workTapePos
  run := fun _ d hd _ => (sph_emit_run b d hd).1
  exit_mem := fun _ _ _ _ => Set.mem_singleton _
  cut := by
    intro _ d hd _ u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    exact Option.some_ne_none _
  env := by
    intro _ d hd _ u hu j
    rw [(sph_emit_run b d hd).2 u hu]
    exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- The two-exit seam attaches the opposite one-bit answer to each record-test verdict. -/
private def sphVerdictTM {k : ℕ} {Q P : Type} [DecidableEq P]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (yes no : P) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((P ⊕ Unit) ⊕ Unit) :=
  seamCompTM₂ R yes no (sphEmitTM k (RecSym.digit false)) ()
    (sphEmitTM k (RecSym.digit true)) ()

/-- A framed record test followed by its opposite-bit emitter halts, and inherits the test's
head envelope. This also covers a halted record whose summary is not singleton true.

**Proof sketch.** The two-exit run theorem selects the one-step emitter. The public branching
contract combines the test's certified interval with the emitter's stationary heads; the hull
is the test's original interval. -/
private lemma sph_verdict_run {k : ℕ} {Q P : Type} [DecidableEq P]
    {ys : List (RecSym Q (Fin 3))} (R : MultiTapeTM k (RecSym Q (Fin 3)) P)
    (entry yes no : P) (hne : yes ≠ no) (d : Cfg k (RecSym Q (Fin 3)) P ys)
    (hd : d.state = some entry) (b : Bool) (t B : ℕ)
    (hr : R.runFrom d t = {d with state := some (if b then yes else no)})
    (hcut : ∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no)
    (henv : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    (sphVerdictTM R yes no).runFrom ((d.mapState Sum.inl).mapState Sum.inl) (t + 2) =
        { state := none
          inputPos := d.inputPos
          workTapes := d.workTapes
          workTapePos := d.workTapePos
          output := d.output ++ [RecSym.digit (!b)] } ∧
      ∀ u ≤ t + 2, ∀ j,
        |((sphVerdictTM R yes no).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  classical
  let d' := {d with state := some (if b then yes else no)}
  let d₀ := (d.mapState (Sum.inl : P → P ⊕ Unit)).mapState
    (Sum.inl : P ⊕ Unit → (P ⊕ Unit) ⊕ Unit)
  let C₀ : Contract R entry {some yes, some no} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => t
      post := fun _ _ => d'
      lo := fun _ _ j => d.workTapePos j - B
      hi := fun _ _ j => d.workTapePos j + B
      run := by intro _ a _ ha; subst a; exact hr
      exit_mem := by
        intro _ _ _ _
        cases b
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        · exact Set.mem_insert _ _
      cut := by
        intro _ a _ ha u hu
        subst a
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact hcut u hu
      env := by
        intro _ a _ ha u hu j
        subst a
        exact Contract.mem_Icc_of_abs_le (henv u hu j) }
  let C := Contract.branch hne C₀ (sphEmitContract (RecSym.digit false) ys)
    (sphEmitContract (RecSym.digit true) ys) (fun _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro)
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl entry)) := by
    rw [Cfg.mapState_state, Cfg.mapState_state, hd]
    rfl
  have hp : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => entry) = d
    simp only [d₀, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  have htime : C.time () d₀ = t + 2 := by
    rw [Contract.branch_time]
    dsimp only [C₀, sphEmitContract]
    rw [ite_self]
  refine ⟨?_, ?_⟩
  · obtain ⟨hy, hn⟩ := seamCompTM₂_run_ofCfg R yes no hne
      (sphEmitTM k (RecSym.digit false)) () (sphEmitTM k (RecSym.digit true)) () hr hcut
    have ht : t + 2 = t + 1 + 1 := by omega
    rw [ht]
    cases b
    · have h := hn rfl 1
      rw [(sph_emit_run (RecSym.digit true) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      apply Cfg.ext
      · rw [Cfg.mapState_state]; rfl
      · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output, Cfg.mapState_output]
        rfl
    · have h := hy rfl 1
      rw [(sph_emit_run (RecSym.digit false) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      apply Cfg.ext
      · rw [Cfg.mapState_state, Cfg.mapState_state]; rfl
      · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
        rfl
  · intro u hu j
    have h := C.env () d₀ hd₀ hp u (htime.symm ▸ hu) j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    simp only [Cfg.mapState_workTapePos, ite_self] at h
    dsimp only [d'] at h
    rw [min_eq_left (by omega), max_eq_left (by omega), Finset.mem_Icc] at h
    dsimp only [d₀, sphVerdictTM] at h ⊢
    exact abs_le.mpr ⟨by omega, by omega⟩


/-- Any halted record returned by the window runner has the actual halting run's state and
output summary, regardless of which stopped round count the runner's record clause supplies.

**Proof sketch.** Compare that round count with one past a certified halting time by the
published stop-uniqueness theorem, then read the public output-summary characterization. -/
private lemma sph_summary (M : FinTM Bool) (x w : List Bool) (s t N : ℕ)
    (ht : M.ComputesInTime x w t)
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s)
    (hN : (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).1 = .halted) :
    ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1).state = none ∧
      ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2 = 1 ↔ w = [true]) := by
  have h := windowRun_summary_of_halts M x ht hs (Nat.lt_succ_self t)
  have heq := windowRun_stop_unique M.tm s summaryTag N (t + 1) (M.tm.initCfg x) 0
    (by rw [hN]; intro hbad; cases hbad)
    (by rw [h]; exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
  rw [heq, h]
  exact ⟨((FinTM.computesInTime_iff _ _ _ _).mp ht).1, outSummaryCode_eq_one_iff w⟩


/-- Once a seam dispatches, no other left-hand anchor is reached. Before dispatch it inherits
the host's avoidance of that anchor.

**Proof sketch.** The public left trajectory gives the host's cut and the distinct dispatch
anchor at the endpoint. The public right trajectory has only right-hand states or a halt. -/
private lemma sph_seam_avoids {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit other : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hne : exit ≠ other)
    (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (ho : ∀ u < t, (A.runFrom d u).state ≠ some other) :
    ∀ u, ((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).state ≠
      some (Sum.inl other) := by
  intro u hbad
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_state] at hbad
    have hh : (A.runFrom d u).state = some other :=
      Option.map_injective Sum.inl_injective hbad
    rcases lt_or_eq_of_le h with h | rfl
    · exact ho u h hh
    · rw [hr, he] at hh
      exact hne (Option.some.inj hh)
  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_state] at hbad
    obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad
    exact Sum.inr_ne_inl hq

/-- Writing a layout's interior between its two blank boundary cells installs that record.
This is the shared boundary argument for the initializer and the stopped runner.

**Proof sketch.** Read `RecordAt` through its public equivalence. Inside the span use the
written field tape. The only other required offsets are minus one and the layout length;
both the old tape and the public layout boundary equations are blank there. -/
private lemma sph_written_record {k : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (k + 1) Γ P x) (q : Option P) (fs : List (List Γ)) (L : ℕ)
    (hL : (joinFields fs).length = L)
    (hl : d.workTapes 0 (d.workTapePos 0 - 1) = none)
    (hr : d.workTapes 0 (d.workTapePos 0 + L) = none) :
    RecordAt
      { d with
        state := q
        workTapes := fun j z =>
          if j = 0 ∧ d.workTapePos 0 ≤ z ∧ z < d.workTapePos 0 + (L : ℤ)
            then fieldsTape fs (z - d.workTapePos 0) else d.workTapes j z }
      0 fs := by
  rw [recordAt_iff]
  intro p hp hp'
  rw [hL] at hp'
  change (if (0 : Fin (k + 1)) = 0 ∧ d.workTapePos 0 ≤ d.workTapePos 0 + p ∧
      d.workTapePos 0 + p < d.workTapePos 0 + (L : ℤ)
    then fieldsTape fs (d.workTapePos 0 + p - d.workTapePos 0)
    else d.workTapes 0 (d.workTapePos 0 + p)) = fieldsTape fs p
  by_cases h : 0 ≤ p ∧ p < (L : ℤ)
  · rw [if_pos ⟨rfl, by omega, by omega⟩]
    congr 1
    ring
  · rw [if_neg (by rintro ⟨_, h₁, h₂⟩; exact h ⟨by omega, by omega⟩)]
    have : p = -1 ∨ p = (L : ℤ) := by omega
    rcases this with rfl | rfl
    · rw [fieldsTape_of_neg fs (by omega), ← sub_eq_add_neg]
      exact hl
    · rw [fieldsTape_of_length_le fs (by rw [hL])]
      exact hr


/-- The runner's three exits use published single-exit seams: a halted run enters the verdict
test, and either a window exit or exhaustion enters the true emitter. Exhaustion never reads
the unspecified record tape. -/
private def sphRunnerTailTM {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S) :
    MultiTapeTM k (RecSym Q (Fin 3)) (((P ⊕ S) ⊕ Unit) ⊕ Unit) :=
  seamCompTM
    (seamCompTM (seamCompTM R (exit .halted) V entry) (Sum.inl (exit .left))
      (sphEmitTM k (RecSym.digit true)) ())
    (Sum.inl (Sum.inl (exit .exhausted))) (sphEmitTM k (RecSym.digit true)) ()

/-- Run the runner's three-exit suffix. A certificate about the halted branch's output is
preserved; both other branches emit true. All heads remain in a common certified interval.

**Proof sketch.** On a halted verdict, both outer seams stay in their left segments while the
test runs. On a window exit, the middle seam dispatches the true emitter; on exhaustion, the
outer seam does so. The public seam trajectories transport the endpoint and each head bound.
The clock and record simulation remain entirely the supplied runner's. -/
private lemma sph_runner_tail_run {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    {ys : List (RecSym Q (Fin 3))}
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (hi : Function.Injective exit) (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S)
    (d d' : Cfg k (RecSym Q (Fin 3)) P ys) (t B : ℕ) (out : WindowExit)
    (hr : R.runFrom d t = d') (he : d'.state = some (exit out))
    (hc : ∀ u < t, ∀ e, (R.runFrom d u).state ≠ some (exit e))
    (ho : d'.output = d.output)
    (hh : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ))
    (pred : Bool → Prop)
    (hv : out = .halted → ∃ v b,
      (V.runFrom (d'.mapState fun _ => entry) v).state = none ∧
      (V.runFrom (d'.mapState fun _ => entry) v).output =
        d'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |(V.runFrom (d'.mapState fun _ => entry) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    ∃ v b,
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).state = none ∧
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).output =
          d.output ++ [RecSym.digit b] ∧
      (out = .halted → pred b) ∧ (out ≠ .halted → b = true) ∧
      ∀ u ≤ v, ∀ j,
        |((sphRunnerTailTM R exit V entry).runFrom
          (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  let E := sphEmitTM k (RecSym.digit true : RecSym Q (Fin 3))
  let A := seamCompTM R (exit .halted) V entry
  let C := seamCompTM A (Sum.inl (exit .left)) E ()
  let a := d.mapState (Sum.inl : P → P ⊕ S)
  let a' := d'.mapState (Sum.inl : P → P ⊕ S)
  let c := a.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  let c' := a'.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  have hAp (u : ℕ) (hu : u ≤ t) : A.runFrom a u = (R.runFrom d u).mapState Sum.inl :=
    seamCompTM_runFrom_left R (exit .halted) V entry (fun u hu => hc u hu .halted) u hu
  have hAr : A.runFrom a t = a' := by rw [hAp t le_rfl, hr]
  have hAc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (A.runFrom a u).state ≠ some (Sum.inl (exit e)) := by
    rw [hAp u hu.le, Cfg.mapState_state]
    intro h
    exact hc u hu e (Option.map_injective Sum.inl_injective h)
  have hCp (u : ℕ) (hu : u ≤ t) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
    seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
      (fun u hu => hAc u hu .left) u hu
  have hCr : C.runFrom c t = c' := by rw [hCp t le_rfl, hAr]
  have hCc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit e))) := by
    rw [hCp u hu.le, Cfg.mapState_state]
    intro h
    exact hAc u hu e (Option.map_injective Sum.inl_injective h)
  cases out with
  | halted =>
    obtain ⟨v, b, hvs, hvo, hpred, hvh⟩ := hv rfl
    have hAl := sph_seam_avoids R (exit .halted) (exit .left) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .left)
    have hAe := sph_seam_avoids R (exit .halted) (exit .exhausted) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .exhausted)
    have hC (u : ℕ) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
      seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
        (fun u _ => hAl u) u le_rfl
    have hCe (u : ℕ) : (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [hC, Cfg.mapState_state]
      intro h
      exact hAe u (Option.map_injective Sum.inl_injective h)
    have hW (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        ((A.runFrom a u).mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)).mapState Sum.inl := by
      rw [seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => hCe u) u le_rfl, hC]
    have hA := seamCompTM_runFrom_right R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) v
    have hAh := sph_seam_heads R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) d.workTapePos B hh hvh
    refine ⟨t + 1 + v, b, ?_, ?_, fun _ => hpred, fun h => False.elim (h rfl), ?_⟩
    · rw [hW, hA, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, hvs]
      rfl
    · rw [hW, hA, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, hvo, ho]
    · intro u hu j
      rw [hW, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hAh u hu j
  | left =>
    have ha' : a'.state = some (Sum.inl (exit .left)) := by
      rw [Cfg.mapState_state, he]; rfl
    have havoid := sph_seam_avoids A (Sum.inl (exit .left))
      (Sum.inl (exit .exhausted)) E () hAr ha'
      (fun h => WindowExit.noConfusion (hi (Sum.inl.inj h)))
      (fun u hu => hAc u hu .left) (fun u hu => hAc u hu .exhausted)
    have hw (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        (C.runFrom c u).mapState Sum.inl :=
      seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => havoid u) u le_rfl
    have hea : (a'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, ha']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (a'.mapState fun _ => ()) hea
    have hC := seamCompTM_run_ofCfg A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) her
    have hAh : ∀ u ≤ t, ∀ j, |(A.runFrom a u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (a'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hCh := sph_seam_heads A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) d.workTapePos B hAh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, ?_⟩
    · rw [hw, hC, Cfg.mapState_state, Cfg.mapState_state]; rfl
    · rw [hw, hC, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, ho]
    · intro u hu j
      rw [hw, Cfg.mapState_workTapePos]
      exact hCh u hu j
  | exhausted =>
    have hc' : c'.state = some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [Cfg.mapState_state, Cfg.mapState_state, he]; rfl
    have hec : (c'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, hc']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (c'.mapState fun _ => ()) hec
    have hW := seamCompTM_run_ofCfg C (Sum.inl (Sum.inl (exit .exhausted))) E ()
      hCr hc' (fun u hu => hCc u hu .exhausted) her
    have hCh : ∀ u ≤ t, ∀ j, |(C.runFrom c u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hCp u hu, Cfg.mapState_workTapePos, hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (c'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hWh := sph_seam_heads C (Sum.inl (Sum.inl (exit .exhausted))) E () hCr hc'
      (fun u hu => hCc u hu .exhausted) d.workTapePos B hCh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, hWh⟩
    · rw [hW, Cfg.mapState_state]; rfl
    · rw [hW, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, ho]


/-- The complete clocked simulation suffix on the tape plan. Starting from the universal
machine's initial record, it halts with one bit. Every halting run that fits the window receives
the opposite acceptance answer, and the suffix's head bound is uniform in the input's code.
[AB09, Theorem 4.8]

**Proof sketch.** Put the published runner and record test on disjoint framed selections, then
attach the tested opposite-bit verdict and the two unconditional true branches. The returned
record's blank boundaries follow from the old record and the public layout boundary equations.
Stop uniqueness identifies its summary with any certified halting run in the window. -/
private lemma sph_suffix (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : ∀ KI m, MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ)
        (d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3)))),
        d.state = some entry → RecordAt d 0 (cfgRecord s (M.tm.initCfg x) 0) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          ((D KI m).runFrom d t).state = none ∧
          ((D KI m).runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |((D KI m).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PR, hFR, hDR, R, ren, rex, CR, _, hinj, hR⟩ := sph_runner_run M
  letI := hFR
  letI := hDR
  obtain ⟨PT, hFT, hDT, T, ten, yes, no, CT, hne, hT⟩ := sph_test_run M
  letI := hFT
  letI := hDT
  let H (KI m : ℕ) := embedEmitTM (sphRunnerSel KI KR m) R
  let J (KI m : ℕ) := embedEmitTM (sphRecordSel (KI + KR + m + 1)) T
  let V (KI m : ℕ) := sphVerdictTM (J KI m) yes no
  let ven : (PT ⊕ Unit) ⊕ Unit := .inl (.inl ten)
  let D (KI m : ℕ) := sphRunnerTailTM (H KI m) rex (V KI m) ven
  let en : (((PR ⊕ ((PT ⊕ Unit) ⊕ Unit)) ⊕ Unit) ⊕ Unit) := .inl (.inl (.inl ren))
  refine ⟨KR, _, inferInstance, inferInstance, D, en, CR + CT, ?_⟩
  intro KI m x s d hd hrec hblank
  let a := d.mapState (fun _ => ren)
  have ha : a.state = some ren := by rw [Cfg.mapState_state, hd]; rfl
  have har : RecordAt a 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact hrec p hp hp'
  have hab : ∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
      ∀ p, a.workTapes j p = none := by
    intro j hj hj' p
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj' p
  have hstart : (((a.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  obtain ⟨t, out, _, he, hc, hh, ho, hword, hend⟩ := hR KI m s (M.tm.initCfg x) 0
    (by rw [MultiTapeTM.initCfg_eq]; exact Cfg.inWindow_init _ _ s) a ha har hab
  let a' := (H KI m).runFrom a t
  have ha' : a'.state = some (rex out) := he
  let L := recordLength M.k x.length s
  let B := (CR + CT) * (L + 1)
  have hRB : CR * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hTB : CT * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  let pred (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length s) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
    b = !(decide (w = [true]))
  have hV : out = .halted → ∃ v b,
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).state = none ∧
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).output =
        a'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |((V KI m).runFrom (a'.mapState fun _ => ven) u).workTapePos j - a.workTapePos j| ≤
          (B : ℤ) := by
    intro hout
    obtain ⟨N, hN, hr⟩ := hend (by rw [hout]; intro hbad; cases hbad)
    let cN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1
    let τN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2
    have hl : a.workTapes 0 (a.workTapePos 0 - 1) = none := by
      have h := (recordAt_iff _ _ _).mp har (-1) le_rfl (by omega)
      rw [fieldsTape_of_neg _ (by omega), ← sub_eq_add_neg] at h
      exact h
    have hright : a.workTapes 0 (a.workTapePos 0 + (L : ℤ)) = none := by
      have h := (recordAt_iff _ _ _).mp har (L : ℤ) (by omega)
        (by rw [joinFields_cfgRecord_length])
      rw [fieldsTape_of_length_le _ (by rw [joinFields_cfgRecord_length])] at h
      exact h
    have hrecN : RecordAt a' 0 (cfgRecord s cN τN) := by
      dsimp only [a']
      rw [hr]
      exact sph_written_record a _ (cfgRecord s cN τN) L
        (joinFields_cfgRecord_length _ _ _) hl hright
    let z := a'.mapState (fun _ => ten)
    have hz : z.state = some ten := by rw [Cfg.mapState_state, he]; rfl
    have hzr : RecordAt z 0 (cfgRecord s cN τN) := by
      rw [recordAt_iff] at hrecN ⊢
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrecN p hp hp'
    obtain ⟨v, _, hcutT, hheadsT, hrunT⟩ := hT (KI + KR + m + 1) s cN τN z hz hzr
    let b := decide (cN.state = none ∧ τN = 1)
    obtain ⟨hvr, hvh⟩ := sph_verdict_run (J KI m) ten yes no hne z hz b v (CT * (L + 1))
      (by simpa only [b, decide_eq_true_eq] using hrunT) hcutT hheadsT
    have hmaps : ((z.mapState Sum.inl).mapState Sum.inl) = a'.mapState (fun _ => ven) := by
      simp only [z, Cfg.mapState_mapState]
      rfl
    rw [hmaps] at hvr hvh
    refine ⟨v + 2, !b, ?_, ?_, ?_, ?_⟩
    · rw [hvr]
    · rw [hvr, Cfg.mapState_output]
    · intro w hw hs
      have hsumm := sph_summary M x w s (M.configBound x.length s) N hw hs (hN.trans hout)
      have hf : (cN.state = none ∧ τN = 1) ↔ w = [true] :=
        ⟨fun h => hsumm.2.mp h.2, fun h => ⟨hsumm.1, hsumm.2.mpr h⟩⟩
      dsimp only [b]
      exact congrArg Bool.not (decide_eq_decide.mpr hf)
    · intro u hu j
      have h := hvh u hu j
      have hzhead : z.workTapePos j = a.workTapePos j := by
        rw [Cfg.mapState_workTapePos]
        dsimp only [a']
        rw [hr]
      rw [hzhead] at h
      exact h.trans (by exact_mod_cast hTB)
  obtain ⟨v, b, hvs, hvo, hpred, _, hvh⟩ := sph_runner_tail_run (H KI m) rex hinj
    (V KI m) ven a a' t B out rfl he hc (ho t le_rfl)
    (fun u hu j => (hh u hu j).trans (by exact_mod_cast hRB)) pred hV
  rw [hstart] at hvs hvo hvh
  refine ⟨v, b, hvs, ?_, ?_, ?_⟩
  · rw [Cfg.mapState_output] at hvo
    exact hvo
  · intro u hu j
    have h := hvh u hu j
    rw [Cfg.mapState_workTapePos] at h
    exact h
  · intro w hw hs
    have hsummary := windowRun_summary_of_halts M x hw hs
      (Nat.lt_succ_self (M.configBound x.length s))
    have hout := hword (M.configBound x.length s + 1) le_rfl
      (by rw [hsummary]
          exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
    rw [hsummary] at hout
    exact hpred hout w hw hs


/-- Initialize the simulated machine's record from the radius word, then run the complete
clocked suffix. Scratch banks are disjoint from the radius and witness tapes.

**Proof sketch.** Invoke the framed initializer, install its record using the shared boundary
calculation, and pass its untouched runner bank to the suffix. The published seam composes the
runs; the initializer restores every head, so both envelopes have the same centre. -/
private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
    ∃ (KI KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ j : Fin (KI + KR + m + 2), j.val < KI + KR + 2 → j ≠ 1 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          (D.runFrom d t).state = none ∧
          (D.runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |(D.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PS, hFS, hDS, S, sen, CS, hS⟩ := sph_suffix M
  letI := hFS
  letI := hDS
  obtain ⟨KI, PI, hFI, hDI, I, ien, iex, CI, hI⟩ := sph_initial_record M KR m
  letI := hFI
  letI := hDI
  let D := seamCompTM I iex (S KI m) sen
  refine ⟨KI, KR, PI ⊕ PS, inferInstance, inferInstance, D, Sum.inl ien, CI + CS, ?_⟩
  intro x s ws hws d hd hin hrad hblank
  let a := d.mapState (fun _ => ien)
  have ha : a.state = some ien := by rw [Cfg.mapState_state, hd]; rfl
  have hstart : a.mapState Sum.inl = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  let L := recordLength M.k x.length s
  have hblank' (j : Fin (KI + KR + m + 2)) (hj : j.val < KI + KR + 2) (hj1 : j ≠ 1)
      (p : ℤ) : a.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj1 p
  obtain ⟨t, _, hc, hh, hr⟩ := hI s ws hws a ha
    (by rw [Cfg.mapState_inputPos]; exact hin)
    (by
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrad p hp hp')
    (by
      intro p _ _
      exact hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    (by
      intro j hj hj' p
      exact hblank' j (by omega) (by
        intro h; subst j; rw [Fin.val_one] at hj; omega) p)
  let a' := I.runFrom a t
  have he : a'.state = some iex := by dsimp only [a']; rw [hr]
  have hah (j) : a'.workTapePos j = d.workTapePos j := by
    dsimp only [a']; rw [hr, Cfg.mapState_workTapePos]
  have hao : a'.output = d.output := by dsimp only [a']; rw [hr, Cfg.mapState_output]
  have har : RecordAt a' 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    have hwritten := sph_written_record a (some iex) (cfgRecord s (M.tm.initCfg x) 0) L
      (joinFields_cfgRecord_length _ _ _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    dsimp only [a']
    rw [recordAt_iff] at hwritten ⊢
    intro p hp hp'
    rw [hr]
    exact hwritten p hp hp'
  let z := a'.mapState (fun _ => sen)
  have hz : z.state = some sen := by rw [Cfg.mapState_state, he]; rfl
  have hzr : RecordAt z 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at har ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact har p hp hp'
  have hzb (j : Fin (KI + KR + m + 2)) (hj : KI + 2 ≤ j.val)
      (hj' : j.val < KI + KR + 2) (p : ℤ) : z.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    dsimp only [a']
    rw [hr]
    have hj0 : j ≠ 0 := by intro h; subst j; rw [Fin.val_zero] at hj; omega
    simpa only [hj0, false_and, ↓reduceIte] using
      hblank' j hj' (by intro h; subst j; rw [Fin.val_one] at hj; omega) p
  obtain ⟨v, b, hvs, hvo, hvh, hpred⟩ := hS KI m s z hz hzr hzb
  have hrun := seamCompTM_run_ofCfg I iex (S KI m) sen (rfl : I.runFrom a t = a')
    he hc (rfl : (S KI m).runFrom z v = (S KI m).runFrom z v)
  rw [hstart] at hrun
  let B := (CI + CS) * (L + ws.length + s + 1)
  have hIB : CI * (L + ws.length + s + 1) ≤ B :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hSB : CS * (L + 1) ≤ B :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)
  refine ⟨t + 1 + v, b, ?_, ?_, ?_, hpred⟩
  · rw [hrun, Cfg.mapState_state, hvs, Option.map_none]
  · rw [hrun, Cfg.mapState_output, hvo, Cfg.mapState_output, hao]
  · have hen := sph_seam_heads I iex (S KI m) sen (rfl : I.runFrom a t = a') he hc
      d.workTapePos B
      (by
        intro u hu j
        have h := hh u hu j
        rw [Cfg.mapState_workTapePos] at h
        exact h.trans (by exact_mod_cast hIB))
      (by
        intro u hu j
        have h := hvh u hu j
        rw [Cfg.mapState_workTapePos, hah] at h
        exact h.trans (by exact_mod_cast hSB))
    rw [hstart] at hen
    exact hen


/-- The complete record-and-radius envelope is linear in any bound above `logSpace`.
The coefficient depends only on the fixed simulated machine's tape count.

**Proof sketch.** The radius needs at most its value in binary digits. An input position
needs at most twice `logSpace n` digits. Insert these bounds in the public record-length
formula and absorb the additive constants using the logarithmic floor. -/
private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n) (k n : ℕ) :
    recordLength k n (g n) + (g n).bits.length + g n + 1 ≤ (4 * k + 9) * g n := by
  have hfloor : 1 ≤ g n := by have h := hg n; rw [logSpace_eq] at h; omega
  have hb : (g n).bits.length ≤ g n := length_bits_le_self _
  have hp : posWidth n ≤ 2 * g n := by
    rw [posWidth_eq]
    have hpow : n + 1 < 2 ^ (Nat.log 2 n + 2) :=
      (LogProg.succ_le_two_pow_log n).trans_lt
        (Nat.pow_lt_pow_right (by decide) (by omega))
    have h := LogProg.length_bits_le hpow
    have hg' := hg n
    rw [logSpace_eq] at hg'
    omega
  rw [recordLength_eq]
  have hk : k ≤ k * g n := Nat.le_mul_of_pos_right k hfloor
  nlinarith


/-- The diagonalizer after validation, on embedded binary inputs. It computes the radius,
rewinds, initializes the record, and runs the clocked opposite-verdict suffix.

**Proof sketch.** Use the returning witness capture and two existing seams. Its blank frame
provides the initializer and runner banks. Add the radius, rewind and record envelopes,
then use the logarithmic floor to bound their sum by a fixed multiple of the radius. -/
private lemma sph_valid_machine (M : FinTM Bool) (g : ℕ → ℕ)
    (hg : ∀ n, logSpace n ≤ g n) (c : ℕ) (G : FinTM Bool)
    (hG : G.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n)) :
    ∃ (k : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM k (RecSym M.State (Fin 3)) P) (entry : P) (B : ℕ),
      ∀ x : List Bool, ∃ t b,
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).state = none ∧
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).output =
          [RecSym.digit b] ∧
        (∀ u ≤ t, ∀ j,
          |(D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) u).workTapePos j| ≤
            ((B * g x.length : ℕ) : ℤ)) ∧
        (∀ w : List Bool,
          M.ComputesInTime x w (M.configBound x.length (g x.length)) →
          M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
          b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KI, KR, PS, hFS, hDS, S, sen, C, hS⟩ := sph_record_suffix M G.k
  letI := hFS
  letI := hDS
  let k := KI + KR + G.k + 2
  let e := RecSym.digitEmb M.State (Fin 3)
  let ι := sphWitnessSel KI KR G.k
  let R := embedSilentRetTM ι 1 (G.tm.liftSymbols e)
  let W := sphRewindsTM k M.State 1
  let wen : (Bool ⊕ InputRewindPhase) ⊕ RewindPhase := .inl (.inl false)
  let A := seamCompTM W (.inr RewindPhase.done) S sen
  let aen : ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS := .inl wen
  let D := seamCompTM R (.inr ()) A aen
  let en : (G.State ⊕ Unit) ⊕ (((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS) :=
    .inl (.inl G.tm.q₀)
  let B := c + 3 + C * (4 * M.k + 9)
  refine ⟨k, _, inferInstance, inferInstance, D, en, B, ?_⟩
  intro x
  let ws := (g x.length).bits
  let start := (embedSilentCfg ι 1 (fun _ _ => none) (fun _ => 0) [] []
    ((G.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : G.State → G.State ⊕ Unit)
  have hcap := sph_witness_cap KI KR G.k
  have hstart : start.mapState Sum.inl = Cfg.init en (x.map e) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.mapState_state, embedSilentCfg_state,
        Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_state]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, embedSilentCfg_inputPos,
        Cfg.liftSymbols_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos, Cfg.init_inputPos]
      apply Fin.ext
      change (1 : Fin (x.length + 2)).val = (1 : Fin ((x.map e).length + 2)).val
      rw [Fin.val_one, Fin.val_one]
    · funext j p
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.init_workTapes]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_tape, Cfg.liftSymbols_workTapes,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapes, Option.map_none]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).1,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).1]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.init_workTapePos]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_pos, Cfg.liftSymbols_workTapePos,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).2,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, List.length_nil, Nat.cast_zero]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).2]
    · rw [Cfg.mapState_output, Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]
  obtain ⟨t, hrs, hrc, hrt, hrp, hrf, hro, _, hrh⟩ :=
    sph_radius_run KI KR (Q := M.State) g c G hG x (fun _ _ => none) (fun _ => 0) []
  let r := R.runFrom start t
  have hrs' : r.state = some (Sum.inr ()) := hrs
  let d := r.mapState (fun _ => false)
  have hd : d.state = some false := by rw [Cfg.mapState_state, hrs']; rfl
  obtain ⟨u, hwr, hwc, hwh⟩ := sph_rewinds_run KI KR G.k ws d hd
    (by funext p; rw [Cfg.mapState_workTapes]; exact congrFun hrt p)
    (by rw [Cfg.mapState_workTapePos]; exact hrp)
  have hwi : (d.mapState Sum.inl).mapState Sum.inl = r.mapState (fun _ => wen) := by
    dsimp only [d]
    rw [Cfg.mapState_mapState, Cfg.mapState_mapState]
    rfl
  rw [hwi] at hwr hwc hwh
  let z := W.runFrom (r.mapState fun _ => wen) u
  have hze : z.state = some (Sum.inr RewindPhase.done) := by dsimp only [z]; rw [hwr]
  have hzt (j p) : z.workTapes j p = r.workTapes j p := by
    dsimp only [z]; rw [hwr, Cfg.mapState_workTapes]
  have hzh (j) : z.workTapePos j = Function.update r.workTapePos 1 0 j := by
    dsimp only [z]; rw [hwr]
    have hheads : d.workTapePos = r.workTapePos := by
      funext i
      rw [Cfg.mapState_workTapePos]
    rw [hheads]
  have hzo : z.output = [] := by
    dsimp only [z]; rw [hwr, Cfg.mapState_output]
    exact hro t le_rfl
  let y := z.mapState (fun _ => sen)
  have hy : y.state = some sen := by rw [Cfg.mapState_state, hze]; rfl
  obtain ⟨v, b, hss, hso, hsh, hpred⟩ := hS (g x.length) ws
    ((counterValue_eq _).symm.trans (counterValue_bits _)) y hy
    (by rw [Cfg.mapState_inputPos]; dsimp only [z]; rw [hwr])
    (by
      intro p _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hzh, Function.update_self,
        zero_add, hzt, hrt])
    (by
      intro j hj hjc p
      rw [Cfg.mapState_workTapes, hzt]
      have hjr : j ∉ Set.range ι := by
        rintro ⟨i, hi⟩
        have h := congrArg Fin.val hi
        simp only [ι, sphWitnessSel, Function.Embedding.coeFn_mk] at h
        omega
      exact congrFun (hrf j hjr hjc).1 p)
  have hai : (r.mapState (fun _ => wen)).mapState Sum.inl = r.mapState (fun _ => aen) := by
    rw [Cfg.mapState_mapState]
    rfl
  have hAr := seamCompTM_run_ofCfg W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc
    (rfl : S.runFrom y v = S.runFrom y v)
  rw [hai] at hAr
  have hDr := seamCompTM_run_ofCfg R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc hAr
  rw [hstart] at hDr
  let rR := c * g x.length + ws.length
  let rW := rR + (ws.length + 1)
  let rS := C * (recordLength M.k x.length (g x.length) + ws.length + g x.length + 1)
  let radius := rW + rS
  have hRH (a : ℕ) (ha : a ≤ t) (j) : |(R.runFrom start a).workTapePos j| ≤ (rR : ℤ) := by
    simpa only [abs_zero, zero_add] using hrh a ha j
  have hWH (a : ℕ) (ha : a ≤ u) (j) :
      |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j| ≤ (rW : ℤ) := by
    have h₁ := hwh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hRH t le_rfl j
    calc
      _ ≤ |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j - r.workTapePos j| +
          |r.workTapePos j| := by
            simpa only [sub_zero] using abs_sub_le
              ((W.runFrom (r.mapState fun _ => wen) a).workTapePos j) (r.workTapePos j) (0 : ℤ)
      _ ≤ ((ws.length + 1 : ℕ) : ℤ) + (rR : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [rW]; push_cast; ring
  have hSH (a : ℕ) (ha : a ≤ v) (j) : |(S.runFrom y a).workTapePos j| ≤ (radius : ℤ) := by
    have h₁ := hsh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hWH u le_rfl j
    calc
      _ ≤ |(S.runFrom y a).workTapePos j - z.workTapePos j| + |z.workTapePos j| := by
        simpa only [sub_zero] using
          abs_sub_le ((S.runFrom y a).workTapePos j) (z.workTapePos j) (0 : ℤ)
      _ ≤ (rS : ℤ) + (rW : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [radius]; push_cast; ring
  have hAH := sph_seam_heads W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hWH a ha j).trans (by dsimp only [radius]; push_cast; omega))
    (by intro a ha j; rw [sub_zero]; exact hSH a ha j)
  rw [hai] at hAH
  have hDH := sph_seam_heads R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hRH a ha j).trans (by dsimp only [radius, rW]; push_cast; omega)) hAH
  rw [hstart] at hDH
  have hsize : radius ≤ B * g x.length := by
    have hrecord := sph_record_size g hg M.k x.length
    have hbits : ws.length ≤ g x.length := length_bits_le_self _
    have hfloor : 1 ≤ g x.length := by have h := hg x.length; rw [logSpace_eq] at h; omega
    have h := Nat.mul_le_mul_left C hrecord
    dsimp only [radius, rW, rR, rS, B]
    nlinarith
  refine ⟨t + 1 + (u + 1 + v), b, ?_, ?_, ?_, hpred⟩
  · rw [hDr, Cfg.mapState_state, Cfg.mapState_state, hss, Option.map_none, Option.map_none]
  · rw [hDr, Cfg.mapState_output, Cfg.mapState_output, hso, Cfg.mapState_output,
      hzo, List.nil_append]
  · intro a ha j
    have h := hDH a ha j
    rw [sub_zero] at h
    exact h.trans (by exact_mod_cast hsize)


/-- Turn a certified bounded halting run into a first-exit contract at its first halt.

**Proof sketch.** The public first-halt theorem preserves the endpoint and shortens the
run. Restrict the given head envelope to that prefix and use equality as the precondition. -/
private lemma sph_halt_contract {k : ℕ} {Γ P : Type} {ys : List Γ}
    (M : MultiTapeTM k Γ P) (entry : P) (d : Cfg k Γ P ys) (t B : ℕ)
    (ht : (M.runFrom d t).state = none)
    (hh : ∀ u ≤ t, ∀ j, |(M.runFrom d u).workTapePos j| ≤ (B : ℤ)) :
    ∃ C : Contract M entry {none} Unit ys,
      (∀ a, C.pre () a ↔ a = d) ∧ C.post () d = M.runFrom d t ∧
      (∀ a j, C.lo () a j = -(B : ℤ) ∧ C.hi () a j = (B : ℤ)) := by
  obtain ⟨u, hu, hc, he⟩ := M.exists_first_halt d ht
  let C : Contract M entry {none} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => u
      post := fun _ _ => M.runFrom d t
      lo := fun _ _ _ => -(B : ℤ)
      hi := fun _ _ _ => (B : ℤ)
      run := by intro _ a _ ha; subst a; exact he
      exit_mem := by intro _ a _ _; exact ht
      cut := by
        intro _ a _ ha v hv
        subst a
        exact hc v hv
      env := by
        intro _ a _ ha v hv j
        subst a
        rw [Finset.mem_Icc]
        exact abs_le.mp (hh v (hv.trans hu) j) }
  exact ⟨C, fun _ => Iff.rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩


/-- Add the published input validator to a binary-input machine. Foreign symbols are rejected
before its work tapes are used, so the resulting finite machine is space bounded on all inputs.

**Proof sketch.** The validation contract branches to a first-halt contract of the supplied
machine or the false emitter. Both use the same absolute head interval. Read the branch's
public endpoint and envelope equations, then sum the interval bound over the physical tapes. -/
private lemma sph_validated_machine {k : ℕ} {Q P : Type} [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P]
    (V : MultiTapeTM k (RecSym Q (Fin 3)) P) (entry : P) (S : ℕ → ℕ)
    (pred : List Bool → Bool → Prop)
    (hV : ∀ x : List Bool, ∃ t b,
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).state = none ∧
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).output =
        [RecSym.digit b] ∧
      (∀ u ≤ t, ∀ j,
        |(V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) u).workTapePos j| ≤
          (S x.length : ℤ)) ∧ pred x b) :
    ∃ D : FinTM (RecSym Q (Fin 3)),
      ∀ ys : List (RecSym Q (Fin 3)), ∃ t b,
        D.ComputesInTime ys [RecSym.digit b] t ∧
        D.tm.spaceUsed (D.tm.initCfg ys) t ≤ k * (2 * S ys.length + 1) ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x b := by
  classical
  let F : MultiTapeTM k (RecSym Q (Fin 3)) (ScanPhase Bool) :=
    inputFoldTM k (fun a c => a && sphDigit c) true
  let E := sphEmitTM k (RecSym.digit false : RecSym Q (Fin 3))
  let R := seamCompTM₂ F (.done true) (.done false) V entry E ()
  let en : (ScanPhase Bool ⊕ P) ⊕ Unit := .inl (.inl (.fwd true))
  let D : FinTM (RecSym Q (Fin 3)) :=
    { k := k
      State := (ScanPhase Bool ⊕ P) ⊕ Unit
      fintypeState := inferInstance
      decEqState := inferInstance
      tm := {R with q₀ := en} }
  refine ⟨D, ?_⟩
  intro ys
  let a : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys := Cfg.init (.fwd true) ys
  obtain ⟨b, hr, hvalid, hcut, hheads⟩ := sph_validation_run a
    (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
  let a' := {a with state := some (ScanPhase.done b)}
  let radius := S ys.length
  have hrad : (0 : ℤ) ≤ radius := Int.natCast_nonneg _
  let C₀ : Contract F (.fwd true) {some (.done true), some (.done false)} Unit ys :=
    { pre := fun _ d => d = a
      time := fun _ _ => 2 * ys.length + 2
      post := fun _ _ => a'
      lo := fun _ _ _ => -(radius : ℤ)
      hi := fun _ _ _ => (radius : ℤ)
      run := by intro _ d _ hd; subst d; exact hr
      exit_mem := by
        intro _ d _ _
        cases b <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, a', or_true, true_or]
      cut := by
        intro _ d _ hd u hu hm
        subst d
        rcases hm with hm | hm
        · exact hcut u hu true hm
        · exact hcut u hu false hm
      env := by
        intro _ d _ hd u hu j
        subst d
        rw [hheads j u hu, Cfg.init_workTapePos, Finset.mem_Icc]
        exact ⟨by omega, hrad⟩ }
  have hstart₁ : a'.mapState (fun _ => entry) = Cfg.init entry ys := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  have hC₁ : ∃ C₁ : Contract V entry {none} Unit ys,
      (b = true → C₁.pre () (Cfg.init entry ys)) ∧
      (∀ d j, C₁.lo () d j = -(radius : ℤ) ∧ C₁.hi () d j = (radius : ℤ)) ∧
      (b = true → ∃ ans,
        (C₁.post () (Cfg.init entry ys)).state = none ∧
        (C₁.post () (Cfg.init entry ys)).output = [RecSym.digit ans] ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans) := by
    by_cases hb : b = true
    · obtain ⟨x, rfl⟩ := hvalid.mp hb
      obtain ⟨v, ans, hvs, hvo, hvh, hp⟩ := hV x
      obtain ⟨C₁, hpre, hpost, henv⟩ := sph_halt_contract V entry
        (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) v radius hvs
        (by simpa only [radius, List.length_map] using hvh)
      refine ⟨C₁, fun _ => (hpre _).mpr rfl, henv, ?_⟩
      intro _
      refine ⟨ans, ?_, ?_, ?_⟩
      · rw [hpost]; exact hvs
      · rw [hpost]; exact hvo
      · intro x' hx
        have heq : x = x' := List.map_injective_iff.mpr (RecSym.digitEmb Q (Fin 3)).injective hx
        subst x'
        exact hp
    · let C₁ : Contract V entry {none} Unit ys :=
        { pre := fun _ _ => False
          time := fun _ _ => 0
          post := fun _ d => d
          lo := fun _ _ _ => -(radius : ℤ)
          hi := fun _ _ _ => (radius : ℤ)
          run := by intro _ _ _ h; exact False.elim h
          exit_mem := by intro _ _ _ h; exact False.elim h
          cut := by intro _ _ _ h; exact False.elim h
          env := by intro _ _ _ h; exact False.elim h }
      exact ⟨C₁, fun h => False.elim (hb h), fun _ _ => ⟨rfl, rfl⟩,
        fun h => False.elim (hb h)⟩
  obtain ⟨C₁, hpre₁, henv₁, hpost₁⟩ := hC₁
  have hne : (ScanPhase.done true : ScanPhase Bool) ≠ .done false := by
    intro h; cases h
  let C := Contract.branch hne C₀ C₁ (sphEmitContract (RecSym.digit false) ys)
    (fun _ => ()) (fun _ => ())
    (by
      intro _ d _ hd he
      have hb : b = true := ScanPhase.done.inj (Option.some.inj he)
      change C₁.pre () (a'.mapState fun _ => entry)
      rw [hstart₁]
      exact hpre₁ hb)
    (fun _ _ _ _ _ => True.intro)
  let d₀ : Cfg k (RecSym Q (Fin 3)) ((ScanPhase Bool ⊕ P) ⊕ Unit) ys := Cfg.init en ys
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl (.fwd true))) := Cfg.init_state _ _
  have hpre : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => ScanPhase.fwd true) = a
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  have hh (u : ℕ) (hu : u ≤ C.time () d₀) (j) :
      |(R.runFrom d₀ u).workTapePos j| ≤ (radius : ℤ) := by
    have h := C.env () d₀ hd₀ hpre u hu j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    rw [(henv₁ _ j).1, (henv₁ _ j).2] at h
    simp only [a', a, Cfg.mapState_workTapePos, Cfg.init_workTapePos] at h
    split_ifs at h
    · simpa only [min_self, max_self, Finset.mem_Icc, ← abs_le] using h
    · rw [min_eq_left (by omega), max_eq_left hrad, Finset.mem_Icc] at h
      exact abs_le.mpr h
  have hend : ∃ ans,
      (R.runFrom d₀ (C.time () d₀)).state = none ∧
      (R.runFrom d₀ (C.time () d₀)).output = [RecSym.digit ans] ∧
      ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans := by
    have hr' := C.run () d₀ hd₀ hpre
    rw [Contract.branch_post] at hr'
    dsimp only [C₀] at hr'
    by_cases hb : b = true
    · obtain ⟨ans, hs, ho, hp⟩ := hpost₁ hb
      rw [if_pos (by change some (ScanPhase.done b) = some (.done true); rw [hb]),
        hstart₁] at hr'
      refine ⟨ans, ?_, ?_, hp⟩
      · rw [hr', Cfg.mapState_state, Cfg.mapState_state, hs, Option.map_none, Option.map_none]
      · rw [hr', Cfg.mapState_output, Cfg.mapState_output, ho]
    · rw [if_neg (by intro h; exact hb (ScanPhase.done.inj (Option.some.inj h)))] at hr'
      refine ⟨false, ?_, ?_, ?_⟩
      · rw [hr', Cfg.mapState_state]
        rfl
      · rw [hr', Cfg.mapState_output]
        dsimp only [sphEmitContract]
        rw [Cfg.mapState_output, Cfg.init_output, List.nil_append]
      · intro x hx
        exact False.elim (hb (hvalid.mpr ⟨x, hx⟩))
  obtain ⟨ans, hstate, hout, hp⟩ := hend
  have hrun (u : ℕ) : D.tm.runFrom (D.tm.initCfg ys) u = R.runFrom d₀ u := by
    rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]
  refine ⟨C.time () d₀, ans, ?_, ?_, hp⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hrun]
    exact ⟨hstate, hout⟩
  · apply MultiTapeTM.spaceUsed_le_of_abs_le
    intro u hu j
    rw [hrun, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos, sub_zero]
    exact hh u hu j


/-- A space-constructible radius admits a diagonal language for any fixed finite binary
machine: whenever that machine halts within the radius, the language gives the opposite bit.

**Proof sketch.** Validate before computing the radius and running the fixed machine's window.
Choose the resulting total output as the language's indicator. The all-input head envelope
bounds space at the halting time and hence at every time. Apply the published alphabet
reduction and absorb its constants using the constructible bound's logarithmic floor. -/
private lemma sph_diagonal_language (M : FinTM Bool) (g : ℕ → ℕ) (hg : SpaceConstructible g) :
    ∃ L : Language Bool, L ∈ SPACE g ∧
      ∀ (x w : List Bool),
        M.ComputesInTime x w (M.configBound x.length (g x.length)) →
        M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
        MultiTapeTM.indicator (L : Set (List Bool)) x = !(decide (w = [true])) := by
  classical
  obtain ⟨hfloor, c, _, G, hG⟩ := (spaceConstructible_iff g).mp hg
  obtain ⟨k, P, hFP, hDP, V, entry, B, hV⟩ := sph_valid_machine M g hfloor c G hG
  letI := hFP
  letI := hDP
  let pred (x : List Bool) (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length (g x.length)) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
    b = !(decide (w = [true]))
  obtain ⟨D, hD⟩ := sph_validated_machine V entry (fun n => B * g n) pred hV
  choose t answer ht hs hp using hD
  let e := RecSym.digitEmb M.State (Fin 3)
  let L : Language Bool := {x | answer (x.map e) = true}
  have hind (x : List Bool) : MultiTapeTM.indicator (L : Set (List Bool)) x =
      answer (x.map e) := by
    let bit := MultiTapeTM.indicator (L : Set (List Bool)) x
    let E : FinTM Bool :=
      { k := 0
        State := Unit
        fintypeState := inferInstance
        decEqState := inferInstance
        tm := sphEmitTM 0 bit }
    have hleaf := (sph_emit_run bit (E.tm.initCfg x)
      (by rw [MultiTapeTM.initCfg_eq, Cfg.init_state])).1
    have he : E.ComputesInTime x [bit] 1 := by
      apply (FinTM.computesInTime_iff _ _ _ _).mpr
      rw [hleaf]
      refine ⟨rfl, ?_⟩
      rw [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append]
    have hlang := (E.toFinNDTM_haltsWithin_and_accepts_iff (L := L) he).2
    have hacc : E.toFinNDTM.AcceptsWithin x 1 ↔ bit = true := by
      rw [FinNDTM.acceptsWithin_iff]
      constructor
      · rintro ⟨w, hw, _, ho⟩
        simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
          MultiTapeTM.toNDTM_runWith, hw] at ho
        rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append] at ho
        exact List.singleton_inj.mp ho
      · intro hb
        refine ⟨[false], rfl, ?_, ?_⟩
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton, hleaf]
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton]
          rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append, hb]
    have htest : answer (x.map e) = true ↔ bit = true := hlang.trans hacc
    change bit = answer (x.map e)
    exact Bool.eq_iff_iff.mpr htest.symm
  let S (n : ℕ) := k * (2 * (B * g n) + 1)
  obtain ⟨c', N, hN⟩ := FinTM.decidesInSpace_of_alphabetReduction e D L S
    (by
      intro x
      refine ⟨t (x.map e), ?_⟩
      rw [hind, List.map_singleton, RecSym.digitEmb_apply]
      exact ht (x.map e))
    (by
      intro ys u
      exact (ht ys).spaceUsed_le_of_halt (hs ys) u)
  have hL : L ∈ SPACE (fun n => S n + 1) := mem_SPACE_iff.mpr ⟨c', N, hN⟩
  have hb (n : ℕ) : S n + 1 ≤ (k * (2 * B + 1) + 1) * g n := by
    have hn : 1 ≤ g n := by have h := hfloor n; rw [logSpace_eq] at h; omega
    calc
      _ ≤ k * (2 * (B * g n) + g n) + g n :=
        Nat.add_le_add (Nat.mul_le_mul_left k (Nat.add_le_add_left hn _)) hn
      _ = _ := by ring
  refine ⟨L, SPACE.mono_const hb hL, ?_⟩
  intro x w htime hspace
  rw [hind]
  exact hp (x.map e) x rfl w htime hspace


/-- A linear-space decider for the quadratically padded language suffices for the separation
from `NP`. [AB09, Exercise 3.2]

**Proof sketch.** If linear space were `NP`, the padded language would belong to `NP`. Its
polynomial-time padding map pulls it back to the original quadratic-space language, by the
published closure of `NP` under polynomial-time preimages. This reverses the strict inclusion
given by the space hierarchy at the linear and quadratic bounds. -/
private lemma sph_linear_ne_NP_of_padding
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g)
    (hpad : ∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
      ({y | ∃ x ∈ L,
        y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
        SPACE (fun n => n + 1)) :
    SPACE (fun n => n + 1) ≠ NP := by
  intro heq
  have hback : SPACE (fun n => n ^ 2 + 1) ⊆ SPACE (fun n => n + 1) := by
    intro L hL
    let p : List Bool → List Bool := fun x =>
      pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)
    let L' : Language Bool := {y | ∃ x ∈ L, y = p x}
    have hp : PolyTimeComputable p :=
      polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary 1 2)
    have hL' : L' ∈ NP := heq ▸ hpad L hL
    have hpull : p ⁻¹' L' = L := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := (show ∃ y ∈ L, p x = p y from hx)
        have he : x = y := by
          simpa only [p, pairFstD_pairEncode] using congrArg pairFstD hxy
        exact he.symm ▸ hy
      · intro hx
        exact (show ∃ y ∈ L, p x = p y from ⟨x, hx, rfl⟩)
    have hpre := preimage_mem_NP hp hL'
    rw [hpull] at hpre
    exact heq.symm ▸ hpre
  have hstrict := hH (fun n => n + 1) (fun n => n ^ 2 + 1)
    spaceConstructible_linear (spaceConstructible_poly 2 (by norm_num))
    (fun A => ⟨A + 1, fun n hn => by
      nlinarith [Nat.mul_le_mul_right (n + 1) hn]⟩)
  exact hstrict.2 hback

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]): for
space-constructible `f` and `g`, if every constant multiple of `f` is
eventually below `g` (that is, `f = o(g)`), then `SPACE f ⊊ SPACE g`.
Constant-factor hypothesis — no square and no logarithmic term, by a
universal simulation with constant-factor space overhead (the
self-application universal `U₀` of the sketch, the sibling of
`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof uses `g`'s witness and floor but, of `f`'s, only the
bundled floor. Positivity of both bounds is automatic from the bundled
`logSpace` floor, so the zero-bound convention needs no side condition.

**Proof sketch.** *Inclusion.* `hfg` at `A = 1` gives `f n ≤ g n` from some
`N` on; below `N` each `f n` is at most `F := max_{n<N} f n` times
`g n ≥ 1` (`g`'s floor), so `f ≤ max F 1 · g` everywhere and
`Complexity.SPACE.mono_const` applies.

*The universal machine `U₀`.* One fixed machine for the scheme
`Complexity.TimeHierarchy.code`: on an input `x = pairEncode α w` it canonizes
`α` from the doubled prefix (the chapter-1 startup, `Turing.universalCanonTM`),
returns its input head to the origin, and simulates the coded machine on `x`
itself — self-application, so no `preTM` copy is needed — with its own input
head as the simulated one (the native device: the simulated input is all of
`U₀`'s input, so its left boundary is a real blank and no position is stored)
and the step block on the canonical table. Its forward ledger: for each
`α` a constant `C_α` such that whenever the coded machine halts on `x` with
some output, having visited at most `s` cells, `U₀` halts on `x` with the
same output, having visited at most `C_α · (s + 1)` cells
(`Turing.exists_selfUniversal`). This is `space_universal`'s forward clause
with the native device in place of the bounded-prefix ruler, so no header
ruler is needed; only this direction is used.

*The diagonalizer `D`.* On input `x` with `n = |x|`, over the record alphabet:
(i) validate the input (`Turing.inputFoldTM`), so that
`D`'s space is bounded on foreign rich inputs, as
`Turing.FinTM.alphabet_reduction_spaceUsed` requires, and compute
`bits (g n)` by `g`'s witness, captured on a work tape, in `O(g n)` cells;
(ii) form the radius `r = a · g n` for a fixed `a ≥ 1`
(`a = 1` suffices, the code-dependent constant being paid by the hypothesis
below; a power of two costs only low zero digits) and write `U₀`'s initial
record on `x` at radius `r`, tagged with the empty-output summary
(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner at `U₀`
(`Turing.exists_configWindowRunnerTM`): each round tests the record for a halted state, else
applies one step of `U₀` (leaving the window is an exit), the tag updated by the three-valued
output summary `Turing.outSummary` (`summaryTag`; append-compatible,
`Turing.outSummary_append_congr`; coded in `Fin 3`), so the emitted word is never buffered.
The runner carries its own configuration-count clock, whose value suffices for every round up
to `Turing.FinTM.configBound U₀ n r + 1`, in `O(record length)` cells.
(iv) Answer `false` if the runner stopped at a halted
record with summary `accept` (output exactly `[true]`,
`Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
with another output, window exit, or clock exhaustion. `D` halts on every
input. Its cells are the witness's `O(g n)`, the record's
`k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
runner's `O(record length)` scratch and clock: all `O(g n)` with
constants depending only on `U₀` and `g`'s witness, **uniformly in the code
part of `x`**, because the window, not `U₀`'s constant, bounds the
simulation; the `posWidth n = O(logSpace n)` terms are
absorbed by `g`'s floor. After the alphabet reduction, the language `L_D`
that `D` decides lies in `SPACE g`.

*`L_D ∉ SPACE f`.* Suppose `M` decides `L_D` within `c₀ · f n` cells. Then
`M` halts within `configBound M n (c₀ · f n)` steps
(`Turing.FinTM.ComputesInTime.of_spaceUsed_le`), and its space bound holds at
every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
configuration frozen after it). The space-faithful normal form
`Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N` within the same space
(`Turing.exists_codeTM_spaceUsed`) and set
`α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
`[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
where `A := C_{α_M} · (c · c₀ + c + 1)`, using `1 ≤ f n`. The hypothesis
`hfg` at this one `A` gives `N₀` with `A · f n ≤ g n ≤ r` for `n ≥ N₀`;
take `w := List.replicate N₀ true`. Then every configuration of `U₀`'s run
on `x` up to its halt is in the radius-`r` window, since each
tape's visited cells form an interval around `0` of size at most `r`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`) and every nonblank cell was
visited (`Turing.MultiTapeTM.mem_visited_of_ne_none`); and the halt comes by
step `configBound U₀ n r` (`ComputesInTime.of_spaceUsed_le` at the bound
`r`), before the clock runs out. So the runner stops at `U₀`'s halted record,
whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. The construction uses
`U₀` with its forward ledger (the step block at one coded work tape, the
native input device and the chapter-1 startup); the configuration-count
windowed runner `exists_configWindowRunnerTM` at `U₀` with the output-summary tag, after
the record initializer `exists_recordInitTM` and followed by the record test
`exists_recordTestTM`; the radius phase (`g`'s witness captured, radius digits);
the window-containment lemma from the visited-interval facts;
`exists_codeTM_spaceUsed` and the all-times space bound of a decider; the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
alphabet reduction. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  classical
  obtain ⟨U, hU⟩ := exists_selfUniversal TimeHierarchy.code
  obtain ⟨L, hLg, hdiag⟩ := sph_diagonal_language U g hg
  refine ⟨sph_inclusion hg hfg, ?_⟩
  intro hback
  obtain ⟨c, M, hM⟩ := mem_SPACE_iff.mp (hback hLg)
  obtain ⟨x, t, ht, hs, htime, _⟩ := sph_code_window f g hf hfg U hU L c M hM
  rw [htime] at ht hs
  have h := hdiag x [MultiTapeTM.indicator (L : Set (List Bool)) x] ht hs
  cases hb : MultiTapeTM.indicator (L : Set (List Bool)) x <;>
    simp only [hb, List.cons.injEq, and_true, Bool.false_eq_true, Bool.true_eq_false, decide_false,
      decide_true, Bool.not_false, Bool.not_true] at h

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear`; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  exact sph_logspace_ssubset space_hierarchy

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` — the literal `SPACE(n)` is the zero-work-tape class).
Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. Padding transfers space bounds down: for
`L ∈ SPACE (n² + 1)`, the padded language
`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate ((|x| + 1)²) true)}` (padded members of
`L` only; padded length exactly `m = (n + 1)² + 2n + 2`) lies in `SPACE (m + 1)`: validate the
padding, then run the `L`-decider on the first component, the pad supplying the room. So
`L' ∈ NP` by the assumption. The padding map is polynomial-time computable and `L` is the
preimage of `L'` under it, so `L ∈ NP` (`Complexity.preimage_mem_NP`), that is
`L ∈ SPACE (n + 1)`. Hence `SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). The argument uses the padded-language space decider,
the padding map's polynomial-time computability, `preimage_mem_NP` and the strictness
extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity

#print axioms Complexity.space_hierarchy
#print axioms Complexity.LOGSPACE_ssubset_PSPACE

## ===== campaign/gates/109-h-landing-fill/evidence/seal/seal-head-before-M5-revert.out =====

35070b60 Merge remote-tracking branch 'origin/complexity/arora-barak-ch3-4' into lean/b6h-landing
157 74
1
Scratch/HSealHead.lean:147:8: warning: declaration uses 'sorry'
Scratch/HSealHead.lean:244:21: error: Application type mismatch: The argument
  ((spaceConstructible_iff g).mp hg).left n
has type
  logSpace n ≤ g n
but is expected to have type
  ?m.45 n < g n
in the application
  Nat.one_le_of_lt (((spaceConstructible_iff g).mp hg).left n)
Scratch/HSealHead.lean:309:21: error: Application type mismatch: The argument
  ((spaceConstructible_iff f).mp hf).left x.length
has type
  logSpace x.length ≤ f x.length
but is expected to have type
  ?m.396 < f x.length
in the application
  Nat.one_le_of_lt (((spaceConstructible_iff f).mp hf).left x.length)
Scratch/HSealHead.lean:1890:44: error: Application type mismatch: The argument
  hg n
has type
  logSpace n ≤ g n
but is expected to have type
  ?m.42 < g n
in the application
  Nat.one_le_of_lt (hg n)
Scratch/HSealHead.lean:2086:53: error: Application type mismatch: The argument
  hg x.length
has type
  logSpace x.length ≤ g x.length
but is expected to have type
  ?m.2124 < g x.length
in the application
  Nat.one_le_of_lt (hg x.length)
Scratch/HSealHead.lean:2382:42: error: Application type mismatch: The argument
  hfloor n
has type
  logSpace n ≤ g n
but is expected to have type
  ?m.570 < g n
in the application
  Nat.one_le_of_lt (hfloor n)
Scratch/HSealHead.lean:2579:8: warning: declaration uses 'sorry'
'Complexity.space_hierarchy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LOGSPACE_ssubset_PSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
exit=1

[exited with code 0]

## ===== campaign/gates/109-h-landing-fill/evidence/seal/seal-head.out =====

Scratch/HSealHead.lean:147:8: warning: declaration uses 'sorry'
Scratch/HSealHead.lean:2579:8: warning: declaration uses 'sorry'
'Complexity.space_hierarchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LOGSPACE_ssubset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0

## ===== TCSlib/Complexity/SpaceComplexity/Hierarchy.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with the space-bounded universal machine of
[AB09, Exercise 4.1] (its forward clause, as the book states it), the
strictness corollary `L ⊊ PSPACE` on the p. 92 chain, and `SPACE(n+1) ≠ NP`
([AB09, Exercise 3.2], stated with the positive normalization). The universal
machine statement has a forward clause with the addend-free bound `C · s`;
the hierarchy uses a fixed self-application universal machine inside a
space-bounded configuration window.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and the layout
  `⟨bits s, ⟨α, x⟩⟩`, and keeps only Exercise 4.1's forward clause: a run of
  the coded machine within `s` work cells is reproduced, output included,
  within constant-factor space. Overruns and divergence are unconstrained, so
  the machine tests no budget, runs no clock and replays nothing. Its space
  bound is Exercise 4.1's `C_α · t`, with no addend: the simulated input, a
  suffix of its input, is read through the bounded-prefix ruler device
  (`Turing.exists_rulerHostTM`), a unary ruler of the header's length, which
  the bound absorbs because every qualifying run visits a cell.
* **The hierarchy takes the window route**: the
  diagonalizer runs one fixed self-application universal machine `U₀` in a
  window of radius `a · g(n)` on the configuration-record rows
  (`Build/CfgRecord.lean`, `Build/RecordTable.lean`), stopped by a
  configuration-count clock, and flips its verdict. The window, not `U₀`'s
  code-dependent constant, bounds the diagonalizer's space. The chapter-1
  interpreter (`Turing.universalInterpreter`) serves neither machine: it
  tracks the simulated input head in unary on its fourth tape, which uses one
  plus the largest simulated input position reached, `Θ(n + 1)` cells on a
  full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
  `S`.
* **Both bounds space-constructible**, as in the book; `g`'s witness drives
  the window radius, and of `f` the proof uses only the
  bundled floor `1 ≤ logSpace n ≤ f n`.
* The `SpaceComplexity.lean` facade imports this module.

## Main results

* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12; addend-free `C · s` since 2026-10-13).
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1], p. 93,
forward clause; spec, fill pending — phase P4.3, restated forward-only
2026-10-12 by design §16b item 3, RD-3 statement gate passed 2026-10-13;
strengthened to the addend-free `C · s` 2026-10-13, statement gate passed
2026-10-14):
for the fixed scheme there is a machine `SU` such that for every code `α`
there is a constant `C > 0` with: whenever the coded machine halts on `x`
with `output`, having visited at most `s` work cells by then, `SU` on input
`⟨bits s, ⟨α, x⟩⟩` halts with the same `output`, having visited at most
`C · s` work cells: the book's `C · t`. Nothing is claimed when the coded
machine overruns `s` or does not halt. The time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound. Every
qualifying run has `s ≥ 1` (`Turing.CodeTM.one_le_spaceUsed`), so the bound
is never `0`.

Deviations from the book's `SU(α, t, x) = M_α(x)` within `C · t` cells:
* **`C` depends on the representation `α`**, not only on `M_α`, as in
  `Turing.universal`, whose module docstring records why an arbitrary
  effective scheme forces this.
* "Halts before using `t` cells" is read as "at most `s` visited cells"; the
  budget is an argument of `SU`, as in the book, but is never read.
* The output is the simulated output itself: with no failure clause there is
  no verdict to tag. The former `[false]` clause, and with it the
  visited-interval counters, the core-count clock and the probe/replay of the
  previous statement, went with design §16b item 3.

There is no input-device addend: the gated `+ logSpace |x| + 1` (a binary
position for the simulated input head) is replaced by a unary ruler of the
header's length, whose cells the bound absorbs (the RD-3 gate's minor 1).

**Proof sketch.** A code-first interpreter in three parts. (i) **Startup.**
Parse the header `bits s`, `α` and the two separators by a finite-state pair
scan, writing one ruler cell per header cell, so that the ruler is `true^ℓ`
with `ℓ = 2|bits s| + 2|α| + 4` (`Turing.pairEncode_pairEncode_length`,
`Turing.pairEncode_pairEncode_drop`) and the physical input head ends at
`ℓ + 1`, the virtual position `1`; the budget is never read. Canonize `α`
into the table and state tapes as `U₀`'s startup does
(`Turing.exists_selfStartupTM`'s phases, reading the code where the header
holds it). Its cells are a constant depending only on `α`
(`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's halting time);
the effective scheme supplies no bound linear in `|α|`, and none is claimed.
(ii) **Input device and step block** (H5's bounded-prefix ruler device and
H2). Run `U₀`'s wrapped round loop (`Turing.exists_selfUniversal`'s sketch:
H2's step block on the output-erased source, with the leaf that forwards each
emission before the next round and before the halt) through the ruler host
`Turing.exists_rulerHostTM` on the virtual input `x`. The host is a positive
finite block simulation: it reads a blank and suppresses left moves at the
virtual left boundary, which it tests by restoring sweeps of `ℓ` cells
(`Turing.exists_rulerTestTM`), so `SU` halts exactly when the round loop does,
with its output, the coded machine's. The chapter-1 interpreter's device
cannot serve: its fourth tape holds a unary boundary marker whose head
`applyRecord` moves with the input head (`Turing.universalInterpreter`), so
that tape uses one plus the largest simulated input position reached,
`Θ(|x| + 1)` cells on a full scan, which a budget `s = o(|x|)` does not
cover (Finding B). (iii) **Space.** The host's bank visits exactly the round
loop's cells: the mirrored tape only the coded machine's, at most `s`, and the
table and summary tapes `O(|table| + 1)`, a constant for fixed `α`. Its ruler
visits `ℓ + 2` cells. Every qualifying run has `s ≥ 1`
(`Turing.CodeTM.one_le_spaceUsed`) and `|bits s| ≤ s`
(`Turing.length_bits_le_self`), so `ℓ ≤ 2s + 2|α| + 4 ≤ (2|α| + 6) · s`, and
the total `C_α + s + ℓ + 2` is at most `C · s`. Fill obligations, named: the
header-ruler startup with the buffered canonization; the H5 ruler host;
`U₀`'s wrapped round loop (H2 at one coded work tape, with its head
envelope); the per-code constant ledger. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * s := by
  sorry

/-- The inclusion half: `hfg` at `A = 1` from some `N` on, and `g`'s floor below `N`.
[AB09, Theorem 4.8, inclusion]

**Proof sketch.** Bound the finitely many exceptional values by their supremum. The positive
floor of `g` absorbs that supremum into one constant, and `SPACE.mono_const` applies. -/
private lemma sph_inclusion {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) : SPACE f ⊆ SPACE g := by
  obtain ⟨N, hN⟩ := hfg 1
  have hfloor : ∀ n, 1 ≤ g n := fun n =>
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff g).mp hg).1 n)
  set F := (Finset.range N).sup f with hF
  refine SPACE.mono_const (a := F + 1) fun n => ?_
  by_cases hn : N ≤ n
  · have := hN n hn
    calc f n ≤ g n := by simpa using this
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · have hle : f n ≤ F := Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))
    calc f n ≤ F + 1 := by omega
      _ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)

/-- A decider in the smaller space class has a padded code on which the fixed universal
machine halts inside the larger window, before its configuration-count clock expires.
[AB09, Theorem 4.8, diagonal contradiction]

**Proof sketch.** Normalize the decider to one binary work tape and then to a coded machine,
using the published space clauses. Choose the domination constant after the code's universal
simulation constant is fixed, and pad the payload to the resulting threshold. The configuration
bound supplies a halting time; the window-summary theorem identifies the run at the next round. -/
private lemma sph_code_window (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) (U₀ : FinTM Bool)
    (hU : ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (TimeHierarchy.code.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
          ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
        ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
          U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1))
    (L : Language Bool) (c₀ : ℕ) (M : FinTM Bool)
    (hM : M.DecidesInSpace L (fun n => c₀ * f n)) :
    ∃ (x : List Bool) (t : ℕ),
      U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t ∧
      U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length ∧
      t = U₀.configBound x.length (g x.length) ∧
      windowRun U₀.tm (g x.length) summaryTag (t + 1) (U₀.tm.initCfg x) 0 =
        (.halted, U₀.tm.runFrom (U₀.tm.initCfg x) t,
          outSummaryCode (outSummary [MultiTapeTM.indicator (L : Set (List Bool)) x])) := by
  have hm := (FinTM.decidesInSpace_iff M L (fun n => c₀ * f n)).mp hM
  have hbounds := hm.computesFunInTime_and_forall_spaceUsed_le
  obtain ⟨M₁, c₁, hk, htime, hspace⟩ := FinTM.one_work_tape_binary_spaceUsed M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
    (fun n => M.configBound n (c₀ * f n)) (fun n => c₀ * f n) hbounds.1 hbounds.2
  obtain ⟨N, hrun, hsp⟩ := exists_codeTM_spaceUsed M₁ hk
  let α := TimeHierarchy.code.encode N
  have hα : TimeHierarchy.code.decode α = N := MachineCode.decode_encode _ _
  obtain ⟨C, _hC, hsim⟩ := hU α
  let A := C * (c₁ * c₀ + c₁ + 1)
  obtain ⟨N₀, hN₀⟩ := hfg A
  let x := pairEncode α (List.replicate N₀ true)
  have hx : N₀ ≤ x.length := by
    simp only [x, length_pairEncode, List.length_replicate]
    omega
  let t₀ := c₁ * (M.configBound x.length (c₀ * f x.length) + 1) ^ 2
  have hn : (TimeHierarchy.code.decode α).toFinTM.ComputesInTime x
      [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ := by
    rw [hα]
    exact (hrun x _ t₀).mpr ((FinTM.computesFunInTime_iff _ _ _).mp htime x)
  have hs : (TimeHierarchy.code.decode α).toFinTM.tm.spaceUsed
      ((TimeHierarchy.code.decode α).toFinTM.tm.initCfg x) t₀ ≤
      c₁ * (c₀ * f x.length + 1) := by
    rw [hα, hsp]
    exact hspace x t₀
  obtain ⟨u, hu, hsu⟩ := hsim (List.replicate N₀ true)
    [MultiTapeTM.indicator (L : Set (List Bool)) x] t₀ (c₁ * (c₀ * f x.length + 1)) hn hs
  have hfloor : 1 ≤ f x.length :=
    le_trans (by rw [logSpace_eq]; omega) (((spaceConstructible_iff f).mp hf).1 x.length)
  have hsmall : C * (c₁ * (c₀ * f x.length + 1) + 1) ≤ A * f x.length := by
    calc
      _ ≤ C * (c₁ * (c₀ * f x.length + f x.length) + f x.length) :=
        Nat.mul_le_mul_left C (Nat.add_le_add
          (Nat.mul_le_mul_left c₁ (Nat.add_le_add_left hfloor _)) hfloor)
      _ = A * f x.length := by dsimp only [A]; ring
  have hwindow : U₀.tm.spaceUsed (U₀.tm.initCfg x) u ≤ g x.length :=
    hsu.trans (hsmall.trans (hN₀ x.length hx))
  let t := U₀.configBound x.length (g x.length)
  have hhalt : U₀.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] t :=
    hu.of_spaceUsed_le hwindow
  have hspace' : U₀.tm.spaceUsed (U₀.tm.initCfg x) t ≤ g x.length :=
    hu.spaceUsed_le_of_halt hwindow t
  exact ⟨x, t, hhalt, hspace', rfl,
    windowRun_summary_of_halts U₀ x hhalt hspace' (Nat.lt_succ_self t)⟩

/-- A square below a power of two, from `4` on.

**Proof sketch.** Induct from `4`; doubling the previous power absorbs the next square. -/
private lemma sph_sq_le_two_pow : ∀ L, 4 ≤ L → L * L ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

/-- The logarithm is dominated by the identity at every constant factor, eventually.

**Proof sketch.** Beyond `2 ^ max 4 (2 * A)`, the integer logarithm is at least both `4` and
`2 * A`. Its square fits below `n`, and dominates `A * (log₂ n + 1)`. -/
private lemma sph_logSpace_dom : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logSpace n ≤ n + 1 := by
  intro A
  refine ⟨2 ^ (max 4 (2 * A)), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := max 4 (2 * A)); omega
  set L := Nat.log 2 n with hL
  have hLge : max 4 (2 * A) ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hsq := sph_sq_le_two_pow L (le_trans (le_max_left _ _) hLge)
  have h2A : 2 * A ≤ L := le_trans (le_max_right _ _) hLge
  rw [logSpace_eq, ← hL]
  nlinarith

/-- **`LOGSPACE ⊂ PSPACE`**, from the space hierarchy's statement. [AB09, §4.3.2]

**Proof sketch.** Apply the hierarchy to logarithmic and linear space, then transport strictness
along the published inclusion of linear space into polynomial space. -/
private lemma sph_logspace_ssubset
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g) :
    LOGSPACE ⊂ PSPACE := by
  have hlin : SPACE (fun n => n + 1) ⊆ PSPACE := by
    have := space_poly_subset_PSPACE 1
    simpa only [pow_one] using this
  obtain ⟨-, hnot⟩ := hH logSpace (fun n => n + 1) spaceConstructible_logSpace
    spaceConstructible_linear sph_logSpace_dom
  refine ⟨LOGSPACE_subset_PSPACE, fun hP => hnot ?_⟩
  rw [← LOGSPACE_eq]
  exact hlin.trans hP

/-- One input-head move before the lifted rewind. The rewind's published contract requires a
positive input position; this leaf supplies it even when the radius witness stops at `0`.
The action changes no work tape or output. [AB09, §1.2]

**Proof sketch.** The transition always moves the input head right and reaches its live anchor.
At the right boundary it stays put; everywhere else its position increases by one. -/
private def sphRightTM (k : ℕ) (Γ : Type) : MultiTapeTM k Γ Bool where
  q₀ := false
  tr := fun _ _ _ => ⟨.pos, fun _ => (none, 0), none, some true⟩

/-- The right-move leaf's framed run and positive endpoint.

**Proof sketch.** Read the one transition field by field, separate the input's right boundary,
and use the zero-step and one-step configurations for the cut and head claim. -/
private lemma sph_right_run {k : ℕ} {Γ : Type} {x : List Γ}
    (d : Cfg k Γ Bool x) (hd : d.state = some false) :
    (sphRightTM k Γ).runFrom d 1 =
        {d with state := some true, inputPos := moveInputPos d.inputPos .pos} ∧
      1 ≤ (moveInputPos d.inputPos .pos).val ∧
      (∀ u < 1, ((sphRightTM k Γ).runFrom d u).state ≠ some true) ∧
      ∀ u ≤ 1, ((sphRightTM k Γ).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphRightTM k Γ).runFrom d 1 =
      {d with state := some true, inputPos := moveInputPos d.inputPos .pos} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]; rfl
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphRightTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphRightTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      simp only [sphRightTM, Option.toList_none, List.append_nil]
  refine ⟨hstep, ?_, ?_, ?_⟩
  · by_cases h : d.inputPos.val = x.length + 1
    · have hp : d.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext h
      rw [hp, SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right _ h]
      exact Nat.succ_pos _
  · intro u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    decide
  · intro u hu
    have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
    rcases this with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]

/-- Emit the final verdict and halt, preserving the input and work tapes. The only output
leaf needed after the record test. [AB09, §1.2] -/
private def sphEmitTM (k : ℕ) {Γ : Type} (b : Γ) : MultiTapeTM k Γ Unit where
  q₀ := ()
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The verdict emitter appends exactly one symbol in one step, with no work-head motion.

**Proof sketch.** Read the five fields of its sole action using the public action equations. -/
private lemma sph_emit_run {k : ℕ} {Γ : Type} {x : List Γ} (b : Γ)
    (d : Cfg k Γ Unit x) (hd : d.state = some ()) :
    (sphEmitTM k b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} ∧
      ∀ u ≤ 1, ((sphEmitTM k b).runFrom d u).workTapePos = d.workTapePos := by
  have hstep : (sphEmitTM k b).runFrom d 1 =
      {d with state := none, output := d.output ++ [b]} := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]
      exact moveInputPos_zero _
    · funext j p
      rw [Action.apply_workTapes]
      simp only [sphEmitTM, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext j
      rw [Action.apply_workTapePos]
      simp only [sphEmitTM, SignType.coe_zero, add_zero]
    · rw [Action.apply_output]
      rfl
  refine ⟨hstep, ?_⟩
  intro u hu
  have : u = 0 ∨ u = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hu
  rcases this with rfl | rfl
  · rw [MultiTapeTM.runFrom_zero]
  · rw [hstep]

/-- The input validator's finite-state test: precisely the embedded binary digits. -/
private def sphDigit {Q : Type} : RecSym Q (Fin 3) → Bool
  | .digit _ => true
  | .cell _ _ => false
  | .st _ => false
  | .tag _ => false

/-- The validator accepts precisely embedded binary words, including the empty word.

**Proof sketch.** Induct on the input. A successful fold forces the head symbol to be a digit;
strip that digit and use the induction hypothesis on the tail. Conversely, prepend the
corresponding Boolean to the decoded tail. -/
private lemma sph_fold_valid {Q : Type} (ys : List (RecSym Q (Fin 3))) (a : Bool) :
    ys.foldl (fun b c => b && sphDigit c) a = true ↔
      a = true ∧ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) := by
  induction ys generalizing a with
  | nil =>
    rw [List.foldl_nil]
    exact ⟨fun h => ⟨h, [], rfl⟩, fun h => h.1⟩
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨hay, x, hx⟩
      obtain ⟨ha, hy⟩ := Bool.and_eq_true_iff.mp hay
      refine ⟨ha, ?_⟩
      cases y with
      | digit b =>
        refine ⟨b :: x, ?_⟩
        rw [List.map_cons, RecSym.digitEmb_apply, ← hx]
      | cell c m => cases hy
      | st q => cases hy
      | tag t => cases hy
    · rintro ⟨ha, x, hx⟩
      cases x with
      | nil => cases hx
      | cons b bs =>
        rw [List.map_cons] at hx
        obtain ⟨hy, ht⟩ := List.cons.inj hx
        refine ⟨Bool.and_eq_true_iff.mpr ⟨ha, ?_⟩, bs, ht⟩
        rw [hy, RecSym.digitEmb_apply]
        rfl

/-- The rich-input validation phase, on all of the diagonalizer's work tapes. Its successful
exit supplies a binary input for every subsequent phase; it moves no work head.
[AB09, Theorem 4.8, alphabet reduction]

**Proof sketch.** Use the published framed input fold and identify its final flag with
`sph_fold_valid`. The framed endpoint also restores the input head to its initial position. -/
private lemma sph_validation_run {k : ℕ} {Q : Type}
    {ys : List (RecSym Q (Fin 3))} (d : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys)
    (hd : d.state = some (.fwd true)) (hin : d.inputPos = 1) :
    ∃ b : Bool,
      (inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d (2 * ys.length + 2) =
        {d with state := some (.done b)} ∧
      (b = true ↔ ∃ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3))) ∧
      (∀ u < 2 * ys.length + 2, ∀ a,
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).state ≠
          some (.done a)) ∧
      ∀ j u, u ≤ 2 * ys.length + 2 →
        ((inputFoldTM k (fun a c => a && sphDigit c) true).runFrom d u).workTapePos j =
          d.workTapePos j := by
  obtain ⟨hr, hc, hh⟩ := inputFoldTM_run_ofCfg (fun a c => a && sphDigit c) true d hd hin
  refine ⟨ys.foldl (fun a c => a && sphDigit c) true, hr, ?_, hc, hh⟩
  exact ⟨fun h => ((sph_fold_valid ys true).mp h).2,
    fun h => (sph_fold_valid ys true).mpr ⟨rfl, h⟩⟩

/-- Witness tapes are after the record, radius, initializer scratch and runner scratch banks.
Separate scratch banks keep the runner disjoint from both the radius and the dirty witness. -/
private def sphWitnessSel (KI KR m : ℕ) : Fin m ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨KI + KR + 2 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : KI + KR + 2 + i.val = KI + KR + 2 + j.val :=
      congrArg (fun z : Fin (KI + KR + m + 2) => z.val) h
    exact Nat.add_left_cancel h'

/-- The radius tape is outside the witness bank, including for a zero-tape witness. -/
private lemma sph_witness_cap (KI KR m : ℕ) :
    (1 : Fin (KI + KR + m + 2)) ∉ Set.range (sphWitnessSel KI KR m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [sphWitnessSel, Function.Embedding.coeFn_mk, Fin.val_one] at this
  omega

/-- The constructibility witness returns with its complete binary radius on tape `1`, preserving
all tapes outside its bank and the radius tape. Its last emission is included in the captured
word. [AB09, Theorem 4.8, radius phase]

**Proof sketch.** Choose the witness's first halting time and lift its run to the record
alphabet. Apply the published returning capture embedding. Its capture and frame equations give
the endpoint. Its selected, capture and frame space equations bound each tape; summing gives a
constant multiple of the witness space and radius length. -/
private lemma sph_radius_run (KI KR : ℕ) {Q : Type} [DecidableEq Q]
    (g : ℕ → ℕ) (c : ℕ) (M : FinTM Bool)
    (hM : M.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n))
    (x : List Bool)
    (tapes : Fin (KI + KR + M.k + 2) → ℤ → Option (RecSym Q (Fin 3)))
    (heads : Fin (KI + KR + M.k + 2) → ℤ) (out : List (RecSym Q (Fin 3))) :
    let e := RecSym.digitEmb Q (Fin 3)
    let ι := sphWitnessSel KI KR M.k
    let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
    let start := (embedSilentCfg ι 1 tapes heads [] out
      ((M.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : M.State → M.State ⊕ Unit)
    ∃ t : ℕ,
      (R.runFrom start t).state = some (Sum.inr ()) ∧
      (∀ u < t, (R.runFrom start u).state ≠ some (Sum.inr ())) ∧
      (R.runFrom start t).workTapes 1 =
        FinTM.bufferTape ((g x.length).bits.map RecSym.digit) ∧
      (R.runFrom start t).workTapePos 1 = ((g x.length).bits.length : ℤ) ∧
      (∀ j, j ∉ Set.range ι → j ≠ 1 →
        (R.runFrom start t).workTapes j = tapes j ∧
          (R.runFrom start t).workTapePos j = heads j) ∧
      (∀ u ≤ t, (R.runFrom start u).output = out) ∧
      R.spaceUsed start t ≤ (KI + KR + M.k + 2) *
        (c * g x.length + (g x.length).bits.length + 1) ∧
      ∀ u ≤ t, ∀ j,
        |(R.runFrom start u).workTapePos j| ≤
          |heads j| + (c * g x.length + (g x.length).bits.length : ℕ) := by
  classical
  dsimp only
  let e := RecSym.digitEmb Q (Fin 3)
  let ι := sphWitnessSel KI KR M.k
  let R := embedSilentRetTM ι 1 (M.tm.liftSymbols e)
  let a := (M.tm.initCfg x).liftSymbols e
  let start := (embedSilentCfg ι 1 tapes heads [] out a).mapState
    (Sum.inl : M.State → M.State ⊕ Unit)
  obtain ⟨v, hv, hsv⟩ := (FinTM.computesInSpace_iff _ _ _).mp hM x
  obtain ⟨hhalt, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp hv
  obtain ⟨t, htv, hlive, heq⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hhalt
  have hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * g x.length :=
    (M.tm.spaceUsed_mono _ htv).trans hsv
  have ho : (M.tm.runFrom (M.tm.initCfg x) t).output = (g x.length).bits :=
    (congrArg Cfg.output heq).trans hout
  have hc : a.state ≠ none := by
    rw [Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have hh : ((M.tm.liftSymbols e).runFrom a t).state = none := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state, heq, hhalt]
  have hl : ∀ u < t, ((M.tm.liftSymbols e).runFrom a u).state ≠ none := by
    intro u hu
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_state]
    exact hlive u hu
  have hcap := sph_witness_cap KI KR M.k
  obtain ⟨hpre, hr, hcut⟩ := embedSilentRetTM_run ι 1 hcap (M.tm.liftSymbols e)
    tapes heads [] out a t hc hl hh
  have hout' : ((M.tm.liftSymbols e).runFrom a t).output =
      (g x.length).bits.map RecSym.digit := by
    rw [MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output, ho]
    apply List.map_congr_left
    intro b _
    exact RecSym.digitEmb_apply _ _ b
  refine ⟨t, ?_, hcut, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).1
    simpa only [List.nil_append, hout'] using h
  · rw [hr]
    have h := (embedSilentCfg_cap ι 1 hcap tapes heads [] out
      ((M.tm.liftSymbols e).runFrom a t)).2
    simpa only [List.nil_append, hout', List.length_map] using h
  · intro j hj hjc
    rw [hr]
    exact embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc
  · intro u hu
    rcases lt_or_eq_of_le hu with hu | rfl
    · rw [hpre u hu, Cfg.mapState_output, embedSilentCfg_output]
    · rw [hr, embedSilentCfg_output]
  · rw [MultiTapeTM.spaceUsed_eq_sum]
    calc
      _ ≤ (Finset.univ : Finset (Fin (KI + KR + M.k + 2))).card •
          (c * g x.length + (g x.length).bits.length + 1) := by
        apply Finset.sum_le_card_nsmul
        intro j _
        rw [MultiTapeTM.spaceUsedByTape_eq_card,
          embedSilentRetTM_visitedByTapeHead,
          ← MultiTapeTM.spaceUsedByTape_eq_card]
        by_cases hj : j ∈ Set.range ι
        · obtain ⟨i, rfl⟩ := hj
          rw [(embedSilentTM_visitedByTapeHead ι 1 hcap _ tapes heads [] out a t i).2]
          have h : (M.tm.liftSymbols e).spaceUsedByTape a t i ≤ c * g x.length :=
            calc
              _ ≤ (M.tm.liftSymbols e).spaceUsed a t :=
                (M.tm.liftSymbols e).spaceUsedByTape_le_spaceUsed a t i
              _ = M.tm.spaceUsed (M.tm.initCfg x) t :=
                MultiTapeTM.liftSymbols_spaceUsed M.tm e (M.tm.initCfg x) t
              _ ≤ _ := hs
          omega
        · by_cases hjc : j = 1
          · subst j
            have h := embedSilentTM_spaceUsedByTape_cap ι 1 hcap
              (M.tm.liftSymbols e) tapes heads [] out a t
            rw [hout', List.length_map] at h
            exact h.trans (by omega)
          · rw [(embedSilentTM_visitedByTapeHead_frame ι 1 hcap _
              tapes heads [] out a t j hj hjc).2]
            omega
      _ = _ := by rw [Finset.card_fin, smul_eq_mul]
  · intro u hu j
    have hpos : (R.runFrom start u).workTapePos j =
        (embedSilentCfg ι 1 tapes heads [] out
          ((M.tm.liftSymbols e).runFrom a u)).workTapePos j := by
      rcases lt_or_eq_of_le hu with hlt | rfl
      · rw [hpre u hlt, Cfg.mapState_workTapePos]
      · rw [hr]
    rw [hpos]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_pos, MultiTapeTM.liftSymbols_runFrom,
        Cfg.liftSymbols_workTapePos]
      have h := ((FinTM.inWindow_of_spaceUsed_le M x hs u hu).core_bounds i).1
      have hn := abs_nonneg (heads (ι i))
      exact h.trans (by push_cast; omega)
    · by_cases hjc : j = 1
      · subst j
        rw [(embedSilentCfg_cap ι 1 hcap tapes heads [] out _).2,
          MultiTapeTM.liftSymbols_runFrom, Cfg.liftSymbols_output,
          List.nil_append, List.length_map, abs_of_nonneg (by omega)]
        have h := (M.tm.output_prefix (M.tm.initCfg x) hu).length_le
        rw [ho] at h
        have hn := abs_nonneg (heads 1)
        push_cast
        omega
      · rw [(embedSilentCfg_unselected ι 1 tapes heads [] out _ j hj hjc).2]
        have hn : (0 : ℤ) ≤ (c * g x.length + (g x.length).bits.length : ℕ) :=
          Int.natCast_nonneg _
        omega


/-- The input rewind uses no work tapes, so its embedding preserves every work tape. -/
private def sphEmptySel (k : ℕ) : Fin 0 ↪ Fin k := Function.Embedding.ofIsEmpty

/-- The lifted binary input rewind, embedded on the empty bank, is valid from any positive
input position of an embedded binary word, with the entire physical work bank framed.

**Proof sketch.** Construct the zero-tape binary configuration at the same input position,
apply the published input rewind, lift its run, and use the R1 reconstruction theorem to
identify its initial and final embeddings with the physical configurations. -/
private lemma sph_input_rewind_run {k : ℕ} {Q : Type} [DecidableEq Q] {x : List Bool}
    (d : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some .start) (hp : 1 ≤ d.inputPos.val) :
    let R := embedEmitTM (sphEmptySel k)
      ((inputRewindTM 0).liftSymbols (RecSym.digitEmb Q (Fin 3)))
    R.runFrom d (d.inputPos.val + 1) = {d with state := some .done, inputPos := 1} ∧
      (∀ u < d.inputPos.val + 1, (R.runFrom d u).state ≠ some .done) ∧
      ∀ u ≤ d.inputPos.val + 1, (R.runFrom d u).workTapePos = d.workTapePos := by
  let e := RecSym.digitEmb Q (Fin 3)
  let a : Cfg 0 Bool InputRewindPhase x :=
    ⟨some .start, ⟨d.inputPos.val, by simpa only [List.length_map] using d.inputPos.isLt⟩,
      Fin.elim0, Fin.elim0, []⟩
  have ha : a.inputPos.val = d.inputPos.val := rfl
  have hi : (a.liftSymbols e).inputPos = d.inputPos := by
    rw [Cfg.liftSymbols_inputPos]
    exact Fin.ext rfl
  have hs : embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
      (a.liftSymbols e) = d := by
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]; exact hd.symm
    · exact hi
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  obtain ⟨hr, hc, hh⟩ := inputRewindTM_run a rfl (ha.symm ▸ hp)
  have hrun (u : ℕ) :
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)).runFrom d u =
        embedEmitCfg (sphEmptySel k) d.workTapes d.workTapePos d.output
          (((inputRewindTM 0).runFrom a u).liftSymbols e) := by
    have h := embedEmitTM_runFrom (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
      d.workTapes d.workTapePos d.output (a.liftSymbols e) u
    rw [hs, MultiTapeTM.liftSymbols_runFrom] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun, ← ha, hr]
    apply embedEmitCfg_eq
    · rw [Cfg.liftSymbols_state]
    · rw [Cfg.liftSymbols_inputPos]
      exact Fin.ext rfl
    · rw [Cfg.liftSymbols_output]
      exact List.append_nil _
    · exact fun i => Fin.elim0 i
    · exact fun _ _ => ⟨rfl, rfl⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state, Cfg.liftSymbols_state]
    exact hc u (ha.symm ▸ hu)
  · intro u _
    rw [hrun]
    funext j
    exact (embedEmitCfg_unselected (sphEmptySel k) d.workTapes d.workTapePos d.output
      (((inputRewindTM 0).runFrom a u).liftSymbols e) j
      (by rintro ⟨i, _⟩; exact Fin.elim0 i)).2

/-- The two rewinds after radius capture: a right move makes the input position positive,
the zero-tape input rewind restores position one, and the radius rewind restores tape one.
Both seams use the published general-configuration composition. -/
private def sphRewindsTM (k : ℕ) (Q : Type) [DecidableEq Q] (cap : Fin k) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) :=
  seamCompTM
    (seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true
      (embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols
        (RecSym.digitEmb Q (Fin 3)))) .start)
    (.inr .done) (rewindTM k cap) .start

/-- A common absolute head interval is preserved by a published general-configuration seam.

**Proof sketch.** Before the dispatch use the public left trajectory; afterwards use the
public right trajectory. State relabelling preserves every work-head position. -/
private lemma sph_seam_heads {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t v : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (p : Fin k → ℤ) (r : ℕ)
    (hA : ∀ u ≤ t, ∀ j, |(A.runFrom d u).workTapePos j - p j| ≤ (r : ℤ))
    (hB : ∀ u ≤ v, ∀ j,
      |(B.runFrom (d'.mapState fun _ => entry) u).workTapePos j - p j| ≤ (r : ℤ)) :
    ∀ u ≤ t + 1 + v, ∀ j,
      |((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).workTapePos j - p j| ≤
        (r : ℤ) := by
  intro u hu j
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_workTapePos]
    exact hA u h j
  · obtain ⟨w, hw, rfl⟩ : ∃ w ≤ v, u = t + 1 + w := ⟨u - (t + 1), by omega, by omega⟩
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_workTapePos]
    exact hB w hw j

/-- The paired rewinds on the tape plan, including an empty captured word and an input head
initially at zero. Every work-tape cell and the accumulated output are preserved.

**Proof sketch.** Compose the one-step right move and the lifted zero-tape rewind at their
first returns. Apply the framed radius rewind at the full captured word's length and compose
again. Read the endpoint through the public state-map equations. -/
private lemma sph_rewinds_run (KI KR m : ℕ) {Q : Type} [DecidableEq Q]
    {x : List Bool} (ws : List Bool)
    (d : Cfg (KI + KR + m + 2) (RecSym Q (Fin 3)) Bool
      (x.map (RecSym.digitEmb Q (Fin 3))))
    (hd : d.state = some false)
    (hcap : d.workTapes 1 = FinTM.bufferTape (ws.map RecSym.digit))
    (hpos : d.workTapePos 1 = (ws.length : ℤ)) :
    ∃ t,
      (sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) t =
        { state := some (Sum.inr RewindPhase.done)
          inputPos := 1
          workTapes := d.workTapes
          workTapePos := Function.update d.workTapePos 1 0
          output := d.output } ∧
      (∀ u < t,
        ((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).state ≠ some (Sum.inr .done)) ∧
      ∀ u ≤ t, ∀ j,
        |((sphRewindsTM (KI + KR + m + 2) Q 1).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j - d.workTapePos j| ≤
            ((ws.length + 1 : ℕ) : ℤ) := by
  let k := KI + KR + m + 2
  let e := RecSym.digitEmb Q (Fin 3)
  let I := embedEmitTM (sphEmptySel k) ((inputRewindTM 0).liftSymbols e)
  let A := seamCompTM (sphRightTM k (RecSym Q (Fin 3))) true I .start
  let d₁ := {d with state := some true, inputPos := moveInputPos d.inputPos .pos}
  let a := d₁.mapState (fun _ => InputRewindPhase.start)
  let d₂ : Cfg k (RecSym Q (Fin 3)) InputRewindPhase (x.map e) :=
    {a with state := some InputRewindPhase.done, inputPos := 1}
  obtain ⟨h₁, hp, hc₁, hh₁⟩ := sph_right_run d hd
  obtain ⟨h₂, hc₂, hh₂⟩ := sph_input_rewind_run a
    (by rw [Cfg.mapState_state]; rfl)
    (by rw [Cfg.mapState_inputPos]; exact hp)
  have hA : A.runFrom (d.mapState Sum.inl) (1 + 1 + (a.inputPos.val + 1)) =
      d₂.mapState Sum.inr :=
    seamCompTM_run_ofCfg (sphRightTM k _) true I .start h₁ rfl hc₁ h₂
  have hAc := seamCompTM_firstReturn_ofCfg (sphRightTM k _) true I .start .done
    h₁ rfl hc₁ h₂ rfl hc₂
  let b := (d₂.mapState (Sum.inr : InputRewindPhase → Bool ⊕ InputRewindPhase)).mapState
    (fun _ => RewindPhase.start)
  have hb : b.state = some .start := by
    rw [Cfg.mapState_state, Cfg.mapState_state]
    rfl
  have hbh : b.workTapePos = d.workTapePos := by
    funext j
    rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  have hbt : b.workTapes = d.workTapes := by
    funext j p
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  obtain ⟨h₃, hc₃, hh₃⟩ := rewindTM_run_ofCfg (1 : Fin k)
    (ws.map (RecSym.digit : Bool → RecSym Q (Fin 3))) ws.length
    (by rw [List.length_map]) b hb (by
      intro p _ _
      rw [hbt, hbh, hpos, sub_self, zero_add, hcap])
  let d₃ := { b with
    state := some RewindPhase.done
    workTapePos := Function.update b.workTapePos 1 (b.workTapePos 1 - ws.length) }
  have hend : d₃.mapState Sum.inr =
      ({ state := some (Sum.inr RewindPhase.done)
         inputPos := 1
         workTapes := d.workTapes
         workTapePos := Function.update d.workTapePos 1 0
         output := d.output } : Cfg k (RecSym Q (Fin 3))
           ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) (x.map e)) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
    · funext j p
      rw [Cfg.mapState_workTapes]
      exact congrFun (congrFun hbt j) p
    · funext j
      rw [Cfg.mapState_workTapePos]
      dsimp only [d₃]
      rw [hbh, hpos, sub_self]
    · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output]
  refine ⟨(1 + 1 + (a.inputPos.val + 1)) + 1 + (ws.length + 2), ?_, ?_, ?_⟩
  · exact (seamCompTM_run_ofCfg A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃).trans hend
  · exact seamCompTM_firstReturn_ofCfg A (.inr .done) (rewindTM k 1) .start .done
      hA (by rw [Cfg.mapState_state]; rfl) hAc h₃ rfl hc₃
  · have hAh := sph_seam_heads (sphRightTM k (RecSym Q (Fin 3))) true I .start
      h₁ rfl hc₁ d.workTapePos (ws.length + 1)
      (by
        intro u hu j
        rw [hh₁ u hu, sub_self, abs_zero]
        omega)
      (by
        intro u hu j
        have h := congrFun (hh₂ u hu) j
        rw [Cfg.mapState_workTapePos] at h
        rw [h, sub_self, abs_zero]
        omega)
    exact sph_seam_heads A (.inr .done) (rewindTM k 1) .start
      hA (by rw [Cfg.mapState_state]; rfl) hAc d.workTapePos (ws.length + 1) hAh
      (by
        intro u hu j
        change |((rewindTM k 1).runFrom b u).workTapePos j - d.workTapePos j| ≤
          ((ws.length + 1 : ℕ) : ℤ)
        have h := hh₃ j u hu
        by_cases hj : j = 1
        · rw [if_pos hj, hbh, Finset.mem_Icc] at h
          exact abs_le.mpr ⟨by push_cast; omega, by push_cast; omega⟩
        · rw [if_neg hj, hbh] at h
          rw [h, sub_self, abs_zero]
          omega)


/-- Read a selected configuration through R1 reconstruction, without unfolding the selector.
This common field calculation is used by the runner and final record test.

**Proof sketch.** Project the public reconstruction identity and use the public equations for
the forwarding transport's selected tapes, positions, state, input and output. -/
private lemma sph_select_fields {m k : ℕ} {Γ S : Type} {x : List Γ}
    (ι : Fin m ↪ Fin k) (d : Cfg k Γ S x) :
    (d.select ι).state = d.state ∧ (d.select ι).inputPos = d.inputPos ∧
      d.output ++ (d.select ι).output = d.output ∧
      (∀ i, (d.select ι).workTapes i = d.workTapes (ι i)) ∧
      (∀ i, (d.select ι).workTapePos i = d.workTapePos (ι i)) := by
  have hr := embedEmitCfg_select ι d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg Cfg.state hr
    rwa [embedEmitCfg_state] at h
  · have h := congrArg Cfg.inputPos hr
    rwa [embedEmitCfg_inputPos] at h
  · have h := congrArg Cfg.output hr
    rwa [embedEmitCfg_output] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapes
        (ι i) = d.workTapes (ι i) := congrArg (fun c => c.workTapes (ι i)) hr
    rwa [embedEmitCfg_selected_tape] at h
  · intro i
    have h : (embedEmitCfg ι d.workTapes d.workTapePos d.output (d.select ι)).workTapePos
        (ι i) = d.workTapePos (ι i) := congrArg (fun c => c.workTapePos (ι i)) hr
    rwa [embedEmitCfg_selected_pos] at h

/-- The record initializer occupies the record, radius and its own contiguous scratch bank. -/
private def sphInitSel (KI KR m : ℕ) : Fin (KI + 2) ↪ Fin (KI + KR + m + 2) :=
  Fin.castLEEmb (by omega)

/-- The initial-record phase on the diagonalizer's tape plan. Only the initializer's scratch
bank must be blank; the witness and runner banks are framed. [AB09, Theorem 4.8]

**Proof sketch.** Select the record, radius and initializer scratch tapes. Read the selected
configuration through the R1 reconstruction equation and its field equations. Apply the
published initial-record row, transport its run by R1 and reconstruct the framed endpoint. -/
private lemma sph_initial_record (M : FinTM Bool) (KR m : ℕ) :
    ∃ (KI : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry exit : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ p : ℤ, -1 ≤ p → p ≤ (recordLength M.k x.length s : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (KI + KR + m + 2), 2 ≤ j.val → j.val < KI + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (recordLength M.k x.length s + ws.length + s + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + (recordLength M.k x.length s : ℤ)
                  then fieldsTape (cfgRecord s (M.tm.initCfg x) 0) (q - d.workTapePos j)
                else d.workTapes j q} := by
  classical
  obtain ⟨KI, P, hF, hD, I, entry, exit, C, hI⟩ :=
    exists_recordInitTM M.k M.tm.q₀ (0 : Fin 3)
  letI := hF
  letI := hD
  let ι := sphInitSel KI KR m
  have h0 : ι 0 = 0 := Fin.ext rfl
  have h1 : ι 1 = 1 := Fin.ext rfl
  refine ⟨KI, P, hF, hD, embedEmitTM ι I, entry, exit, C, ?_⟩
  intro x s ws hws d hd hin hrad hslot hblank
  let a := d.select ι
  have hrecon : embedEmitCfg ι d.workTapes d.workTapePos d.output a = d :=
    embedEmitCfg_select ι d
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  obtain ⟨t, htime, hcut, henv, hr⟩ := hI s ws hws a (hstate.trans hd) (hinput.trans hin)
    (by intro p hp hp'; rw [htapes, hheads, h1]; exact hrad p hp hp')
    (by intro p hp hp'; rw [htapes, hheads, h0]; exact hslot p hp hp')
    (by
      intro j hj p
      rw [htapes]
      exact hblank (ι j) hj (by have := j.isLt; exact this) p)
  have hrun (u : ℕ) :
      (embedEmitTM ι I).runFrom d u =
        embedEmitCfg ι d.workTapes d.workTapePos d.output (I.runFrom a u) := by
    have h := embedEmitTM_runFrom ι I d.workTapes d.workTapePos d.output a u
    rwa [hrecon] at h
  refine ⟨t, htime, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr, MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput

/-- The runner uses record tape zero and its scratch bank, never the radius or witness bank. -/
private def sphRunnerSel (KI KR m : ℕ) : Fin (KR + 1) ↪ Fin (KI + KR + m + 2) where
  toFun i := ⟨if i.val = 0 then 0 else KI + 1 + i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' : (if i.val = 0 then 0 else KI + 1 + i.val) =
        (if j.val = 0 then 0 else KI + 1 + j.val) := congrArg Fin.val h
    split_ifs at h' <;> omega

/-- The published clocked runner on the diagonalizer's full tape plan. Its blank scratch
condition excludes both the radius tape and the dirty witness bank. [AB09, Theorem 4.8]

**Proof sketch.** Select record tape zero and the runner scratch bank. Apply the published
configuration-count runner with `summaryTag`, and transport its run, head envelope, silence
and nonexhausted record endpoint by R1. No new clock or simulation is constructed. -/
private lemma sph_runner_run (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (KR + 1) (RecSym M.State (Fin 3)) P)
      (entry : P) (exit : WindowExit → P) (C : ℕ),
      (∀ e, exit e ≠ entry) ∧ Function.Injective exit ∧
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3),
      c.InWindow s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        let H := embedEmitTM (sphRunnerSel KI KR m) R
        ∃ (t : ℕ) (out : WindowExit),
          t ≤ C * 2 ^ (C * (recordLength M.k x.length s + 1)) ∧
          (H.runFrom d t).state = some (exit out) ∧
          (∀ u < t, ∀ e, (H.runFrom d u).state ≠ some (exit e)) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ u ≤ t, (H.runFrom d u).output = d.output) ∧
          (∀ N ≤ M.configBound x.length s + 1,
            (windowRun M.tm s summaryTag N c τ).1 ≠ .exhausted →
            out = (windowRun M.tm s summaryTag N c τ).1) ∧
          (out ≠ .exhausted → ∃ N,
            (windowRun M.tm s summaryTag N c τ).1 = out ∧
            H.runFrom d t =
              { d with
                state := some (exit out)
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos 0 ≤ q ∧
                      q < d.workTapePos 0 + (recordLength M.k x.length s : ℤ)
                    then fieldsTape (cfgRecord s (windowRun M.tm s summaryTag N c τ).2.1
                      (windowRun M.tm s summaryTag N c τ).2.2) (q - d.workTapePos 0)
                  else d.workTapes j q }) := by
  classical
  obtain ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, hR⟩ :=
    exists_configWindowRunnerTM M summaryTag summaryTag_none
  letI := hF
  letI := hD
  refine ⟨KR, P, hF, hD, R, entry, exit, C, hne, hinj, ?_⟩
  intro KI m x s c τ hc d hd hrec hblank
  dsimp only
  let ι := sphRunnerSel KI KR m
  have h0 : ι 0 = 0 := by
    apply Fin.ext
    simp only [ι, sphRunnerSel, Function.Embedding.coeFn_mk, Fin.val_zero, if_pos]
  have hv (i : Fin (KR + 1)) (hi : i ≠ 0) : (ι i).val = KI + 1 + i.val := by
    have hz : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    exact if_neg hz
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, out, ht, he, hcut, henv, hs, _, hvote, hend⟩ := hR s c τ hc a
    (hstate.trans hd) hrec' (by
      intro i hi p
      rw [htapes]
      apply hblank (ι i)
      · rw [hv i hi]
        have : 0 < i.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hi)
        omega
      · rw [hv i hi]
        have := i.isLt
        omega)
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, out, ht, ?_, ?_, ?_, ?_, hvote, ?_⟩
  · rw [hrun, embedEmitCfg_state]
    exact he
  · intro u hu e
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu e
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · intro u hu
    rw [hrun, embedEmitCfg_output, hs u hu]
    exact houtput
  · intro hn
    obtain ⟨N, hN, hr⟩ := hend hn
    refine ⟨N, hN, ?_⟩
    rw [hrun, hr]
    apply Cfg.ext
    · rw [embedEmitCfg_state]
    · rw [embedEmitCfg_inputPos]
      exact hinput
    · funext j q
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_tape]
        have hz : ι i = 0 ↔ i = 0 := by rw [← h0]; exact ι.injective.eq_iff
        simp only [a, hheads, htapes, h0, hz]
      · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).1]
        have hj0 : j ≠ 0 := fun h => hj ⟨0, h0.trans h.symm⟩
        simp only [hj0, false_and, ite_false]
    · funext j
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedEmitCfg_selected_pos]
        exact hheads i
      · exact (embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2
    · rw [embedEmitCfg_output]
      exact houtput


/-- A one-tape record test selects the physical record tape alone. -/
private def sphRecordSel (k : ℕ) : Fin 1 ↪ Fin (k + 1) where
  toFun _ := 0
  inj' := fun _ _ _ => Subsingleton.elim _ _

/-- The final record test, on the full work bank, asks whether the encoded configuration is
halted and its output summary is the singleton-true summary. It preserves every physical field
except its finite verdict state. [AB09, Theorem 4.8]

**Proof sketch.** Apply the published one-tape record test to the selected record tape and
transport the framed endpoint and head envelope by R1. -/
private lemma sph_test_run (M : FinTM Bool) :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM 1 (RecSym M.State (Fin 3)) P) (entry yes no : P) (C : ℕ),
      yes ≠ no ∧
      ∀ (k : ℕ) {x : List Bool} (s : ℕ) (c : Cfg M.k Bool M.State x) (τ : Fin 3)
        {ys : List (RecSym M.State (Fin 3))}
        (d : Cfg (k + 1) (RecSym M.State (Fin 3)) P ys),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        let H := embedEmitTM (sphRecordSel k) R
        ∃ t ≤ C * (recordLength M.k x.length s + 1),
          (∀ u < t, (H.runFrom d u).state ≠ some yes ∧
            (H.runFrom d u).state ≠ some no) ∧
          (∀ u ≤ t, ∀ j, |(H.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          H.runFrom d t =
            {d with state := some (if c.state = none ∧ τ = 1 then yes else no)} := by
  classical
  obtain ⟨P, hF, hD, R, entry, yes, no, C, hne, hR⟩ :=
    exists_recordTestTM (k := M.k)
      (fun (q : Option M.State) (τ : Fin 3) => decide (q = none ∧ τ = 1))
  letI := hF
  letI := hD
  refine ⟨P, hF, hD, R, entry, yes, no, C, hne, ?_⟩
  intro k x s c τ ys d hd hrec
  dsimp only
  let ι := sphRecordSel k
  have h0 : ι 0 = 0 := rfl
  let a := d.select ι
  obtain ⟨hstate, hinput, houtput, htapes, hheads⟩ := sph_select_fields ι d
  have hrec' : RecordAt a 0 (cfgRecord s c τ) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [htapes, hheads, h0]
    exact hrec p hp hp'
  obtain ⟨t, ht, hcut, henv, hr⟩ := hR s c τ a (hstate.trans hd) hrec'
  rw [joinFields_cfgRecord_length] at ht henv
  have hrun (u : ℕ) : (embedEmitTM ι R).runFrom d u =
      embedEmitCfg ι d.workTapes d.workTapePos d.output (R.runFrom a u) := by
    have h := embedEmitTM_runFrom ι R d.workTapes d.workTapePos d.output a u
    rwa [embedEmitCfg_select] at h
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro u hu
    rw [hrun, embedEmitCfg_state]
    exact hcut u hu
  · intro u hu j
    rw [hrun]
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_pos, ← hheads]
      exact henv u hu i
    · rw [(embedEmitCfg_unselected ι d.workTapes d.workTapePos d.output _ j hj).2]
      simp only [sub_self, abs_zero, Nat.cast_nonneg]
  · rw [hrun, hr]
    apply embedEmitCfg_eq
    · simp only [decide_eq_true_eq]
    · exact hinput
    · exact houtput
    · intro i
      exact ⟨htapes i, hheads i⟩
    · exact fun _ _ => ⟨rfl, rfl⟩


/-- The emitter leaf as a framed contract, with a singleton head interval on every tape. -/
private def sphEmitContract {k : ℕ} {Γ : Type} (b : Γ) (x : List Γ) :
    Contract (sphEmitTM k b) () {none} Unit x where
  pre := fun _ _ => True
  time := fun _ _ => 1
  post := fun _ d => {d with state := none, output := d.output ++ [b]}
  lo := fun _ d => d.workTapePos
  hi := fun _ d => d.workTapePos
  run := fun _ d hd _ => (sph_emit_run b d hd).1
  exit_mem := fun _ _ _ _ => Set.mem_singleton _
  cut := by
    intro _ d hd _ u hu
    have : u = 0 := Nat.lt_one_iff.mp hu
    subst u
    rw [MultiTapeTM.runFrom_zero, hd]
    exact Option.some_ne_none _
  env := by
    intro _ d hd _ u hu j
    rw [(sph_emit_run b d hd).2 u hu]
    exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- The two-exit seam attaches the opposite one-bit answer to each record-test verdict. -/
private def sphVerdictTM {k : ℕ} {Q P : Type} [DecidableEq P]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (yes no : P) :
    MultiTapeTM k (RecSym Q (Fin 3)) ((P ⊕ Unit) ⊕ Unit) :=
  seamCompTM₂ R yes no (sphEmitTM k (RecSym.digit false)) ()
    (sphEmitTM k (RecSym.digit true)) ()

/-- A framed record test followed by its opposite-bit emitter halts, and inherits the test's
head envelope. This also covers a halted record whose summary is not singleton true.

**Proof sketch.** The two-exit run theorem selects the one-step emitter. The public branching
contract combines the test's certified interval with the emitter's stationary heads; the hull
is the test's original interval. -/
private lemma sph_verdict_run {k : ℕ} {Q P : Type} [DecidableEq P]
    {ys : List (RecSym Q (Fin 3))} (R : MultiTapeTM k (RecSym Q (Fin 3)) P)
    (entry yes no : P) (hne : yes ≠ no) (d : Cfg k (RecSym Q (Fin 3)) P ys)
    (hd : d.state = some entry) (b : Bool) (t B : ℕ)
    (hr : R.runFrom d t = {d with state := some (if b then yes else no)})
    (hcut : ∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no)
    (henv : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    (sphVerdictTM R yes no).runFrom ((d.mapState Sum.inl).mapState Sum.inl) (t + 2) =
        { state := none
          inputPos := d.inputPos
          workTapes := d.workTapes
          workTapePos := d.workTapePos
          output := d.output ++ [RecSym.digit (!b)] } ∧
      ∀ u ≤ t + 2, ∀ j,
        |((sphVerdictTM R yes no).runFrom
          ((d.mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  classical
  let d' := {d with state := some (if b then yes else no)}
  let d₀ := (d.mapState (Sum.inl : P → P ⊕ Unit)).mapState
    (Sum.inl : P ⊕ Unit → (P ⊕ Unit) ⊕ Unit)
  let C₀ : Contract R entry {some yes, some no} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => t
      post := fun _ _ => d'
      lo := fun _ _ j => d.workTapePos j - B
      hi := fun _ _ j => d.workTapePos j + B
      run := by intro _ a _ ha; subst a; exact hr
      exit_mem := by
        intro _ _ _ _
        cases b
        · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        · exact Set.mem_insert _ _
      cut := by
        intro _ a _ ha u hu
        subst a
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact hcut u hu
      env := by
        intro _ a _ ha u hu j
        subst a
        exact Contract.mem_Icc_of_abs_le (henv u hu j) }
  let C := Contract.branch hne C₀ (sphEmitContract (RecSym.digit false) ys)
    (sphEmitContract (RecSym.digit true) ys) (fun _ => ()) (fun _ => ())
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro)
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl entry)) := by
    rw [Cfg.mapState_state, Cfg.mapState_state, hd]
    rfl
  have hp : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => entry) = d
    simp only [d₀, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  have htime : C.time () d₀ = t + 2 := by
    rw [Contract.branch_time]
    dsimp only [C₀, sphEmitContract]
    rw [ite_self]
  refine ⟨?_, ?_⟩
  · obtain ⟨hy, hn⟩ := seamCompTM₂_run_ofCfg R yes no hne
      (sphEmitTM k (RecSym.digit false)) () (sphEmitTM k (RecSym.digit true)) () hr hcut
    have ht : t + 2 = t + 1 + 1 := by omega
    rw [ht]
    cases b
    · have h := hn rfl 1
      rw [(sph_emit_run (RecSym.digit true) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      apply Cfg.ext
      · rw [Cfg.mapState_state]; rfl
      · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output, Cfg.mapState_output]
        rfl
    · have h := hy rfl 1
      rw [(sph_emit_run (RecSym.digit false) _
        (by rw [Cfg.mapState_state]; rfl)).1] at h
      rw [h]
      apply Cfg.ext
      · rw [Cfg.mapState_state, Cfg.mapState_state]; rfl
      · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
      · funext j p
        rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
      · funext j
        rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      · rw [Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output]
        rfl
  · intro u hu j
    have h := C.env () d₀ hd₀ hp u (htime.symm ▸ hu) j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    simp only [Cfg.mapState_workTapePos, ite_self] at h
    dsimp only [d'] at h
    rw [min_eq_left (by omega), max_eq_left (by omega), Finset.mem_Icc] at h
    dsimp only [d₀, sphVerdictTM] at h ⊢
    exact abs_le.mpr ⟨by omega, by omega⟩


/-- Any halted record returned by the window runner has the actual halting run's state and
output summary, regardless of which stopped round count the runner's record clause supplies.

**Proof sketch.** Compare that round count with one past a certified halting time by the
published stop-uniqueness theorem, then read the public output-summary characterization. -/
private lemma sph_summary (M : FinTM Bool) (x w : List Bool) (s t N : ℕ)
    (ht : M.ComputesInTime x w t)
    (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s)
    (hN : (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).1 = .halted) :
    ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1).state = none ∧
      ((windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2 = 1 ↔ w = [true]) := by
  have h := windowRun_summary_of_halts M x ht hs (Nat.lt_succ_self t)
  have heq := windowRun_stop_unique M.tm s summaryTag N (t + 1) (M.tm.initCfg x) 0
    (by rw [hN]; intro hbad; cases hbad)
    (by rw [h]; exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
  rw [heq, h]
  exact ⟨((FinTM.computesInTime_iff _ _ _ _).mp ht).1, outSummaryCode_eq_one_iff w⟩


/-- Once a seam dispatches, no other left-hand anchor is reached. Before dispatch it inherits
the host's avoidance of that anchor.

**Proof sketch.** The public left trajectory gives the host's cut and the distinct dispatch
anchor at the endpoint. The public right trajectory has only right-hand states or a halt. -/
private lemma sph_seam_avoids {k : ℕ} {Γ P Q : Type} [DecidableEq P] {x : List Γ}
    (A : MultiTapeTM k Γ P) (exit other : P) (B : MultiTapeTM k Γ Q) (entry : Q)
    {d d' : Cfg k Γ P x} {t : ℕ} (hr : A.runFrom d t = d')
    (he : d'.state = some exit) (hne : exit ≠ other)
    (hc : ∀ u < t, (A.runFrom d u).state ≠ some exit)
    (ho : ∀ u < t, (A.runFrom d u).state ≠ some other) :
    ∀ u, ((seamCompTM A exit B entry).runFrom (d.mapState Sum.inl) u).state ≠
      some (Sum.inl other) := by
  intro u hbad
  by_cases h : u ≤ t
  · rw [seamCompTM_runFrom_left A exit B entry hc u h, Cfg.mapState_state] at hbad
    have hh : (A.runFrom d u).state = some other :=
      Option.map_injective Sum.inl_injective hbad
    rcases lt_or_eq_of_le h with h | rfl
    · exact ho u h hh
    · rw [hr, he] at hh
      exact hne (Option.some.inj hh)
  · obtain ⟨w, rfl⟩ : ∃ w, u = t + 1 + w := Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)
    rw [seamCompTM_runFrom_right A exit B entry hr he hc w, Cfg.mapState_state] at hbad
    obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad
    exact Sum.inr_ne_inl hq

/-- Writing a layout's interior between its two blank boundary cells installs that record.
This is the shared boundary argument for the initializer and the stopped runner.

**Proof sketch.** Read `RecordAt` through its public equivalence. Inside the span use the
written field tape. The only other required offsets are minus one and the layout length;
both the old tape and the public layout boundary equations are blank there. -/
private lemma sph_written_record {k : ℕ} {Γ P : Type} {x : List Γ}
    (d : Cfg (k + 1) Γ P x) (q : Option P) (fs : List (List Γ)) (L : ℕ)
    (hL : (joinFields fs).length = L)
    (hl : d.workTapes 0 (d.workTapePos 0 - 1) = none)
    (hr : d.workTapes 0 (d.workTapePos 0 + L) = none) :
    RecordAt
      { d with
        state := q
        workTapes := fun j z =>
          if j = 0 ∧ d.workTapePos 0 ≤ z ∧ z < d.workTapePos 0 + (L : ℤ)
            then fieldsTape fs (z - d.workTapePos 0) else d.workTapes j z }
      0 fs := by
  rw [recordAt_iff]
  intro p hp hp'
  rw [hL] at hp'
  change (if (0 : Fin (k + 1)) = 0 ∧ d.workTapePos 0 ≤ d.workTapePos 0 + p ∧
      d.workTapePos 0 + p < d.workTapePos 0 + (L : ℤ)
    then fieldsTape fs (d.workTapePos 0 + p - d.workTapePos 0)
    else d.workTapes 0 (d.workTapePos 0 + p)) = fieldsTape fs p
  by_cases h : 0 ≤ p ∧ p < (L : ℤ)
  · rw [if_pos ⟨rfl, by omega, by omega⟩]
    congr 1
    ring
  · rw [if_neg (by rintro ⟨_, h₁, h₂⟩; exact h ⟨by omega, by omega⟩)]
    have : p = -1 ∨ p = (L : ℤ) := by omega
    rcases this with rfl | rfl
    · rw [fieldsTape_of_neg fs (by omega), ← sub_eq_add_neg]
      exact hl
    · rw [fieldsTape_of_length_le fs (by rw [hL])]
      exact hr


/-- The runner's three exits use published single-exit seams: a halted run enters the verdict
test, and either a window exit or exhaustion enters the true emitter. Exhaustion never reads
the unspecified record tape. -/
private def sphRunnerTailTM {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S) :
    MultiTapeTM k (RecSym Q (Fin 3)) (((P ⊕ S) ⊕ Unit) ⊕ Unit) :=
  seamCompTM
    (seamCompTM (seamCompTM R (exit .halted) V entry) (Sum.inl (exit .left))
      (sphEmitTM k (RecSym.digit true)) ())
    (Sum.inl (Sum.inl (exit .exhausted))) (sphEmitTM k (RecSym.digit true)) ()

/-- Run the runner's three-exit suffix. A certificate about the halted branch's output is
preserved; both other branches emit true. All heads remain in a common certified interval.

**Proof sketch.** On a halted verdict, both outer seams stay in their left segments while the
test runs. On a window exit, the middle seam dispatches the true emitter; on exhaustion, the
outer seam does so. The public seam trajectories transport the endpoint and each head bound.
The clock and record simulation remain entirely the supplied runner's. -/
private lemma sph_runner_tail_run {k : ℕ} {Q P S : Type} [DecidableEq P] [DecidableEq S]
    {ys : List (RecSym Q (Fin 3))}
    (R : MultiTapeTM k (RecSym Q (Fin 3)) P) (exit : WindowExit → P)
    (hi : Function.Injective exit) (V : MultiTapeTM k (RecSym Q (Fin 3)) S) (entry : S)
    (d d' : Cfg k (RecSym Q (Fin 3)) P ys) (t B : ℕ) (out : WindowExit)
    (hr : R.runFrom d t = d') (he : d'.state = some (exit out))
    (hc : ∀ u < t, ∀ e, (R.runFrom d u).state ≠ some (exit e))
    (ho : d'.output = d.output)
    (hh : ∀ u ≤ t, ∀ j, |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ (B : ℤ))
    (pred : Bool → Prop)
    (hv : out = .halted → ∃ v b,
      (V.runFrom (d'.mapState fun _ => entry) v).state = none ∧
      (V.runFrom (d'.mapState fun _ => entry) v).output =
        d'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |(V.runFrom (d'.mapState fun _ => entry) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ)) :
    ∃ v b,
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).state = none ∧
      ((sphRunnerTailTM R exit V entry).runFrom
        (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) v).output =
          d.output ++ [RecSym.digit b] ∧
      (out = .halted → pred b) ∧ (out ≠ .halted → b = true) ∧
      ∀ u ≤ v, ∀ j,
        |((sphRunnerTailTM R exit V entry).runFrom
          (((d.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) u).workTapePos j -
          d.workTapePos j| ≤ (B : ℤ) := by
  let E := sphEmitTM k (RecSym.digit true : RecSym Q (Fin 3))
  let A := seamCompTM R (exit .halted) V entry
  let C := seamCompTM A (Sum.inl (exit .left)) E ()
  let a := d.mapState (Sum.inl : P → P ⊕ S)
  let a' := d'.mapState (Sum.inl : P → P ⊕ S)
  let c := a.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  let c' := a'.mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)
  have hAp (u : ℕ) (hu : u ≤ t) : A.runFrom a u = (R.runFrom d u).mapState Sum.inl :=
    seamCompTM_runFrom_left R (exit .halted) V entry (fun u hu => hc u hu .halted) u hu
  have hAr : A.runFrom a t = a' := by rw [hAp t le_rfl, hr]
  have hAc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (A.runFrom a u).state ≠ some (Sum.inl (exit e)) := by
    rw [hAp u hu.le, Cfg.mapState_state]
    intro h
    exact hc u hu e (Option.map_injective Sum.inl_injective h)
  have hCp (u : ℕ) (hu : u ≤ t) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
    seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
      (fun u hu => hAc u hu .left) u hu
  have hCr : C.runFrom c t = c' := by rw [hCp t le_rfl, hAr]
  have hCc (u : ℕ) (hu : u < t) (e : WindowExit) :
      (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit e))) := by
    rw [hCp u hu.le, Cfg.mapState_state]
    intro h
    exact hAc u hu e (Option.map_injective Sum.inl_injective h)
  cases out with
  | halted =>
    obtain ⟨v, b, hvs, hvo, hpred, hvh⟩ := hv rfl
    have hAl := sph_seam_avoids R (exit .halted) (exit .left) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .left)
    have hAe := sph_seam_avoids R (exit .halted) (exit .exhausted) V entry hr he
      (fun h => WindowExit.noConfusion (hi h)) (fun u hu => hc u hu .halted)
      (fun u hu => hc u hu .exhausted)
    have hC (u : ℕ) : C.runFrom c u = (A.runFrom a u).mapState Sum.inl :=
      seamCompTM_runFrom_left A (Sum.inl (exit .left)) E ()
        (fun u _ => hAl u) u le_rfl
    have hCe (u : ℕ) : (C.runFrom c u).state ≠ some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [hC, Cfg.mapState_state]
      intro h
      exact hAe u (Option.map_injective Sum.inl_injective h)
    have hW (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        ((A.runFrom a u).mapState (Sum.inl : P ⊕ S → (P ⊕ S) ⊕ Unit)).mapState Sum.inl := by
      rw [seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => hCe u) u le_rfl, hC]
    have hA := seamCompTM_runFrom_right R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) v
    have hAh := sph_seam_heads R (exit .halted) V entry hr he
      (fun u hu => hc u hu .halted) d.workTapePos B hh hvh
    refine ⟨t + 1 + v, b, ?_, ?_, fun _ => hpred, fun h => False.elim (h rfl), ?_⟩
    · rw [hW, hA, Cfg.mapState_state, Cfg.mapState_state, Cfg.mapState_state, hvs]
      rfl
    · rw [hW, hA, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output, hvo, ho]
    · intro u hu j
      rw [hW, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hAh u hu j
  | left =>
    have ha' : a'.state = some (Sum.inl (exit .left)) := by
      rw [Cfg.mapState_state, he]; rfl
    have havoid := sph_seam_avoids A (Sum.inl (exit .left))
      (Sum.inl (exit .exhausted)) E () hAr ha'
      (fun h => WindowExit.noConfusion (hi (Sum.inl.inj h)))
      (fun u hu => hAc u hu .left) (fun u hu => hAc u hu .exhausted)
    have hw (u : ℕ) : (sphRunnerTailTM R exit V entry).runFrom (c.mapState Sum.inl) u =
        (C.runFrom c u).mapState Sum.inl :=
      seamCompTM_runFrom_left C (Sum.inl (Sum.inl (exit .exhausted))) E ()
        (fun u _ => havoid u) u le_rfl
    have hea : (a'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, ha']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (a'.mapState fun _ => ()) hea
    have hC := seamCompTM_run_ofCfg A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) her
    have hAh : ∀ u ≤ t, ∀ j, |(A.runFrom a u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (a'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hCh := sph_seam_heads A (Sum.inl (exit .left)) E () hAr ha'
      (fun u hu => hAc u hu .left) d.workTapePos B hAh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, ?_⟩
    · rw [hw, hC, Cfg.mapState_state, Cfg.mapState_state]; rfl
    · rw [hw, hC, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, Cfg.mapState_output, ho]
    · intro u hu j
      rw [hw, Cfg.mapState_workTapePos]
      exact hCh u hu j
  | exhausted =>
    have hc' : c'.state = some (Sum.inl (Sum.inl (exit .exhausted))) := by
      rw [Cfg.mapState_state, Cfg.mapState_state, he]; rfl
    have hec : (c'.mapState fun _ => ()).state = some () := by
      rw [Cfg.mapState_state, hc']; rfl
    obtain ⟨her, heh⟩ := sph_emit_run (RecSym.digit true) (c'.mapState fun _ => ()) hec
    have hW := seamCompTM_run_ofCfg C (Sum.inl (Sum.inl (exit .exhausted))) E ()
      hCr hc' (fun u hu => hCc u hu .exhausted) her
    have hCh : ∀ u ≤ t, ∀ j, |(C.runFrom c u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [hCp u hu, Cfg.mapState_workTapePos, hAp u hu, Cfg.mapState_workTapePos]
      exact hh u hu j
    have hEh : ∀ u ≤ 1, ∀ j,
        |(E.runFrom (c'.mapState fun _ => ()) u).workTapePos j - d.workTapePos j| ≤ (B : ℤ) := by
      intro u hu j
      rw [heh u hu, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos,
        Cfg.mapState_workTapePos]
      exact hr ▸ hh t le_rfl j
    have hWh := sph_seam_heads C (Sum.inl (Sum.inl (exit .exhausted))) E () hCr hc'
      (fun u hu => hCc u hu .exhausted) d.workTapePos B hCh hEh
    refine ⟨t + 1 + 1, true, ?_, ?_, fun h => WindowExit.noConfusion h, fun _ => rfl, hWh⟩
    · rw [hW, Cfg.mapState_state]; rfl
    · rw [hW, Cfg.mapState_output, Cfg.mapState_output, Cfg.mapState_output,
        Cfg.mapState_output, ho]


/-- The complete clocked simulation suffix on the tape plan. Starting from the universal
machine's initial record, it halts with one bit. Every halting run that fits the window receives
the opposite acceptance answer, and the suffix's head bound is uniform in the input's code.
[AB09, Theorem 4.8]

**Proof sketch.** Put the published runner and record test on disjoint framed selections, then
attach the tested opposite-bit verdict and the two unconditional true branches. The returned
record's blank boundaries follow from the old record and the public layout boundary equations.
Stop uniqueness identifies its summary with any certified halting run in the window. -/
private lemma sph_suffix (M : FinTM Bool) :
    ∃ (KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : ∀ KI m, MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ (KI m : ℕ) {x : List Bool} (s : ℕ)
        (d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3)))),
        d.state = some entry → RecordAt d 0 (cfgRecord s (M.tm.initCfg x) 0) →
        (∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          ((D KI m).runFrom d t).state = none ∧
          ((D KI m).runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |((D KI m).runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PR, hFR, hDR, R, ren, rex, CR, _, hinj, hR⟩ := sph_runner_run M
  letI := hFR
  letI := hDR
  obtain ⟨PT, hFT, hDT, T, ten, yes, no, CT, hne, hT⟩ := sph_test_run M
  letI := hFT
  letI := hDT
  let H (KI m : ℕ) := embedEmitTM (sphRunnerSel KI KR m) R
  let J (KI m : ℕ) := embedEmitTM (sphRecordSel (KI + KR + m + 1)) T
  let V (KI m : ℕ) := sphVerdictTM (J KI m) yes no
  let ven : (PT ⊕ Unit) ⊕ Unit := .inl (.inl ten)
  let D (KI m : ℕ) := sphRunnerTailTM (H KI m) rex (V KI m) ven
  let en : (((PR ⊕ ((PT ⊕ Unit) ⊕ Unit)) ⊕ Unit) ⊕ Unit) := .inl (.inl (.inl ren))
  refine ⟨KR, _, inferInstance, inferInstance, D, en, CR + CT, ?_⟩
  intro KI m x s d hd hrec hblank
  let a := d.mapState (fun _ => ren)
  have ha : a.state = some ren := by rw [Cfg.mapState_state, hd]; rfl
  have har : RecordAt a 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at hrec ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact hrec p hp hp'
  have hab : ∀ j : Fin (KI + KR + m + 2), KI + 2 ≤ j.val → j.val < KI + KR + 2 →
      ∀ p, a.workTapes j p = none := by
    intro j hj hj' p
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj' p
  have hstart : (((a.mapState Sum.inl).mapState Sum.inl).mapState Sum.inl) = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  obtain ⟨t, out, _, he, hc, hh, ho, hword, hend⟩ := hR KI m s (M.tm.initCfg x) 0
    (by rw [MultiTapeTM.initCfg_eq]; exact Cfg.inWindow_init _ _ s) a ha har hab
  let a' := (H KI m).runFrom a t
  have ha' : a'.state = some (rex out) := he
  let L := recordLength M.k x.length s
  let B := (CR + CT) * (L + 1)
  have hRB : CR * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hTB : CT * (L + 1) ≤ B := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  let pred (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length s) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
    b = !(decide (w = [true]))
  have hV : out = .halted → ∃ v b,
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).state = none ∧
      ((V KI m).runFrom (a'.mapState fun _ => ven) v).output =
        a'.output ++ [RecSym.digit b] ∧ pred b ∧
      ∀ u ≤ v, ∀ j,
        |((V KI m).runFrom (a'.mapState fun _ => ven) u).workTapePos j - a.workTapePos j| ≤
          (B : ℤ) := by
    intro hout
    obtain ⟨N, hN, hr⟩ := hend (by rw [hout]; intro hbad; cases hbad)
    let cN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.1
    let τN := (windowRun M.tm s summaryTag N (M.tm.initCfg x) 0).2.2
    have hl : a.workTapes 0 (a.workTapePos 0 - 1) = none := by
      have h := (recordAt_iff _ _ _).mp har (-1) le_rfl (by omega)
      rw [fieldsTape_of_neg _ (by omega), ← sub_eq_add_neg] at h
      exact h
    have hright : a.workTapes 0 (a.workTapePos 0 + (L : ℤ)) = none := by
      have h := (recordAt_iff _ _ _).mp har (L : ℤ) (by omega)
        (by rw [joinFields_cfgRecord_length])
      rw [fieldsTape_of_length_le _ (by rw [joinFields_cfgRecord_length])] at h
      exact h
    have hrecN : RecordAt a' 0 (cfgRecord s cN τN) := by
      dsimp only [a']
      rw [hr]
      exact sph_written_record a _ (cfgRecord s cN τN) L
        (joinFields_cfgRecord_length _ _ _) hl hright
    let z := a'.mapState (fun _ => ten)
    have hz : z.state = some ten := by rw [Cfg.mapState_state, he]; rfl
    have hzr : RecordAt z 0 (cfgRecord s cN τN) := by
      rw [recordAt_iff] at hrecN ⊢
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrecN p hp hp'
    obtain ⟨v, _, hcutT, hheadsT, hrunT⟩ := hT (KI + KR + m + 1) s cN τN z hz hzr
    let b := decide (cN.state = none ∧ τN = 1)
    obtain ⟨hvr, hvh⟩ := sph_verdict_run (J KI m) ten yes no hne z hz b v (CT * (L + 1))
      (by simpa only [b, decide_eq_true_eq] using hrunT) hcutT hheadsT
    have hmaps : ((z.mapState Sum.inl).mapState Sum.inl) = a'.mapState (fun _ => ven) := by
      simp only [z, Cfg.mapState_mapState]
      rfl
    rw [hmaps] at hvr hvh
    refine ⟨v + 2, !b, ?_, ?_, ?_, ?_⟩
    · rw [hvr]
    · rw [hvr, Cfg.mapState_output]
    · intro w hw hs
      have hsumm := sph_summary M x w s (M.configBound x.length s) N hw hs (hN.trans hout)
      have hf : (cN.state = none ∧ τN = 1) ↔ w = [true] :=
        ⟨fun h => hsumm.2.mp h.2, fun h => ⟨hsumm.1, hsumm.2.mpr h⟩⟩
      dsimp only [b]
      exact congrArg Bool.not (decide_eq_decide.mpr hf)
    · intro u hu j
      have h := hvh u hu j
      have hzhead : z.workTapePos j = a.workTapePos j := by
        rw [Cfg.mapState_workTapePos]
        dsimp only [a']
        rw [hr]
      rw [hzhead] at h
      exact h.trans (by exact_mod_cast hTB)
  obtain ⟨v, b, hvs, hvo, hpred, _, hvh⟩ := sph_runner_tail_run (H KI m) rex hinj
    (V KI m) ven a a' t B out rfl he hc (ho t le_rfl)
    (fun u hu j => (hh u hu j).trans (by exact_mod_cast hRB)) pred hV
  rw [hstart] at hvs hvo hvh
  refine ⟨v, b, hvs, ?_, ?_, ?_⟩
  · rw [Cfg.mapState_output] at hvo
    exact hvo
  · intro u hu j
    have h := hvh u hu j
    rw [Cfg.mapState_workTapePos] at h
    exact h
  · intro w hw hs
    have hsummary := windowRun_summary_of_halts M x hw hs
      (Nat.lt_succ_self (M.configBound x.length s))
    have hout := hword (M.configBound x.length s + 1) le_rfl
      (by rw [hsummary]
          exact (fun hbad => WindowExit.noConfusion hbad : WindowExit.halted ≠ .exhausted))
    rw [hsummary] at hout
    exact hpred hout w hw hs


/-- Initialize the simulated machine's record from the radius word, then run the complete
clocked suffix. Scratch banks are disjoint from the radius and witness tapes.

**Proof sketch.** Invoke the framed initializer, install its record using the shared boundary
calculation, and pass its untouched runner bank to the suffix. The published seam composes the
runs; the initializer restores every head, so both envelopes have the same centre. -/
private lemma sph_record_suffix (M : FinTM Bool) (m : ℕ) :
    ∃ (KI KR : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM (KI + KR + m + 2) (RecSym M.State (Fin 3)) P)
      (entry : P) (C : ℕ),
      ∀ {x : List Bool} (s : ℕ) (ws : List Bool), Nat.ofDigits 2 (ws.map Bool.toNat) = s →
      ∀ d : Cfg (KI + KR + m + 2) (RecSym M.State (Fin 3)) P
          (x.map (RecSym.digitEmb M.State (Fin 3))),
        d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ (ws.length : ℤ) →
          d.workTapes 1 (d.workTapePos 1 + p) = FinTM.bufferTape (ws.map RecSym.digit) p) →
        (∀ j : Fin (KI + KR + m + 2), j.val < KI + KR + 2 → j ≠ 1 →
          ∀ p, d.workTapes j p = none) →
        ∃ t b,
          (D.runFrom d t).state = none ∧
          (D.runFrom d t).output = d.output ++ [RecSym.digit b] ∧
          (∀ u ≤ t, ∀ j, |(D.runFrom d u).workTapePos j - d.workTapePos j| ≤
            ((C * (recordLength M.k x.length s + ws.length + s + 1) : ℕ) : ℤ)) ∧
          (∀ w : List Bool,
            M.ComputesInTime x w (M.configBound x.length s) →
            M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length s) ≤ s →
            b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KR, PS, hFS, hDS, S, sen, CS, hS⟩ := sph_suffix M
  letI := hFS
  letI := hDS
  obtain ⟨KI, PI, hFI, hDI, I, ien, iex, CI, hI⟩ := sph_initial_record M KR m
  letI := hFI
  letI := hDI
  let D := seamCompTM I iex (S KI m) sen
  refine ⟨KI, KR, PI ⊕ PS, inferInstance, inferInstance, D, Sum.inl ien, CI + CS, ?_⟩
  intro x s ws hws d hd hin hrad hblank
  let a := d.mapState (fun _ => ien)
  have ha : a.state = some ien := by rw [Cfg.mapState_state, hd]; rfl
  have hstart : a.mapState Sum.inl = d := by
    simp only [a, Cfg.mapState_mapState]
    exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  let L := recordLength M.k x.length s
  have hblank' (j : Fin (KI + KR + m + 2)) (hj : j.val < KI + KR + 2) (hj1 : j ≠ 1)
      (p : ℤ) : a.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    exact hblank j hj hj1 p
  obtain ⟨t, _, hc, hh, hr⟩ := hI s ws hws a ha
    (by rw [Cfg.mapState_inputPos]; exact hin)
    (by
      intro p hp hp'
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
      exact hrad p hp hp')
    (by
      intro p _ _
      exact hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    (by
      intro j hj hj' p
      exact hblank' j (by omega) (by
        intro h; subst j; rw [Fin.val_one] at hj; omega) p)
  let a' := I.runFrom a t
  have he : a'.state = some iex := by dsimp only [a']; rw [hr]
  have hah (j) : a'.workTapePos j = d.workTapePos j := by
    dsimp only [a']; rw [hr, Cfg.mapState_workTapePos]
  have hao : a'.output = d.output := by dsimp only [a']; rw [hr, Cfg.mapState_output]
  have har : RecordAt a' 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    have hwritten := sph_written_record a (some iex) (cfgRecord s (M.tm.initCfg x) 0) L
      (joinFields_cfgRecord_length _ _ _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
      (hblank' 0 (by rw [Fin.val_zero]; omega) Fin.zero_ne_one _)
    dsimp only [a']
    rw [recordAt_iff] at hwritten ⊢
    intro p hp hp'
    rw [hr]
    exact hwritten p hp hp'
  let z := a'.mapState (fun _ => sen)
  have hz : z.state = some sen := by rw [Cfg.mapState_state, he]; rfl
  have hzr : RecordAt z 0 (cfgRecord s (M.tm.initCfg x) 0) := by
    rw [recordAt_iff] at har ⊢
    intro p hp hp'
    rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
    exact har p hp hp'
  have hzb (j : Fin (KI + KR + m + 2)) (hj : KI + 2 ≤ j.val)
      (hj' : j.val < KI + KR + 2) (p : ℤ) : z.workTapes j p = none := by
    rw [Cfg.mapState_workTapes]
    dsimp only [a']
    rw [hr]
    have hj0 : j ≠ 0 := by intro h; subst j; rw [Fin.val_zero] at hj; omega
    simpa only [hj0, false_and, ↓reduceIte] using
      hblank' j hj' (by intro h; subst j; rw [Fin.val_one] at hj; omega) p
  obtain ⟨v, b, hvs, hvo, hvh, hpred⟩ := hS KI m s z hz hzr hzb
  have hrun := seamCompTM_run_ofCfg I iex (S KI m) sen (rfl : I.runFrom a t = a')
    he hc (rfl : (S KI m).runFrom z v = (S KI m).runFrom z v)
  rw [hstart] at hrun
  let B := (CI + CS) * (L + ws.length + s + 1)
  have hIB : CI * (L + ws.length + s + 1) ≤ B :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hSB : CS * (L + 1) ≤ B :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)
  refine ⟨t + 1 + v, b, ?_, ?_, ?_, hpred⟩
  · rw [hrun, Cfg.mapState_state, hvs, Option.map_none]
  · rw [hrun, Cfg.mapState_output, hvo, Cfg.mapState_output, hao]
  · have hen := sph_seam_heads I iex (S KI m) sen (rfl : I.runFrom a t = a') he hc
      d.workTapePos B
      (by
        intro u hu j
        have h := hh u hu j
        rw [Cfg.mapState_workTapePos] at h
        exact h.trans (by exact_mod_cast hIB))
      (by
        intro u hu j
        have h := hvh u hu j
        rw [Cfg.mapState_workTapePos, hah] at h
        exact h.trans (by exact_mod_cast hSB))
    rw [hstart] at hen
    exact hen


/-- The complete record-and-radius envelope is linear in any bound above `logSpace`.
The coefficient depends only on the fixed simulated machine's tape count.

**Proof sketch.** The radius needs at most its value in binary digits. An input position
needs at most twice `logSpace n` digits. Insert these bounds in the public record-length
formula and absorb the additive constants using the logarithmic floor. -/
private lemma sph_record_size (g : ℕ → ℕ) (hg : ∀ n, logSpace n ≤ g n) (k n : ℕ) :
    recordLength k n (g n) + (g n).bits.length + g n + 1 ≤ (4 * k + 9) * g n := by
  have hfloor : 1 ≤ g n := by have h := hg n; rw [logSpace_eq] at h; omega
  have hb : (g n).bits.length ≤ g n := length_bits_le_self _
  have hp : posWidth n ≤ 2 * g n := by
    rw [posWidth_eq]
    have hpow : n + 1 < 2 ^ (Nat.log 2 n + 2) :=
      (LogProg.succ_le_two_pow_log n).trans_lt
        (Nat.pow_lt_pow_right (by decide) (by omega))
    have h := LogProg.length_bits_le hpow
    have hg' := hg n
    rw [logSpace_eq] at hg'
    omega
  rw [recordLength_eq]
  have hk : k ≤ k * g n := Nat.le_mul_of_pos_right k hfloor
  nlinarith


/-- The diagonalizer after validation, on embedded binary inputs. It computes the radius,
rewinds, initializes the record, and runs the clocked opposite-verdict suffix.

**Proof sketch.** Use the returning witness capture and two existing seams. Its blank frame
provides the initializer and runner banks. Add the radius, rewind and record envelopes,
then use the logarithmic floor to bound their sum by a fixed multiple of the radius. -/
private lemma sph_valid_machine (M : FinTM Bool) (g : ℕ → ℕ)
    (hg : ∀ n, logSpace n ≤ g n) (c : ℕ) (G : FinTM Bool)
    (hG : G.ComputesInSpace (fun x => (g x.length).bits) (fun n => c * g n)) :
    ∃ (k : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (D : MultiTapeTM k (RecSym M.State (Fin 3)) P) (entry : P) (B : ℕ),
      ∀ x : List Bool, ∃ t b,
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).state = none ∧
        (D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) t).output =
          [RecSym.digit b] ∧
        (∀ u ≤ t, ∀ j,
          |(D.runFrom (Cfg.init entry (x.map (RecSym.digitEmb M.State (Fin 3)))) u).workTapePos j| ≤
            ((B * g x.length : ℕ) : ℤ)) ∧
        (∀ w : List Bool,
          M.ComputesInTime x w (M.configBound x.length (g x.length)) →
          M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
          b = !(decide (w = [true]))) := by
  classical
  obtain ⟨KI, KR, PS, hFS, hDS, S, sen, C, hS⟩ := sph_record_suffix M G.k
  letI := hFS
  letI := hDS
  let k := KI + KR + G.k + 2
  let e := RecSym.digitEmb M.State (Fin 3)
  let ι := sphWitnessSel KI KR G.k
  let R := embedSilentRetTM ι 1 (G.tm.liftSymbols e)
  let W := sphRewindsTM k M.State 1
  let wen : (Bool ⊕ InputRewindPhase) ⊕ RewindPhase := .inl (.inl false)
  let A := seamCompTM W (.inr RewindPhase.done) S sen
  let aen : ((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS := .inl wen
  let D := seamCompTM R (.inr ()) A aen
  let en : (G.State ⊕ Unit) ⊕ (((Bool ⊕ InputRewindPhase) ⊕ RewindPhase) ⊕ PS) :=
    .inl (.inl G.tm.q₀)
  let B := c + 3 + C * (4 * M.k + 9)
  refine ⟨k, _, inferInstance, inferInstance, D, en, B, ?_⟩
  intro x
  let ws := (g x.length).bits
  let start := (embedSilentCfg ι 1 (fun _ _ => none) (fun _ => 0) [] []
    ((G.tm.initCfg x).liftSymbols e)).mapState (Sum.inl : G.State → G.State ⊕ Unit)
  have hcap := sph_witness_cap KI KR G.k
  have hstart : start.mapState Sum.inl = Cfg.init en (x.map e) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.mapState_state, embedSilentCfg_state,
        Cfg.liftSymbols_state, MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_state]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos, embedSilentCfg_inputPos,
        Cfg.liftSymbols_inputPos, MultiTapeTM.initCfg_eq, Cfg.init_inputPos, Cfg.init_inputPos]
      apply Fin.ext
      change (1 : Fin (x.length + 2)).val = (1 : Fin ((x.map e).length + 2)).val
      rw [Fin.val_one, Fin.val_one]
    · funext j p
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes, Cfg.init_workTapes]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_tape, Cfg.liftSymbols_workTapes,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapes, Option.map_none]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).1,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, FinTM.bufferTape_nil]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).1]
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos, Cfg.init_workTapePos]
      by_cases hj : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hj
        rw [embedSilentCfg_selected_pos, Cfg.liftSymbols_workTapePos,
          MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
      · by_cases hjc : j = 1
        · subst j
          rw [(embedSilentCfg_cap ι 1 hcap _ _ [] [] _).2,
            Cfg.liftSymbols_output, MultiTapeTM.initCfg_eq, Cfg.init_output,
            List.map_nil, List.nil_append, List.length_nil, Nat.cast_zero]
        · rw [(embedSilentCfg_unselected ι 1 _ _ [] [] _ j hj hjc).2]
    · rw [Cfg.mapState_output, Cfg.mapState_output, embedSilentCfg_output, Cfg.init_output]
  obtain ⟨t, hrs, hrc, hrt, hrp, hrf, hro, _, hrh⟩ :=
    sph_radius_run KI KR (Q := M.State) g c G hG x (fun _ _ => none) (fun _ => 0) []
  let r := R.runFrom start t
  have hrs' : r.state = some (Sum.inr ()) := hrs
  let d := r.mapState (fun _ => false)
  have hd : d.state = some false := by rw [Cfg.mapState_state, hrs']; rfl
  obtain ⟨u, hwr, hwc, hwh⟩ := sph_rewinds_run KI KR G.k ws d hd
    (by funext p; rw [Cfg.mapState_workTapes]; exact congrFun hrt p)
    (by rw [Cfg.mapState_workTapePos]; exact hrp)
  have hwi : (d.mapState Sum.inl).mapState Sum.inl = r.mapState (fun _ => wen) := by
    dsimp only [d]
    rw [Cfg.mapState_mapState, Cfg.mapState_mapState]
    rfl
  rw [hwi] at hwr hwc hwh
  let z := W.runFrom (r.mapState fun _ => wen) u
  have hze : z.state = some (Sum.inr RewindPhase.done) := by dsimp only [z]; rw [hwr]
  have hzt (j p) : z.workTapes j p = r.workTapes j p := by
    dsimp only [z]; rw [hwr, Cfg.mapState_workTapes]
  have hzh (j) : z.workTapePos j = Function.update r.workTapePos 1 0 j := by
    dsimp only [z]; rw [hwr]
    have hheads : d.workTapePos = r.workTapePos := by
      funext i
      rw [Cfg.mapState_workTapePos]
    rw [hheads]
  have hzo : z.output = [] := by
    dsimp only [z]; rw [hwr, Cfg.mapState_output]
    exact hro t le_rfl
  let y := z.mapState (fun _ => sen)
  have hy : y.state = some sen := by rw [Cfg.mapState_state, hze]; rfl
  obtain ⟨v, b, hss, hso, hsh, hpred⟩ := hS (g x.length) ws
    ((counterValue_eq _).symm.trans (counterValue_bits _)) y hy
    (by rw [Cfg.mapState_inputPos]; dsimp only [z]; rw [hwr])
    (by
      intro p _ _
      rw [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, hzh, Function.update_self,
        zero_add, hzt, hrt])
    (by
      intro j hj hjc p
      rw [Cfg.mapState_workTapes, hzt]
      have hjr : j ∉ Set.range ι := by
        rintro ⟨i, hi⟩
        have h := congrArg Fin.val hi
        simp only [ι, sphWitnessSel, Function.Embedding.coeFn_mk] at h
        omega
      exact congrFun (hrf j hjr hjc).1 p)
  have hai : (r.mapState (fun _ => wen)).mapState Sum.inl = r.mapState (fun _ => aen) := by
    rw [Cfg.mapState_mapState]
    rfl
  have hAr := seamCompTM_run_ofCfg W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc
    (rfl : S.runFrom y v = S.runFrom y v)
  rw [hai] at hAr
  have hDr := seamCompTM_run_ofCfg R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc hAr
  rw [hstart] at hDr
  let rR := c * g x.length + ws.length
  let rW := rR + (ws.length + 1)
  let rS := C * (recordLength M.k x.length (g x.length) + ws.length + g x.length + 1)
  let radius := rW + rS
  have hRH (a : ℕ) (ha : a ≤ t) (j) : |(R.runFrom start a).workTapePos j| ≤ (rR : ℤ) := by
    simpa only [abs_zero, zero_add] using hrh a ha j
  have hWH (a : ℕ) (ha : a ≤ u) (j) :
      |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j| ≤ (rW : ℤ) := by
    have h₁ := hwh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hRH t le_rfl j
    calc
      _ ≤ |(W.runFrom (r.mapState fun _ => wen) a).workTapePos j - r.workTapePos j| +
          |r.workTapePos j| := by
            simpa only [sub_zero] using abs_sub_le
              ((W.runFrom (r.mapState fun _ => wen) a).workTapePos j) (r.workTapePos j) (0 : ℤ)
      _ ≤ ((ws.length + 1 : ℕ) : ℤ) + (rR : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [rW]; push_cast; ring
  have hSH (a : ℕ) (ha : a ≤ v) (j) : |(S.runFrom y a).workTapePos j| ≤ (radius : ℤ) := by
    have h₁ := hsh a ha j
    rw [Cfg.mapState_workTapePos] at h₁
    have h₂ := hWH u le_rfl j
    calc
      _ ≤ |(S.runFrom y a).workTapePos j - z.workTapePos j| + |z.workTapePos j| := by
        simpa only [sub_zero] using
          abs_sub_le ((S.runFrom y a).workTapePos j) (z.workTapePos j) (0 : ℤ)
      _ ≤ (rS : ℤ) + (rW : ℤ) := add_le_add h₁ h₂
      _ = _ := by dsimp only [radius]; push_cast; ring
  have hAH := sph_seam_heads W (.inr RewindPhase.done) S sen
    (rfl : W.runFrom (r.mapState fun _ => wen) u = z) hze hwc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hWH a ha j).trans (by dsimp only [radius]; push_cast; omega))
    (by intro a ha j; rw [sub_zero]; exact hSH a ha j)
  rw [hai] at hAH
  have hDH := sph_seam_heads R (.inr ()) A aen
    (rfl : R.runFrom start t = r) hrs' hrc (fun _ => 0) radius
    (by
      intro a ha j
      rw [sub_zero]
      exact (hRH a ha j).trans (by dsimp only [radius, rW]; push_cast; omega)) hAH
  rw [hstart] at hDH
  have hsize : radius ≤ B * g x.length := by
    have hrecord := sph_record_size g hg M.k x.length
    have hbits : ws.length ≤ g x.length := length_bits_le_self _
    have hfloor : 1 ≤ g x.length := by have h := hg x.length; rw [logSpace_eq] at h; omega
    have h := Nat.mul_le_mul_left C hrecord
    dsimp only [radius, rW, rR, rS, B]
    nlinarith
  refine ⟨t + 1 + (u + 1 + v), b, ?_, ?_, ?_, hpred⟩
  · rw [hDr, Cfg.mapState_state, Cfg.mapState_state, hss, Option.map_none, Option.map_none]
  · rw [hDr, Cfg.mapState_output, Cfg.mapState_output, hso, Cfg.mapState_output,
      hzo, List.nil_append]
  · intro a ha j
    have h := hDH a ha j
    rw [sub_zero] at h
    exact h.trans (by exact_mod_cast hsize)


/-- Turn a certified bounded halting run into a first-exit contract at its first halt.

**Proof sketch.** The public first-halt theorem preserves the endpoint and shortens the
run. Restrict the given head envelope to that prefix and use equality as the precondition. -/
private lemma sph_halt_contract {k : ℕ} {Γ P : Type} {ys : List Γ}
    (M : MultiTapeTM k Γ P) (entry : P) (d : Cfg k Γ P ys) (t B : ℕ)
    (ht : (M.runFrom d t).state = none)
    (hh : ∀ u ≤ t, ∀ j, |(M.runFrom d u).workTapePos j| ≤ (B : ℤ)) :
    ∃ C : Contract M entry {none} Unit ys,
      (∀ a, C.pre () a ↔ a = d) ∧ C.post () d = M.runFrom d t ∧
      (∀ a j, C.lo () a j = -(B : ℤ) ∧ C.hi () a j = (B : ℤ)) := by
  obtain ⟨u, hu, hc, he⟩ := M.exists_first_halt d ht
  let C : Contract M entry {none} Unit ys :=
    { pre := fun _ a => a = d
      time := fun _ _ => u
      post := fun _ _ => M.runFrom d t
      lo := fun _ _ _ => -(B : ℤ)
      hi := fun _ _ _ => (B : ℤ)
      run := by intro _ a _ ha; subst a; exact he
      exit_mem := by intro _ a _ _; exact ht
      cut := by
        intro _ a _ ha v hv
        subst a
        exact hc v hv
      env := by
        intro _ a _ ha v hv j
        subst a
        rw [Finset.mem_Icc]
        exact abs_le.mp (hh v (hv.trans hu) j) }
  exact ⟨C, fun _ => Iff.rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩


/-- Add the published input validator to a binary-input machine. Foreign symbols are rejected
before its work tapes are used, so the resulting finite machine is space bounded on all inputs.

**Proof sketch.** The validation contract branches to a first-halt contract of the supplied
machine or the false emitter. Both use the same absolute head interval. Read the branch's
public endpoint and envelope equations, then sum the interval bound over the physical tapes. -/
private lemma sph_validated_machine {k : ℕ} {Q P : Type} [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P]
    (V : MultiTapeTM k (RecSym Q (Fin 3)) P) (entry : P) (S : ℕ → ℕ)
    (pred : List Bool → Bool → Prop)
    (hV : ∀ x : List Bool, ∃ t b,
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).state = none ∧
      (V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) t).output =
        [RecSym.digit b] ∧
      (∀ u ≤ t, ∀ j,
        |(V.runFrom (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) u).workTapePos j| ≤
          (S x.length : ℤ)) ∧ pred x b) :
    ∃ D : FinTM (RecSym Q (Fin 3)),
      ∀ ys : List (RecSym Q (Fin 3)), ∃ t b,
        D.ComputesInTime ys [RecSym.digit b] t ∧
        D.tm.spaceUsed (D.tm.initCfg ys) t ≤ k * (2 * S ys.length + 1) ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x b := by
  classical
  let F : MultiTapeTM k (RecSym Q (Fin 3)) (ScanPhase Bool) :=
    inputFoldTM k (fun a c => a && sphDigit c) true
  let E := sphEmitTM k (RecSym.digit false : RecSym Q (Fin 3))
  let R := seamCompTM₂ F (.done true) (.done false) V entry E ()
  let en : (ScanPhase Bool ⊕ P) ⊕ Unit := .inl (.inl (.fwd true))
  let D : FinTM (RecSym Q (Fin 3)) :=
    { k := k
      State := (ScanPhase Bool ⊕ P) ⊕ Unit
      fintypeState := inferInstance
      decEqState := inferInstance
      tm := {R with q₀ := en} }
  refine ⟨D, ?_⟩
  intro ys
  let a : Cfg k (RecSym Q (Fin 3)) (ScanPhase Bool) ys := Cfg.init (.fwd true) ys
  obtain ⟨b, hr, hvalid, hcut, hheads⟩ := sph_validation_run a
    (Cfg.init_state _ _) (Cfg.init_inputPos _ _)
  let a' := {a with state := some (ScanPhase.done b)}
  let radius := S ys.length
  have hrad : (0 : ℤ) ≤ radius := Int.natCast_nonneg _
  let C₀ : Contract F (.fwd true) {some (.done true), some (.done false)} Unit ys :=
    { pre := fun _ d => d = a
      time := fun _ _ => 2 * ys.length + 2
      post := fun _ _ => a'
      lo := fun _ _ _ => -(radius : ℤ)
      hi := fun _ _ _ => (radius : ℤ)
      run := by intro _ d _ hd; subst d; exact hr
      exit_mem := by
        intro _ d _ _
        cases b <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, a', or_true, true_or]
      cut := by
        intro _ d _ hd u hu hm
        subst d
        rcases hm with hm | hm
        · exact hcut u hu true hm
        · exact hcut u hu false hm
      env := by
        intro _ d _ hd u hu j
        subst d
        rw [hheads j u hu, Cfg.init_workTapePos, Finset.mem_Icc]
        exact ⟨by omega, hrad⟩ }
  have hstart₁ : a'.mapState (fun _ => entry) = Cfg.init entry ys := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  have hC₁ : ∃ C₁ : Contract V entry {none} Unit ys,
      (b = true → C₁.pre () (Cfg.init entry ys)) ∧
      (∀ d j, C₁.lo () d j = -(radius : ℤ) ∧ C₁.hi () d j = (radius : ℤ)) ∧
      (b = true → ∃ ans,
        (C₁.post () (Cfg.init entry ys)).state = none ∧
        (C₁.post () (Cfg.init entry ys)).output = [RecSym.digit ans] ∧
        ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans) := by
    by_cases hb : b = true
    · obtain ⟨x, rfl⟩ := hvalid.mp hb
      obtain ⟨v, ans, hvs, hvo, hvh, hp⟩ := hV x
      obtain ⟨C₁, hpre, hpost, henv⟩ := sph_halt_contract V entry
        (Cfg.init entry (x.map (RecSym.digitEmb Q (Fin 3)))) v radius hvs
        (by simpa only [radius, List.length_map] using hvh)
      refine ⟨C₁, fun _ => (hpre _).mpr rfl, henv, ?_⟩
      intro _
      refine ⟨ans, ?_, ?_, ?_⟩
      · rw [hpost]; exact hvs
      · rw [hpost]; exact hvo
      · intro x' hx
        have heq : x = x' := List.map_injective_iff.mpr (RecSym.digitEmb Q (Fin 3)).injective hx
        subst x'
        exact hp
    · let C₁ : Contract V entry {none} Unit ys :=
        { pre := fun _ _ => False
          time := fun _ _ => 0
          post := fun _ d => d
          lo := fun _ _ _ => -(radius : ℤ)
          hi := fun _ _ _ => (radius : ℤ)
          run := by intro _ _ _ h; exact False.elim h
          exit_mem := by intro _ _ _ h; exact False.elim h
          cut := by intro _ _ _ h; exact False.elim h
          env := by intro _ _ _ h; exact False.elim h }
      exact ⟨C₁, fun h => False.elim (hb h), fun _ _ => ⟨rfl, rfl⟩,
        fun h => False.elim (hb h)⟩
  obtain ⟨C₁, hpre₁, henv₁, hpost₁⟩ := hC₁
  have hne : (ScanPhase.done true : ScanPhase Bool) ≠ .done false := by
    intro h; cases h
  let C := Contract.branch hne C₀ C₁ (sphEmitContract (RecSym.digit false) ys)
    (fun _ => ()) (fun _ => ())
    (by
      intro _ d _ hd he
      have hb : b = true := ScanPhase.done.inj (Option.some.inj he)
      change C₁.pre () (a'.mapState fun _ => entry)
      rw [hstart₁]
      exact hpre₁ hb)
    (fun _ _ _ _ _ => True.intro)
  let d₀ : Cfg k (RecSym Q (Fin 3)) ((ScanPhase Bool ⊕ P) ⊕ Unit) ys := Cfg.init en ys
  have hd₀ : d₀.state = some (Sum.inl (Sum.inl (.fwd true))) := Cfg.init_state _ _
  have hpre : C.pre () d₀ := by
    rw [Contract.branch_pre]
    change (d₀.mapState fun _ => ScanPhase.fwd true) = a
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.init_state, Cfg.init_state]; rfl
    · rw [Cfg.mapState_inputPos, Cfg.init_inputPos, Cfg.init_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  have hh (u : ℕ) (hu : u ≤ C.time () d₀) (j) :
      |(R.runFrom d₀ u).workTapePos j| ≤ (radius : ℤ) := by
    have h := C.env () d₀ hd₀ hpre u hu j
    rw [Contract.branch_lo, Contract.branch_hi] at h
    dsimp only [C₀, sphEmitContract] at h
    rw [(henv₁ _ j).1, (henv₁ _ j).2] at h
    simp only [a', a, Cfg.mapState_workTapePos, Cfg.init_workTapePos] at h
    split_ifs at h
    · simpa only [min_self, max_self, Finset.mem_Icc, ← abs_le] using h
    · rw [min_eq_left (by omega), max_eq_left hrad, Finset.mem_Icc] at h
      exact abs_le.mpr h
  have hend : ∃ ans,
      (R.runFrom d₀ (C.time () d₀)).state = none ∧
      (R.runFrom d₀ (C.time () d₀)).output = [RecSym.digit ans] ∧
      ∀ x : List Bool, ys = x.map (RecSym.digitEmb Q (Fin 3)) → pred x ans := by
    have hr' := C.run () d₀ hd₀ hpre
    rw [Contract.branch_post] at hr'
    dsimp only [C₀] at hr'
    by_cases hb : b = true
    · obtain ⟨ans, hs, ho, hp⟩ := hpost₁ hb
      rw [if_pos (by change some (ScanPhase.done b) = some (.done true); rw [hb]),
        hstart₁] at hr'
      refine ⟨ans, ?_, ?_, hp⟩
      · rw [hr', Cfg.mapState_state, Cfg.mapState_state, hs, Option.map_none, Option.map_none]
      · rw [hr', Cfg.mapState_output, Cfg.mapState_output, ho]
    · rw [if_neg (by intro h; exact hb (ScanPhase.done.inj (Option.some.inj h)))] at hr'
      refine ⟨false, ?_, ?_, ?_⟩
      · rw [hr', Cfg.mapState_state]
        rfl
      · rw [hr', Cfg.mapState_output]
        dsimp only [sphEmitContract]
        rw [Cfg.mapState_output, Cfg.init_output, List.nil_append]
      · intro x hx
        exact False.elim (hb (hvalid.mpr ⟨x, hx⟩))
  obtain ⟨ans, hstate, hout, hp⟩ := hend
  have hrun (u : ℕ) : D.tm.runFrom (D.tm.initCfg ys) u = R.runFrom d₀ u := by
    rw [MultiTapeTM.initCfg_with_q₀, MultiTapeTM.runFrom_with_q₀]
  refine ⟨C.time () d₀, ans, ?_, ?_, hp⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [hrun]
    exact ⟨hstate, hout⟩
  · apply MultiTapeTM.spaceUsed_le_of_abs_le
    intro u hu j
    rw [hrun, MultiTapeTM.initCfg_with_q₀, Cfg.init_workTapePos, sub_zero]
    exact hh u hu j


/-- A space-constructible radius admits a diagonal language for any fixed finite binary
machine: whenever that machine halts within the radius, the language gives the opposite bit.

**Proof sketch.** Validate before computing the radius and running the fixed machine's window.
Choose the resulting total output as the language's indicator. The all-input head envelope
bounds space at the halting time and hence at every time. Apply the published alphabet
reduction and absorb its constants using the constructible bound's logarithmic floor. -/
private lemma sph_diagonal_language (M : FinTM Bool) (g : ℕ → ℕ) (hg : SpaceConstructible g) :
    ∃ L : Language Bool, L ∈ SPACE g ∧
      ∀ (x w : List Bool),
        M.ComputesInTime x w (M.configBound x.length (g x.length)) →
        M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
        MultiTapeTM.indicator (L : Set (List Bool)) x = !(decide (w = [true])) := by
  classical
  obtain ⟨hfloor, c, _, G, hG⟩ := (spaceConstructible_iff g).mp hg
  obtain ⟨k, P, hFP, hDP, V, entry, B, hV⟩ := sph_valid_machine M g hfloor c G hG
  letI := hFP
  letI := hDP
  let pred (x : List Bool) (b : Bool) := ∀ w : List Bool,
    M.ComputesInTime x w (M.configBound x.length (g x.length)) →
    M.tm.spaceUsed (M.tm.initCfg x) (M.configBound x.length (g x.length)) ≤ g x.length →
    b = !(decide (w = [true]))
  obtain ⟨D, hD⟩ := sph_validated_machine V entry (fun n => B * g n) pred hV
  choose t answer ht hs hp using hD
  let e := RecSym.digitEmb M.State (Fin 3)
  let L : Language Bool := {x | answer (x.map e) = true}
  have hind (x : List Bool) : MultiTapeTM.indicator (L : Set (List Bool)) x =
      answer (x.map e) := by
    let bit := MultiTapeTM.indicator (L : Set (List Bool)) x
    let E : FinTM Bool :=
      { k := 0
        State := Unit
        fintypeState := inferInstance
        decEqState := inferInstance
        tm := sphEmitTM 0 bit }
    have hleaf := (sph_emit_run bit (E.tm.initCfg x)
      (by rw [MultiTapeTM.initCfg_eq, Cfg.init_state])).1
    have he : E.ComputesInTime x [bit] 1 := by
      apply (FinTM.computesInTime_iff _ _ _ _).mpr
      rw [hleaf]
      refine ⟨rfl, ?_⟩
      rw [MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append]
    have hlang := (E.toFinNDTM_haltsWithin_and_accepts_iff (L := L) he).2
    have hacc : E.toFinNDTM.AcceptsWithin x 1 ↔ bit = true := by
      rw [FinNDTM.acceptsWithin_iff]
      constructor
      · rintro ⟨w, hw, _, ho⟩
        simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
          MultiTapeTM.toNDTM_runWith, hw] at ho
        rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append] at ho
        exact List.singleton_inj.mp ho
      · intro hb
        refine ⟨[false], rfl, ?_, ?_⟩
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton, hleaf]
        · simp only [FinTM.toFinNDTM_k, FinTM.toFinNDTM_State, FinTM.toFinNDTM_tm,
          MultiTapeTM.toNDTM_initCfg,
            MultiTapeTM.toNDTM_runWith, List.length_singleton]
          rw [hleaf, MultiTapeTM.initCfg_eq, Cfg.init_output, List.nil_append, hb]
    have htest : answer (x.map e) = true ↔ bit = true := hlang.trans hacc
    change bit = answer (x.map e)
    exact Bool.eq_iff_iff.mpr htest.symm
  let S (n : ℕ) := k * (2 * (B * g n) + 1)
  obtain ⟨c', N, hN⟩ := FinTM.decidesInSpace_of_alphabetReduction e D L S
    (by
      intro x
      refine ⟨t (x.map e), ?_⟩
      rw [hind, List.map_singleton, RecSym.digitEmb_apply]
      exact ht (x.map e))
    (by
      intro ys u
      exact (ht ys).spaceUsed_le_of_halt (hs ys) u)
  have hL : L ∈ SPACE (fun n => S n + 1) := mem_SPACE_iff.mpr ⟨c', N, hN⟩
  have hb (n : ℕ) : S n + 1 ≤ (k * (2 * B + 1) + 1) * g n := by
    have hn : 1 ≤ g n := by have h := hfloor n; rw [logSpace_eq] at h; omega
    calc
      _ ≤ k * (2 * (B * g n) + g n) + g n :=
        Nat.add_le_add (Nat.mul_le_mul_left k (Nat.add_le_add_left hn _)) hn
      _ = _ := by ring
  refine ⟨L, SPACE.mono_const hb hL, ?_⟩
  intro x w htime hspace
  rw [hind]
  exact hp (x.map e) x rfl w htime hspace


/-- A linear-space decider for the quadratically padded language suffices for the separation
from `NP`. [AB09, Exercise 3.2]

**Proof sketch.** If linear space were `NP`, the padded language would belong to `NP`. Its
polynomial-time padding map pulls it back to the original quadratic-space language, by the
published closure of `NP` under polynomial-time preimages. This reverses the strict inclusion
given by the space hierarchy at the linear and quadratic bounds. -/
private lemma sph_linear_ne_NP_of_padding
    (hH : ∀ f g : ℕ → ℕ, SpaceConstructible f → SpaceConstructible g →
      (∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) → SPACE f ⊂ SPACE g)
    (hpad : ∀ L : Language Bool, L ∈ SPACE (fun n => n ^ 2 + 1) →
      ({y | ∃ x ∈ L,
        y = pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)} : Language Bool) ∈
        SPACE (fun n => n + 1)) :
    SPACE (fun n => n + 1) ≠ NP := by
  intro heq
  have hback : SPACE (fun n => n ^ 2 + 1) ⊆ SPACE (fun n => n + 1) := by
    intro L hL
    let p : List Bool → List Bool := fun x =>
      pairEncode x (List.replicate (1 * (x.length + 1) ^ 2) true)
    let L' : Language Bool := {y | ∃ x ∈ L, y = p x}
    have hp : PolyTimeComputable p :=
      polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary 1 2)
    have hL' : L' ∈ NP := heq ▸ hpad L hL
    have hpull : p ⁻¹' L' = L := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := (show ∃ y ∈ L, p x = p y from hx)
        have he : x = y := by
          simpa only [p, pairFstD_pairEncode] using congrArg pairFstD hxy
        exact he.symm ▸ hy
      · intro hx
        exact (show ∃ y ∈ L, p x = p y from ⟨x, hx, rfl⟩)
    have hpre := preimage_mem_NP hp hL'
    rw [hpull] at hpre
    exact heq.symm ▸ hpre
  have hstrict := hH (fun n => n + 1) (fun n => n ^ 2 + 1)
    spaceConstructible_linear (spaceConstructible_poly 2 (by norm_num))
    (fun A => ⟨A + 1, fun n hn => by
      nlinarith [Nat.mul_le_mul_right (n + 1) hn]⟩)
  exact hstrict.2 hback

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]): for
space-constructible `f` and `g`, if every constant multiple of `f` is
eventually below `g` (that is, `f = o(g)`), then `SPACE f ⊊ SPACE g`.
Constant-factor hypothesis — no square and no logarithmic term, by a
universal simulation with constant-factor space overhead (the
self-application universal `U₀` of the sketch, the sibling of
`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof uses `g`'s witness and floor but, of `f`'s, only the
bundled floor. Positivity of both bounds is automatic from the bundled
`logSpace` floor, so the zero-bound convention needs no side condition.

**Proof sketch.** *Inclusion.* `hfg` at `A = 1` gives `f n ≤ g n` from some
`N` on; below `N` each `f n` is at most `F := max_{n<N} f n` times
`g n ≥ 1` (`g`'s floor), so `f ≤ max F 1 · g` everywhere and
`Complexity.SPACE.mono_const` applies.

*The universal machine `U₀`.* One fixed machine for the scheme
`Complexity.TimeHierarchy.code`: on an input `x = pairEncode α w` it canonizes
`α` from the doubled prefix (the chapter-1 startup, `Turing.universalCanonTM`),
returns its input head to the origin, and simulates the coded machine on `x`
itself — self-application, so no `preTM` copy is needed — with its own input
head as the simulated one (the native device: the simulated input is all of
`U₀`'s input, so its left boundary is a real blank and no position is stored)
and the step block on the canonical table. Its forward ledger: for each
`α` a constant `C_α` such that whenever the coded machine halts on `x` with
some output, having visited at most `s` cells, `U₀` halts on `x` with the
same output, having visited at most `C_α · (s + 1)` cells
(`Turing.exists_selfUniversal`). This is `space_universal`'s forward clause
with the native device in place of the bounded-prefix ruler, so no header
ruler is needed; only this direction is used.

*The diagonalizer `D`.* On input `x` with `n = |x|`, over the record alphabet:
(i) validate the input (`Turing.inputFoldTM`), so that
`D`'s space is bounded on foreign rich inputs, as
`Turing.FinTM.alphabet_reduction_spaceUsed` requires, and compute
`bits (g n)` by `g`'s witness, captured on a work tape, in `O(g n)` cells;
(ii) form the radius `r = a · g n` for a fixed `a ≥ 1`
(`a = 1` suffices, the code-dependent constant being paid by the hypothesis
below; a power of two costs only low zero digits) and write `U₀`'s initial
record on `x` at radius `r`, tagged with the empty-output summary
(`Turing.exists_recordInitTM`); (iii) run the configuration-count windowed runner at `U₀`
(`Turing.exists_configWindowRunnerTM`): each round tests the record for a halted state, else
applies one step of `U₀` (leaving the window is an exit), the tag updated by the three-valued
output summary `Turing.outSummary` (`summaryTag`; append-compatible,
`Turing.outSummary_append_congr`; coded in `Fin 3`), so the emitted word is never buffered.
The runner carries its own configuration-count clock, whose value suffices for every round up
to `Turing.FinTM.configBound U₀ n r + 1`, in `O(record length)` cells.
(iv) Answer `false` if the runner stopped at a halted
record with summary `accept` (output exactly `[true]`,
`Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
with another output, window exit, or clock exhaustion. `D` halts on every
input. Its cells are the witness's `O(g n)`, the record's
`k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
runner's `O(record length)` scratch and clock: all `O(g n)` with
constants depending only on `U₀` and `g`'s witness, **uniformly in the code
part of `x`**, because the window, not `U₀`'s constant, bounds the
simulation; the `posWidth n = O(logSpace n)` terms are
absorbed by `g`'s floor. After the alphabet reduction, the language `L_D`
that `D` decides lies in `SPACE g`.

*`L_D ∉ SPACE f`.* Suppose `M` decides `L_D` within `c₀ · f n` cells. Then
`M` halts within `configBound M n (c₀ · f n)` steps
(`Turing.FinTM.ComputesInTime.of_spaceUsed_le`), and its space bound holds at
every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
configuration frozen after it). The space-faithful normal form
`Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N` within the same space
(`Turing.exists_codeTM_spaceUsed`) and set
`α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
`[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
where `A := C_{α_M} · (c · c₀ + c + 1)`, using `1 ≤ f n`. The hypothesis
`hfg` at this one `A` gives `N₀` with `A · f n ≤ g n ≤ r` for `n ≥ N₀`;
take `w := List.replicate N₀ true`. Then every configuration of `U₀`'s run
on `x` up to its halt is in the radius-`r` window, since each
tape's visited cells form an interval around `0` of size at most `r`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`) and every nonblank cell was
visited (`Turing.MultiTapeTM.mem_visited_of_ne_none`); and the halt comes by
step `configBound U₀ n r` (`ComputesInTime.of_spaceUsed_le` at the bound
`r`), before the clock runs out. So the runner stops at `U₀`'s halted record,
whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. The construction uses
`U₀` with its forward ledger (the step block at one coded work tape, the
native input device and the chapter-1 startup); the configuration-count
windowed runner `exists_configWindowRunnerTM` at `U₀` with the output-summary tag, after
the record initializer `exists_recordInitTM` and followed by the record test
`exists_recordTestTM`; the radius phase (`g`'s witness captured, radius digits);
the window-containment lemma from the visited-interval facts;
`exists_codeTM_spaceUsed` and the all-times space bound of a decider; the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
alphabet reduction. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  classical
  obtain ⟨U, hU⟩ := exists_selfUniversal TimeHierarchy.code
  obtain ⟨L, hLg, hdiag⟩ := sph_diagonal_language U g hg
  refine ⟨sph_inclusion hg hfg, ?_⟩
  intro hback
  obtain ⟨c, M, hM⟩ := mem_SPACE_iff.mp (hback hLg)
  obtain ⟨x, t, ht, hs, htime, _⟩ := sph_code_window f g hf hfg U hU L c M hM
  rw [htime] at ht hs
  have h := hdiag x [MultiTapeTM.indicator (L : Set (List Bool)) x] ht hs
  cases hb : MultiTapeTM.indicator (L : Set (List Bool)) x <;>
    simp only [hb, List.cons.injEq, and_true, Bool.false_eq_true, Bool.true_eq_false, decide_false,
      decide_true, Bool.not_false, Bool.not_true] at h

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear`; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  exact sph_logspace_ssubset space_hierarchy

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` — the literal `SPACE(n)` is the zero-work-tape class).
Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. Padding transfers space bounds down: for
`L ∈ SPACE (n² + 1)`, the padded language
`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate ((|x| + 1)²) true)}` (padded members of
`L` only; padded length exactly `m = (n + 1)² + 2n + 2`) lies in `SPACE (m + 1)`: validate the
padding, then run the `L`-decider on the first component, the pad supplying the room. So
`L' ∈ NP` by the assumption. The padding map is polynomial-time computable and `L` is the
preimage of `L'` under it, so `L ∈ NP` (`Complexity.preimage_mem_NP`), that is
`L ∈ SPACE (n + 1)`. Hence `SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). The argument uses the padded-language space decider,
the padding map's polynomial-time computability, `preimage_mem_NP` and the strictness
extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity
```
