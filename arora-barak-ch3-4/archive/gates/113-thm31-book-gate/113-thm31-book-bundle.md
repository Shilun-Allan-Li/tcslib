## ===== campaign/gates/113-thm31-book/pack.md =====

# External audit pack: the book-form time hierarchy (PR #223, a statement-and-proof gate)

## Why this PR

[AB09, Theorem 3.1] says that if `f, g` are time-constructible and `f(n) log f(n) = o(g(n))`,
then `DTIME(f) ⊊ DTIME(g)`. Until now the library proved it only with quadratic overhead:
`time_hierarchy`, needing `(f n + n + 1)² = o(g)` (`TimeHierarchy/Diagonal.lean`, Hydroxyi's
file). The parameterized argument (U2 Part 1, #100) reduces any hierarchy to a **self-simulator**
at some overhead. This PR supplies the `O(t log t)` self-simulator and states the book's form.

The self-simulator is U2-U, the self-application universal machine at two work tapes
(`exists_selfUniversalK 2`). Its normal form is `two_work_tapes_binary`, which rests on
`two_work_tapes_run` ([HS66]), proved by G5 in #211, now merged.

**Rulings:**
- 2026-10-14, all as recommended:
  - Q7: state both forms, with the book form under `∀ n, n ≤ f n` rather than
    `TimeConstructible f`;
  - Q8: the home is the end of `Diagonal.lean`, authorized;
  - Q10: no `DTIME(n+1) ⊊ DTIME((n+1)²)` illustration;
  - no U2-V;
  - the facade sentence is fixed here.
- 2026-11-06 (the user): land after #211, admission-free, **with `time_hierarchy_book_of_pos`**.

**The PR:** #223 on `lean/thm31-book`, head `05050b3d` (full hash in the bundle header). It
consists of the change `0a4520df`, the facade `1e92eaa9`, the docstring `a08d70d9`, and merges of
the campaign, the last after #218 and #219. It changes two files:
- `TimeHierarchy/Diagonal.lean`: 536 → 799 lines, 24 → 40 public, 0 → 1 private;
- the `TimeHierarchy` facade (one sentence).

## The statements (verify)

```lean
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g
```

**Reading against the book:**
- `f log f = o(g)` is read as "for every `A`, eventually `A · f n · log₂ f n ≤ g n`", the
  library's convention, as in `time_hierarchy`.
- `hf : n ≤ f n` replaces `TimeConstructible f` (Q7). Under it, `log₂ f n ≥ 1` once `n ≥ 2`, so
  the case `f n ≤ 1` (`Nat.log 2 (f n) = 0`) occurs only for `n ≤ 1`, which an eventual
  hypothesis never reaches. Without `hf` the statement would be false: at `f = 1`,
  `f log f = 0` and the hypothesis holds for every `g`. The docstring says so.
  `time_hierarchy_log` needs no hypothesis on `f`.
- `DTIME (g + 1)` is the library's form, as in `time_hierarchy`. `_of_pos` gives the book's
  literal `DTIME g` for positive `g`, mirroring `time_hierarchy_of_pos`.

## What changed (verify)

**New declarations** (all at the end of `Diagonal.lean`, namespace `Complexity.TimeHierarchy`
unless marked):
- `logOverhead t := (t + 1) * (Nat.log 2 (t + 1) + 1)` and `logDiagOverhead t n`, each with its
  `_eq`;
- the arithmetic: `le_logDiagOverhead`, `logOverhead_add_le`, `logOverhead_mul_le`,
  `logDiagOverhead_le_book`, and one private `eventually_logDiagOverhead_le`;
- `code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2`, with `_eq`;
- `twoTapeSelfSimulator : SelfSimulator logOverhead`, with `_W` and `_decode` (`rfl`):
  - **`simulates`:** `W := Classical.choose (exists_selfUniversalK 2 code₂.toK)`. The forward
    clause gives `C · (t + 1)` steps, lifted to `C · (t + |pairEncode α w| + 1)` by `.mono`,
    through `EffectiveMachineCode2.toK_toFinTM`.
  - **`normalForm`:** chains `two_work_tapes_binary`, then `exists_code2TM`, then `code₂.encode`
    with `MachineCode2.decode_encode`, then `logOverhead_mul_le`.
- in namespace `Complexity`: the three theorems. Each applies
  `(twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le)` with `le_logDiagOverhead`.
  The book forms pass the private helper's conclusion to `.time_hierarchy` or
  `.time_hierarchy_of_pos`.

**Unchanged:** every existing declaration of `Diagonal.lean`, byte-identical
(`evidence/freeze/`). The module docstring's opening, "Divergences", "Main definitions" and
"Main results" are rewritten. The facade's sentence "quadratic overhead in place of the book's
`f log f`" now names `time_hierarchy_book`.

**Imports:** `Robustness/TwoTapes` and `UniversalK` are added. Neither closure contains
`Diagonal`.

## Known deviations (for the audit)

- **Rule 10, two reads in `twoTapeSelfSimulator.normalForm`:**
  - `rintro ⟨c₀, M, hM⟩` destructures a `DTIME` membership;
  - `hM` is passed where `computesFunInTime_iff`'s right side is expected (`DecidesInTime`).

  Neither definition has a published characterization (no `mem_DTIME_iff`; no `FinTM`
  `decidesInTime_iff`). The received `oneTapeSelfSimulator` reads both the same way. The seal
  below isolates exactly these two. Publishing the two equations in `ClassP/DTIME` would replay
  most of the tree. It is recorded for the dedup window.
- **The lint's check 8** reads `code₂` and `code₂_eq` as `code`, because the identifier class is
  ASCII-only. `code₂_eq` exists.

## Brief for the auditor

1. **The statements:** are they the book's Theorem 3.1 under the conventions above? Check the
   boundary cases: `f n ≤ 1`, `g` vanishing (the `+ 1`), and the `Nat.log` floors.
2. **The proofs:**
   - Is `twoTapeSelfSimulator` a valid `SelfSimulator logOverhead`, in both its clauses?
   - Is the arithmetic right: `logOverhead_add_le` (`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`),
     `logOverhead_mul_le`, and `logDiagOverhead_le_book` (`≤ 12 · f log f` for `2 ≤ n ≤ f`)?
3. **Rule 10:** are the two disclosed reads the only ones? Is the seal adequate?
4. **Duplication:** does anything re-derive a published lemma? The screen and gate 24's carried
   checks are below.
5. **Public text:** is it accurate, attributed, and free of campaign labels?

## Repository-side attestations (verify or challenge)

- **Axioms** (`evidence/probes/axioms.*`): `time_hierarchy_log`, `time_hierarchy_book`,
  `time_hierarchy_book_of_pos`, `twoTapeSelfSimulator` and `two_work_tapes_run` all use
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10** (`evidence/probes/seal.*`): three verbatim copies of the new section, each in its
  own namespace under `attribute [local irreducible]`:
  - **A** seals `DTIME`, `DecidesInTime`, `TimeConstructible`, `ComputesInTime`,
    `ComputesFunInTime`, `EffectiveCodeK.toFinTM`, `EffectiveMachineCode2.toK`,
    `Code2TM.toFinTM`, `indicator`, `toDiagSimulator` and `mono`;
  - **B** seals all but `DTIME`;
  - **C** seals all but `DTIME` and `DecidesInTime`.

  Each copy opens with `fail_if_success rfl` controls. The output has exactly two errors: A at
  the `DTIME` destructuring (line 170) and B at the `DecidesInTime` read (line 422). C
  elaborates.
- **Gate 24's carried sanity checks** (`evidence/probes/sanity.*`): all of the following
  elaborate with exit 0:
  - `¬ Nonempty (DiagSimulator (fun _ _ => 0))`;
  - `¬ Nonempty (SelfSimulator (fun _ => 0))`;
  - no `SelfSimulator` with a constant `decode`;
  - the `rfl` projections of `mono`/`toDiagSimulator` and of the new instance.
- **Freeze** (`evidence/freeze/`, the head against the campaign's Lean `7027dead`):
  - `Diagonal`: 24 → 40 public (the 16 above), 0 → 1 private. No existing declaration changed,
    and none was removed.
  - The facade: no declarations.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `TimeHierarchy` gives 0 FAIL, 4 WARN over 5 files, at both base and
    head.
  - The policy linter gives 3 findings at both, the facade's pre-existing missing `set_option`s.
- **Screen** (`evidence/screen/`, the `TimeHierarchy` population at base and head):
  - the head has 72 declarations, 23 pairs and 3,903 characters, against 62, 16 and 3,277 at
    the base;
  - 7 pairs are new, all between new declarations or with a short projection: the three
    theorem forms against each other, `logOverhead_add_le` against `le_logDiagOverhead`, and
    `twoTapeSelfSimulator_decode` against `diagLang_not_mem_DTIME`'s one line;
  - none pairs with `oneTapeSelfSimulator`.
- **Replay** (`evidence/merged-tree/`): `replay-lt32` at `05050b3d` covers `Diagonal`'s
  downstream closure (14 modules, now including `Hierarchy`), chained from the campaign snapshot
  after #218 and #219. **14 modules, 0 failed.** The static check finds 0 mismatches. The 2
  `sorry` warnings are `Hierarchy`'s F6 and E-PAD.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/113-thm31-book/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `thm31-book-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/113-thm31-book/STATUS.md =====

# Gate 113 (#223, the book-form time hierarchy)

- 2026-11-06: #223 opened after #211 merged; `replay-lt32` (14/0, after #218/#219); probes (axioms, seal A/B/C, gate 24 sanity), freeze, lint, screen; pack written; staged.

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

## ===== campaign/gates/24-diagonal-p1-statements/resolutions.md =====

# Diagonal Part 1 statement gate: resolutions (round 1; gate CLOSED)

**Gate:** the in-place parameterization of Hydroxyi's `TimeHierarchy/Diagonal.lean` over a
diagonal simulator `DiagSimulator Φ` and a self-simulator `SelfSimulator Ψ`, with the four received
theorems re-derived as one-line instances (`audits/diagonal-p1-statements-pack.md`; bundle SHA-256
`8e4448c3f8e030876e2d5c56107af492dfbd0a7cb7f18f588d61617f1b8863c8`, 64 sections, dispatch folder
24; evidence `audits/evidence/diagonal-p1/`, committed in `fba93e7e`).

**Round 1** (`audits/diagonal-p1-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 2
minors. The gate closes.** Both minors concern evidence checkers, not the Lean statements, and are
repaired in this closing commit (`workflow.md` §3).
- **Surface:** all ten received heads byte-identical; the six retained bodies and the header
  identical; the landed file rebuilt independently by `mklanded.py` and by the patch.
- **Definitions:** all 14 new declarations and the 8 generated constructors and projections
  reviewed; the timeout convention (accept on timeout, as received) is harmless.
- **Adversarial instances:** zero overhead, a non-halting `W`, a constant `decode` and `Ψ = 0` are
  each impossible; `T = 0` and the zero constants are harmless vacuity.
- **Fit for U2-U at k = 2:** the verdict-only clause, the `+1` and the padding quantifier order
  admit the planned instance; the `f log f` arithmetic from the probe gives the book form.
- **Consumers:** the five importers need no edit.
- **No duplication debt.** The received proofs were removed, not kept beside the generic ones.

The auditor did not run Lean. The elaboration, axiom and full-tree results stay maintainer
evidence (at base `cd450a52`, with a source-graph precheck at `c9cc485b`), and the fresh run and
replay at the actual landing tip remain landing obligations.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| m1 | minor | `names.py`'s whole-word screen excluded a preceding dot, so a fully qualified `def Complexity.TimeHierarchy.DiagSimulator := 0` passed | **Fixed.** The lookbehind no longer excludes the dot: a component counts alone or after a dot. Two new negative controls must fail and do: `names-qualified-decl` (that declaration) and `names-qualified-ref` (`@Complexity.TimeHierarchy.SelfSimulator.normalForm` in a proof). The old screen passes both (defect reproduced). `run.sh` now screens the base **and** the tip's whole tree (`git archive` of the tip; the tip's `Diagonal.lean` must equal the base's). Both pass: 723 files each, 0 occurrences, at `cd450a52` and `ff4cab18`. It runs again at the landing tip |
| m2 | minor | `copy-text-screen.py` (v1) skipped every pair with the same `(basename, short name)`, so the generic `DiagSimulator.time_hierarchy_of_pos` was never compared with a restored received `Complexity.time_hierarchy_of_pos` | **Fixed by the retrofit screen v3** (`audits/evidence/retrofit/copy-text-screen-v3.py`, SHA-256 `f4feac91…f181`). It identifies a declaration by path and source position and skips only the same declaration. A short name repeated in a file is labelled by its namespace-qualified name, with `#k` if still repeated. Where no file repeats a screened short name, the output is byte-identical to v2's. The auditor's mutation is the negative control `screen-restore`, and it fails as required. On the mutated tree v2 still reports 16 pairs (3,277 characters); v3 reports 18 (3,667), the new pair both ways: `DiagSimulator.time_hierarchy_of_pos` reproduces `Complexity.time_hierarchy_of_pos` at 86%, and the reverse at 83%. The control also checks that this exact pair is the one reported. Baseline, target and delta are regenerated with v3: before 16, after 16, new 0, gone 0; the pair lists equal the gate's v1 logs. Retrofit-wide: `audits/evidence/screenfix/v3/` |

**Negative controls: 9, all PASS** (`logs/negative-controls.log`), the six of the gate plus
`names-qualified-decl`, `names-qualified-ref` and `screen-restore`. `run.sh` requires all nine.

**What was re-run for this commit** (`scripts/closing-repair.sh`, read-only on the repository): the
names step on base and tip, the nine negative controls (one Lean elaboration, the cut control,
against `oleans-ltip3`), and the v3 screens with their delta. The other checks are unchanged
from the gate's run, and so are their logs and `logs/summary.log`. **`run.sh` runs in full, fresh,
at the landing tip**, with that tip's snapshot as its new third argument.

The bundle manifest named `BUNDLE-FILES.txt`, which was not in the bundle (the auditor checked the
section inventory directly). It is now committed with the evidence, so `SHA256SUMS` verifies.

## Rulings on the pack's questions (all as proposed)

1. **Field `W`:** kept (it follows `clockTM K W`).
2. **`diag_cost_le`:** kept, as the authorization requires. Any later retirement would be a
   separate compatibility decision.
3. **Verdict-only `SelfSimulator.simulates`:** kept. U2-U's full-output clause implies it, and it
   does not introduce the declined verdict-only universal row.
4. **The facade sentence:** unchanged in Part 1, because it is still true. It changes in the
   end-of-chain PR that lands `time_hierarchy_book`.

## Suggestions recorded for later (not gate conditions)

- **Compiled sanity checks:** `¬ Nonempty (DiagSimulator (fun _ _ => 0))`,
  `¬ Nonempty (SelfSimulator (fun _ => 0))`, no `SelfSimulator` with a constant `decode`, and
  machine-projection identities for `DiagSimulator.mono` and `SelfSimulator.toDiagSimulator`
  (`rfl`). These go to the end-of-chain PR, or to a small follow-up if wanted sooner
  (`backlog.md` RD-5).
- **`hΦ`:** sufficient but not minimal. Kept, as recommended.

## Landing

One PR applies `patches/Diagonal.patch` to `TCSlib/Complexity/TimeHierarchy/Diagonal.lean`. The
replay is the 11-module downstream closure (`replay-order.txt`, root excluded). Before the PR, the
full `run.sh` runs at the landing tip. MIG-1 S (open now) lands first. Diagonal then lands on the
post-S tip: `tipcheck.py`'s conditions, the name screen on that tip's tree, and the cut checks
against the S replay's snapshot.

## ===== campaign/gates/113-thm31-book/evidence/freeze/declfreeze-Diagonal.txt =====

public before/after: 24 40 private before/after: 0 1
public added: ['Complexity.TimeHierarchy.code₂', 'Complexity.TimeHierarchy.code₂_eq', 'Complexity.TimeHierarchy.le_logDiagOverhead', 'Complexity.TimeHierarchy.logDiagOverhead', 'Complexity.TimeHierarchy.logDiagOverhead_eq', 'Complexity.TimeHierarchy.logDiagOverhead_le_book', 'Complexity.TimeHierarchy.logOverhead', 'Complexity.TimeHierarchy.logOverhead_add_le', 'Complexity.TimeHierarchy.logOverhead_eq', 'Complexity.TimeHierarchy.logOverhead_mul_le', 'Complexity.TimeHierarchy.twoTapeSelfSimulator', 'Complexity.TimeHierarchy.twoTapeSelfSimulator_W', 'Complexity.TimeHierarchy.twoTapeSelfSimulator_decode', 'Complexity.time_hierarchy_book', 'Complexity.time_hierarchy_book_of_pos', 'Complexity.time_hierarchy_log']
public removed: []
private removed: []
private added: ['Complexity.TimeHierarchy.eventually_logDiagOverhead_le']
private changed: []

## ===== campaign/gates/113-thm31-book/evidence/freeze/declfreeze-TimeHierarchy.txt =====

public before/after: 0 0 private before/after: 0 0
public added: []
public removed: []
private removed: []
private added: []
private changed: []

## ===== campaign/gates/113-thm31-book/evidence/lint/campaign-TimeHierarchy-base.txt =====

WARN  TCSlib/Complexity/TimeHierarchy/ClockLoop.lean     2 public def(s) without a lemma beside them (check 8): ctrBound, loopAnswer
WARN  TCSlib/Complexity/TimeHierarchy/ClockMachine.lean  3 public def(s) without a lemma beside them (check 8): OutReg.push, clockTr, ctrIdx
WARN  TCSlib/Complexity/TimeHierarchy/CodePrefix.lean    1 public def(s) without a lemma beside them (check 8): preTr
WARN  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      5 public def(s) without a lemma beside them (check 8): SelfSimulator.toDiagSimulator, code, diagSim, mono, oneTapeSelfSimulator
INFO  TCSlib/Complexity/TimeHierarchy/ClockLoop.lean     369 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/ClockMachine.lean  539 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/CodePrefix.lean    280 lines; 7 public / 3 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      536 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Separation.lean    183 lines; 6 public / 3 private declarations

style_lint: 0 FAIL, 4 WARN over 5 files

## ===== campaign/gates/113-thm31-book/evidence/lint/campaign-TimeHierarchy-head.txt =====

WARN  TCSlib/Complexity/TimeHierarchy/ClockLoop.lean     2 public def(s) without a lemma beside them (check 8): ctrBound, loopAnswer
WARN  TCSlib/Complexity/TimeHierarchy/ClockMachine.lean  3 public def(s) without a lemma beside them (check 8): OutReg.push, clockTr, ctrIdx
WARN  TCSlib/Complexity/TimeHierarchy/CodePrefix.lean    1 public def(s) without a lemma beside them (check 8): preTr
WARN  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      6 public def(s) without a lemma beside them (check 8): SelfSimulator.toDiagSimulator, code, code, diagSim, mono, oneTapeSelfSimulator
INFO  TCSlib/Complexity/TimeHierarchy/ClockLoop.lean     369 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/ClockMachine.lean  539 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/CodePrefix.lean    280 lines; 7 public / 3 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      807 lines > target 600
INFO  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      807 lines; 40 public / 1 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Separation.lean    183 lines; 6 public / 3 private declarations

style_lint: 0 FAIL, 4 WARN over 5 files

## ===== campaign/gates/113-thm31-book/evidence/lint/policy-base.txt =====


3 findings in 2 files

TCSlib/Complexity/TimeHierarchy.lean: missing `set_option maxHeartbeats 0`
TCSlib/Complexity/TimeHierarchy.lean: missing `set_option relaxedAutoImplicit false`
TCSlib/Complexity/TimeHierarchy.lean: missing `set_option autoImplicit false`

## ===== campaign/gates/113-thm31-book/evidence/lint/policy-head.txt =====


3 findings in 2 files

TCSlib/Complexity/TimeHierarchy.lean: missing `set_option maxHeartbeats 0`
TCSlib/Complexity/TimeHierarchy.lean: missing `set_option relaxedAutoImplicit false`
TCSlib/Complexity/TimeHierarchy.lean: missing `set_option autoImplicit false`

## ===== campaign/gates/113-thm31-book/evidence/merged-tree/down-lt32.txt =====

TCSlib/Complexity/TimeHierarchy/Diagonal
TCSlib/Complexity/TimeHierarchy/Separation
TCSlib/Complexity/CircuitComplexity/Meyer
TCSlib/Complexity/CircuitComplexity
TCSlib/Complexity/Diagonalization/EXPCOM
TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/Relativization
TCSlib/Complexity/Diagonalization
TCSlib/Complexity/Randomized/QuasiPolyHierarchy
TCSlib/Complexity/Randomized/BPPEqP
TCSlib/Complexity/Randomized
TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity
TCSlib/Complexity/TimeHierarchy

## ===== campaign/gates/113-thm31-book/evidence/merged-tree/replay-lt32-static.txt =====

modules 14, mismatches 0, static total 2

## ===== campaign/gates/113-thm31-book/evidence/merged-tree/replay-lt32.log =====

# replay-lt32 at 05050b3d: #223, the book-form time hierarchy, on the campaign after #218/#219 (14 modules), fresh .oleans into oleans-lt32
TCSlib/Complexity/TimeHierarchy/Diagonal exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/Separation exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer exit=0 errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/EXPCOM exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/NotTimeConstructible exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization/Relativization exit=0 errors=0 sorry=0
TCSlib/Complexity/Diagonalization exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/QuasiPolyHierarchy exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPEqP exit=0 errors=0 sorry=0
TCSlib/Complexity/Randomized exit=0 errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Hierarchy exit=0 errors=0 sorry=2
TCSlib/Complexity/SpaceComplexity exit=0 errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy exit=0 errors=0 sorry=0
# modules=14 failed=0

## ===== campaign/gates/113-thm31-book/evidence/merged-tree/replay-lt32.sh =====

#!/usr/bin/env bash
# Replay lt32 (#223, the book-form time hierarchy, on the campaign after #218/#219; branch lean/thm31-book, stacked on the campaign after #218, #219 (oleans-lcamp6)): its downstream closure (14 modules),
# fresh .oleans into oleans-lt32, a copy of oleans-lcamp6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-t31"
LIST="/home/user/tcslib-scratch/fills/replay/down-lt32.txt"
LOG="$S/fills/replay/replay-lt32.log"
PINS="TCSlib/Complexity/TimeHierarchy.lean:50904f92525c9220f4bf7fc19a972b6e645a6db5
TCSlib/Complexity/TimeHierarchy/Diagonal.lean:654b1c51bc47e340cb1295d77edbb1ffc1c546d8"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/thm31-book 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 7a66896024c86de6399955a399faf501e04ac2f1 HEAD || { echo "precheck: the head must contain the campaign after #218, #219 (oleans-lcamp6); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 7a66896024c86de6399955a399faf501e04ac2f1 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #218, #219 (oleans-lcamp6) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp6.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "14" ] || { echo "precheck: the replay list must have 14 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lt32" ] && { echo "precheck: $S/oleans-lt32 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp6" ] || { echo "precheck: oleans-lcamp6 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp6" "$S/oleans-lt32" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lt32 at $(git rev-parse --short HEAD): #223, the book-form time hierarchy, on the campaign after #218/#219 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lt32"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lt32 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=14 failed=0" || { echo "replay: a module failed, or the count is not 14" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/113-thm31-book/evidence/probes/axioms.lean.txt =====

import TCSlib.Complexity.TimeHierarchy.Diagonal

#print axioms Complexity.time_hierarchy_log
#print axioms Complexity.time_hierarchy_book
#print axioms Complexity.time_hierarchy_book_of_pos
#print axioms Complexity.TimeHierarchy.twoTapeSelfSimulator
#print axioms Turing.FinTM.two_work_tapes_run

## ===== campaign/gates/113-thm31-book/evidence/probes/axioms.out =====

'Complexity.time_hierarchy_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.time_hierarchy_book' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.time_hierarchy_book_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TimeHierarchy.twoTapeSelfSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.two_work_tapes_run' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== campaign/gates/113-thm31-book/evidence/probes/sanity.lean.txt =====

import TCSlib.Complexity.TimeHierarchy.Separation
import TCSlib.Complexity.ClassP.Examples

/-! Gate 24's carried sanity checks (`resolutions.md`, "Suggestions recorded for later"), as
`example`s against the head `Diagonal.lean`, plus the projections of the new instance. -/

set_option autoImplicit false

open Turing Turing.FinTM Complexity Complexity.TimeHierarchy

/-- 1. No diagonal simulator has zero overhead: `PAL ∈ DTIME (n + 1)` forces a completed
verdict within `A · 0 = 0` steps, against `not_computesInTime_zero`. -/
example : ¬ Nonempty (DiagSimulator (fun _ _ => 0)) := by
  rintro ⟨S⟩
  obtain ⟨A, N₀, hA⟩ := S.simulates _ _ PAL_mem_DTIME_linear
  obtain ⟨x, -, hx⟩ := hA N₀ le_rfl
  exact not_computesInTime_zero S.W x _ (hx.mono (by simp))

/-- 2. No self-simulator has zero normal-form overhead: padded, it would be a diagonal
simulator of overhead `n + 1`, whose diagonal language at `g = 2ⁿ` lies in `DTIME (2ⁿ + 1)`
(`diagLangOf_mem_DTIME`) and, as `A (n + 1) ≤ 2ⁿ` eventually, not in it
(`DiagSimulator.diagLang_not_mem_DTIME`). -/
example : ¬ Nonempty (SelfSimulator (fun _ => 0)) := by
  rintro ⟨S⟩
  have hin := diagLangOf_mem_DTIME S.toDiagSimulator.W timeConstructible_two_pow
  refine S.toDiagSimulator.diagLang_not_mem_DTIME (g := fun n => 2 ^ n)
    (T := fun n => 2 ^ n + 1) ?_ hin
  intro A N
  obtain ⟨M, hM⟩ := eventually_poly_le_two_pow A 1
  exact ⟨max N M, le_max_left _ _, by simpa using hM (max N M) (le_max_right _ _)⟩

/-- 3. No self-simulator has a constant `decode`: one machine would decide both `PAL` and a
language `L ∈ DTIME (2ⁿ) \ DTIME (n + 1)` (`dtime_poly_ssubset_dtime_two_pow 1`), so `L = PAL`
by output uniqueness, and then `L ∈ DTIME (n + 1)`. -/
example {Ψ : ℕ → ℕ} (S : SelfSimulator Ψ) (M : FinTM Bool) : ¬ ∀ α, S.decode α = M := by
  intro hM
  obtain ⟨L, hL, hLn⟩ := Set.exists_of_ssubset (dtime_poly_ssubset_dtime_two_pow 1)
  have hP : PAL ∈ DTIME (fun n => n ^ 1 + 1) := by simpa using PAL_mem_DTIME_linear
  obtain ⟨α₁, c₁, h₁⟩ := S.normalForm _ _ hP
  obtain ⟨α₂, c₂, h₂⟩ := S.normalForm _ _ hL
  apply hLn
  have hEq : L = PAL := by
    ext x
    have e₁ := h₁ x
    rw [hM α₁] at e₁
    have e₂ := h₂ x
    rw [hM α₂] at e₂
    have e := e₁.output_unique e₂
    simp only [List.cons.injEq, and_true] at e
    by_cases hx : x ∈ L <;> by_cases hy : x ∈ PAL <;> simp_all [MultiTapeTM.indicator]
  rw [hEq]; exact hP

/-- 4. The machine projections of `DiagSimulator.mono` and `SelfSimulator.toDiagSimulator`. -/
example {Φ Φ' : ℕ → ℕ → ℕ} (S : DiagSimulator Φ) (K : ℕ) (h : ∀ t n, Φ t n ≤ K * Φ' t n) :
    (S.mono K h).W = S.W := rfl

example {Ψ : ℕ → ℕ} (S : SelfSimulator Ψ) : S.toDiagSimulator.W = S.W := rfl

/-- 5. The new instance's projections, and its padded, weakened diagonal simulator's machine. -/
example : twoTapeSelfSimulator.W = Classical.choose (exists_selfUniversalK 2 code₂.toK) :=
  twoTapeSelfSimulator_W

example (α : List Bool) : twoTapeSelfSimulator.decode α = (code₂.decode α).toFinTM :=
  twoTapeSelfSimulator_decode α

example : (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).W =
    twoTapeSelfSimulator.W := rfl

-- ===== output: devtools/seyoon/leanelab.sh <wt-t31> <overlay over oleans-lcamp2> Scratch/T31Sanity.lean =====
-- exit=0, no messages (empty output)

## ===== campaign/gates/113-thm31-book/evidence/probes/sanity.out =====



## ===== campaign/gates/113-thm31-book/evidence/probes/seal.lean.txt =====

import TCSlib.Complexity.TimeHierarchy.Diagonal

/-! Rule-10 seal probe for the new section of `Diagonal.lean`: three verbatim copies of it, each
in its own namespace, under `attribute [local irreducible]` on other-file definitions. A: all of
them; B: all but `DTIME`; C: all but `DTIME` and `DecidesInTime`. Each section opens with `rfl`
controls (`fail_if_success`), which pass only while the seal is active. -/

set_option maxHeartbeats 0
set_option autoImplicit false

section SealA
attribute [local irreducible] Complexity.DTIME Turing.FinTM.DecidesInTime Complexity.TimeConstructible Turing.FinTM.ComputesInTime Turing.FinTM.ComputesFunInTime Turing.EffectiveCodeK.toFinTM Turing.EffectiveMachineCode2.toK Turing.Code2TM.toFinTM Turing.MultiTapeTM.indicator Complexity.TimeHierarchy.SelfSimulator.toDiagSimulator Complexity.TimeHierarchy.DiagSimulator.mono

open Turing Turing.FinTM Complexity Complexity.TimeHierarchy in
example (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := by
  fail_if_success rfl
  exact EffectiveMachineCode2.toK_toFinTM c α
open Turing Complexity in
example (L : Language Bool) (T : ℕ → ℕ) (h : L ∈ DTIME T) : True := by
  fail_if_success obtain ⟨c, M, hM⟩ := h
  trivial

/-! ### The book form: overhead `f log f` -/

namespace Complexity.TimeHierarchy.T31SealA

open Turing Turing.FinTM

/-- **The Hennie–Stearns normal-form overhead** [AB09, §1.7]:
`logOverhead t = (t + 1)(log₂(t + 1) + 1)`, the time bound of
`Turing.FinTM.two_work_tapes_binary` at a budget `t`, with `log₂` the floor logarithm
`Nat.log 2`. -/
def logOverhead (t : ℕ) : ℕ := (t + 1) * (Nat.log 2 (t + 1) + 1)

/-- The formula of `logOverhead`: `logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1)`, by
definition. -/
theorem logOverhead_eq (t : ℕ) : logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1) := rfl

/-- **The diagonal overhead of the book form** [AB09, Theorem 3.1, proof]:
`logDiagOverhead t n = (t + n + 1)(log₂(t + n + 1) + 1)`, the `f log f` analogue of the
received overhead `(t + n + 1)²`. -/
def logDiagOverhead (t n : ℕ) : ℕ := (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)

/-- The formula of `logDiagOverhead`:
`logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)`, by definition. -/
theorem logDiagOverhead_eq (t n : ℕ) :
    logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) := rfl

/-- The book form's overhead dominates the time [AB09, Theorem 3.1, proof]:
`t ≤ logDiagOverhead t n` for all `t` and `n`. -/
theorem le_logDiagOverhead (t n : ℕ) : t ≤ logDiagOverhead t n := by
  rw [logDiagOverhead_eq]
  have h : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Input padding at the book form's overhead** [AB09, Theorem 3.1, proof]:
`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, the bound that turns the padded overhead of
`SelfSimulator.toDiagSimulator` at `logOverhead` into `logDiagOverhead`.

**Proof sketch.** `log₂` is monotone and `t + 1 ≤ t + n + 1`, so
`logOverhead t ≤ logDiagOverhead t n`; and `n + 1 ≤ t + n + 1 ≤ logDiagOverhead t n`. -/
theorem logOverhead_add_le (t n : ℕ) : logOverhead t + n + 1 ≤ 2 * logDiagOverhead t n := by
  rw [logOverhead_eq, logDiagOverhead_eq]
  have hlog : Nat.log 2 (t + 1) ≤ Nat.log 2 (t + n + 1) := Nat.log_mono_right (by omega)
  have h1 : (t + 1) * (Nat.log 2 (t + 1) + 1) ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Constant-factor absorption** of the Hennie–Stearns overhead [AB09, §1.7]:
`logOverhead (c₀ T) ≤ (c₀ + 1)(log₂(c₀ + 1) + 2) · logOverhead T`, so a decider within `c₀ T`
normal-forms within a constant multiple of `logOverhead T`.

**Proof sketch.** Let `m = log₂(c₀ + 1) + 1`, so `c₀ + 1 < 2^m`, and `T + 1 < 2^(log₂(T + 1) + 1)`.
Then `c₀ T + 1 ≤ (c₀ + 1)(T + 1) < 2^(m + log₂(T + 1) + 1)`, so
`log₂(c₀ T + 1) ≤ log₂(T + 1) + m` and `log₂(c₀ T + 1) + 1 ≤ (m + 1)(log₂(T + 1) + 1)`;
multiply by `c₀ T + 1 ≤ (c₀ + 1)(T + 1)`. -/
theorem logOverhead_mul_le (c₀ T : ℕ) :
    logOverhead (c₀ * T) ≤ (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead T := by
  rw [logOverhead_eq, logOverhead_eq]
  set m := Nat.log 2 (c₀ + 1) + 1 with hm
  set l := Nat.log 2 (T + 1) with hl
  have hc : c₀ + 1 < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) _
  have hT : T + 1 < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1 : c₀ * T + 1 ≤ (c₀ + 1) * (T + 1) := by nlinarith
  have h2 : (c₀ + 1) * (T + 1) < 2 ^ m * 2 ^ (l + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hc hT
  have hlog : Nat.log 2 (c₀ * T + 1) < m + (l + 1) := by
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_add]
    omega
  have h3 : Nat.log 2 (c₀ * T + 1) + 1 ≤ (m + 1) * (l + 1) := by nlinarith
  calc (c₀ * T + 1) * (Nat.log 2 (c₀ * T + 1) + 1)
      ≤ ((c₀ + 1) * (T + 1)) * ((m + 1) * (l + 1)) := Nat.mul_le_mul h1 h3
    _ = (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * ((T + 1) * (l + 1)) := by rw [hm]; ring

/-- **The arithmetic of the book form** [AB09, Theorem 3.1]: for `2 ≤ n ≤ f`,
`logDiagOverhead f n ≤ 12 · f · log₂ f`.

**Proof sketch.** `f ≥ 2`, so `log₂ f ≥ 1`. From `n ≤ f`: `f + n + 1 ≤ 3f`, and
`f + n + 1 ≤ 4f`, so `log₂(f + n + 1) ≤ log₂(4f) = log₂ f + 2` and
`log₂(f + n + 1) + 1 ≤ log₂ f + 3 ≤ 4 log₂ f`. Multiply: at most `3f · 4 log₂ f`. -/
theorem logDiagOverhead_le_book {f n : ℕ} (hn : 2 ≤ n) (hf : n ≤ f) :
    logDiagOverhead f n ≤ 12 * (f * Nat.log 2 f) := by
  rw [logDiagOverhead_eq]
  have hf2 : 2 ≤ f := le_trans hn hf
  have hlog1 : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by norm_num) (by simpa using hf2)
  have h3 : f + n + 1 ≤ f * 2 * 2 := by omega
  have hlog : Nat.log 2 (f + n + 1) ≤ Nat.log 2 f + 2 := by
    calc Nat.log 2 (f + n + 1) ≤ Nat.log 2 (f * 2 * 2) := Nat.log_mono_right h3
      _ = Nat.log 2 f + 2 := by
        rw [Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hA : f + n + 1 ≤ 3 * f := by omega
  have hB : Nat.log 2 (f + n + 1) + 1 ≤ 4 * Nat.log 2 f := by omega
  calc (f + n + 1) * (Nat.log 2 (f + n + 1) + 1) ≤ (3 * f) * (4 * Nat.log 2 f) :=
        Nat.mul_le_mul hA hB
    _ = 12 * (f * Nat.log 2 f) := by ring

/-- The book form's hypothesis gives the diagonal one: if `n ≤ f n` and, for every `A`,
eventually `A · f n log₂ f n ≤ g n`, then for every `A`, eventually
`A · logDiagOverhead (f n) n ≤ g n` (`logDiagOverhead_le_book` at the constant `12 A`, for
`n ≥ 2`). -/
private theorem eventually_logDiagOverhead_le {f g : ℕ → ℕ} (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logDiagOverhead (f n) n ≤ g n := by
  intro A
  obtain ⟨N, hN⟩ := hfg (12 * A)
  refine ⟨max N 2, fun n hn => ?_⟩
  calc A * logDiagOverhead (f n) n ≤ A * (12 * (f n * Nat.log 2 (f n))) :=
        Nat.mul_le_mul_left A (logDiagOverhead_le_book (le_of_max_le_right hn) (hf n))
    _ = 12 * A * (f n * Nat.log 2 (f n)) := by ring
    _ ≤ g n := hN n (le_of_max_le_left hn)

/-- **The fixed two-work-tape representation scheme** of the book form [AB09, §1.4] (any
scheme works; `Turing.exists_effectiveMachineCode2` provides one). -/
noncomputable def code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2

/-- The definition of `code₂`: `code₂ = Classical.choice Turing.exists_effectiveMachineCode2`. -/
theorem code₂_eq : code₂ = Classical.choice exists_effectiveMachineCode2 := rfl

/-- **The two-tape self-simulator** [AB09, Theorem 3.1, proof; §1.4.1 and §1.7]: the
self-application universal machine for the two-work-tape codes of `code₂`
(`Turing.exists_selfUniversalK` at `k = 2`; `decode α` the machine `code₂.decode α`), with the
Hennie–Stearns normal form, whose overhead is `logOverhead`.

**Proof sketch.** *Simulation:* for each code `α`, `Turing.exists_selfUniversalK` gives a
constant `C` such that whenever the machine coded by `α` (the same bundled machine in the
`k`-tape view, `Turing.EffectiveMachineCode2.toK_toFinTM`) halts on `pairEncode α w` with `[b]`
within `t` steps, the universal machine does so within
`C (t + 1) ≤ C (t + |pairEncode α w| + 1)` steps. *Normal form:* a decider within `c₀ T`
becomes a two-work-tape binary machine within `c₁ · logOverhead (c₀ T)`
(`Turing.FinTM.two_work_tapes_binary`), then a coded machine `N` with the same runs
(`Turing.exists_code2TM`), whose code `code₂.encode N` decodes back to `N`; and
`c₁ · logOverhead (c₀ T) ≤ c₁ (c₀ + 1)(log₂(c₀ + 1) + 2) (logOverhead T + 1)`
(`logOverhead_mul_le`). -/
noncomputable def twoTapeSelfSimulator : SelfSimulator logOverhead where
  W := Classical.choose (exists_selfUniversalK 2 code₂.toK)
  decode α := (code₂.decode α).toFinTM
  simulates α := by
    obtain ⟨C, -, hC⟩ := Classical.choose_spec (exists_selfUniversalK 2 code₂.toK) α
    refine ⟨C, fun w b t h => ?_⟩
    have h' : (code₂.toK.toFinTM α).ComputesInTime (pairEncode α w) [b] t := by
      rw [EffectiveMachineCode2.toK_toFinTM]; exact h
    exact ((hC w).1 [b] t h').1.mono (Nat.mul_le_mul_left C (by omega))
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := two_work_tapes_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n)
      ((computesFunInTime_iff _ _ _).2 hM)
    obtain ⟨N, hN⟩ := exists_code2TM M₁ hk
    refine ⟨code₂.encode N, c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)), fun x => ?_⟩
    dsimp only
    rw [code₂.toMachineCode2.decode_encode N]
    apply ((hN x _ _).2 ((computesFunInTime_iff _ _ _).1 h₁ x)).mono
    calc c₁ * ((c₀ * T x.length + 1) * (Nat.log 2 (c₀ * T x.length + 1) + 1))
        = c₁ * logOverhead (c₀ * T x.length) := by rw [logOverhead_eq]
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead (T x.length)) :=
          Nat.mul_le_mul_left c₁ (logOverhead_mul_le c₀ _)
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)) * (logOverhead (T x.length) + 1) := by
          rw [Nat.mul_assoc c₁]
          exact Nat.mul_le_mul_left c₁ (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- The two-tape self-simulator's machine is the self-application universal machine of
`code₂` at `k = 2`, by definition. -/
theorem twoTapeSelfSimulator_W :
    twoTapeSelfSimulator.W = Classical.choose (exists_selfUniversalK 2 code₂.toK) := rfl

/-- The two-tape self-simulator's code `α` denotes the machine `code₂.decode α`, by
definition. -/
theorem twoTapeSelfSimulator_decode (α : List Bool) :
    twoTapeSelfSimulator.decode α = (code₂.decode α).toFinTM := rfl

end Complexity.TimeHierarchy.T31SealA

namespace Complexity.TimeHierarchy.T31SealA

open TimeHierarchy

/-- **The Time Hierarchy Theorem at overhead `f log f`** [AB09, Theorem 3.1], with the input
length kept: if `g` is time constructible and
`(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))` — i.e. for every constant `A`, eventually
`A · (f n + n + 1)(log₂(f n + n + 1) + 1) ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`. No
hypothesis on `f` is needed; `Complexity.time_hierarchy_book` is the book's form.

**Proof sketch.** The case `Φ = logDiagOverhead` of `DiagSimulator.time_hierarchy`, at the
two-tape self-simulator `twoTapeSelfSimulator` padded by `SelfSimulator.toDiagSimulator`
(overhead `logOverhead t + n + 1`) and weakened by `DiagSimulator.mono`
(`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, `logOverhead_add_le`), with
`t ≤ logDiagOverhead t n` (`le_logDiagOverhead`). *Inclusion:* `f n ≤ g n` eventually, the
smaller lengths absorbed into the constant. *Strictness:* the diagonal language of the
two-tape universal machine lies in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in
`DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`). -/
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg fun A => (hfg A).imp fun _ hN n hn => by
      rw [logDiagOverhead_eq]; exact hN n hn

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the book's form: if `g` is time
constructible, `n ≤ f(n)` for all `n`, and `f(n) log₂ f(n) = o(g(n))` — i.e. for every
constant `A`, eventually `A · f n · log₂ f n ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): `n ≤ f(n)` in place of time
constructibility of `f` (every time-constructible `f` satisfies it); `log₂` is the floor
logarithm `Nat.log 2`, which vanishes at `f n ≤ 1`, hence only at `n ≤ 1` here, outside the
eventual hypothesis; and the larger class is `DTIME (g + 1)`, which differs from `DTIME g` only
in the degenerate case `g 0 = 0` (`Complexity.time_hierarchy_book_of_pos`).

**Proof sketch.** For `n ≥ 2`, `n ≤ f n` gives
`(f n + n + 1)(log₂(f n + n + 1) + 1) ≤ 12 · f n · log₂ f n` (`logDiagOverhead_le_book`), so
the hypothesis at `12 A` gives `A · logDiagOverhead (f n) n ≤ g n` eventually; conclude as in
`Complexity.time_hierarchy_log`, by `DiagSimulator.time_hierarchy` at the two-tape
self-simulator `twoTapeSelfSimulator`. -/
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg (eventually_logDiagOverhead_le hf hfg)

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1], in the book's
form: as `Complexity.time_hierarchy_book`, with the larger class exactly `DTIME g` when `g`
never vanishes — the book's `DTIME(f) ⊊ DTIME(g)`.

**Proof sketch.** As `Complexity.time_hierarchy_book`, through
`DiagSimulator.time_hierarchy_of_pos` in place of `DiagSimulator.time_hierarchy`:
`c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) = DTIME g`. -/
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy_of_pos
    le_logDiagOverhead hg hpos (eventually_logDiagOverhead_le hf hfg)

end Complexity.TimeHierarchy.T31SealA

end SealA

section SealB
attribute [local irreducible] Turing.FinTM.DecidesInTime Complexity.TimeConstructible Turing.FinTM.ComputesInTime Turing.FinTM.ComputesFunInTime Turing.EffectiveCodeK.toFinTM Turing.EffectiveMachineCode2.toK Turing.Code2TM.toFinTM Turing.MultiTapeTM.indicator Complexity.TimeHierarchy.SelfSimulator.toDiagSimulator Complexity.TimeHierarchy.DiagSimulator.mono

open Turing Turing.FinTM Complexity Complexity.TimeHierarchy in
example (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := by
  fail_if_success rfl
  exact EffectiveMachineCode2.toK_toFinTM c α

/-! ### The book form: overhead `f log f` -/

namespace Complexity.TimeHierarchy.T31SealB

open Turing Turing.FinTM

/-- **The Hennie–Stearns normal-form overhead** [AB09, §1.7]:
`logOverhead t = (t + 1)(log₂(t + 1) + 1)`, the time bound of
`Turing.FinTM.two_work_tapes_binary` at a budget `t`, with `log₂` the floor logarithm
`Nat.log 2`. -/
def logOverhead (t : ℕ) : ℕ := (t + 1) * (Nat.log 2 (t + 1) + 1)

/-- The formula of `logOverhead`: `logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1)`, by
definition. -/
theorem logOverhead_eq (t : ℕ) : logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1) := rfl

/-- **The diagonal overhead of the book form** [AB09, Theorem 3.1, proof]:
`logDiagOverhead t n = (t + n + 1)(log₂(t + n + 1) + 1)`, the `f log f` analogue of the
received overhead `(t + n + 1)²`. -/
def logDiagOverhead (t n : ℕ) : ℕ := (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)

/-- The formula of `logDiagOverhead`:
`logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)`, by definition. -/
theorem logDiagOverhead_eq (t n : ℕ) :
    logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) := rfl

/-- The book form's overhead dominates the time [AB09, Theorem 3.1, proof]:
`t ≤ logDiagOverhead t n` for all `t` and `n`. -/
theorem le_logDiagOverhead (t n : ℕ) : t ≤ logDiagOverhead t n := by
  rw [logDiagOverhead_eq]
  have h : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Input padding at the book form's overhead** [AB09, Theorem 3.1, proof]:
`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, the bound that turns the padded overhead of
`SelfSimulator.toDiagSimulator` at `logOverhead` into `logDiagOverhead`.

**Proof sketch.** `log₂` is monotone and `t + 1 ≤ t + n + 1`, so
`logOverhead t ≤ logDiagOverhead t n`; and `n + 1 ≤ t + n + 1 ≤ logDiagOverhead t n`. -/
theorem logOverhead_add_le (t n : ℕ) : logOverhead t + n + 1 ≤ 2 * logDiagOverhead t n := by
  rw [logOverhead_eq, logDiagOverhead_eq]
  have hlog : Nat.log 2 (t + 1) ≤ Nat.log 2 (t + n + 1) := Nat.log_mono_right (by omega)
  have h1 : (t + 1) * (Nat.log 2 (t + 1) + 1) ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Constant-factor absorption** of the Hennie–Stearns overhead [AB09, §1.7]:
`logOverhead (c₀ T) ≤ (c₀ + 1)(log₂(c₀ + 1) + 2) · logOverhead T`, so a decider within `c₀ T`
normal-forms within a constant multiple of `logOverhead T`.

**Proof sketch.** Let `m = log₂(c₀ + 1) + 1`, so `c₀ + 1 < 2^m`, and `T + 1 < 2^(log₂(T + 1) + 1)`.
Then `c₀ T + 1 ≤ (c₀ + 1)(T + 1) < 2^(m + log₂(T + 1) + 1)`, so
`log₂(c₀ T + 1) ≤ log₂(T + 1) + m` and `log₂(c₀ T + 1) + 1 ≤ (m + 1)(log₂(T + 1) + 1)`;
multiply by `c₀ T + 1 ≤ (c₀ + 1)(T + 1)`. -/
theorem logOverhead_mul_le (c₀ T : ℕ) :
    logOverhead (c₀ * T) ≤ (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead T := by
  rw [logOverhead_eq, logOverhead_eq]
  set m := Nat.log 2 (c₀ + 1) + 1 with hm
  set l := Nat.log 2 (T + 1) with hl
  have hc : c₀ + 1 < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) _
  have hT : T + 1 < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1 : c₀ * T + 1 ≤ (c₀ + 1) * (T + 1) := by nlinarith
  have h2 : (c₀ + 1) * (T + 1) < 2 ^ m * 2 ^ (l + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hc hT
  have hlog : Nat.log 2 (c₀ * T + 1) < m + (l + 1) := by
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_add]
    omega
  have h3 : Nat.log 2 (c₀ * T + 1) + 1 ≤ (m + 1) * (l + 1) := by nlinarith
  calc (c₀ * T + 1) * (Nat.log 2 (c₀ * T + 1) + 1)
      ≤ ((c₀ + 1) * (T + 1)) * ((m + 1) * (l + 1)) := Nat.mul_le_mul h1 h3
    _ = (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * ((T + 1) * (l + 1)) := by rw [hm]; ring

/-- **The arithmetic of the book form** [AB09, Theorem 3.1]: for `2 ≤ n ≤ f`,
`logDiagOverhead f n ≤ 12 · f · log₂ f`.

**Proof sketch.** `f ≥ 2`, so `log₂ f ≥ 1`. From `n ≤ f`: `f + n + 1 ≤ 3f`, and
`f + n + 1 ≤ 4f`, so `log₂(f + n + 1) ≤ log₂(4f) = log₂ f + 2` and
`log₂(f + n + 1) + 1 ≤ log₂ f + 3 ≤ 4 log₂ f`. Multiply: at most `3f · 4 log₂ f`. -/
theorem logDiagOverhead_le_book {f n : ℕ} (hn : 2 ≤ n) (hf : n ≤ f) :
    logDiagOverhead f n ≤ 12 * (f * Nat.log 2 f) := by
  rw [logDiagOverhead_eq]
  have hf2 : 2 ≤ f := le_trans hn hf
  have hlog1 : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by norm_num) (by simpa using hf2)
  have h3 : f + n + 1 ≤ f * 2 * 2 := by omega
  have hlog : Nat.log 2 (f + n + 1) ≤ Nat.log 2 f + 2 := by
    calc Nat.log 2 (f + n + 1) ≤ Nat.log 2 (f * 2 * 2) := Nat.log_mono_right h3
      _ = Nat.log 2 f + 2 := by
        rw [Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hA : f + n + 1 ≤ 3 * f := by omega
  have hB : Nat.log 2 (f + n + 1) + 1 ≤ 4 * Nat.log 2 f := by omega
  calc (f + n + 1) * (Nat.log 2 (f + n + 1) + 1) ≤ (3 * f) * (4 * Nat.log 2 f) :=
        Nat.mul_le_mul hA hB
    _ = 12 * (f * Nat.log 2 f) := by ring

/-- The book form's hypothesis gives the diagonal one: if `n ≤ f n` and, for every `A`,
eventually `A · f n log₂ f n ≤ g n`, then for every `A`, eventually
`A · logDiagOverhead (f n) n ≤ g n` (`logDiagOverhead_le_book` at the constant `12 A`, for
`n ≥ 2`). -/
private theorem eventually_logDiagOverhead_le {f g : ℕ → ℕ} (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logDiagOverhead (f n) n ≤ g n := by
  intro A
  obtain ⟨N, hN⟩ := hfg (12 * A)
  refine ⟨max N 2, fun n hn => ?_⟩
  calc A * logDiagOverhead (f n) n ≤ A * (12 * (f n * Nat.log 2 (f n))) :=
        Nat.mul_le_mul_left A (logDiagOverhead_le_book (le_of_max_le_right hn) (hf n))
    _ = 12 * A * (f n * Nat.log 2 (f n)) := by ring
    _ ≤ g n := hN n (le_of_max_le_left hn)

/-- **The fixed two-work-tape representation scheme** of the book form [AB09, §1.4] (any
scheme works; `Turing.exists_effectiveMachineCode2` provides one). -/
noncomputable def code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2

/-- The definition of `code₂`: `code₂ = Classical.choice Turing.exists_effectiveMachineCode2`. -/
theorem code₂_eq : code₂ = Classical.choice exists_effectiveMachineCode2 := rfl

/-- **The two-tape self-simulator** [AB09, Theorem 3.1, proof; §1.4.1 and §1.7]: the
self-application universal machine for the two-work-tape codes of `code₂`
(`Turing.exists_selfUniversalK` at `k = 2`; `decode α` the machine `code₂.decode α`), with the
Hennie–Stearns normal form, whose overhead is `logOverhead`.

**Proof sketch.** *Simulation:* for each code `α`, `Turing.exists_selfUniversalK` gives a
constant `C` such that whenever the machine coded by `α` (the same bundled machine in the
`k`-tape view, `Turing.EffectiveMachineCode2.toK_toFinTM`) halts on `pairEncode α w` with `[b]`
within `t` steps, the universal machine does so within
`C (t + 1) ≤ C (t + |pairEncode α w| + 1)` steps. *Normal form:* a decider within `c₀ T`
becomes a two-work-tape binary machine within `c₁ · logOverhead (c₀ T)`
(`Turing.FinTM.two_work_tapes_binary`), then a coded machine `N` with the same runs
(`Turing.exists_code2TM`), whose code `code₂.encode N` decodes back to `N`; and
`c₁ · logOverhead (c₀ T) ≤ c₁ (c₀ + 1)(log₂(c₀ + 1) + 2) (logOverhead T + 1)`
(`logOverhead_mul_le`). -/
noncomputable def twoTapeSelfSimulator : SelfSimulator logOverhead where
  W := Classical.choose (exists_selfUniversalK 2 code₂.toK)
  decode α := (code₂.decode α).toFinTM
  simulates α := by
    obtain ⟨C, -, hC⟩ := Classical.choose_spec (exists_selfUniversalK 2 code₂.toK) α
    refine ⟨C, fun w b t h => ?_⟩
    have h' : (code₂.toK.toFinTM α).ComputesInTime (pairEncode α w) [b] t := by
      rw [EffectiveMachineCode2.toK_toFinTM]; exact h
    exact ((hC w).1 [b] t h').1.mono (Nat.mul_le_mul_left C (by omega))
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := two_work_tapes_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n)
      ((computesFunInTime_iff _ _ _).2 hM)
    obtain ⟨N, hN⟩ := exists_code2TM M₁ hk
    refine ⟨code₂.encode N, c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)), fun x => ?_⟩
    dsimp only
    rw [code₂.toMachineCode2.decode_encode N]
    apply ((hN x _ _).2 ((computesFunInTime_iff _ _ _).1 h₁ x)).mono
    calc c₁ * ((c₀ * T x.length + 1) * (Nat.log 2 (c₀ * T x.length + 1) + 1))
        = c₁ * logOverhead (c₀ * T x.length) := by rw [logOverhead_eq]
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead (T x.length)) :=
          Nat.mul_le_mul_left c₁ (logOverhead_mul_le c₀ _)
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)) * (logOverhead (T x.length) + 1) := by
          rw [Nat.mul_assoc c₁]
          exact Nat.mul_le_mul_left c₁ (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- The two-tape self-simulator's machine is the self-application universal machine of
`code₂` at `k = 2`, by definition. -/
theorem twoTapeSelfSimulator_W :
    twoTapeSelfSimulator.W = Classical.choose (exists_selfUniversalK 2 code₂.toK) := rfl

/-- The two-tape self-simulator's code `α` denotes the machine `code₂.decode α`, by
definition. -/
theorem twoTapeSelfSimulator_decode (α : List Bool) :
    twoTapeSelfSimulator.decode α = (code₂.decode α).toFinTM := rfl

end Complexity.TimeHierarchy.T31SealB

namespace Complexity.TimeHierarchy.T31SealB

open TimeHierarchy

/-- **The Time Hierarchy Theorem at overhead `f log f`** [AB09, Theorem 3.1], with the input
length kept: if `g` is time constructible and
`(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))` — i.e. for every constant `A`, eventually
`A · (f n + n + 1)(log₂(f n + n + 1) + 1) ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`. No
hypothesis on `f` is needed; `Complexity.time_hierarchy_book` is the book's form.

**Proof sketch.** The case `Φ = logDiagOverhead` of `DiagSimulator.time_hierarchy`, at the
two-tape self-simulator `twoTapeSelfSimulator` padded by `SelfSimulator.toDiagSimulator`
(overhead `logOverhead t + n + 1`) and weakened by `DiagSimulator.mono`
(`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, `logOverhead_add_le`), with
`t ≤ logDiagOverhead t n` (`le_logDiagOverhead`). *Inclusion:* `f n ≤ g n` eventually, the
smaller lengths absorbed into the constant. *Strictness:* the diagonal language of the
two-tape universal machine lies in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in
`DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`). -/
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg fun A => (hfg A).imp fun _ hN n hn => by
      rw [logDiagOverhead_eq]; exact hN n hn

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the book's form: if `g` is time
constructible, `n ≤ f(n)` for all `n`, and `f(n) log₂ f(n) = o(g(n))` — i.e. for every
constant `A`, eventually `A · f n · log₂ f n ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): `n ≤ f(n)` in place of time
constructibility of `f` (every time-constructible `f` satisfies it); `log₂` is the floor
logarithm `Nat.log 2`, which vanishes at `f n ≤ 1`, hence only at `n ≤ 1` here, outside the
eventual hypothesis; and the larger class is `DTIME (g + 1)`, which differs from `DTIME g` only
in the degenerate case `g 0 = 0` (`Complexity.time_hierarchy_book_of_pos`).

**Proof sketch.** For `n ≥ 2`, `n ≤ f n` gives
`(f n + n + 1)(log₂(f n + n + 1) + 1) ≤ 12 · f n · log₂ f n` (`logDiagOverhead_le_book`), so
the hypothesis at `12 A` gives `A · logDiagOverhead (f n) n ≤ g n` eventually; conclude as in
`Complexity.time_hierarchy_log`, by `DiagSimulator.time_hierarchy` at the two-tape
self-simulator `twoTapeSelfSimulator`. -/
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg (eventually_logDiagOverhead_le hf hfg)

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1], in the book's
form: as `Complexity.time_hierarchy_book`, with the larger class exactly `DTIME g` when `g`
never vanishes — the book's `DTIME(f) ⊊ DTIME(g)`.

**Proof sketch.** As `Complexity.time_hierarchy_book`, through
`DiagSimulator.time_hierarchy_of_pos` in place of `DiagSimulator.time_hierarchy`:
`c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) = DTIME g`. -/
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy_of_pos
    le_logDiagOverhead hg hpos (eventually_logDiagOverhead_le hf hfg)

end Complexity.TimeHierarchy.T31SealB

end SealB

section SealC
attribute [local irreducible] Complexity.TimeConstructible Turing.FinTM.ComputesInTime Turing.FinTM.ComputesFunInTime Turing.EffectiveCodeK.toFinTM Turing.EffectiveMachineCode2.toK Turing.Code2TM.toFinTM Turing.MultiTapeTM.indicator Complexity.TimeHierarchy.SelfSimulator.toDiagSimulator Complexity.TimeHierarchy.DiagSimulator.mono

open Turing Turing.FinTM Complexity Complexity.TimeHierarchy in
example (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := by
  fail_if_success rfl
  exact EffectiveMachineCode2.toK_toFinTM c α

/-! ### The book form: overhead `f log f` -/

namespace Complexity.TimeHierarchy.T31SealC

open Turing Turing.FinTM

/-- **The Hennie–Stearns normal-form overhead** [AB09, §1.7]:
`logOverhead t = (t + 1)(log₂(t + 1) + 1)`, the time bound of
`Turing.FinTM.two_work_tapes_binary` at a budget `t`, with `log₂` the floor logarithm
`Nat.log 2`. -/
def logOverhead (t : ℕ) : ℕ := (t + 1) * (Nat.log 2 (t + 1) + 1)

/-- The formula of `logOverhead`: `logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1)`, by
definition. -/
theorem logOverhead_eq (t : ℕ) : logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1) := rfl

/-- **The diagonal overhead of the book form** [AB09, Theorem 3.1, proof]:
`logDiagOverhead t n = (t + n + 1)(log₂(t + n + 1) + 1)`, the `f log f` analogue of the
received overhead `(t + n + 1)²`. -/
def logDiagOverhead (t n : ℕ) : ℕ := (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)

/-- The formula of `logDiagOverhead`:
`logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)`, by definition. -/
theorem logDiagOverhead_eq (t n : ℕ) :
    logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) := rfl

/-- The book form's overhead dominates the time [AB09, Theorem 3.1, proof]:
`t ≤ logDiagOverhead t n` for all `t` and `n`. -/
theorem le_logDiagOverhead (t n : ℕ) : t ≤ logDiagOverhead t n := by
  rw [logDiagOverhead_eq]
  have h : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Input padding at the book form's overhead** [AB09, Theorem 3.1, proof]:
`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, the bound that turns the padded overhead of
`SelfSimulator.toDiagSimulator` at `logOverhead` into `logDiagOverhead`.

**Proof sketch.** `log₂` is monotone and `t + 1 ≤ t + n + 1`, so
`logOverhead t ≤ logDiagOverhead t n`; and `n + 1 ≤ t + n + 1 ≤ logDiagOverhead t n`. -/
theorem logOverhead_add_le (t n : ℕ) : logOverhead t + n + 1 ≤ 2 * logDiagOverhead t n := by
  rw [logOverhead_eq, logDiagOverhead_eq]
  have hlog : Nat.log 2 (t + 1) ≤ Nat.log 2 (t + n + 1) := Nat.log_mono_right (by omega)
  have h1 : (t + 1) * (Nat.log 2 (t + 1) + 1) ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Constant-factor absorption** of the Hennie–Stearns overhead [AB09, §1.7]:
`logOverhead (c₀ T) ≤ (c₀ + 1)(log₂(c₀ + 1) + 2) · logOverhead T`, so a decider within `c₀ T`
normal-forms within a constant multiple of `logOverhead T`.

**Proof sketch.** Let `m = log₂(c₀ + 1) + 1`, so `c₀ + 1 < 2^m`, and `T + 1 < 2^(log₂(T + 1) + 1)`.
Then `c₀ T + 1 ≤ (c₀ + 1)(T + 1) < 2^(m + log₂(T + 1) + 1)`, so
`log₂(c₀ T + 1) ≤ log₂(T + 1) + m` and `log₂(c₀ T + 1) + 1 ≤ (m + 1)(log₂(T + 1) + 1)`;
multiply by `c₀ T + 1 ≤ (c₀ + 1)(T + 1)`. -/
theorem logOverhead_mul_le (c₀ T : ℕ) :
    logOverhead (c₀ * T) ≤ (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead T := by
  rw [logOverhead_eq, logOverhead_eq]
  set m := Nat.log 2 (c₀ + 1) + 1 with hm
  set l := Nat.log 2 (T + 1) with hl
  have hc : c₀ + 1 < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) _
  have hT : T + 1 < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1 : c₀ * T + 1 ≤ (c₀ + 1) * (T + 1) := by nlinarith
  have h2 : (c₀ + 1) * (T + 1) < 2 ^ m * 2 ^ (l + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hc hT
  have hlog : Nat.log 2 (c₀ * T + 1) < m + (l + 1) := by
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_add]
    omega
  have h3 : Nat.log 2 (c₀ * T + 1) + 1 ≤ (m + 1) * (l + 1) := by nlinarith
  calc (c₀ * T + 1) * (Nat.log 2 (c₀ * T + 1) + 1)
      ≤ ((c₀ + 1) * (T + 1)) * ((m + 1) * (l + 1)) := Nat.mul_le_mul h1 h3
    _ = (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * ((T + 1) * (l + 1)) := by rw [hm]; ring

/-- **The arithmetic of the book form** [AB09, Theorem 3.1]: for `2 ≤ n ≤ f`,
`logDiagOverhead f n ≤ 12 · f · log₂ f`.

**Proof sketch.** `f ≥ 2`, so `log₂ f ≥ 1`. From `n ≤ f`: `f + n + 1 ≤ 3f`, and
`f + n + 1 ≤ 4f`, so `log₂(f + n + 1) ≤ log₂(4f) = log₂ f + 2` and
`log₂(f + n + 1) + 1 ≤ log₂ f + 3 ≤ 4 log₂ f`. Multiply: at most `3f · 4 log₂ f`. -/
theorem logDiagOverhead_le_book {f n : ℕ} (hn : 2 ≤ n) (hf : n ≤ f) :
    logDiagOverhead f n ≤ 12 * (f * Nat.log 2 f) := by
  rw [logDiagOverhead_eq]
  have hf2 : 2 ≤ f := le_trans hn hf
  have hlog1 : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by norm_num) (by simpa using hf2)
  have h3 : f + n + 1 ≤ f * 2 * 2 := by omega
  have hlog : Nat.log 2 (f + n + 1) ≤ Nat.log 2 f + 2 := by
    calc Nat.log 2 (f + n + 1) ≤ Nat.log 2 (f * 2 * 2) := Nat.log_mono_right h3
      _ = Nat.log 2 f + 2 := by
        rw [Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hA : f + n + 1 ≤ 3 * f := by omega
  have hB : Nat.log 2 (f + n + 1) + 1 ≤ 4 * Nat.log 2 f := by omega
  calc (f + n + 1) * (Nat.log 2 (f + n + 1) + 1) ≤ (3 * f) * (4 * Nat.log 2 f) :=
        Nat.mul_le_mul hA hB
    _ = 12 * (f * Nat.log 2 f) := by ring

/-- The book form's hypothesis gives the diagonal one: if `n ≤ f n` and, for every `A`,
eventually `A · f n log₂ f n ≤ g n`, then for every `A`, eventually
`A · logDiagOverhead (f n) n ≤ g n` (`logDiagOverhead_le_book` at the constant `12 A`, for
`n ≥ 2`). -/
private theorem eventually_logDiagOverhead_le {f g : ℕ → ℕ} (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logDiagOverhead (f n) n ≤ g n := by
  intro A
  obtain ⟨N, hN⟩ := hfg (12 * A)
  refine ⟨max N 2, fun n hn => ?_⟩
  calc A * logDiagOverhead (f n) n ≤ A * (12 * (f n * Nat.log 2 (f n))) :=
        Nat.mul_le_mul_left A (logDiagOverhead_le_book (le_of_max_le_right hn) (hf n))
    _ = 12 * A * (f n * Nat.log 2 (f n)) := by ring
    _ ≤ g n := hN n (le_of_max_le_left hn)

/-- **The fixed two-work-tape representation scheme** of the book form [AB09, §1.4] (any
scheme works; `Turing.exists_effectiveMachineCode2` provides one). -/
noncomputable def code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2

/-- The definition of `code₂`: `code₂ = Classical.choice Turing.exists_effectiveMachineCode2`. -/
theorem code₂_eq : code₂ = Classical.choice exists_effectiveMachineCode2 := rfl

/-- **The two-tape self-simulator** [AB09, Theorem 3.1, proof; §1.4.1 and §1.7]: the
self-application universal machine for the two-work-tape codes of `code₂`
(`Turing.exists_selfUniversalK` at `k = 2`; `decode α` the machine `code₂.decode α`), with the
Hennie–Stearns normal form, whose overhead is `logOverhead`.

**Proof sketch.** *Simulation:* for each code `α`, `Turing.exists_selfUniversalK` gives a
constant `C` such that whenever the machine coded by `α` (the same bundled machine in the
`k`-tape view, `Turing.EffectiveMachineCode2.toK_toFinTM`) halts on `pairEncode α w` with `[b]`
within `t` steps, the universal machine does so within
`C (t + 1) ≤ C (t + |pairEncode α w| + 1)` steps. *Normal form:* a decider within `c₀ T`
becomes a two-work-tape binary machine within `c₁ · logOverhead (c₀ T)`
(`Turing.FinTM.two_work_tapes_binary`), then a coded machine `N` with the same runs
(`Turing.exists_code2TM`), whose code `code₂.encode N` decodes back to `N`; and
`c₁ · logOverhead (c₀ T) ≤ c₁ (c₀ + 1)(log₂(c₀ + 1) + 2) (logOverhead T + 1)`
(`logOverhead_mul_le`). -/
noncomputable def twoTapeSelfSimulator : SelfSimulator logOverhead where
  W := Classical.choose (exists_selfUniversalK 2 code₂.toK)
  decode α := (code₂.decode α).toFinTM
  simulates α := by
    obtain ⟨C, -, hC⟩ := Classical.choose_spec (exists_selfUniversalK 2 code₂.toK) α
    refine ⟨C, fun w b t h => ?_⟩
    have h' : (code₂.toK.toFinTM α).ComputesInTime (pairEncode α w) [b] t := by
      rw [EffectiveMachineCode2.toK_toFinTM]; exact h
    exact ((hC w).1 [b] t h').1.mono (Nat.mul_le_mul_left C (by omega))
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := two_work_tapes_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n)
      ((computesFunInTime_iff _ _ _).2 hM)
    obtain ⟨N, hN⟩ := exists_code2TM M₁ hk
    refine ⟨code₂.encode N, c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)), fun x => ?_⟩
    dsimp only
    rw [code₂.toMachineCode2.decode_encode N]
    apply ((hN x _ _).2 ((computesFunInTime_iff _ _ _).1 h₁ x)).mono
    calc c₁ * ((c₀ * T x.length + 1) * (Nat.log 2 (c₀ * T x.length + 1) + 1))
        = c₁ * logOverhead (c₀ * T x.length) := by rw [logOverhead_eq]
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead (T x.length)) :=
          Nat.mul_le_mul_left c₁ (logOverhead_mul_le c₀ _)
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)) * (logOverhead (T x.length) + 1) := by
          rw [Nat.mul_assoc c₁]
          exact Nat.mul_le_mul_left c₁ (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- The two-tape self-simulator's machine is the self-application universal machine of
`code₂` at `k = 2`, by definition. -/
theorem twoTapeSelfSimulator_W :
    twoTapeSelfSimulator.W = Classical.choose (exists_selfUniversalK 2 code₂.toK) := rfl

/-- The two-tape self-simulator's code `α` denotes the machine `code₂.decode α`, by
definition. -/
theorem twoTapeSelfSimulator_decode (α : List Bool) :
    twoTapeSelfSimulator.decode α = (code₂.decode α).toFinTM := rfl

end Complexity.TimeHierarchy.T31SealC

namespace Complexity.TimeHierarchy.T31SealC

open TimeHierarchy

/-- **The Time Hierarchy Theorem at overhead `f log f`** [AB09, Theorem 3.1], with the input
length kept: if `g` is time constructible and
`(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))` — i.e. for every constant `A`, eventually
`A · (f n + n + 1)(log₂(f n + n + 1) + 1) ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`. No
hypothesis on `f` is needed; `Complexity.time_hierarchy_book` is the book's form.

**Proof sketch.** The case `Φ = logDiagOverhead` of `DiagSimulator.time_hierarchy`, at the
two-tape self-simulator `twoTapeSelfSimulator` padded by `SelfSimulator.toDiagSimulator`
(overhead `logOverhead t + n + 1`) and weakened by `DiagSimulator.mono`
(`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, `logOverhead_add_le`), with
`t ≤ logDiagOverhead t n` (`le_logDiagOverhead`). *Inclusion:* `f n ≤ g n` eventually, the
smaller lengths absorbed into the constant. *Strictness:* the diagonal language of the
two-tape universal machine lies in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in
`DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`). -/
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg fun A => (hfg A).imp fun _ hN n hn => by
      rw [logDiagOverhead_eq]; exact hN n hn

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the book's form: if `g` is time
constructible, `n ≤ f(n)` for all `n`, and `f(n) log₂ f(n) = o(g(n))` — i.e. for every
constant `A`, eventually `A · f n · log₂ f n ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): `n ≤ f(n)` in place of time
constructibility of `f` (every time-constructible `f` satisfies it); `log₂` is the floor
logarithm `Nat.log 2`, which vanishes at `f n ≤ 1`, hence only at `n ≤ 1` here, outside the
eventual hypothesis; and the larger class is `DTIME (g + 1)`, which differs from `DTIME g` only
in the degenerate case `g 0 = 0` (`Complexity.time_hierarchy_book_of_pos`).

**Proof sketch.** For `n ≥ 2`, `n ≤ f n` gives
`(f n + n + 1)(log₂(f n + n + 1) + 1) ≤ 12 · f n · log₂ f n` (`logDiagOverhead_le_book`), so
the hypothesis at `12 A` gives `A · logDiagOverhead (f n) n ≤ g n` eventually; conclude as in
`Complexity.time_hierarchy_log`, by `DiagSimulator.time_hierarchy` at the two-tape
self-simulator `twoTapeSelfSimulator`. -/
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg (eventually_logDiagOverhead_le hf hfg)

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1], in the book's
form: as `Complexity.time_hierarchy_book`, with the larger class exactly `DTIME g` when `g`
never vanishes — the book's `DTIME(f) ⊊ DTIME(g)`.

**Proof sketch.** As `Complexity.time_hierarchy_book`, through
`DiagSimulator.time_hierarchy_of_pos` in place of `DiagSimulator.time_hierarchy`:
`c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) = DTIME g`. -/
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy_of_pos
    le_logDiagOverhead hg hpos (eventually_logDiagOverhead_le hf hfg)

end Complexity.TimeHierarchy.T31SealC

end SealC

## ===== campaign/gates/113-thm31-book/evidence/probes/seal.out =====

Scratch/T31Seal.lean:20:41: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Scratch/T31Seal.lean:170:11: error: Tactic `rcases` failed: `a✝ : DTIME T L` is not an inductive datatype
Scratch/T31Seal.lean:422:39: error: Application type mismatch: The argument
  hM
has type
  M.DecidesInTime L fun n => c₀ * T n
but is expected to have type
  ∀ (input : List Bool), M.ComputesInTime input [MultiTapeTM.indicator L input] (c₀ * T input.length)
in the application
  (computesFunInTime_iff M (fun x => [MultiTapeTM.indicator L x]) fun n => c₀ * T n).mpr hM

## ===== campaign/gates/113-thm31-book/evidence/screen/pairdiff.txt =====

head pairs 23; union of earlier 16; new at head 7; earlier-only 0
  NEW   Diagonal.lean::Complexity.TimeHierarchy.diagLang_not_mem_DTIME  reproduces  Diagonal.lean::twoTapeSelfSimulator_decode: 63/66 = 95%
  NEW   Diagonal.lean::time_hierarchy_book_of_pos  reproduces  Diagonal.lean::time_hierarchy_book: 113/133 = 85%
  NEW   Diagonal.lean::logOverhead_add_le  reproduces  Diagonal.lean::le_logDiagOverhead: 80/109 = 73%
  NEW   Diagonal.lean::time_hierarchy_log  reproduces  Diagonal.lean::time_hierarchy_book: 97/133 = 73%
  NEW   Diagonal.lean::time_hierarchy_book  reproduces  Diagonal.lean::time_hierarchy_book_of_pos: 113/157 = 72%
  NEW   Diagonal.lean::twoTapeSelfSimulator_decode  reproduces  Diagonal.lean::Complexity.TimeHierarchy.diagLang_not_mem_DTIME: 63/103 = 61%
  NEW   Diagonal.lean::time_hierarchy_book  reproduces  Diagonal.lean::time_hierarchy_log: 97/159 = 61%

## ===== campaign/gates/113-thm31-book/evidence/screen/pop-base.txt =====

TCSlib/Complexity/TimeHierarchy/ClockLoop.lean
TCSlib/Complexity/TimeHierarchy/ClockMachine.lean
TCSlib/Complexity/TimeHierarchy/CodePrefix.lean
TCSlib/Complexity/TimeHierarchy/Diagonal.lean
TCSlib/Complexity/TimeHierarchy/Separation.lean

## ===== campaign/gates/113-thm31-book/evidence/screen/pop-head.txt =====

TCSlib/Complexity/TimeHierarchy/ClockLoop.lean
TCSlib/Complexity/TimeHierarchy/ClockMachine.lean
TCSlib/Complexity/TimeHierarchy/CodePrefix.lean
TCSlib/Complexity/TimeHierarchy/Diagonal.lean
TCSlib/Complexity/TimeHierarchy/Separation.lean

## ===== campaign/gates/113-thm31-book/evidence/screen/screen-base.txt =====

declarations screened: 62; copy pairs (target reproduces >= half of source): 16; reproduced text: 3,277 chars
   ClockLoop.lean::wstep  reproduces  ClockLoop.lean::underflow_step: 90/93 = 97%
   ClockMachine.lean::ctrVal_replicate_true  reproduces  ClockMachine.lean::ctrVal_replicate_false: 91/115 = 79%
   ClockLoop.lean::borrow_run  reproduces  ClockLoop.lean::underflow_step: 66/93 = 71%
   ClockLoop.lean::ret_run  reproduces  ClockLoop.lean::underflow_step: 63/93 = 68%
   ClockLoop.lean::wstep  reproduces  ClockMachine.lean::kCfg_init: 185/274 = 68%
   CodePrefix.lean::pre_scan  reproduces  CodePrefix.lean::pre_copy: 579/863 = 67%
   ClockMachine.lean::cScanCfg_run  reproduces  ClockLoop.lean::ret_run: 435/657 = 66%
   ClockLoop.lean::ret_run  reproduces  ClockMachine.lean::cScanCfg_run: 435/682 = 64%
   ClockMachine.lean::ctrAction_apply  reproduces  ClockMachine.lean::kCfg_init: 168/274 = 61%
   ClockMachine.lean::kCfg_step  reproduces  ClockMachine.lean::kCfg_init: 161/274 = 59%
   ClockMachine.lean::ctrPop_replicate  reproduces  ClockMachine.lean::ctrVal_replicate_false: 64/115 = 56%
   ClockMachine.lean::kCfg_step  reproduces  ClockLoop.lean::wstep: 376/680 = 55%
   ClockLoop.lean::wstep  reproduces  ClockMachine.lean::ctrAction_apply: 225/417 = 54%
   ClockMachine.lean::ctrVal_replicate_true  reproduces  ClockMachine.lean::ctrPop_replicate: 64/121 = 53%
   ClockMachine.lean::ctrVal_replicate_false  reproduces  ClockMachine.lean::ctrPop_replicate: 64/121 = 53%
   ClockMachine.lean::kCfg_step  reproduces  ClockMachine.lean::ctrAction_apply: 211/417 = 51%

## ===== campaign/gates/113-thm31-book/evidence/screen/screen-head.txt =====

declarations screened: 72; copy pairs (target reproduces >= half of source): 23; reproduced text: 3,903 chars
   ClockLoop.lean::wstep  reproduces  ClockLoop.lean::underflow_step: 90/93 = 97%
   Diagonal.lean::Complexity.TimeHierarchy.diagLang_not_mem_DTIME  reproduces  Diagonal.lean::twoTapeSelfSimulator_decode: 63/66 = 95%
   Diagonal.lean::time_hierarchy_book_of_pos  reproduces  Diagonal.lean::time_hierarchy_book: 113/133 = 85%
   ClockMachine.lean::ctrVal_replicate_true  reproduces  ClockMachine.lean::ctrVal_replicate_false: 91/115 = 79%
   Diagonal.lean::logOverhead_add_le  reproduces  Diagonal.lean::le_logDiagOverhead: 80/109 = 73%
   Diagonal.lean::time_hierarchy_log  reproduces  Diagonal.lean::time_hierarchy_book: 97/133 = 73%
   Diagonal.lean::time_hierarchy_book  reproduces  Diagonal.lean::time_hierarchy_book_of_pos: 113/157 = 72%
   ClockLoop.lean::borrow_run  reproduces  ClockLoop.lean::underflow_step: 66/93 = 71%
   ClockLoop.lean::ret_run  reproduces  ClockLoop.lean::underflow_step: 63/93 = 68%
   ClockLoop.lean::wstep  reproduces  ClockMachine.lean::kCfg_init: 185/274 = 68%
   CodePrefix.lean::pre_scan  reproduces  CodePrefix.lean::pre_copy: 579/863 = 67%
   ClockMachine.lean::cScanCfg_run  reproduces  ClockLoop.lean::ret_run: 435/657 = 66%
   ClockLoop.lean::ret_run  reproduces  ClockMachine.lean::cScanCfg_run: 435/682 = 64%
   ClockMachine.lean::ctrAction_apply  reproduces  ClockMachine.lean::kCfg_init: 168/274 = 61%
   Diagonal.lean::twoTapeSelfSimulator_decode  reproduces  Diagonal.lean::Complexity.TimeHierarchy.diagLang_not_mem_DTIME: 63/103 = 61%
   Diagonal.lean::time_hierarchy_book  reproduces  Diagonal.lean::time_hierarchy_log: 97/159 = 61%
   ClockMachine.lean::kCfg_step  reproduces  ClockMachine.lean::kCfg_init: 161/274 = 59%
   ClockMachine.lean::ctrPop_replicate  reproduces  ClockMachine.lean::ctrVal_replicate_false: 64/115 = 56%
   ClockMachine.lean::kCfg_step  reproduces  ClockLoop.lean::wstep: 376/680 = 55%
   ClockLoop.lean::wstep  reproduces  ClockMachine.lean::ctrAction_apply: 225/417 = 54%
   ClockMachine.lean::ctrVal_replicate_true  reproduces  ClockMachine.lean::ctrPop_replicate: 64/121 = 53%
   ClockMachine.lean::ctrVal_replicate_false  reproduces  ClockMachine.lean::ctrPop_replicate: 64/121 = 53%
   ClockMachine.lean::kCfg_step  reproduces  ClockMachine.lean::ctrAction_apply: 211/417 = 51%

## ===== TCSlib/Complexity/TimeHierarchy/Diagonal.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.Robustness.TwoTapes
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.UniversalK

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Time Hierarchy Theorem

[AB09, Theorem 3.1]: if `f, g` are time-constructible functions with
`f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g)`. This file proves the theorem
twice. First, through the universal machine `Turing.universal`, with quadratic overhead:

  if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`, then
  `DTIME(f) ⊊ DTIME(g + 1)`.

Then in the book's form (`Complexity.time_hierarchy_book`), through the two-work-tape
self-universal machine and its `O(t log t)` overhead: if `g` is time constructible, `n ≤ f(n)`
and `f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g + 1)`.

## The diagonal language

Fix the effective representation scheme `code` and the universal machine `univTM`
(`Turing.universal`). The simulator `diagSim` composes the prefix-duplication machine
`preTM` with `univTM`; on an input `x = pairEncode α w` it runs the machine coded by
`α` on `x` itself. The diagonal language is

  `diagLang g = {x | diagSim does not halt on x with output [true] within g(|x|) steps}`,

decided within `O(g(n))` by the clocked runner `clockTM K diagSim`, where `K` is the
time-constructibility witness of `g` (`diagLang_mem_DTIME`). If a machine `M`
decided `diagLang g` within `c·T(n)`, take a code `α` of its one-work-tape normal form
and the inputs `x = pairEncode α 1^m`: the simulation of `M` on `x` finishes within
`A·(T(n) + n + 1)²` steps for a constant `A` depending only on `M`, which is at most
`g(n)` for suitable `n` — and then `diagSim`'s verdict on `x` contradicts `M`'s
(`diagLang_not_mem_DTIME`).

## The parameterized argument

The argument is stated once, over the simulator and its overhead; the received theorem is its
instance at `diagSim` (user authorization, 2026-10-14; design note
`audits/evidence/u2/U2-design.md` §3).

* `diagLangOf W g` is the diagonal language of an arbitrary machine `W`. It lies in
  `DTIME (g + 1)` for every `W` (`diagLangOf_mem_DTIME`), because the clocked runner counts
  `W`'s own steps.
* A `DiagSimulator Φ` is a machine that reproduces, on some input of every large length `n`,
  the verdict of every `DTIME T` language within `A · Φ (T n) n` steps, `A` depending on the
  language. Its diagonal language escapes `DTIME T` whenever `A · Φ (T n) n ≤ g n` infinitely
  often for every `A` (`DiagSimulator.diagLang_not_mem_DTIME`); hence the hierarchy theorem
  with overhead `Φ` (`DiagSimulator.time_hierarchy`, `DiagSimulator.time_hierarchy_of_pos`).
* A `SelfSimulator Ψ` is the universal-machine form of that hypothesis: a machine that runs
  each code on its own input at a cost linear per code, and a normal form of overhead `Ψ` for
  `DTIME` deciders. Padding the input makes it a `DiagSimulator` with overhead `Ψ t + n + 1`
  (`SelfSimulator.toDiagSimulator`).
* The received instance is `diagSim` with the one-work-tape normal form, `Ψ t = (t + 1)²`
  (`oneTapeSelfSimulator`), weakened to the overhead `(t + n + 1)²` (`sqDiagSimulator`).
  `diagLang_mem_DTIME`, `diagLang_not_mem_DTIME`, `time_hierarchy` and
  `time_hierarchy_of_pos` are its corollaries, with their statements unchanged.

## Divergences from [AB09, Theorem 3.1]

* **Two overheads: the book's `f log f`, and the received `f²`.** The book's universal machine
  has `O(T log T)` overhead ([AB09, Theorem 1.9 / §1.7]). The book form is the instance of the
  parameterized argument (above) at the two-tape self-simulator `twoTapeSelfSimulator`: the
  self-application universal machine for two-work-tape codes (`Turing.exists_selfUniversalK`
  at `k = 2`), linear on coded machines, with the Hennie–Stearns normal form of overhead
  `logOverhead t = (t + 1)(log₂(t + 1) + 1)` (`Turing.FinTM.two_work_tapes_binary`,
  [AB09, §1.7]). Its hypothesis is `(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))`, written out as
  `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)(log₂(f n + n + 1) + 1) ≤ g n`
  (`Complexity.time_hierarchy_log`), and, under `n ≤ f(n)`, the book's
  `f(n) log₂ f(n) = o(g(n))` (`Complexity.time_hierarchy_book`, with
  `logDiagOverhead f n ≤ 12 · f · log₂ f` for `2 ≤ n ≤ f`, `logDiagOverhead_le_book`). The
  received form, kept beside it, is the instance at `diagSim`, whose coded machines are
  one-work-tape binary machines, normal-formed with quadratic slowdown
  (`Turing.FinTM.one_work_tape_binary`, [AB09, Claims 1.5–1.6]); its hypothesis is
  `(f(n) + n + 1)² = o(g(n))`, written out as `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)² ≤ g n`
  (`Complexity.time_hierarchy`). In both, the `+ n + 1` absorbs the linear cost of reading the
  input and the `+ 1` normalization of `DTIME` bounds.
* **Separations below the quadratic threshold.** Because of the `+ n + 1` term the received
  hypothesis forces `g(n) = ω(n²)`, and the best linear-time separation it yields is roughly
  `DTIME(n) ⊊ DTIME(n^(2+ε))`. The book form has no such threshold. The book's illustration
  `DTIME(n) ⊊ DTIME(n^1.5)` is not derived here: it needs a time-constructibility witness for a
  bound such as `n ⌊√n⌋`.
* **`n ≤ f(n)` in place of time constructibility of `f`.** The book assumes both `f` and `g`
  time constructible, `f` only for symmetry. The book form assumes only `n ≤ f(n)`, which every
  time-constructible `f` satisfies: it absorbs the `+ n + 1` into `f(n)` and makes
  `log₂ f(n) ≥ 1` for `n ≥ 2`. `log₂` is the floor logarithm `Nat.log 2`, which vanishes at
  `f(n) ≤ 1`, hence, under `n ≤ f(n)`, only at `n ≤ 1`, where an eventual hypothesis says
  nothing. The received form and `Complexity.time_hierarchy_log` need no hypothesis on `f`.
* **`DTIME(g + 1)` instead of `DTIME(g)`.** `TimeConstructible g` permits `g 0 = 0`,
  and `DTIME` of a bound vanishing anywhere is empty
  (`Complexity.DTIME_eq_empty_of_exists_zero`); the `+ 1` repairs this degenerate
  case only (for `n ≥ 1`, `g n ≥ n ≥ 1`). For a bound that never vanishes the larger class
  is the book's `DTIME(g)` (`Complexity.time_hierarchy_of_pos`,
  `Complexity.time_hierarchy_book_of_pos`).
* **Padding the input, not the code.** The book uses that every machine has
  infinitely many codes. Here the universal machine's constant depends on the code
  string (`Turing.universal`, `Turing.exists_selfUniversalK` — the canonizer time of the
  representation scheme is an opaque bound), so the diagonal argument fixes one code `α` and
  pads the *input* `pairEncode α 1^m`. The received instance recovers the code from the input
  by `preTM`; the two-tape instance runs the coded machine on the very input that carries its
  code (self-application).
* **The clock counts the diagonal machine's own simulation steps**, via the clocked
  runner `Complexity.TimeHierarchy.clockTM`.
* The separation is proved in the stronger *infinitely-often* form:
  `diagLang_not_mem_DTIME` needs `A · (T n + n + 1)² ≤ g n` only for infinitely many
  `n`, for each `A` (`DiagSimulator.diagLang_not_mem_DTIME`, for every overhead).

## Main definitions

* `Complexity.TimeHierarchy.code`, `univTM`, `diagSim` — the fixed scheme, universal
  machine, and simulator.
* `Complexity.TimeHierarchy.diagLang` — the diagonal language.
* `Complexity.TimeHierarchy.diagLangOf` — the diagonal language of an arbitrary simulator.
* `Complexity.TimeHierarchy.DiagSimulator`, `SelfSimulator` — the hypothesis on a simulator,
  at the level of padded simulation and at the level of a universal machine with a normal
  form; `DiagSimulator.mono`, `SelfSimulator.toDiagSimulator` — weakening and input padding.
* `Complexity.TimeHierarchy.oneTapeSelfSimulator`, `sqDiagSimulator` — the received instance.
* `Complexity.TimeHierarchy.logOverhead`, `logDiagOverhead` — the overheads `(t+1)(log₂(t+1)+1)`
  and `(t+n+1)(log₂(t+n+1)+1)`.
* `Complexity.TimeHierarchy.code₂`, `twoTapeSelfSimulator` — the two-work-tape scheme and the
  self-simulator at `logOverhead`, from `Turing.exists_selfUniversalK` at two work tapes.

## Main results

* `Complexity.TimeHierarchy.diagLang_mem_DTIME` — `diagLang g ∈ DTIME (g + 1)`.
* `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` — `diagLang g ∉ DTIME T` whenever
  `A · (T n + n + 1)² ≤ g n` infinitely often for every `A`.
* `Complexity.time_hierarchy` — [AB09, Theorem 3.1], in the form above.
* `Complexity.time_hierarchy_of_pos` — the same with `DTIME g` when `g` never vanishes.
* `Complexity.TimeHierarchy.diagLangOf_mem_DTIME`, `DiagSimulator.diagLang_not_mem_DTIME`,
  `DiagSimulator.time_hierarchy`, `DiagSimulator.time_hierarchy_of_pos` — the parameterized
  argument, of which the four results above are the instance at `sqDiagSimulator`.
* `Complexity.time_hierarchy_book` — [AB09, Theorem 3.1] in the book's form: if `g` is time
  constructible, `n ≤ f(n)` and `f(n) log₂ f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g + 1)`.
* `Complexity.time_hierarchy_book_of_pos` — the same with `DTIME g` when `g` never vanishes.
* `Complexity.time_hierarchy_log` — the same at `(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))`,
  with no hypothesis on `f`; the three are the instance of the parameterized argument at the
  two-tape self-simulator `Complexity.TimeHierarchy.twoTapeSelfSimulator`, of overhead
  `logOverhead`, padded to `logDiagOverhead` (`logOverhead_add_le`).
* `Complexity.TimeHierarchy.logOverhead_mul_le`, `logDiagOverhead_le_book` — the arithmetic of
  the book form: constant-factor absorption, and `logDiagOverhead f n ≤ 12 · f · log₂ f`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1, pp. 69–70; §1.4.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The fixed effective representation scheme of the hierarchy construction (any
scheme works; `Turing.exists_effectiveMachineCode` provides one). -/
noncomputable def code : EffectiveMachineCode := Classical.choice exists_effectiveMachineCode

/-- The universal machine for `code`, from `Turing.universal`. -/
noncomputable def univTM : FinTM Bool := Classical.choose (universal code)

/-- The universal machine's specification (`Turing.universal`). -/
lemma univTM_spec : ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
    (∀ (output : List Bool) (t : ℕ),
      (code.decode α).toFinTM.ComputesInTime x output t →
      univTM.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
    (∀ output : List Bool,
      (∃ t, univTM.ComputesInTime (pairEncode α x) output t) →
      ∃ t, (code.decode α).toFinTM.ComputesInTime x output t) :=
  Classical.choose_spec (universal code)

/-- The diagonal simulator: duplicate the code prefix (`preTM`), then run the
universal machine. On `x = pairEncode α w` it runs the machine coded by `α` on `x`. -/
noncomputable def diagSim : FinTM Bool := bufferedCompTM preTM univTM

/-- **The diagonal language** of the hierarchy theorem [AB09, Theorem 3.1, proof]:
the strings `x` on which the diagonal simulator does **not** halt with output `[true]`
within `g(|x|)` steps. -/
def diagLang (g : ℕ → ℕ) : Language Bool :=
  {x | ¬diagSim.ComputesInTime x [true] (g x.length)}

/-! ### The parameterized argument -/

/-- **The diagonal language of a simulator `W`** [AB09, Theorem 3.1, proof]: the strings `x`
on which `W` does **not** halt with output `[true]` within `g(|x|)` steps. The received
`diagLang g` is the case `W = diagSim` (`diagLang_eq_diagLangOf`). -/
def diagLangOf (W : FinTM Bool) (g : ℕ → ℕ) : Language Bool :=
  {x | ¬W.ComputesInTime x [true] (g x.length)}

/-- The received diagonal language is the diagonal language of `diagSim`, by definition. -/
theorem diagLang_eq_diagLangOf (g : ℕ → ℕ) : diagLang g = diagLangOf diagSim g := rfl

/-- **The diagonal language of any simulator is decidable in time `O(g)`** [AB09, Theorem 3.1,
proof]: for time-constructible `g` and every machine `W`, `diagLangOf W g ∈ DTIME (g + 1)`.
Nothing is assumed of `W`: the clocked runner counts `W`'s own steps.

**Proof sketch.** Run the clocked runner `clockTM K W`, with `K` the time-constructibility
witness of `g`: its budget word is `bits (g n)` of value `g n`, so by `clockTM_spec` it outputs
`[x ∈ diagLangOf W g]` within `c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤
(c_K + 15)(g n + 1)` steps, using `|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLangOf_mem_DTIME (W : FinTM Bool) {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLangOf W g ∈ DTIME (fun n => g n + 1) := by
  classical
  obtain ⟨hgn, cK, _, K, hK⟩ := hg
  refine ⟨cK + 15, clockTM K W, fun x => ?_⟩
  have h := clockTM_spec K W x (g x.length).bits _ (hK x)
  rw [ctrVal_bits] at h
  have hout : [!(decide (W.ComputesInTime x [true] (g x.length)))] =
      [MultiTapeTM.indicator (diagLangOf W g : Set (List Bool)) x] := by
    by_cases hx : W.ComputesInTime x [true] (g x.length)
    · have : x ∉ (diagLangOf W g : Set (List Bool)) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (diagLangOf W g : Set (List Bool)) := hx
      simp [MultiTapeTM.indicator, hx, this]
  rw [hout] at h
  apply h.mono
  have h1 := length_bits_le_self (g x.length)
  have h2 := hgn x.length
  nlinarith

/-- **A diagonal simulator with overhead `Φ`** (the hypothesis of the diagonal argument
[AB09, Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md` §3): a machine `W`
such that for every time bound `T` and every language `L ∈ DTIME T` there are constants `A`
and `N₀` with: for every length `n ≥ N₀` some input `x` of length `n` makes `W` halt with the
verdict `[x ∈ L]` within `A · Φ (T n) n` steps. No clock is part of it: the clocked runner
supplies one for every `W` (`diagLangOf_mem_DTIME`). Deviation: the book simulates a code of
the machine at hand, which has infinitely many codes; here the simulator is only required to
succeed on one input of each large length, which is what the diagonal argument uses. -/
structure DiagSimulator (Φ : ℕ → ℕ → ℕ) where
  /-- the simulating machine -/
  W : FinTM Bool
  /-- padded simulation of every `DTIME T` language within `A · Φ (T n) n` steps -/
  simulates : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ A N₀ : ℕ, ∀ n ≥ N₀, ∃ x : List Bool, x.length = n ∧
      W.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (A * Φ (T n) n)

namespace DiagSimulator

variable {Φ : ℕ → ℕ → ℕ}

/-- **Weakening the overhead** up to a constant factor: a diagonal simulator with overhead `Φ`
is one, with the same machine, with overhead `Φ'` whenever `Φ ≤ K · Φ'` pointwise. -/
def mono (S : DiagSimulator Φ) {Φ' : ℕ → ℕ → ℕ} (K : ℕ) (h : ∀ t n, Φ t n ≤ K * Φ' t n) :
    DiagSimulator Φ' where
  W := S.W
  simulates T L hL := by
    obtain ⟨A, N₀, hA⟩ := S.simulates T L hL
    refine ⟨A * K, N₀, fun n hn => ?_⟩
    obtain ⟨x, hx, hW⟩ := hA n hn
    exact ⟨x, hx, hW.mono (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left A (h _ _))⟩

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof], for a diagonal
simulator with overhead `Φ`, provided `A · Φ (T n) n ≤ g n` for infinitely many `n`, for every
constant `A` (the infinitely-often form).

**Proof sketch.** Suppose `diagLangOf W g ∈ DTIME T`. The simulation clause gives `A` and
`N₀`; pick `n ≥ N₀` with `A · Φ (T n) n ≤ g n`, and an input `x` of length `n` on which `W`
halts with `[χ(x)]` within `A · Φ (T n) n ≤ g n` steps, `χ` the indicator of the diagonal
language. If `χ(x) = true` then `x ∈ diagLangOf W g`, so `W` does not output `[true]` within
`g n`, a contradiction; if `χ(x) = false` then `x ∉ diagLangOf W g`, so `W` outputs `[true]`
within `g n`, against the uniqueness of its output `[false]`. -/
theorem diagLang_not_mem_DTIME (S : DiagSimulator Φ) {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * Φ (T n) n ≤ g n) :
    diagLangOf S.W g ∉ DTIME T := by
  classical
  intro hL
  obtain ⟨A, N₀, hA⟩ := S.simulates T _ hL
  obtain ⟨n, hn, hgn⟩ := hT A N₀
  obtain ⟨x, hx, hW⟩ := hA n hn
  let χ := MultiTapeTM.indicator (diagLangOf S.W g : Set (List Bool))
  have hD : S.W.ComputesInTime x [χ x] (g x.length) := hW.mono (by rw [hx]; exact hgn)
  by_cases hmem : x ∈ (diagLangOf S.W g : Set (List Bool))
  · have hχ : χ x = true := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD
    exact hmem hD
  · have hχ : χ x = false := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD
    have htrue : S.W.ComputesInTime x [true] (g x.length) := by
      by_contra hc
      exact hmem hc
    have := htrue.output_unique hD
    simp at this

/-- **The Time Hierarchy Theorem with overhead `Φ`** [AB09, Theorem 3.1], for a diagonal
simulator: if `g` is time constructible, `t ≤ Φ t n` for all `t` and `n`, and for every
constant `A` eventually `A · Φ (f n) n ≤ g n`, then `DTIME(f) ⊊ DTIME(g + 1)`. The deviations
of `Complexity.time_hierarchy` apply (`f` need not be time constructible; `DTIME (g + 1)`).

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` and `t ≤ Φ t n` give `f n ≤ g n`
for `n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* `diagLangOf W g` lies
in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in `DTIME f`
(`DiagSimulator.diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) := by
  refine ⟨?_, fun hsub => S.diagLang_not_mem_DTIME (g := g) (T := f) ?_
    (hsub (diagLangOf_mem_DTIME S.W hg))⟩
  · -- inclusion
    obtain ⟨N, hN⟩ := hfg 1
    let F := ∑ i ∈ Finset.range N, f i
    have hle : ∀ n, f n ≤ (F + 1) * (g n + 1) := by
      intro n
      by_cases hn : n < N
      · have : f n ≤ F := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr hn)
        nlinarith
      · have h := hN n (by omega)
        have h' := hΦ (f n) n
        have : f n ≤ g n := by omega
        nlinarith
    rintro L ⟨c, M, hM⟩
    exact ⟨c * (F + 1), M, fun x => (hM x).mono (by
      simp only [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (hle x.length))⟩
  · intro A N₀
    obtain ⟨N, hN⟩ := hfg A
    exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **The Time Hierarchy Theorem with overhead `Φ`, for a positive bound** [AB09,
Theorem 3.1]: as `DiagSimulator.time_hierarchy`, with the larger class exactly `DTIME g` when
`g` never vanishes.

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the
reverse inclusion is `Complexity.DTIME.mono`; conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
    DTIME f ⊂ DTIME g := by
  have heq : DTIME (fun n => g n + 1) = DTIME g := by
    apply Set.Subset.antisymm
    · rintro L ⟨c, M, hM⟩
      refine ⟨2 * c, M, fun x => (hM x).mono ?_⟩
      have := hpos x.length
      dsimp only
      nlinarith
    · exact DTIME.mono (fun n => Nat.le_succ _)
  rw [← heq]
  exact S.time_hierarchy hΦ hg hfg

end DiagSimulator

/-- **A self-simulator with normal-form overhead `Ψ`** (the universal-machine form of the
hypothesis [AB09, §1.4 and Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md`
§3): a machine `W` and machines `decode α` indexed by codes `α`, such that
* for every code `α` there is a constant `C`, depending on `α` only, with: whenever
  `decode α` halts on `pairEncode α w` with a one-bit output `[b]` within `t` steps, `W` halts
  on the same input with `[b]` within `C · (t + |pairEncode α w| + 1)` steps (self-application:
  the coded machine runs on the very input that carries its code);
* every `DTIME T` language has a code `α` whose machine decides it within
  `c · (Ψ (T n) + 1)` steps, for a constant `c` (the normal form).

No clock, no uniformity in the code and no output beyond the one-bit verdict is required.
Deviation: the book uses that every machine has infinitely many codes; here one code is fixed
and the input is padded (`SelfSimulator.toDiagSimulator`), as in the received proof, because
the constant `C` depends on the code string. -/
structure SelfSimulator (Ψ : ℕ → ℕ) where
  /-- the self-application simulator -/
  W : FinTM Bool
  /-- the machine each code denotes -/
  decode : List Bool → FinTM Bool
  /-- per-code linear self-simulation of one-bit verdicts -/
  simulates : ∀ α : List Bool, ∃ C : ℕ, ∀ (w : List Bool) (b : Bool) (t : ℕ),
    (decode α).ComputesInTime (pairEncode α w) [b] t →
    W.ComputesInTime (pairEncode α w) [b] (C * (t + (pairEncode α w).length + 1))
  /-- the normal form: every `DTIME T` language has a coded decider within `c · (Ψ T + 1)` -/
  normalForm : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ (α : List Bool) (c : ℕ), ∀ x : List Bool,
      (decode α).ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x]
        (c * (Ψ (T x.length) + 1))

/-- **Input padding** [AB09, Theorem 3.1, proof]: a self-simulator with normal-form overhead
`Ψ` is a diagonal simulator, with the same machine, with overhead `Ψ t + n + 1`.

**Proof sketch.** For `L ∈ DTIME T` take the normal form's code `α` and constant `c`, and the
simulation constant `C` of `α`. For `n ≥ 2|α| + 2` the input
`x = pairEncode α 1^(n - 2|α| - 2)` has length `n`; `decode α` decides `L` on it within
`c (Ψ (T n) + 1)` steps, so `W` reproduces the verdict within
`C (c (Ψ (T n) + 1) + n + 1) ≤ C (c + 1) (Ψ (T n) + n + 1)` steps. -/
def SelfSimulator.toDiagSimulator {Ψ : ℕ → ℕ} (S : SelfSimulator Ψ) :
    DiagSimulator (fun t n => Ψ t + n + 1) where
  W := S.W
  simulates T L hL := by
    obtain ⟨α, c, hc⟩ := S.normalForm T L hL
    obtain ⟨C, hC⟩ := S.simulates α
    refine ⟨C * (c + 1), 2 * α.length + 2, fun n hn => ?_⟩
    have hx : (pairEncode α (List.replicate (n - (2 * α.length + 2)) true)).length = n := by
      simp only [length_pairEncode, List.length_replicate]; omega
    refine ⟨pairEncode α (List.replicate (n - (2 * α.length + 2)) true), hx, ?_⟩
    have h := hC _ _ _ (hc (pairEncode α (List.replicate (n - (2 * α.length + 2)) true)))
    rw [hx] at h
    apply h.mono
    have hle : c * (Ψ (T n) + 1) + n + 1 ≤ (c + 1) * (Ψ (T n) + n + 1) := by nlinarith
    calc C * (c * (Ψ (T n) + 1) + n + 1) ≤ C * ((c + 1) * (Ψ (T n) + n + 1)) :=
          Nat.mul_le_mul_left C hle
      _ = C * (c + 1) * (Ψ (T n) + n + 1) := by ring

/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** The case `W = diagSim` of `diagLangOf_mem_DTIME`, since `diagLang g` is
`diagLangOf diagSim g` by definition (`diagLang_eq_diagLangOf`): the clocked runner
`clockTM K diagSim`, with `K` the time-constructibility witness of `g`, decides it within
`(c_K + 15)(g n + 1)` steps. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) :=
  diagLangOf_mem_DTIME diagSim hg

/-- The polynomial bookkeeping of the received diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. Kept with its statement; the parameterized argument does its
bookkeeping in `oneTapeSelfSimulator`, `SelfSimulator.toDiagSimulator` and `sqDiagSimulator`,
and no declaration of this file uses this lemma. -/
lemma diag_cost_le (n T c₀ c₁ C : ℕ) :
    5 * n + 7 + C * (c₁ * (c₀ * T + 1) ^ 2 + 1) ≤
      (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) * (T + n + 1) ^ 2 := by
  have hX : 1 ≤ T + n + 1 := by omega
  have hX2 : T + n + 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hlin : c₀ * T + 1 ≤ (c₀ + 1) * (T + n + 1) := by nlinarith
  have hsq : (c₀ * T + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T + n + 1) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
  have hone : 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hinner : c₁ * (c₀ * T + 1) ^ 2 + 1 ≤ (c₁ * (c₀ + 1) ^ 2 + 1) * (T + n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith
  have hC := Nat.mul_le_mul_left C hinner
  nlinarith

/-! ### The received instance -/

/-- **The received self-simulator** [AB09, Theorem 3.1, proof; Claims 1.5–1.6]: `diagSim` is a
self-simulator for the codes of `code` (`decode α` the machine `code.decode α`), with the
one-work-tape normal form, whose overhead is the square `Ψ t = (t + 1)²`.

**Proof sketch.** *Simulation:* on `x = pairEncode α w`, `preTM` writes `pairEncode α x`
within `3|x| + 5` steps (`preTM_computes`, `scanPre_pairEncode_append`), and `univTM` simulates
the coded machine on `x` within `C (t + 1)` steps (`univTM_spec`); buffered composition adds
the intermediate length plus two, `|pairEncode α x| + 2 ≤ 2|x| + 2`
(`bufferedCompTM_computesInTime`): in all at most `(C + 7)(t + |x| + 1)` steps. *Normal form:*
a decider within `c₀ T` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`), then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), whose code `code.encode N` decodes back to `N`; and
`c₁ (c₀ T + 1)² ≤ c₁ (c₀ + 1)² ((T + 1)² + 1)`. -/
noncomputable def oneTapeSelfSimulator : SelfSimulator (fun t => (t + 1) ^ 2) where
  W := diagSim
  decode α := (code.decode α).toFinTM
  simulates α := by
    obtain ⟨C, hC⟩ := univTM_spec α
    refine ⟨C + 7, fun w b t h => ?_⟩
    have hU := (hC (pairEncode α w)).1 [b] t h
    have hP := preTM_computes (pairEncode α w)
    rw [scanPre_pairEncode_append α w] at hP
    have hD := bufferedCompTM_computesInTime preTM univTM hP hU
    apply hD.mono
    have h1 : (pairEncode α (pairEncode α w)).length ≤ 2 * (pairEncode α w).length := by
      simp only [length_pairEncode]; omega
    nlinarith
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n) hM
    obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
    refine ⟨code.encode N, c₁ * (c₀ + 1) ^ 2, fun x => ?_⟩
    rw [show code.decode (code.encode N) = N from code.toMachineCode.decode_encode N]
    apply ((hN x _ _).2 (h₁ x)).mono
    have hlin : c₀ * T x.length + 1 ≤ (c₀ + 1) * (T x.length + 1) := by nlinarith
    have hsq : (c₀ * T x.length + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T x.length + 1) ^ 2 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith

/-- The received overhead dominates the time: `t ≤ (t + n + 1)²` for all `t` and `n`. -/
theorem le_sq_overhead (t n : ℕ) : t ≤ (t + n + 1) ^ 2 := by
  have h : t + n + 1 ≤ (t + n + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
  omega

/-- **The received diagonal simulator**: `diagSim` with the overhead `(t + n + 1)²` of the
received theorem, from `oneTapeSelfSimulator` by input padding
(`SelfSimulator.toDiagSimulator`) and `(t + 1)² + n + 1 ≤ 2 (t + n + 1)²`. -/
noncomputable def sqDiagSimulator : DiagSimulator (fun t n => (t + n + 1) ^ 2) :=
  oneTapeSelfSimulator.toDiagSimulator.mono 2 (fun t n => by
    show (t + 1) ^ 2 + n + 1 ≤ 2 * (t + n + 1) ^ 2
    have h1 : (t + 1) ^ 2 ≤ (t + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : t + n + 1 ≤ (t + n + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _
    omega)

/-- The received diagonal simulator's machine is `diagSim`, by definition. -/
theorem sqDiagSimulator_W : sqDiagSimulator.W = diagSim := rfl

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** The case `sqDiagSimulator` of `DiagSimulator.diagLang_not_mem_DTIME`,
whose machine is `diagSim` (`sqDiagSimulator_W`). Its simulation clause is
`oneTapeSelfSimulator`'s, padded by `SelfSimulator.toDiagSimulator`: a decider `M` of
`diagLang g` within `c₀ T(n)` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`) and then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), with code `α = ⌞N⌟`. On `x = pairEncode α 1^(n - 2|α| - 2)`, of
length `n`, `preTM` and `univTM` reproduce `M`'s verdict `[χ(x)]` within `A (T n + n + 1)²`
steps, `A` depending on `M` only. At an `n` with `A (T n + n + 1)² ≤ g n` that verdict
contradicts the definition of `diagLang g`: if `χ(x) = true`, `diagSim` does not output
`[true]` within `g n`; if `χ(x) = false`, it does, against the uniqueness of its output
`[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T :=
  sqDiagSimulator.diagLang_not_mem_DTIME hT

end Complexity.TimeHierarchy

namespace Complexity

open TimeHierarchy

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the form supported by this
development: if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))` — i.e. for
every constant `A`, eventually `A · (f n + n + 1)² ≤ g n` — then
`DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): the overhead is quadratic
(`(f + n + 1)²` in place of `f log f`), owing to the one-work-tape normal form of
coded machines; `f` need not be time constructible; and the larger class is
`DTIME (g + 1)`, which differs from `DTIME g` only in the degenerate case `g 0 = 0`.

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of `DiagSimulator.time_hierarchy` at
`sqDiagSimulator`, with `t ≤ (t + n + 1)²` (`le_sq_overhead`). *Inclusion:* the hypothesis
with `A = 1` gives `f n ≤ g n` for `n ≥ N`; the finitely many smaller lengths are absorbed
into the constant, so `f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`.
*Strictness:* the diagonal language `diagLang g` lies in `DTIME (g + 1)`
(`diagLangOf_mem_DTIME`) but not in `DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`, whose
infinitely-often hypothesis follows from the eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of
`DiagSimulator.time_hierarchy_of_pos` at `sqDiagSimulator`: `c (g n + 1) ≤ 2c · g n` when
`g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the reverse inclusion is `Complexity.DTIME.mono`;
conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g :=
  sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg

end Complexity

/-! ### The book form: overhead `f log f` -/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- **The Hennie–Stearns normal-form overhead** [AB09, §1.7]:
`logOverhead t = (t + 1)(log₂(t + 1) + 1)`, the time bound of
`Turing.FinTM.two_work_tapes_binary` at a budget `t`, with `log₂` the floor logarithm
`Nat.log 2`. -/
def logOverhead (t : ℕ) : ℕ := (t + 1) * (Nat.log 2 (t + 1) + 1)

/-- The formula of `logOverhead`: `logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1)`, by
definition. -/
theorem logOverhead_eq (t : ℕ) : logOverhead t = (t + 1) * (Nat.log 2 (t + 1) + 1) := rfl

/-- **The diagonal overhead of the book form** [AB09, Theorem 3.1, proof]:
`logDiagOverhead t n = (t + n + 1)(log₂(t + n + 1) + 1)`, the `f log f` analogue of the
received overhead `(t + n + 1)²`. -/
def logDiagOverhead (t n : ℕ) : ℕ := (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)

/-- The formula of `logDiagOverhead`:
`logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1)`, by definition. -/
theorem logDiagOverhead_eq (t n : ℕ) :
    logDiagOverhead t n = (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) := rfl

/-- The book form's overhead dominates the time [AB09, Theorem 3.1, proof]:
`t ≤ logDiagOverhead t n` for all `t` and `n`. -/
theorem le_logDiagOverhead (t n : ℕ) : t ≤ logDiagOverhead t n := by
  rw [logDiagOverhead_eq]
  have h : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Input padding at the book form's overhead** [AB09, Theorem 3.1, proof]:
`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, the bound that turns the padded overhead of
`SelfSimulator.toDiagSimulator` at `logOverhead` into `logDiagOverhead`.

**Proof sketch.** `log₂` is monotone and `t + 1 ≤ t + n + 1`, so
`logOverhead t ≤ logDiagOverhead t n`; and `n + 1 ≤ t + n + 1 ≤ logDiagOverhead t n`. -/
theorem logOverhead_add_le (t n : ℕ) : logOverhead t + n + 1 ≤ 2 * logDiagOverhead t n := by
  rw [logOverhead_eq, logDiagOverhead_eq]
  have hlog : Nat.log 2 (t + 1) ≤ Nat.log 2 (t + n + 1) := Nat.log_mono_right (by omega)
  have h1 : (t + 1) * (Nat.log 2 (t + 1) + 1) ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : t + n + 1 ≤ (t + n + 1) * (Nat.log 2 (t + n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- **Constant-factor absorption** of the Hennie–Stearns overhead [AB09, §1.7]:
`logOverhead (c₀ T) ≤ (c₀ + 1)(log₂(c₀ + 1) + 2) · logOverhead T`, so a decider within `c₀ T`
normal-forms within a constant multiple of `logOverhead T`.

**Proof sketch.** Let `m = log₂(c₀ + 1) + 1`, so `c₀ + 1 < 2^m`, and `T + 1 < 2^(log₂(T + 1) + 1)`.
Then `c₀ T + 1 ≤ (c₀ + 1)(T + 1) < 2^(m + log₂(T + 1) + 1)`, so
`log₂(c₀ T + 1) ≤ log₂(T + 1) + m` and `log₂(c₀ T + 1) + 1 ≤ (m + 1)(log₂(T + 1) + 1)`;
multiply by `c₀ T + 1 ≤ (c₀ + 1)(T + 1)`. -/
theorem logOverhead_mul_le (c₀ T : ℕ) :
    logOverhead (c₀ * T) ≤ (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead T := by
  rw [logOverhead_eq, logOverhead_eq]
  set m := Nat.log 2 (c₀ + 1) + 1 with hm
  set l := Nat.log 2 (T + 1) with hl
  have hc : c₀ + 1 < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) _
  have hT : T + 1 < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1 : c₀ * T + 1 ≤ (c₀ + 1) * (T + 1) := by nlinarith
  have h2 : (c₀ + 1) * (T + 1) < 2 ^ m * 2 ^ (l + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hc hT
  have hlog : Nat.log 2 (c₀ * T + 1) < m + (l + 1) := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    rw [pow_add]
    exact lt_of_le_of_lt h1 h2
  have h3 : Nat.log 2 (c₀ * T + 1) + 1 ≤ (m + 1) * (l + 1) := by nlinarith
  calc (c₀ * T + 1) * (Nat.log 2 (c₀ * T + 1) + 1)
      ≤ ((c₀ + 1) * (T + 1)) * ((m + 1) * (l + 1)) := Nat.mul_le_mul h1 h3
    _ = (c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * ((T + 1) * (l + 1)) := by rw [hm]; ring

/-- **The arithmetic of the book form** [AB09, Theorem 3.1]: for `2 ≤ n ≤ f`,
`logDiagOverhead f n ≤ 12 · f · log₂ f`.

**Proof sketch.** `f ≥ 2`, so `log₂ f ≥ 1`. From `n ≤ f`: `f + n + 1 ≤ 3f`, and
`f + n + 1 ≤ 4f`, so `log₂(f + n + 1) ≤ log₂(4f) = log₂ f + 2` and
`log₂(f + n + 1) + 1 ≤ log₂ f + 3 ≤ 4 log₂ f`. Multiply: at most `3f · 4 log₂ f`. -/
theorem logDiagOverhead_le_book {f n : ℕ} (hn : 2 ≤ n) (hf : n ≤ f) :
    logDiagOverhead f n ≤ 12 * (f * Nat.log 2 f) := by
  rw [logDiagOverhead_eq]
  have hf2 : 2 ≤ f := le_trans hn hf
  have hlog1 : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by norm_num) (by simpa using hf2)
  have h3 : f + n + 1 ≤ f * 2 * 2 := by omega
  have hlog : Nat.log 2 (f + n + 1) ≤ Nat.log 2 f + 2 := by
    calc Nat.log 2 (f + n + 1) ≤ Nat.log 2 (f * 2 * 2) := Nat.log_mono_right h3
      _ = Nat.log 2 f + 2 := by
        rw [Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  have hA : f + n + 1 ≤ 3 * f := by omega
  have hB : Nat.log 2 (f + n + 1) + 1 ≤ 4 * Nat.log 2 f := by omega
  calc (f + n + 1) * (Nat.log 2 (f + n + 1) + 1) ≤ (3 * f) * (4 * Nat.log 2 f) :=
        Nat.mul_le_mul hA hB
    _ = 12 * (f * Nat.log 2 f) := by ring

/-- The book form's hypothesis gives the diagonal one: if `n ≤ f n` and, for every `A`,
eventually `A · f n log₂ f n ≤ g n`, then for every `A`, eventually
`A · logDiagOverhead (f n) n ≤ g n` (`logDiagOverhead_le_book` at the constant `12 A`, for
`n ≥ 2`). -/
private theorem eventually_logDiagOverhead_le {f g : ℕ → ℕ} (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * logDiagOverhead (f n) n ≤ g n := by
  intro A
  obtain ⟨N, hN⟩ := hfg (12 * A)
  refine ⟨max N 2, fun n hn => ?_⟩
  calc A * logDiagOverhead (f n) n ≤ A * (12 * (f n * Nat.log 2 (f n))) :=
        Nat.mul_le_mul_left A (logDiagOverhead_le_book (le_of_max_le_right hn) (hf n))
    _ = 12 * A * (f n * Nat.log 2 (f n)) := by ring
    _ ≤ g n := hN n (le_of_max_le_left hn)

/-- **The fixed two-work-tape representation scheme** of the book form [AB09, §1.4] (any
scheme works; `Turing.exists_effectiveMachineCode2` provides one). -/
noncomputable def code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2

/-- The definition of `code₂`: `code₂ = Classical.choice Turing.exists_effectiveMachineCode2`. -/
theorem code₂_eq : code₂ = Classical.choice exists_effectiveMachineCode2 := rfl

/-- **The two-tape self-simulator** [AB09, Theorem 3.1, proof; §1.4.1 and §1.7]: the
self-application universal machine for the two-work-tape codes of `code₂`
(`Turing.exists_selfUniversalK` at `k = 2`; `decode α` the machine `code₂.decode α`), with the
Hennie–Stearns normal form, whose overhead is `logOverhead`.

**Proof sketch.** *Simulation:* for each code `α`, `Turing.exists_selfUniversalK` gives a
constant `C` such that whenever the machine coded by `α` (the same bundled machine in the
`k`-tape view, `Turing.EffectiveMachineCode2.toK_toFinTM`) halts on `pairEncode α w` with `[b]`
within `t` steps, the universal machine does so within
`C (t + 1) ≤ C (t + |pairEncode α w| + 1)` steps. *Normal form:* a decider within `c₀ T`
becomes a two-work-tape binary machine within `c₁ · logOverhead (c₀ T)`
(`Turing.FinTM.two_work_tapes_binary`), then a coded machine `N` with the same runs
(`Turing.exists_code2TM`), whose code `code₂.encode N` decodes back to `N`; and
`c₁ · logOverhead (c₀ T) ≤ c₁ (c₀ + 1)(log₂(c₀ + 1) + 2) (logOverhead T + 1)`
(`logOverhead_mul_le`). -/
noncomputable def twoTapeSelfSimulator : SelfSimulator logOverhead where
  W := Classical.choose (exists_selfUniversalK 2 code₂.toK)
  decode α := (code₂.decode α).toFinTM
  simulates α := by
    obtain ⟨C, -, hC⟩ := Classical.choose_spec (exists_selfUniversalK 2 code₂.toK) α
    refine ⟨C, fun w b t h => ?_⟩
    have h' : (code₂.toK.toFinTM α).ComputesInTime (pairEncode α w) [b] t := by
      rw [EffectiveMachineCode2.toK_toFinTM]; exact h
    exact ((hC w).1 [b] t h').1.mono (Nat.mul_le_mul_left C (by omega))
  normalForm T L := by
    rintro ⟨c₀, M, hM⟩
    obtain ⟨M₁, c₁, hk, h₁⟩ := two_work_tapes_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) (fun n => c₀ * T n)
      ((computesFunInTime_iff _ _ _).2 hM)
    obtain ⟨N, hN⟩ := exists_code2TM M₁ hk
    refine ⟨code₂.encode N, c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)), fun x => ?_⟩
    show (code₂.decode (code₂.encode N)).toFinTM.ComputesInTime _ _ _
    rw [code₂.toMachineCode2.decode_encode N]
    apply ((hN x _ _).2 ((computesFunInTime_iff _ _ _).1 h₁ x)).mono
    calc c₁ * ((c₀ * T x.length + 1) * (Nat.log 2 (c₀ * T x.length + 1) + 1))
        = c₁ * logOverhead (c₀ * T x.length) := by rw [logOverhead_eq]
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2) * logOverhead (T x.length)) :=
          Nat.mul_le_mul_left c₁ (logOverhead_mul_le c₀ _)
      _ ≤ c₁ * ((c₀ + 1) * (Nat.log 2 (c₀ + 1) + 2)) * (logOverhead (T x.length) + 1) := by
          rw [Nat.mul_assoc c₁]
          exact Nat.mul_le_mul_left c₁ (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- The two-tape self-simulator's machine is the self-application universal machine of
`code₂` at `k = 2`, by definition. -/
theorem twoTapeSelfSimulator_W :
    twoTapeSelfSimulator.W = Classical.choose (exists_selfUniversalK 2 code₂.toK) := rfl

/-- The two-tape self-simulator's code `α` denotes the machine `code₂.decode α`, by
definition. -/
theorem twoTapeSelfSimulator_decode (α : List Bool) :
    twoTapeSelfSimulator.decode α = (code₂.decode α).toFinTM := rfl

end Complexity.TimeHierarchy

namespace Complexity

open TimeHierarchy

/-- **The Time Hierarchy Theorem at overhead `f log f`** [AB09, Theorem 3.1], with the input
length kept: if `g` is time constructible and
`(f(n) + n + 1) log₂(f(n) + n + 1) = o(g(n))` — i.e. for every constant `A`, eventually
`A · (f n + n + 1)(log₂(f n + n + 1) + 1) ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`. No
hypothesis on `f` is needed; `Complexity.time_hierarchy_book` is the book's form.

**Proof sketch.** The case `Φ = logDiagOverhead` of `DiagSimulator.time_hierarchy`, at the
two-tape self-simulator `twoTapeSelfSimulator` padded by `SelfSimulator.toDiagSimulator`
(overhead `logOverhead t + n + 1`) and weakened by `DiagSimulator.mono`
(`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`, `logOverhead_add_le`), with
`t ≤ logDiagOverhead t n` (`le_logDiagOverhead`). *Inclusion:* `f n ≤ g n` eventually, the
smaller lengths absorbed into the constant. *Strictness:* the diagonal language of the
two-tape universal machine lies in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in
`DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`). -/
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg fun A => (hfg A).imp fun _ hN n hn => by
      rw [logDiagOverhead_eq]; exact hN n hn

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the book's form: if `g` is time
constructible, `n ≤ f(n)` for all `n`, and `f(n) log₂ f(n) = o(g(n))` — i.e. for every
constant `A`, eventually `A · f n · log₂ f n ≤ g n` — then `DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): `n ≤ f(n)` in place of time
constructibility of `f` (every time-constructible `f` satisfies it); `log₂` is the floor
logarithm `Nat.log 2`, which vanishes at `f n ≤ 1`, hence only at `n ≤ 1` here, outside the
eventual hypothesis; and the larger class is `DTIME (g + 1)`, which differs from `DTIME g` only
in the degenerate case `g 0 = 0` (`Complexity.time_hierarchy_book_of_pos`).

**Proof sketch.** For `n ≥ 2`, `n ≤ f n` gives
`(f n + n + 1)(log₂(f n + n + 1) + 1) ≤ 12 · f n · log₂ f n` (`logDiagOverhead_le_book`), so
the hypothesis at `12 A` gives `A · logDiagOverhead (f n) n ≤ g n` eventually; conclude as in
`Complexity.time_hierarchy_log`, by `DiagSimulator.time_hierarchy` at the two-tape
self-simulator `twoTapeSelfSimulator`. -/
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy
    le_logDiagOverhead hg (eventually_logDiagOverhead_le hf hfg)

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1], in the book's
form: as `Complexity.time_hierarchy_book`, with the larger class exactly `DTIME g` when `g`
never vanishes — the book's `DTIME(f) ⊊ DTIME(g)`.

**Proof sketch.** As `Complexity.time_hierarchy_book`, through
`DiagSimulator.time_hierarchy_of_pos` in place of `DiagSimulator.time_hierarchy`:
`c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) = DTIME g`. -/
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g :=
  (twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy_of_pos
    le_logDiagOverhead hg hpos (eventually_logDiagOverhead_le hf hfg)

end Complexity
```

## ===== TCSlib/Complexity/TimeHierarchy.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TimeHierarchy.ClockMachine
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.TimeHierarchy.Separation

/-!
# The Time Hierarchy Theorem

[AB09, §3.1, Theorem 3.1]: more time decides more languages. The headline results are
`Complexity.time_hierarchy_book` (if `g` is time constructible, `n ≤ f(n)` and
`f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g + 1)` — the book's overhead, see
`TimeHierarchy.Diagonal` for all divergences), the quadratic-overhead form
`Complexity.time_hierarchy` (`(f(n) + n + 1)² = o(g(n))`, no hypothesis on `f`), and its
consequence `Complexity.P_ssubset_EXP` (`P ⊊ EXP`).

## Contents

- `TimeHierarchy.ClockMachine`: the clocked runner `clockTM K W` (budget word from `K` on a
  binary counter tape; `W` run step by step against it) and its setup phases
- `TimeHierarchy.ClockLoop`: the counter loop with amortized cost analysis and the runner's
  specification `clockTM_spec`
- `TimeHierarchy.CodePrefix`: the code-prefix duplication machine `preTM`
  (`pairEncode α w ↦ pairEncode α (pairEncode α w)`) and timed partial composition
- `TimeHierarchy.Diagonal`: the diagonal language, its upper and lower bounds, and
  `Complexity.time_hierarchy` [AB09, Theorem 3.1]
- `TimeHierarchy.Separation`: `2ⁿ` is time constructible, `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)`,
  and `P ⊊ EXP`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1.)
-/
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity
```
