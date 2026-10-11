# External audit pack — B7 statement mini-phase (P4.4b): input access, the oracle-input simulator, query reshapings

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). B7 is
the deterministic-logspace cluster. Its targets were stated and audited at
phase P4.4: `audits/ch4-p44-findings.md` and `audits/ch4-p44-resolutions.md`,
attached. The targets are:

- `ImplicitlyLogspaceComputable.comp` (composition, [AB09] Lemma 4.17(1));
- `LogspaceReducible.trans`;
- `mem_LOGSPACE_of_logspaceReducible` (Lemma 4.17(2));
- `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE`;
- `multLang_mem_LOGSPACE`.

**Why a statement mini-phase.** Fill research found that the received
logspace program layer (`SpaceComplexity/Machines/*`, a colleague's audited
compiler, `LogProg.compile_space`) cannot host the audited routes. Two
capabilities are missing:

- **G1, oracle-served input.** A call presents its callee with a
  *physically* laid-out virtual input (the whole host input, or its leading
  `1`-run, plus register words). Nothing serves a callee's input symbols
  through further calls.
- **G2, random access to a non-unary input.** The ARM input instructions
  presuppose unary-first inputs.

This PR (#24, `integrate/b7-statements`, commit `db99af44`) lands the
missing contracts as **statements with sketches**, plus proved helpers. It
records two **route changes** to audited statements in
`audits/ch4-p44-resolutions-addendum.md`:

- T3 goes direct, via the new N2;
- `comp` is derived from N2 and N4.

**No proof is under audit except the small proved helpers. What you audit is
the statements:** are they true, adequately strong for their consumers, free
of vacuity, and well placed? The gate closes on zero blockers and zero majors.

## What is proposed (verify)

| File (new unless noted) | Declarations | Status |
|---|---|---|
| `Logspace/InputAccess.lean` | the input-read fragment `LogProg.readIn_run` (exits in state `ex x[i]?` with everything else restored; head range `[-1, \|bits(\|x\|+1)\|]`, independent of `i`); **N1** `implicitlyLogspaceComputable_id`; `inputBitLang`/`inputLenLang` and their membership corollaries; `LogProg.vword_whole₁`; `indicator_indexLang_pairEncode` | 2 sorried (`readIn_run`, N1); the rest proved |
| `Logspace/PreimageHost.lean` | the oracle-input simulator: the program `LogProg.OIS.prog M` (**defined**), with run contract `OIS.run` and space contract `OIS.compile_decides`; the clamping table `OIS.nextPh`; **N2** `mem_LOGSPACE_preimage (hf : ImplicitlyLogspaceComputable f) (hC : C ∈ LOGSPACE) : {x \| f x ∈ C} ∈ LOGSPACE` | 3 sorried (`OIS.run`, `OIS.compile_decides`, N2); the program and table are definitions |
| `Logspace/QueryReshape.lean` | **N3** `implicitlyLogspaceComputable_dropIdx`; **N4** `ImplicitlyLogspaceComputable.compQ`; proved helpers: `dropIdx`, `dropIdx_pairEncode`, `compQ`, `compQ_pairEncode`, `pairEncode_ne_nil`, `mem_indexLang_compQ_iff`, `compQ_length_le` | 2 sorried (N3, N4) |
| `Logspace/Reductions.lean` (changed) | import `QueryReshape`; `comp`'s docstring corrected (its sketch claimed a received capability that does not exist) | statements unchanged; 4 targets still sorried |
| `Logspace/Mult.lean` (changed) | import `InputAccess`; docstring corrected (the cited parse toolkit reads only `⟨1ⁿ, ⟨u, w⟩⟩`; the acceptance condition is Q8's) | statement unchanged; 1 target sorried |
| `SpaceComplexity.lean` (facade) | the three new modules | — |

The derivations of the frozen targets from the new contracts elaborate in the
attached pre-ship probe:

- T3 is N2 at `C`;
- `comp` combines N2 with N4: the query languages of `g ∘ f` are preimages of
  `g`'s along `compQ f`;
- T2 and T5 are logic.

## Brief for the auditor

1. **Truth.** Blind-restate every sorried statement from its signature, then
   decide whether it is true as stated. The statements are N1–N4,
   `readIn_run`, `OIS.run` and `OIS.compile_decides`. Give the argument, or a
   counterexample. N2 is [AB09] Lemma 4.17(2) in preimage form; N1 is
   logspace random access.
2. **The fragment and the engine as reusable contracts.** These two are
   meant for later logspace programs: the PATH reduction's transducer, matrix
   indexing, and the NL side.
   - **`readIn_run`.** Is the frame clause ("everything else restored")
     exactly right? Is the head range right, including at `i ≥ |x|` and
     `x = []`?
   - **`OIS.run`.** It requires the oracle laws only on *genuine* queries:
     length at `i ≤ |v|`, bit at `i < |v|`. Is that both sufficient and
     necessary? Is the work-register range `±S` right, with `S` the space up
     to time `t` rather than up to the first halt?
   - **`OIS.nextPh`.** Does the clamping table match `moveInputPos` at both
     boundaries, including `v = []`?
   - **`OIS.compile_decides`.** Should its radius parameter `B` be a
     monotone space function instead?
3. **Adequacy.** Do N1–N4 suffice for all five frozen targets, by the
   routes in the addendum? Do they leave nothing implicit that the fill
   would have to invent, such as a missing length bound, an unstated
   canonicality, or the behaviour on malformed queries?
4. **The route changes.** Are the addendum's two route changes sound
   replacements for the audited P4.4 routes, and is the original statement
   gate's reasoning preserved where it still applies?
5. **Vacuity and degenerate cases.** Check, in particular:
   - each oracle and engine contract for vacuous satisfaction (for example,
     an empty language, or an engine whose run contract holds because
     nothing ever halts);
   - `f` constant, and `C` empty or everything;
   - `x = []`;
   - malformed `⟨x, bits i⟩` queries.
6. **Placement and naming.** The files are campaign-owned under `Logspace/`
   and add declarations to the colleague's `Complexity.LogProg` namespace.
   Is that acceptable, or should they take their own namespace? Is N1
   better stated as `ImplicitlyLogspaceComputable id` or as the two
   memberships?
7. **Docstrings.** Check the two corrected sketches, and every new docstring
   for accuracy. T3's docstring still describes the superseded `χ_C` route;
   say whether to correct it now or by a flagged appendix at fill.
8. **Duplication.** No new copy-text pair appeared (53 before and after).
   Is any proved helper a re-proof of a received lemma?
9. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/b7-statements-sweep-{before,after}.log`): the
  8 new, changed and downstream modules exit 0 with 0 errors. The sorry
  warnings are exactly the 7 new statements plus the 5 existing B7 targets
  (and `Path`'s 2 and Immerman–Szelepcsényi's 3, unchanged).
* **Probe** (`audits/evidence/b7/B7StatementsProbe.lean.txt`): 0 errors, and
  no sorry of its own. It runs `readIn_run` on a concrete program and `OIS`
  on a concrete decider, and derives T2, T3, T5 and `comp`. Its axiom prints
  (`audits/logs/b7-statements-axioms.log`) show `sorryAx` only through the
  12 sorried declarations; the proved helpers lie within the standard triple.
* **Freeze** (`…-declfreeze.log`): no existing statement changed.
* **Lint** (`…-stylelint.log`): 0 FAIL, 0 WARN.
* **Screen** (`…-screen-{before,after}.txt`): 53 pairs before and after. The
  screen script is attached.
* **Inputs.** All new and changed sources, the received `Machines/` layer the
  contracts cite, `ImplicitPoly.lean` (the engine's template), and
  `SpaceComplexity/Basic.lean` are attached.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b7-statements-findings.md`.

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

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), and the program layers (`LogProg.ARM`,
`CounterProg`) where a register-level description suffices. Before writing a transition
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
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

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
  inherit the list.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, all committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`):

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `audits/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree).
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
`audits/ch2-phase1-{pack,findings,reaudit-…,round3-…,resolutions}.md` loop.

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
   merge, flagged for the next audit.
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.

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
  sketch-before-sorry, file sizes, `## References`, facade coverage. Campaign
  baseline: zero FAIL (legacy pre-campaign files outside the audited surface are
  tolerated and listed).
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

## ===== audits/TEMPLATE.md =====

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

## ===== audits/duplication-ledger.md =====

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

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.

## ===== arm-extensions-proposal.md =====

# Proposal: extending the `LogProg` ARM layer for chapters 3-4

*For Jason (Hydroxyi) — from the Arora-Barak chapters 3-4 campaign
(branch `complexity/arora-barak-ch3-4`; Seyoon). This is the colleague-sync
item recorded in `AroraBarakChapters3-4Plan.md` §2.5/§4b and `backlog.md`
§2. Your `SpaceComplexity/Machines/` tree is co-owned per our CH34-Q2
agreement ("extend in place"), so nothing below gets drafted without your
sign-off on the interfaces.*

## Why

Chapter 4 is mostly space-bounded machine work, and the campaign's recorded
strategy is to write those algorithms as **register programs, not
hand-built transition tables** — your `LogProg.ARM` + `compile_space` is
the substrate. Three gaps stand between the current layer and the
chapter-4 fills.

## The three proposed extensions

Each would be its own audited statement phase (our usual loop: sorried
statements with sketches → external audit gate → fill), drafted by us
against interfaces you approve, or co-drafted — your call.

1. **A nondeterministic ARM.** A `choose` instruction (binary
   nondeterministic branch) compiling to `FinNDTM`, with the
   `compile_space` theorem carried over, and `arm_decides`-style bridges
   to `NSPACE`/`NL`. First customers: `PATH ∈ NL`, the
   Immerman-Szelepcsényi inductive counting, and Corollary 4.21.

2. **A polynomial-width ARM variant.** Registers of `poly(n)` bits rather
   than `O(log n)`, for the `PSPACE`-level algorithms: `TQBF ∈ PSPACE`,
   `NP ⊆ PSPACE`, and Savitch at the polynomial level. Structurally
   either a generalization of `compile_space` (width as a parameter) or a
   sibling compiler — we have no preference and would follow your sense of
   which fits the existing proof architecture better.

3. **A configuration codec as a program.** Encode a fixed machine's
   configurations — work tapes windowed to `s` cells, the input head as a
   register — in `O(s)`-bit register contents, with a successor/adjacency
   test as an ARM program. This is shared by Theorem 4.2(iii), Savitch,
   Theorem 4.18, Corollary 4.21, and the `TQBF`-hardness emitter. The
   counting half would extend your deterministic `ConfigCount` to NDTMs,
   adapting (citing, never vendoring) cslib's upstream
   `MultiTape/ConfigBound.lean` design — cslib targets a newer Lean, so
   nothing ports directly.

## A design question on `CounterProg`

The `2^O(S)`-time searches need to read the input at a simulated head
position, but `CounterProg`'s input access is one-way (`rd` only
advances). Two options we see: ARM-style indexed input access, or a rewind
instruction. Do you have a preference (or a third option)?

## Two provenance questions (asked, not asserted)

Our 2026-10-08 citation audit flagged two design similarities purely so
citations can be added **if** applicable — no assertion intended:

* Did the `LogProg` compiler draw on Édouard Bonnet's lax-434930
  `classical-complexity` (`TimeCompiler` module)?
* Does `ConfigCount.core` relate to cslib `ConfigBound`'s `Cfg.core`
  (upstream, Sept 2026)?

A one-line "no" settles both.

## Process and housekeeping

* Our side runs a statement-freeze + external-audit discipline
  (`workflow.md`), including a duplication policy (`policy.md`,
  **Duplication**): anything we add to your tree arrives as audited
  statements with named owners, never ad-hoc copies.
* Separately: `main` has moved a lot recently (your `BooleanAnalysis`
  work) — when we sync, it would be good to also agree on merge
  coordination for the eventual chapter-3/4 PRs (one per chapter, each
  carrying sweep + axiom evidence, per the recorded plan).

**What we need from you**: a yes/no/modify on each extension's interface
sketch above, the `CounterProg` preference, and the two one-line
provenance answers. Full detail: `AroraBarakChapters3-4Plan.md` §2.5
(design), §4b (where this sits in the roadmap), `backlog.md` §2 (the
tracking entry), `machine-library-design.md` (the construction-layer
conventions anything new would follow).

## Addendum (2026-10-11): two deterministic gaps found while preparing B7

While preparing the deterministic-logspace cluster (Lemma 4.17, `MULT ∈ L`), we found two gaps
in the deterministic layer that the list above does not mention. Your P0 notes already flag
the second: general composition is pending.

1. **Random access to a general input.** The ARM input instructions assume unary-first inputs
   `⟨1ⁿ, …⟩`. A call's first segment is the whole input or its leading `1`-run, so an ARM
   cannot read a non-unary input at a register-held position.
2. **Oracle-served virtual input.** A call cannot serve a decider's input symbols through
   further calls. This is the Fig. 4.3 shape behind Lemma 4.17.

We are building both as **campaign-owned library fragments under `SpaceComplexity/Logspace/`**,
on top of your compiler (`compile_space`, the bank, and the increment, decrement, equality,
clear and rewind fragments). Nothing in `Machines/` changes:

- `InputAccess.lean`: `LogProg.readIn_run` and `implicitlyLogspaceComputable_id`;
- `PreimageHost.lean`: the oracle-input simulator `LogProg.OIS` and `mem_LOGSPACE_preimage`.

They are in a statement gate now (`audits/ch4-p44-resolutions-addendum.md`). If you would
rather host them in `Machines/`, we are glad to move them.

**One suggestion for extension 1 (the nondeterministic ARM).** Would you consider giving it an
oracle-input call mode natively? That is, a read whose input symbol is served by a
deterministic decider queried on `⟨x, i⟩`. Then a later `NL` downward-closure engine
(`mem_NL_of_logspaceReducible`, P4.4 audit note 6) would not need to duplicate `OIS`. As
always, the interface is your call.

## ===== audits/ch4-p44-findings.md =====

# P4.4 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 2 minors, 5 notes.** All six definitions and eleven sorried statements were checked. The two defects are in the `mem_LOGSPACE_of_logspaceReducible` proof sketch; neither requires changing its statement. This is a mathematical statement audit, not a Lean proof certification or permission to treat the pending constructions as proved.

The supplied bundle's SHA-256 is exactly `899d3c43d6576dff48f96dccaee4b56370699563ee03b2cc010eea96072698ca`. The declared baseline is `200f4693a40f30302efed75a4e23ac31216172b7`. The P4.2 surface is treated as supplied, with the upstream observation explicitly prefixed below. This verdict does not close P4.2 or the routine-infrastructure gate.

**Findings**

Paths in this table are relative to `TCSlib/Complexity/SpaceComplexity/`, except where indicated. Line numbers refer to the extracted attachment, not the enclosing bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Logspace/Reductions.lean:106–108` · `mem_LOGSPACE_of_logspaceReducible` | The characteristic function's length language is total. | Its output has length one, so a genuine query is accepted iff `i < 1`, equivalently `i = 0`. The query `pairEncode x [true]`, representing index 1, is rejected for every `x`. Malformed query strings are also rejected. | Say that the length language is exactly `{pairEncode x [] : x : List Bool}`, a regular language. Distinguish this from a total **decider** for that language. |
| 2 | minor | `Logspace/Reductions.lean:110–113` · same declaration | Specializing index 0 is a fixed-suffix specialization. | `pairEncode x [] = dbl x ++ [false,true]`, not `x ++ [false,true]`. For example, input `[true]` must be presented to the query machine as `1101`, not `101`. | Name a fixed-index **paired-input** specialization. Prove it directly by simulating the query decider on the doubled virtual input with its separator; do not invoke the downward-closure theorem being proved. |
| 3 | note | `Logspace/Reductions.lean:76–88` · `ImplicitlyLogspaceComputable.comp` | The virtual-input argument supplies both query languages. | Correct, including empty outputs, but the actual virtual input is `pairEncode (f x) (Nat.bits i)`. Query indices are unbounded in the definition; an arbitrary binary index cannot simply be copied into logarithmic workspace. | Carry malformed-query rejection, index-length/overflow handling, the paired layout, and the length-query boundary test into the fill. Question 2 gives a sufficient ledger. No signature change. |
| 4 | note | `Logspace/Path.lean:111–129` · `PATH_NLComplete`; plan's P4.4 row | Accepting normalization discharges the P0 unique-terminal caveat. | It is a sound **planned** discharge, explicitly listed as a fill obligation. The received `cleanTM` discipline alone is insufficient: the P0 report records that it does not reset the input head. Normalization also changes the machine and potentially its space constant. | Prove preservation of acceptance, all-branch halting, and space; blank all work tapes, park all work heads **and the input head**, preserve the output summary, and use the normalized machine's count/window. Until then, describe the caveat as assigned here, not already proved closed. |
| 5 | note | `Logspace/ImmermanSzelepcsenyi.lean:60–79` · `compl_PATH_mem_NL` | The counting verifier uses one read-once choice word. | Sound with sequentially regenerated path certificates. The negative test must check `A u v = false`, where `u` is enumerated from the previous ball; strict ordering and exact previous counts are indispensable. | Make these predicates and the complete outer enumeration explicit in the fill brief. Include canonical field validation and accept its failure before counting. Question 6 supplies the invariant and stream layout. |
| 6 | note | `Logspace/ImmermanSzelepcsenyi.lean:85–91` · `NL_eq_coNL` | Downward closure of `NL` follows from virtual-input simulation. | True, but not a consequence of the deterministic downward-closure statement alone. The simulation must preserve nondeterministic acceptance and all-branch halting while deterministic query subroutines consume ignored choice bits. | Recommend an additive `mem_NL_of_logspaceReducible` contract before fill. Its promotion is not required to pass this gate: the pack and workflow explicitly permit this named fill obligation. |
| 7 | note | `[P4.2] ConfigGraph.lean` · `coreSum`, `CfgStep`, `configBound`, `reflTransGen_cfgStep_iff` | These declarations are the configuration-graph surface used by P4.4. | The declarations are consistent, but `CfgStep` is on full configurations and `coreSum` is not itself a finite numbered graph. A count and a full-configuration reachability dictionary do not alone provide a numbered-graph codec or path-lifting theorem. | No correction to these signatures is requested. The P4.4 consumer must supply the bounded codec, reject/omit transitions leaving its window, and prove path projection and lifting using `coreSum_stepWith`. Do not claim those interfaces are already exported by P4.2. |

**Evidence and source boundary**

The bundle contains 24 attachments. A comment-stripped inventory of the four target modules confirms exactly six `def`s, eleven theorem declarations, eleven `sorry`s, and the scoped `≤ₗ` notation. Their per-file counts agree with the pack: Reductions 2/5, Path 3/2, Immerman–Szelepcsényi 0/3, Mult 1/1 (definitions/statements).

The supplied sweep names the four modules and the facade, records the declared revision at its start, contains eleven admission warnings and no `error:` lines, and ends with `P4.4_SWEEP_DONE`. The style log reports zero failures/warnings over 42 files. These textual attestations agree with the pack. Neither `lean` nor `lake` is available on PATH here, and the bundle is not a Git checkout: I did not independently elaborate, inspect fresh `.olean`s, reproduce lint, or verify `git diff ec400dc5 200f4693`. The raw NDTM implementation, `ConfigCount` codec implementation, and cited `Machines/*` infrastructure are not separate attachments; their relevant supplied interfaces and the closed-context attestations were used. No GitHub interaction or source modification was performed.

The comparison source was the **2009 book itself**, read from the [AB09 PDF mirror](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf), not the differently numbered 2007 draft. Printed-page references:

| Source | Comparison baseline |
|---|---|
| §4.1.2, p. 82, Example 4.7 and (4.1) | Multiplication is in deterministic logspace; bounded nondeterministic walks decide directed reachability. |
| Definition 4.16, Lemma 4.17, Figure 4.3, pp. 88–89 | Polynomial output length plus logspace bit/length queries define reductions; composition and deterministic downward closure hold. |
| Theorem 4.18, p. 89 | Configuration graphs give `NL`-hardness of `PATH`. |
| Definition 4.19, p. 90 | Polynomial read-once certificates characterize `NL`. |
| Theorem 4.20 and Corollary 4.21, pp. 91–92 | Inductive counting gives complement closure, including constructible bounds above logarithmic space. |

The following are independent checks of the supplied formal surface and its implementation obligations, not claims of completed Lean constructions.

**Definition restatements from the Lean bodies**

The received interface must be expanded first. `ImplicitlyLogspaceComputable f` is precisely the conjunction

\[
\begin{aligned}
&\exists C,c\in\mathbb N\;\forall x,\quad |f(x)|\le C(|x|+1)^c,\\
&\{\operatorname{pairEncode}(x,\operatorname{bits}(i)):
                 (f(x)).\operatorname{getD}(i,\mathrm{false})=\mathrm{true}\}
       \in\mathrm{LOGSPACE},\\
&\{\operatorname{pairEncode}(x,\operatorname{bits}(i)):i<|f(x)|\}
       \in\mathrm{LOGSPACE}.
\end{aligned}
\]

Each set has existential membership over genuine encodings: all malformed pairs and noncanonical index representations are excluded. Indices begin at zero; `bits` is canonical little-endian binary, with `bits 0 = []`. The bit query returns false outside the output; the length query separately distinguishes a zero bit from absence. `LOGSPACE` measures workspace against the **entire encoded query's length**.

| Definition | Mathematical restatement | Fidelity check |
|---|---|---|
| `LogspaceReducible B C` | Some total string function satisfying all three conditions above has `x ∈ B ↔ f x ∈ C` for every string `x`. | Correct many-one direction and quantifiers. The two inherited normalizations are discussed in question 1. |
| `NLComplete C` | `C ∈ NL`, and every `B ∈ NL` has such a reduction to `C`. | Both membership and hardness are required; no nontriviality hypothesis is hidden. |
| `GraphReach A s t` | There is a finite sequence of directed edges `A u v = true` from `s` to `t`, allowing zero edges. | Correct reflexive directed reachability, irrespective of self-loops. |
| `encodePATH n A s t` | Pair the all-true word of length `n` with a pair of the row-major `n × n` Boolean matrix and the pair of canonical endpoint representations. | Row `u`, column `v` has matrix index `u*n+v`; the dependent endpoint types enforce `n > 0`. |
| `PATH` | A string belongs exactly when it equals an encoding of some such graph and endpoints with `GraphReach A s t`. | No decoder fallback; malformed strings are outside the language. The witnesses cannot disagree about the decoded graph. |
| `multLang` | A string belongs exactly when it is the nested paired encoding of canonical binary representations of two naturals and their product. | Includes both zero operands. Pair/triple syntax and canonical binary conventions are explicitly fixed rather than supplied by the book. |

**All eleven statement checks**

The constructions referenced below are detailed in the numbered answers. “True” here means the stated mathematical contract is supported, not that its `sorry` has been eliminated.

| # | Sorried declaration | True-as-stated argument |
|---|---|---|
| T1 | `ImplicitlyLogspaceComputable.comp` | The composite output bound is polynomial by the inequality in question 2. Simulating either query decider for `g` on the virtual paired input, and servicing virtual `f`-bits and boundaries with its two supplied deciders, uses logarithmic space. Malformed and oversized queries can be rejected within that bound; each simulation halts. |
| T2 | `LogspaceReducible.trans` | Extract witnesses `f,g` and apply T1. For every `x`, `x ∈ B ↔ f x ∈ C ↔ g(f x) ∈ D`; thus `g ∘ f` has the required membership equivalence. |
| T3 | `mem_LOGSPACE_of_logspaceReducible` | The one-bit characteristic function of `C` has a polynomial bound and the two logspace query languages specified in question 3. Apply T1 to its composition with the reduction, then directly specialize the query decider to `pairEncode x []`. This proves the statement after correcting findings 1–2. |
| T4 | `LogspaceReducible.polyTimeReducible` | Apply the received `ImplicitlyLogspaceComputable.polyTimeComputable` to the same witness. `PolyTimeReducible` requires exactly that resulting computability property and the unchanged membership equivalence. |
| T5 | `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` | Every member of `NL` reduces to the complete language, so T3 puts it in `LOGSPACE`. The converse inclusion is the supplied `LOGSPACE_subset_NL`. The reverse direction of the book's “iff” remark follows immediately from `NLComplete`'s membership conjunct and the equality. |
| T6 | `PATH_mem_NL` | Validate the complete encoding, check `s=t` immediately, then guess at most `n` edges with bounded vertex registers. A reachable target has a simple path of at most `n−1` edges, and all guessed walks stop at the cap. Space is logarithmic in the actual input length, including validation. |
| T7 | `PATH_NLComplete` | T6 proves membership. A bounded configuration graph retaining the output summary, with a single accepting target, gives a polynomial-size graph whose encoded bits and length are computable in logspace. Projection/lifting proves the membership equivalence; normalization and codec construction remain genuine named fill obligations. |
| T8 | `compl_PATH_mem_NL` | Accept malformed inputs. On valid instances, the induction in question 6 ensures that any surviving branch has the exact ball counts, while true certificates exist for every needed classification. The final exclusion test succeeds exactly when the target is unreachable, using bounded loops and logarithmic workspace. |
| T9 | `NL_eq_coNL` | For `B ∈ NL`, complement the membership equivalence of its reduction to `PATH` to get `Bᶜ ≤ₗ PATHᶜ`. T8 and nondeterministic downward closure give `Bᶜ ∈ NL`. Applying that implication to complements proves the reverse inclusion as well. |
| T10 | `NSPACE_compl_eq` | Compute the window from the constructibility witness and run the same counting algorithm on bounded configuration codes. Their lengths, all counters, and adjacency tests require `O(S n)` space by question 7. This constructs a decider for each complement; applying closure twice gives the displayed set equality. |
| T11 | `multLang_mem_LOGSPACE` | Validate all three canonical number fields and compute product columns with the bounded carry invariant in question 8. Compare every relevant output bit, reject excessive result length, and check that no carry remains. Zero operands and empty binary words need no extra space or hypothesis. |

**Answers to the eight numbered questions**

**1. Reducibility and the received divergences.** Both query languages and the polynomial output bound are present; none is inferred from the others. Reindexing `i` to `i+1` reconciles the zero-based and one-based conventions without changing the intended function class. The polynomial normalization does change a *literal*, all-input reading of the book's bound: the constant function with output `[false,false]` witnesses

\[
\operatorname{Set.univ}\le_l\{[\mathrm{false},\mathrm{false}]\}
\]

here, whereas `|f(x)| ≤ |x|^c` forces length at most one on every one-bit input and cannot witness this reduction. This is an already-declared, appropriate normalization of polynomial boundedness, not an undeclared discrepancy. Neither change damages composition or the intended complexity-theoretic results.

**2. Composition.** Suppose the bounds for `f,g` are `C(|x|+1)^c` and `D(|y|+1)^d`. Since `(|x|+1)^c ≥ 1`,

\[
\begin{aligned}
|g(f(x))|&\le D(|f(x)|+1)^d\\
&\le D\bigl((C+1)(|x|+1)^c\bigr)^d\\
&=D(C+1)^d(|x|+1)^{cd}.
\end{aligned}
\]

This includes zero constants/exponents and empty outputs. On a query word `w`, parse the aligned pair and validate the canonical index. Before storing its numerical value, compare its bit-length and, if necessary, its bits against the displayed polynomial bound: values at or beyond the bound make both queries false. Parsing an arbitrarily long index requires only counters of `O(log(|w|+2))` bits; an index small enough to retain has `O(log(|x|+2))` bits.

Compute `|f(x)|` by sequential length queries up to its polynomial bound. Simulate `g`'s appropriate query machine on `pairEncode (f x) (bits i)`: duplicated data positions use `f`'s bit query, the separator and index suffix use direct arithmetic, and endmarkers use the computed length. The virtual input length is polynomial in `|x|+1` after the index check. The suspended outer workspace, virtual head, inner query workspace, and counters occupy a constant number of logarithmic regions; calls reuse these regions rather than accumulating them. The two machines halt, and inner queries are deterministic. This supplies **both** `indexLang` memberships without storing `f(x)`.

**3. Transitivity, downward closure, polynomial refinement, collapse.** For the one-bit characteristic function `χ_C`, the exact query conditions on genuine pairs are

\[
\begin{aligned}
(\chi_C(x)).\operatorname{getD}(i,\mathrm{false})=\mathrm{true}
   &\iff i=0\ \land\ x\in C,\\
i<|\chi_C(x)|&\iff i=0.
\end{aligned}
\]

The first is decided by checking the paired shape/index and simulating the `C` decider on the decoded first component; the second is regular. For the last specialization step, directly simulate the resulting query decider on `dbl x ++ [false,true]`. A virtual head into this word needs `O(log(|x|+2))` bits and maps each doubled position back to one input bit. This elementary construction is independent of the general downward-closure theorem, avoiding circularity. T2, T4, and T5 then follow by the displayed membership equivalences and received inclusions.

**4. Encoding and `PATH`.** Applying `pairDecode` to equal encodings first gives equal unary words, hence equal vertex counts. Two further pair decodings give equal flattened matrices and endpoint bitstrings; `Nat.bits` injectivity gives equal endpoint values. For the now-common `n`, the matrix's entry at `u*n+v` recovers `A u v`, so function extensionality recovers the entire matrix.

Repeated use of `length_pairEncode` gives

\[
|\operatorname{encodePATH}(n,A,s,t)|
 =2n^2+2n+2|\operatorname{bits}(s)|+|\operatorname{bits}(t)|+6.
\]

Thus every instance is nonempty. `Fin 0` rules out a graph with designated vertices at `n=0`; it does not omit any legitimate empty-graph instance with two actual vertices. The zero-length path is legitimate: `GraphReach A s s` holds even without a loop. An empty endpoint word represents vertex zero unambiguously because the pair separator delimits it.

The validator must check three pair layers, an all-true nonempty unary field, exactly `n²` matrix bits, and canonical endpoint words denoting values below `n`. Canonical words are empty or end in `true`; merely interpreting padded binary numerals numerically is insufficient. Injectivity is useful for proving this validator exact and for lifting the decoded graph's result back to existential language membership. No total decoder fallback is needed.

**5. `PATH` membership and hardness.** Validation uses counters bounded polynomially in input length. After it succeeds, two vertex registers, a round counter, and matrix-address arithmetic remain logarithmic; when `n=1`, the counter still needs a constant number of cells. Test equality with the target before the first guessed edge, enforce guessed vertices `< n`, and halt every branch after at most `n` rounds.

For hardness, enumerate bounded configurations with blank tape outside the chosen window, including input-head position, state, tape contents/heads, and `OutSummary`. An adjacency test checks one possible transition and compares the resulting bounded code; it must not clamp an out-of-window successor into a valid vertex. From the real initial configuration, the space bound ensures every actual reachable configuration stays in the window. Conversely, step compatibility of the summary allows each coded path to be lifted to a real choice-word run. Halted state **and** `.accept` summary are required for acceptance.

An erase-and-park implementation is possible: record enough visited-boundary information during simulation, redirect halts into cleanup, erase the visited regions, return work heads to fixed origins, and return the input head to a fixed boundary. Preserve original output or track its summary without turning a dead output into acceptance. Boundary records and cleanup use `O(c₀ logSpace |x| + logSpace |x|)` space; count the **new** machine with a suitably enlarged constant. `cleanTM` is a model for part of this construction, not a supplied proof of it. Alternatively, a graph-level extra accepting sink would avoid machine cleanup, but would require revising the declared proof route, not the theorem.

The count is polynomial in `|x|+1` for a fixed machine and logarithmic window. Squaring it for an adjacency matrix remains polynomial. The paired encoding's length follows from question 4 and the endpoint-code lengths; its length query is arithmetic in the input length and index (the sketch's “in `i`” suppresses the input-length dependence). The default-false bit query must also handle every out-of-range index. None of this needs the P4.3 adjacency-CNF result.

**6. Counting and the single choice word.** For valid graphs, use the pack's balls `C_i` and counts `c_i`. Their defining recurrence is

\[
C_0=\{s\},\qquad
C_i=C_{i-1}\cup\{v:\exists u\in C_{i-1},\ A(u,v)=\mathrm{true}\}.
\]

Assume the preceding count is correct. A strictly increasing list of `c_{i-1}` vertices, each equipped with a verified path of length at most `i−1`, is a subset of `C_{i-1}` of the same size; hence it is exactly `C_{i-1}`. Therefore requiring, for every listed `u`, both `u ≠ v` and `A(u,v)=false` proves exactly `v ∉ C_i`. Notice the direction `u→v`.

At stage `i`, process **every** vertex `v=0,…,n−1`. Guess its membership flag and check either a length-at-most-`i` path or the preceding negative certificate; count the positive flags and compare that count with the proposed `c_i`. Starting from the verified `c_0=1`, induction forces every retained count to be correct. At the end, enumerate `c_n` distinct certified members of `C_n`, excluding `t`. This succeeds iff `t∉C_n`; finite-graph cycle removal gives `C_n` equal to the reachable set.

The stream order is: stage, next classified vertex, its flag, its positive path **or** its negative list of vertices and fresh positive paths, then the next classified vertex. Store the outer vertex and counter while consuming the inner path; discard each path after checking it. Later certificates may use different paths to the same vertex. No path or prior certificate bit is revisited, and the number of simultaneously stored registers is constant. Bound each list and path length, reject out-of-range values, and use fixed finite loop bounds even on dishonest choices. There are at most `O(n^4 log(n+2))` meaningful certificate bits; input rescans and deterministic microsteps still give a polynomial running bound in encoded input length.

A physical NDTM step consumes a choice bit even during deterministic work. Those bits can be ignored; successful certificate bits occupy the guessing steps, and the word is padded after halting to the common budget. Thus the direct construction needs no separate certificate-tape model. Finally, accept validator failure deterministically: `PATHᶜ` includes **all** malformed words, not just well-formed nonreachable instances.

**7. Complement equalities and the closure obligation.** The deterministic reduction remains unchanged under complementation:

\[
x\in B^c\iff f(x)\in C^c.
\]

For nondeterministic downward closure, retain the target machine's simulated configuration while running deterministic `f`-queries, then resume with the next actual nondeterministic choice. Each host branch projects to a target branch; every target branch can be realized by inserting ignored bits during the deterministic work. The target's all-branch halting budget on the fixed input `f(x)`, together with the finitely many halting query calls needed within that budget, gives a finite common host budget. Polynomial output length makes all workspace logarithmic. An appropriate standalone contract is

```lean
theorem mem_NL_of_logspaceReducible {B C : Language Bool}
    (h : B ≤ₗ C) (hC : C ∈ NL) : B ∈ NL
```

Its explicit promotion would improve the frozen audit surface; the present named-obligation policy does not require it as a condition of PASS.

For the general bound, write `n=|x|`, `s=c₀*S n`, `k=N.k`, and `q=Fintype.card N.State`. The supplied count obeys

\[
\begin{aligned}
N.\operatorname{configBound}(n,s)
 &=3(q+1)(n+2)3^{k(2s+1)}(2s+1)^k\\
 &\le3(q+1)(n+2)2^{5ks+3k}\\
 &\le3(q+1)2^{(5kc_0+1)S(n)+3k+1}.
\end{aligned}
\]

Here `3^r ≤ 2^(2r)`, `2s+1 ≤ 2^(s+1)`, and the bundled logarithmic floor supplies `n+2 ≤ 2^(S n+1)`. Thus vertex codes and counters have `O(S n)` bits, even though the number of vertices can be exponential. Compute and retain the binary window bound using the constructibility witness, then reuse the counting space. Constructibility supplies this effective bound; it is not additionally needed for the combinatorial induction. The separately bundled logarithmic floor pays for input addressing and constant overhead. No monotonicity of `S` is required.

For the exact set equality, closure sends a member of the right-hand side to a member of the left-hand side. If `L` belongs to the left, apply closure to `Lᶜ` and use `(Lᶜ)ᶜ=L` to obtain membership on the right. Empty inputs are harmless because `S 0 ≥ logSpace 0 = 1`.

**8. Multiplication.** Pair injectivity and binary injectivity make the existential language exactly the canonical triples satisfying the product equation. In particular,

\[
\operatorname{pairEncode}([],\operatorname{pairEncode}([],[]))=0101\in\mathrm{multLang};
\]

the whole empty word is not a member. Both `a=0` and `b=0` require the product field to be empty.

For input bits `a_p,b_q`, maintain the carry and column sum via

\[
\begin{aligned}
\operatorname{carry}_0&=0,\\
\operatorname{column}_j&=\sum_{p+q=j}a_p b_q,\\
\operatorname{productbit}_j&=(\operatorname{carry}_j+\operatorname{column}_j)\bmod2,\\
\operatorname{carry}_{j+1}&=\left\lfloor
 (\operatorname{carry}_j+\operatorname{column}_j)/2\right\rfloor.
\end{aligned}
\]

The correctness invariant is

\[
\sum_{r<j}2^r\operatorname{column}_r
 =\sum_{r<j}2^r\operatorname{productbit}_r+2^j\operatorname{carry}_j.
\]

If `m` is the total encoded input length, then `column_j ≤ m`; induction gives `carry_j ≤ m`, and the temporary sum is at most `2m`. All counters and arithmetic therefore use `O(log(m+2))` bits. Validate canonical words, reject a result field longer than the sum of the two operand bit-lengths, and compare through that many columns using zero for missing result bits. This handles products whose bit-length is smaller than the maximum column count, including zero; “simultaneous end” must not mean that these lengths are always equal.

**Adversarial instantiations**

Bitstrings in this table spell Boolean lists with `0=false`, `1=true`.

| Test | Instantiation and calculation | Outcome |
|---|---|---|
| A1 | Empty word `[]`. Every graph encoding has length at least 10; every multiplication encoding at least 4. | Outside `PATH` and `multLang`; inside `PATHᶜ`. |
| A2 | `n=1`, no edges, `s=t=0`; encoding `1101000101`. | In `PATH` by the zero-edge path. A walk requiring a first edge would be wrong. |
| A3 | Same graph with its self-loop; encoding `1101110101`. | Still in `PATH`, with no encoding collision with A2. |
| A4 | Attempted zero-vertex shape `010101` (three nested empty pairs). | No `Fin 0` endpoint exists; reject as an instance and accept in the complement. |
| A5 | A2 with endpoint zero encoded as `[false]` instead of `[]`. | Numerically suggestive but noncanonical: outside `PATH`, inside its complement. |
| A6 | Two vertices, only edge `0→1`. | `(s,t)=(0,1)` is reachable; `(1,0)` is not. Reversing adjacency in the negative certificate fails this test. |
| A7 | `(a,b)=(0,0)` gives `0101`; `(0,1)` gives `011101`. | Both in `multLang`. Empty fields are genuine zero representations. |
| A8 | Triple `⟨0,b,1⟩`, or any correct product field with an extra terminal `false` bit. | Both rejected: the first arithmetically, the second by canonical validation. |
| A9 | `NLComplete ∅` would require the universal language to reduce to the empty language; `NLComplete Set.univ` would require the empty language to reduce to the universal language. | Both impossible. Both source languages have constant-output deciders in `NL`, so the hardness quantifier is not vacuous. |
| A10 | `f x=[]` for every `x`. Its two query languages are empty, and its length bound has `C=0`. | A valid implicit function. It reduces exactly `B=Set.univ` when `[]∈C`, and exactly `B=∅` otherwise. |
| A11 | One-bit characteristic output queried at index 1. | Length query is false for every input, witnessing finding 1. |
| A12 | A bounded function outputs `[false]` on an undecidable language and `[]` otherwise. | Its bit language is empty, but its length query at index 0 is undecidable. The received third conjunct correctly excludes it. |
| A13 | A machine emits `true`, then `false`, then halts. | Its live `.accept` summary is not acceptance; the terminal summary is `.dead`. Hardness must require halting and preserve the summary. |
| A14 | Constant two-bit reduction from `Set.univ` to the singleton containing `00`. | Allowed here, excluded by the literal `length(x)^c` bound on one-bit inputs; confirms the declared normalization's exact effect. |
| A15 | `S=logSpace`, including input length zero; also a zero-work-tape source machine. | The complement construction has positive administrative space available. A zero-tape source does not force its simulator to use zero tapes. |

As independent finite checks, a direct Python translation verified 961 pair round-trips with no collisions; all 4,674 graph encodings for `1≤n≤3`, their lengths, decoding, and injectivity; 13,954 local inductive-counting cases; and 12,288 multiplication checks with `0≤a,b<64` (correct product, padded representation, and incorrect product). All passed. These checks are diagnostic evidence, not Lean tests or substitutes for the general arguments above.

**Suggested additive sanity contracts**

No existing frozen statement needs alteration. Useful permanent checks are: the exact `encodePATH` length; recovery/injectivity of its components; `encodePATH n A s t ∈ PATH ↔ GraphReach A s t`; reflexive membership; exclusion of the empty word; acceptance of every malformed word by `PATHᶜ`; membership of the zero-product encodings; the fixed-index `indexLang` specialization; and the proposed nondeterministic downward-closure contract. The codec, normalization, and compiler proofs remain fill obligations, not new conclusions certified by this report.

**Notation glossary.** `|x|` is word length; `[]` is the empty word; `bits` is `Nat.bits`; `dbl` repeats each bit; `≤ₗ` is the supplied logspace reducibility; `Lᶜ`/`L^c` is language complement; `Set.univ` is all Boolean words. `χ_C` is the one-bit characteristic function of `C`. `C,c,D,d` are the respective output-bound constants/exponents for `f,g`. `C_i,c_i` are the reachable ball and its size. In the configuration calculation, `n=|x|`, `s=c₀S(n)`, `k` is the tape count, and `q` the live-state count. In the multiplication calculation, `m` is encoded input length, `a_p,b_q` are operand bits, and `column_j`, `carry_j`, `productbit_j` are the displayed grade-school quantities. All other identifiers are those of the supplied pack.

## ===== audits/ch4-p44-resolutions.md =====

# Chapter 4, phase P4.4 (logspace reductions, PATH, Immerman-Szelepcsényi) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 2 minors, 5 notes** (`audits/ch4-p44-findings.md`, verbatim). All 6
definitions blind-restated clean (with the received
`ImplicitlyLogspaceComputable` conjuncts spelled out exactly); all 11 sorried
statements accepted with independent derivations — the composite
output-length inequality, the exact `encodePATH` length equation
`2n² + 2n + 2|bits s| + |bits t| + 6` with full injectivity, the
inductive-counting invariant with the ascending-order/exact-count forcing
argument and a one-choice-word stream layout, the `O(S n)`-bit vertex-code
ledger for Corollary 4.21, and the bounded-carry invariant for `MULT`. The
bundle hash was independently recomputed; 15 adversarial instantiations plus
~32,000 finite checks (pair round trips, all graph encodings for `n ≤ 3`,
counting cases, multiplication triples) all passed.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `mem_LOGSPACE_of_logspaceReducible`'s sketch no longer calls the characteristic function's length language "total": it is **exactly** `{pairEncode x [] | x}` — a regular language; index `1` and malformed strings are rejected |
| 2 | The same sketch's final step is now a fixed-index **paired-input** specialization: the index-`0` query string is `pairEncode x [] = dbl x ++ [false, true]` (the doubled word with separator, not `x` itself), decided by simulating the query machine on that doubled virtual input directly — independent of the theorem being proved, avoiding circularity |

Also applied with note 4's disposition (prose accuracy, disclosed here):
`PATH_NLComplete`'s sketch now says the P0 unique-terminal caveat is
**assigned for discharge here**, not already closed — the received `cleanTM`
is the model only (the P0 record notes it does not reset the input head), and
the normalization must park the input head and re-prove acceptance,
all-branch halting, and the space constant for the normalized machine.

Re-verification: `Reductions`, `Path`, `ImmermanSzelepcsenyi` re-elaborate
with zero errors (11 `sorry` warnings exactly across the four modules).

## Notes (dispositions recorded)

* **Note 3 (composition ledger)**: malformed-query rejection, index
  length/overflow handling before storing a value, the paired virtual-input
  layout `pairEncode (f x) (bits i)`, and the length-query boundary test —
  carried verbatim into the `comp` fill brief, with the auditor's full
  question-2 ledger.
* **Note 5 (counting verifier)**: the direction-sensitive negative test
  (`A u v = false` with `u` from the previous ball), strict ascending order,
  exact previous counts, canonical-field validation accepted on failure, and
  the stage/vertex/flag/certificate stream layout — carried verbatim into
  the fill brief.
* **Note 6 (`NL` downward closure)**: the recommended standalone contract
  `mem_NL_of_logspaceReducible` is recorded as a **future additive
  statement** (the named-fill-obligation policy needs no promotion to pass);
  its proof route (suspended simulation, ignored choice bits during
  deterministic query work, budget from the target's all-branch halting) is
  banked for the fill.
* **Note 7 ([P4.2], cross-filed)**: the P4.2 carrier-bridge distinction —
  disposition recorded in `audits/ch4-p42-resolutions.md` (that gate closed
  the same day); the P4.4 consumer builds the bounded codec and path
  lifting itself and does not treat them as exported by P4.2.
* **Auditor-supplied material banked for fill**: the exact validator
  requirements (canonical endpoint words — empty or ending in `true`), the
  `O(n⁴ log(n+2))` certificate-bit estimate, the erase-and-park alternative
  via a graph-level accepting sink (recorded as fallback only — the declared
  route stays machine-level normalization), and the suggested additive
  sanity contracts (encoding length/injectivity, `encodePATH ∈ PATH ↔
  GraphReach`, zero-product memberships, the fixed-index specialization).

## Consequences

* **The chapter-4 statement program is fully gated**: P4.1, P4.2, and P4.4
  closed; P4.3 is in its repair round (`audits/ch4-p43-findings.md` — its
  blocker concerns the P4.3-side codec statement, not this phase's surface).
* The nondeterministic-ARM extension keeps its two named customers (the
  `PATH` walk, the counting verifier) with the §12 gate; nothing here
  changes that deferral.
* Statement-freeze baseline for the closed surface: the closing commit
  (minors are sketch prose only; no declaration changed).

## ===== audits/ch4-p44-resolutions-addendum.md =====

# Chapter 4, phase P4.4 — resolutions addendum: B7 route changes (statement mini-phase P4.4b)

**Status: OPEN for the P4.4b statement gate (2026-10-11; user-approved restructure).** This
addendum supplements `audits/ch4-p44-resolutions.md`. It changes no P4.4 statement. Two proof
routes change, the sketch prose of two declarations is corrected, and seven new sorried
statements are added for gating.

## Why

Plan §4e listed cluster B7 as "unblocked via the received `LogProg` layer". The pre-issue
review of B7 found this false for `comp`, `mem_LOGSPACE_of_logspaceReducible` (by its binding
route) and `multLang_mem_LOGSPACE`. The received layer has two deterministic gaps:

- **G1, no oracle-served virtual input.** A call's virtual input is read physically: the whole
  host input, or its leading run of `1`s, followed by register words (`Machines/Program.lean`,
  `Mode`). No call can serve a decider's input symbols through further calls. The P0 reception
  record already says so: `audits/ch34-p0-findings.md` note 10, and its line 184, "general
  implicit composition remain[s] real work".
- **G2, no random access to a general input.** The input instructions of `LogProg.ARM`
  presuppose `⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩` (`Machines/ARM.lean:72–82`).

## Route change 1 — `Complexity.mem_LOGSPACE_of_logspaceReducible` (T3)

- **Was:** the sketch, as amended by resolutions minors 1–2.
  - `χ_C` is implicitly logspace computable;
  - `χ_C ∘ f` is too, by `comp`;
  - specialize its bit query at index `0`.
- **Problem:** `χ_C`'s bit language is `{pairEncode x [] | x ∈ C}`. Deciding it runs `C`'s
  decider on the undoubled first component of the host, which is itself an instance of G1. So
  the route needs the engine twice, and `comp` as well.
- **Now:** `obtain ⟨f, hf, hB⟩ := h`, then `Set.ext hB`, then
  `Complexity.mem_LOGSPACE_preimage hf hC`. The engine runs once: the oracle-input simulator
  `Complexity.LogProg.OIS` of `Logspace/PreimageHost.lean`, which is [AB09, Fig. 4.3]'s
  construction.
- **Finding 2's circularity rule is kept.** The engine cites nothing from `Reductions`.

## Route change 2 — `Complexity.ImplicitlyLogspaceComputable.comp` (T1)

- **Was:** run `g`'s query machine on a virtual input served by `f`'s queries "via the
  received call protocol". G1 and G2 block this.
- **Now:**
  - Both query languages of `g ∘ f` are preimages of `g`'s along `Complexity.compQ f`
    (`⟨x, bits i⟩ ↦ ⟨f x, bits i⟩`, malformed queries ↦ `[]`). This is
    `Complexity.mem_indexLang_compQ_iff`, proved.
  - Hence both are in `L` by `mem_LOGSPACE_preimage` together with
    `Complexity.ImplicitlyLogspaceComputable.compQ`.
  - The composite bound is question 2's `D (C + 1)^d (|x| + 1)^{cd}`.
  - This is the same Fig. 4.3 simulation, factored once through the engine.
- **Where question 2's ledger now lives.** Note 3 is carried verbatim into `compQ`'s
  machine:
  - malformed-query rejection;
  - index-length and overflow handling before a value is stored;
  - the paired layout;
  - the length boundary test.
- **How that machine queries `f`.** Its host is `⟨⟨x, bits i⟩, bits p⟩`, so it reaches `f` at
  `⟨x, bits j⟩` through the twice-lifted languages `{z | dropIdx (dropIdx z) ∈ ·}`.

## Unchanged

- All five B7 statements; the routes of `trans` (T2) and of
  `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` (T5).
- `multLang_mem_LOGSPACE`'s route (audit question 8). Only its input reading is new: an ARM
  reads the input through `whole`-mode calls to `Complexity.inputBitLang` and
  `Complexity.inputLenLang`.
- T5 needs no nondeterministic construction.

## New statements for the P4.4b gate (seven sorried)

| Statement | File | Role |
|---|---|---|
| `Complexity.LogProg.readIn_run` | `Logspace/InputAccess.lean` | program fragment: read input bit `i` (index in binary on a register) into the control state; registers restored; space independent of `i` |
| `Complexity.implicitlyLogspaceComputable_id` (N1) | `Logspace/InputAccess.lean` | input random access in `L`; stated as the corollary of `readIn_run` |
| `Complexity.LogProg.OIS.run` | `Logspace/PreimageHost.lean` | the simulator's run contract against any truthful oracle |
| `Complexity.LogProg.OIS.compile_decides` | `Logspace/PreimageHost.lean` | its space contract, compiled against a two-decider bank |
| `Complexity.mem_LOGSPACE_preimage` (N2) | `Logspace/PreimageHost.lean` | logspace preimages; stated as the corollary of `compile_decides` |
| `Complexity.implicitlyLogspaceComputable_dropIdx` (N3) | `Logspace/QueryReshape.lean` | index dropping |
| `Complexity.ImplicitlyLogspaceComputable.compQ` (N4) | `Logspace/QueryReshape.lean` | `comp`'s query reshaping |

**Definitions:**
- `LogProg.RdPh` and `LogProg.readTr` (the fragment's transition table, from received actions
  only);
- the `LogProg.OIS` program: `Ph`, `nextPh`, `liftAct`, `tr`, `call`, `prog`, `start`, `lo`,
  `hi`;
- `inputBitLang`, `inputLenLang`, `dropIdx`, `compQ`.

**Proved helpers:** `pairEncode_ne_nil`, `indicator_indexLang_pairEncode`,
`LogProg.vword_whole₁`, `dropIdx_pairEncode`, `dropIdx_length_le`, `compQ_pairEncode`,
`mem_indexLang_compQ_iff`, `compQ_length_le`. Two corollaries are proved modulo N1:
`inputBitLang_mem` and `inputLenLang_mem`.

**Pre-ship probe:** `audits/evidence/b7/B7StatementsProbe.lean.txt` (output `.out`). It has
0 errors. It exercises the fragment and the simulator on concrete instances, and it derives T2,
T3, T5 and `comp` from the contracts.

## Sketch-prose corrections (decision D5; statements unchanged)

- **`comp`** (`Reductions`): the claim that the received layer "is built for exactly this
  shape" is replaced by the gap statement and the route above.
- **`multLang_mem_LOGSPACE`** (`Mult`):
  - the claim that `Machines/Parse2`/`ParseCmp` read `⟨u, ⟨v, w⟩⟩` is replaced by the input
    access route;
  - "accept at the simultaneous end" becomes question 8's acceptance condition: all columns
    through `|a| + |b|`, missing result bits read as `0`, no remaining carry;
  - `arm_decides` becomes `arm_decides_poly`.

## Questions for the gate

1. **`readIn_run`.** Are the head range `[-1, |bits (|x| + 1)|]` and the frame clause right?
   The frame clause says only the counter's tape and the two heads change, and that the
   output and the other registers are untouched.
2. **`OIS.run`.**
   - Are the oracle laws needed only on genuine queries, for length at `i ≤ |v|` and for bit at
     `i < |v|`?
   - Is the work-register range `[-S, S]` right, with `S` the space up to `t` rather than up
     to the first halt?
3. **`OIS.nextPh`.** Does the clamped-move table match `Turing.moveInputPos` at both
   boundaries, including `v = []`?
4. **`OIS.compile_decides`.** Should the hypothesis `B` (over `i ≤ |v|`, all `j`) be
   replaced by monotone space functions?
5. **N1's form.** N1 is stated as `ImplicitlyLogspaceComputable id`, not as the two
   memberships. Is that acceptable?
6. **T3's sketch.** It still describes the superseded `χ_C` route. Correct it now, or leave a
   flagged appendix at the fill?
7. **Namespaces.** Campaign files add to `Complexity.LogProg`; this is policy §1's
   area-local root. Is that acceptable?

## ===== audits/evidence/b7/B7StatementsProbe.lean.txt =====

import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.Mult

/-!
# B7 statement mini-phase (P4.4b): pre-ship probe (maintainer-run; not part of the library)

Exercises the P4.4b contracts against the branch `integrate/b7-statements`:

* R1–R3  the input-read fragment `LogProg.readIn_run` on a concrete two-register program
         whose transitions are `LogProg.readTr` by `rfl` (the hypotheses are satisfiable),
         and its exit on a concrete configuration.
* O1–O4  the oracle-input simulator `LogProg.OIS` on a concrete decider: the call nodes, the
         phase table `nextPh`, the lifted step, the compiled machine's type, and the call's
         virtual input; `OIS.run` and `OIS.compile_decides` applied.
* N2'    the indicator identity behind `mem_LOGSPACE_preimage` from `OIS.compile_decides`.
* A1–A2  an ARM call to the access bank reads the input bit; `arm_decides_poly` at
         `multLang` over the access bank.
* D1–D4  the frozen targets from N1–N4: T3 from N2, `comp` from N2 and N4, the
         twice-lifted query languages, the four-oracle bank of N4's machine; T2 and T5.

It has 0 errors and no `sorry` of its own; the axiom prints show `sorryAx` exactly through the
seven P4.4b statements and the five B7 targets.
-/

set_option autoImplicit false

open Turing Complexity Complexity.LogProg

namespace B7SProbe

/-! ## R1–R3: the input-read fragment on a concrete program -/

/-- The demo program's states: the fragment's phases, and an exit emitting the symbol read. -/
inductive DSt where
  | rd (ph : RdPh)
  | out (a : Option Bool)
  deriving DecidableEq

/-- The demo transitions: the read fragment on index register `0`, counter `1`; the exit emits
the symbol (if any) and halts. -/
def demoTr : DSt → Option Bool → (Fin 2 → Option Bool) → Action 2 Bool DSt
  | .rd ph, a, w => readTr 0 1 DSt.rd DSt.out ph a w
  | .out a, _, _ => ⟨0, fun _ => (none, 0), a, none⟩

/-- The demo program (no calls). -/
def demo : RProg 2 0 DSt := ⟨⟨.rd .eC, demoTr⟩, fun _ => none⟩

/-- The demo entry configuration: `bits i` on the index register, an empty counter. -/
def entry (x : List Bool) (i : ℕ) : Cfg 2 Bool DSt x :=
  ⟨some (.rd .eC), ⟨1, by omega⟩,
    fun r => if r = 0 then FinTM.bufferTape (Nat.bits i) else FinTM.bufferTape [], fun _ => 0, []⟩

-- R1: the fragment's hypotheses hold by `rfl` for the demo program.
example : ∀ ph a w, demo.tm.tr (DSt.rd ph) a w = readTr 0 1 DSt.rd DSt.out ph a w :=
  fun _ _ _ => rfl
example : ∀ ph, demo.call (DSt.rd ph) = none := fun _ => rfl

-- R2: `readIn_run` applies, and the exit is the symbol `x[i]?`.
example (x : List Bool) (i : ℕ) :
    ∃ T, rrun demo (fun j => j.elim0) { entry x i with state := some (DSt.rd .eC) } T =
      { entry x i with state := some (DSt.out x[i]?) } :=
  (readIn_run demo (fun j => j.elim0) 0 1 (by decide) DSt.rd DSt.out (fun _ _ _ => rfl)
    (fun _ => rfl) (entry x i) i (by simp [entry]) (by simp [entry]) rfl rfl rfl).imp
    fun _ h => h.1

-- R3: the entry configuration is unchanged by the state update (the fragment starts in place).
example (x : List Bool) (i : ℕ) : { entry x i with state := some (DSt.rd .eC) } = entry x i := rfl

/-! ## O1–O4: the simulator on a concrete decider -/

/-- A concrete decider: one work tape, one state, halting at once with output `true`. -/
def M₁ : FinTM Bool where
  k := 1
  State := Unit
  tm := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), some true, none⟩⟩

-- O1: the call nodes, and nothing else calls.
example (s : M₁.State) : (OIS.prog M₁).call (s, .ask) =
    some ⟨0, .whole, [OIS.q M₁], (s, .bit), (s, .work none false)⟩ := rfl
example (s : M₁.State) : (OIS.prog M₁).call (s, .bit) =
    some ⟨1, .whole, [OIS.q M₁], (s, .work (some true) false), (s, .work (some false) false)⟩ :=
  rfl
example (s : M₁.State) (a : Option Bool) (lb : Bool) :
    (OIS.prog M₁).call (s, .work a lb) = none := rfl

-- O2: the phase table on all six move cases.
example : OIS.nextPh 1 true false = .ask := rfl
example : OIS.nextPh 0 true false = .work none true := rfl
example : OIS.nextPh (-1) false false = .zt := rfl
example : OIS.nextPh 1 false false = .iC := rfl
example : OIS.nextPh 1 false true = .ask := rfl
example : OIS.nextPh 0 false true = .ask := rfl

-- O3: the simulated step is `M₁`'s action lifted: it halts with `M₁`'s output.
example (w : Fin 2 → Option Bool) :
    (OIS.prog M₁).tm.tr ((), .work none false) none w =
      ⟨0, Fin.lastCases (motive := fun _ => Option (Option Bool) × SignType) (none, 0)
        fun _ => (none, 0), some true, none⟩ := rfl

-- O4: the call's virtual input, and the compiled machine against a two-decider bank.
example (x : List Bool) (i : ℕ) (V : Fin 2 → List Bool) (hV : V (OIS.q M₁) = Nat.bits i) :
    vword (callSegs (d := 2) ⟨0, .whole, [OIS.q M₁], ((), OIS.Ph.bit),
      ((), OIS.Ph.work none false)⟩ x V) = pairEncode x (Nat.bits i) := by
  rw [vword_whole₁, hV]
example (Ms : Fin 2 → FinTM Bool) : FinTM Bool :=
  compileFinTM (OIS.prog M₁) (OIS.start M₁) (bankTM Ms) (bankStart Ms)

-- O5: the run and space contracts apply at the concrete decider.
example (x v : List Bool) (o : Fin 2 → List Bool → Bool)
    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false) :
    ∃ N, (rrun (OIS.prog M₁) o (Cfg.init (OIS.start M₁) x) N).state = none :=
  (OIS.run M₁ x v o ho0 ho1 1 rfl).imp fun _ h => h.1
example (Ms : Fin 2 → FinTM Bool) (As : Fin 2 → Language Bool) (sb : Fin 2 → ℕ → ℕ)
    (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j)) (x v : List Bool)
    (hA0 : ∀ i ≤ v.length, pairEncode x (Nat.bits i) ∈ As 0 ↔ i < v.length)
    (hA1 : ∀ i < v.length, pairEncode x (Nat.bits i) ∈ As 1 ↔ v.getD i false = true)
    (ht : M₁.ComputesInTime v [true] 1) (B : ℕ)
    (hB : ∀ j, ∀ i ≤ v.length, max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B) :
    ∃ T, (compileFinTM (OIS.prog M₁) (OIS.start M₁) (bankTM Ms) (bankStart Ms)).ComputesInTime
      x [true] T :=
  (OIS.compile_decides M₁ Ms As sb hMs x v [true] hA0 hA1 1 ht B hB).imp fun _ h => h.1

-- N2': the indicator identity that turns `compile_decides` at `v := f x` into N2.
example (f : List Bool → List Bool) (C : Language Bool) (x : List Bool) :
    MultiTapeTM.indicator (C : Set (List Bool)) (f x) =
      MultiTapeTM.indicator (({x | f x ∈ C} : Language Bool) : Set (List Bool)) x := by
  simp only [MultiTapeTM.indicator]; rfl

/-! ## A1–A2: the access bank -/

/-- The access bank of an abstract register machine. -/
def acc : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

theorem acc_mem : ∀ j, acc j ∈ LOGSPACE := Fin.forall_fin_two.mpr ⟨inputBitLang_mem, inputLenLang_mem⟩

-- A1: a `whole` call on `[r]` to the bit language reads the input bit at `v r`.
example {m : ℕ} {Λ : Type} (A : ARM m 2 Λ) (u : List Bool) (l l₁ l₀ : Λ) (r : Fin m)
    (v : Fin m → ℕ) (res : Option Bool) (hA : A l = .call 0 .whole [r] l₁ l₀) :
    astep A (fun j V => MultiTapeTM.indicator (acc j : Set (List Bool)) V) u (some l, v, res) =
      (some (if u.getD (v r) false then l₁ else l₀), v, res) := by
  simp only [astep, hA, vword_whole₁]
  have := indicator_indexLang_pairEncode (fun z r => z.getD r false = true) u (v r)
  simp only [acc, Matrix.cons_val_zero, inputBitLang] at this ⊢
  simp only [this, decide_eq_true_eq]

-- A2: `arm_decides_poly` at `multLang` over the access bank (the MULT route).
example {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (A : ARM m 2 Λ) (l₀ : Λ) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (acc j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (multLang : Set (List Bool)) x)) :
    multLang ∈ LOGSPACE :=
  arm_decides_poly A l₀ acc acc_mem C₀ c₀ hcorr

/-! ## D1–D4: the frozen targets from the contracts -/

-- D1: T3 (`mem_LOGSPACE_of_logspaceReducible`) from N2.
example {B C : Language Bool} (h : B ≤ₗ C) (hC : C ∈ LOGSPACE) : B ∈ LOGSPACE := by
  obtain ⟨f, hf, hB⟩ := h
  rw [show B = ({x | f x ∈ C} : Language Bool) from Set.ext hB]
  exact mem_LOGSPACE_preimage hf hC

/-- The composite output bound of [AB09, Lemma 4.17] (P4.4 audit, question 2). -/
theorem comp_length_le {f g : List Bool → List Bool} {C c D d : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c)
    (hg : ∀ y, (g y).length ≤ D * (y.length + 1) ^ d) (x : List Bool) :
    (g (f x)).length ≤ D * (C + 1) ^ d * (x.length + 1) ^ (c * d) := by
  have h1 : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have h2 : (f x).length + 1 ≤ (C + 1) * (x.length + 1) ^ c := by
    have := hf x
    have e : (C + 1) * (x.length + 1) ^ c = C * (x.length + 1) ^ c + (x.length + 1) ^ c := by
      ring
    omega
  calc (g (f x)).length ≤ D * ((f x).length + 1) ^ d := hg _
    _ ≤ D * ((C + 1) * (x.length + 1) ^ c) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 d)
    _ = D * (C + 1) ^ d * (x.length + 1) ^ (c * d) := by rw [mul_pow, ← pow_mul]; ring

-- D2: `comp` from N2 and N4.
example {f g : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    (hg : ImplicitlyLogspaceComputable g) : ImplicitlyLogspaceComputable (g ∘ f) := by
  have hQ := hf.compQ
  obtain ⟨⟨C, c, hC⟩, -, -⟩ := hf
  obtain ⟨⟨D, d, hD⟩, hgb, hgl⟩ := hg
  refine ⟨⟨D * (C + 1) ^ d, c * d, comp_length_le (f := f) (g := g) hC hD⟩, ?_, ?_⟩
  · rw [show indexLang (fun x i => ((g ∘ f) x).getD i false = true) =
        ({w | compQ f w ∈ indexLang fun y i => (g y).getD i false = true} : Language Bool) from
      Set.ext (mem_indexLang_compQ_iff f fun y i => (g y).getD i false = true)]
    exact mem_LOGSPACE_preimage hQ hgb
  · rw [show indexLang (fun x i => i < ((g ∘ f) x).length) =
        ({w | compQ f w ∈ indexLang fun y i => i < (g y).length} : Language Bool) from
      Set.ext (mem_indexLang_compQ_iff f fun y i => i < (g y).length)]
    exact mem_LOGSPACE_preimage hQ hgl

-- D3: inside N4, the twice-lifted query languages are in `L` (N2 twice along N3), and a call
-- from the host `⟨⟨⟨x, bits i⟩, bits p⟩, bits j⟩` answers `f`'s query at `⟨x, bits j⟩`.
example {L : Language Bool} (hL : L ∈ LOGSPACE) :
    ({z | dropIdx (dropIdx z) ∈ L} : Language Bool) ∈ LOGSPACE :=
  mem_LOGSPACE_preimage (C := ({z | dropIdx z ∈ L} : Language Bool))
    implicitlyLogspaceComputable_dropIdx
    (mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx hL)
example (f : List Bool → List Bool) (x : List Bool) (i p j : ℕ) :
    pairEncode (pairEncode (pairEncode x (Nat.bits i)) (Nat.bits p)) (Nat.bits j) ∈
        ({z | dropIdx (dropIdx z) ∈ indexLang (fun x j => (f x).getD j false = true)} :
          Language Bool) ↔
      (f x).getD j false = true := by
  simp only [Set.mem_setOf_eq, dropIdx_pairEncode]
  exact pairEncode_mem_indexLang _ x j

-- D4: N4's machine runs over a four-oracle bank (access, then the lifted queries of `f`).
example {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f) {L : Language Bool}
    {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ] (A : ARM m 4 Λ) (l₀ : Λ) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator
        ((![inputBitLang, inputLenLang,
          {z | dropIdx (dropIdx z) ∈ indexLang fun x i => (f x).getD i false = true},
          {z | dropIdx (dropIdx z) ∈ indexLang fun x i => i < (f x).length}] :
          Fin 4 → Language Bool) j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  have lift : ∀ {L' : Language Bool}, L' ∈ LOGSPACE →
      ({z | dropIdx (dropIdx z) ∈ L'} : Language Bool) ∈ LOGSPACE := fun hL' =>
    mem_LOGSPACE_preimage (C := ({z | dropIdx z ∈ _} : Language Bool))
      implicitlyLogspaceComputable_dropIdx
      (mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx hL')
  refine arm_decides_poly A l₀ _ (fun j => ?_) C₀ c₀ hcorr
  fin_cases j
  · exact inputBitLang_mem
  · exact inputLenLang_mem
  · exact lift hf.2.1
  · exact lift hf.2.2

-- T2 (`trans`) from `comp`, and T5 from T3 and C1a, against the frozen statements.
example {B C D : Language Bool} (h₁ : B ≤ₗ C) (h₂ : C ≤ₗ D) : B ≤ₗ D := by
  obtain ⟨f, hf, hB⟩ := h₁
  obtain ⟨g, hg, hC⟩ := h₂
  exact ⟨g ∘ f, hf.comp hg, fun x => (hB x).trans (hC (f x))⟩
example {C : Language Bool} (h : NLComplete C) (hC : C ∈ LOGSPACE) : NL = LOGSPACE :=
  Set.Subset.antisymm (fun B hB => mem_LOGSPACE_of_logspaceReducible (h.2 B hB) hC)
    LOGSPACE_subset_NL

end B7SProbe

-- The seven P4.4b statements (each `sorryAx`).
#print axioms Complexity.LogProg.readIn_run
#print axioms Complexity.implicitlyLogspaceComputable_id
#print axioms Complexity.LogProg.OIS.run
#print axioms Complexity.LogProg.OIS.compile_decides
#print axioms Complexity.mem_LOGSPACE_preimage
#print axioms Complexity.implicitlyLogspaceComputable_dropIdx
#print axioms Complexity.ImplicitlyLogspaceComputable.compQ
-- The landed proved helpers (each within `[propext, Classical.choice, Quot.sound]`).
#print axioms Complexity.pairEncode_ne_nil
#print axioms Complexity.indicator_indexLang_pairEncode
#print axioms Complexity.LogProg.vword_whole₁
#print axioms Complexity.dropIdx_pairEncode
#print axioms Complexity.dropIdx_length_le
#print axioms Complexity.compQ_pairEncode
#print axioms Complexity.mem_indexLang_compQ_iff
#print axioms Complexity.compQ_length_le
-- Through N1 only.
#print axioms Complexity.inputBitLang_mem
#print axioms Complexity.inputLenLang_mem
-- The five B7 targets (each `sorryAx` until the fill).
#print axioms Complexity.ImplicitlyLogspaceComputable.comp
#print axioms Complexity.LogspaceReducible.trans
#print axioms Complexity.mem_LOGSPACE_of_logspaceReducible
#print axioms Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE
#print axioms Complexity.multLang_mem_LOGSPACE
-- Received lemmas the fill routes cite (each within the standard triple).
#print axioms Complexity.LogProg.compile_space
#print axioms Complexity.LogProg.bank_cleanRun
#print axioms Complexity.LogProg.arm_decides_poly
#print axioms Complexity.LogProg.inc_run
#print axioms Complexity.LogProg.dec_run
#print axioms Complexity.LogProg.eq_run
#print axioms Complexity.LogProg.clr_run
#print axioms Complexity.LogProg.rewind_x
#print axioms Complexity.LogProg.canon_eq_bits
#print axioms Turing.MultiTapeTM.abs_pos_lt_card_visited
#print axioms Complexity.LOGSPACE_subset_NL

## ===== audits/evidence/b7/b7-statements.patch =====

diff --git a/TCSlib/Complexity/SpaceComplexity.lean b/TCSlib/Complexity/SpaceComplexity.lean
index 78674bf2..b266e7ca 100644
--- a/TCSlib/Complexity/SpaceComplexity.lean
+++ b/TCSlib/Complexity/SpaceComplexity.lean
@@ -41,6 +41,9 @@ import TCSlib.Complexity.SpaceComplexity.ZeroSpace
 import TCSlib.Complexity.SpaceComplexity.ConfigGraph
 import TCSlib.Complexity.SpaceComplexity.Savitch
 import TCSlib.Complexity.SpaceComplexity.Hierarchy
+import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess
+import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
+import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
 import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
 import TCSlib.Complexity.SpaceComplexity.Logspace.Path
 import TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi
@@ -113,6 +116,10 @@ running counter program is simulated by an abstract register machine in
 - `SpaceComplexity.Savitch`: Savitch's theorem and `PSPACE = NPSPACE` (phase P4.2)
 - `SpaceComplexity.Hierarchy`: the space-bounded universal machine, Thm 4.8,
   `L ⊊ PSPACE`, Ex 3.2 (phase P4.3)
+- `SpaceComplexity.Logspace.{InputAccess, PreimageHost, QueryReshape}`: random access to a
+  general input (a register-program read fragment; `id` implicitly logspace), the
+  oracle-input simulator of Fig. 4.3 (logspace preimages along implicit functions), and the
+  query reshapings of composition (phase P4.4b)
 - `SpaceComplexity.Logspace.{Reductions, Path, ImmermanSzelepcsenyi, Mult}`: `≤ₗ` and
   Lemma 4.17, `PATH` and Thm 4.18, Thm 4.20 and Cor 4.21, `MULT ∈ L` (phase P4.4)
 
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean
new file mode 100644
index 00000000..2853639b
--- /dev/null
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean
@@ -0,0 +1,200 @@
+/-
+Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: Seyoon Ragavan
+-/
+import TCSlib.Complexity.SpaceComplexity.Machines.DblLang
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Random access to a general input in logarithmic space
+
+A logspace machine reads its input at a position held in binary on a work tape [AB09, §4.1:
+"a pointer into the input"]. The received `LogProg` layer has no such access for a general
+(non-unary) input: the input instructions of `Complexity.LogProg.ARM` presuppose inputs
+`⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩`, and a call's virtual input is the whole input or its leading run
+of `1`s followed by register words (P0 reception audit, `audits/ch34-p0-findings.md`). This
+file supplies the missing piece twice, at the two levels later logspace programs use:
+
+* **as a program fragment**: `Complexity.LogProg.readIn_run` reads bit `i` of the input,
+  `i` held in binary on a register, into the control state (a counter register stepped up to
+  `i` in lockstep with the input head, the received equality, increment, rewind and clear
+  fragments), and restores everything else;
+* **as a language pair**: `Complexity.implicitlyLogspaceComputable_id` — the bit and length
+  languages of the identity, `Complexity.inputBitLang` and `Complexity.inputLenLang`, are in
+  `L` — so an abstract register machine reads its own input at a register-held position by a
+  `whole`-mode call with that register as its one argument (`Complexity.LogProg.vword_whole₁`,
+  `Complexity.indicator_indexLang_pairEncode`).
+
+Phase P4.4b of `AroraBarakChapters3-4Plan.md` (the B7 statement mini-phase, recorded in
+`audits/ch4-p44-resolutions-addendum.md`). The fragment is campaign-owned and lives here,
+not in `Machines/`, by decision D3; it is built only from received fragments.
+
+## Main definitions
+
+* `Complexity.LogProg.RdPh`, `Complexity.LogProg.readTr` — the phases and the transition
+  table of the input-read fragment.
+* `Complexity.inputBitLang`, `Complexity.inputLenLang` — `{⟨u, i⟩ | uᵢ = 1}` and
+  `{⟨u, i⟩ | i < |u|}`.
+
+## Main results
+
+* `Complexity.LogProg.vword_whole₁` — a `whole` call with one argument presents `⟨u, V r⟩`.
+* `Complexity.indicator_indexLang_pairEncode` — the answer of an `indexLang` decider on a
+  genuine pair.
+* `Complexity.pairEncode_ne_nil` — no pair is empty (so `[]` lies in no `indexLang`).
+* `Complexity.LogProg.readIn_run` — the input-read fragment (sorried; phase-P4.4b
+  statement).
+* `Complexity.implicitlyLogspaceComputable_id` — input random access in `L` (sorried;
+  phase-P4.4b statement), with `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16.)
+-/
+
+namespace Complexity
+
+open Turing
+
+/-- No pair encoding is the empty word: `pairEncode x y` contains the separator. -/
+theorem pairEncode_ne_nil (x y : List Bool) : pairEncode x y ≠ [] := by
+  intro h
+  have := congrArg List.length h
+  simp [length_pairEncode] at this
+
+/-- **The answer of an index-language decider on a genuine pair**: the indicator of
+`indexLang p` at `⟨u, bits v⟩` is the decision of `p u v`. -/
+theorem indicator_indexLang_pairEncode (p : List Bool → ℕ → Prop) (u : List Bool) (v : ℕ) :
+    MultiTapeTM.indicator (indexLang p : Set (List Bool)) (pairEncode u (Nat.bits v)) =
+      @decide (p u v) (Classical.dec _) := by
+  rw [LogProg.indicator_eq_decide]
+  exact decide_eq_decide.mpr (pairEncode_mem_indexLang p u v)
+
+namespace LogProg
+
+/-- **A `whole`-mode call with one argument** presents the pair of the whole input and the
+argument register's word: its virtual input is `⟨u, V r⟩`. -/
+theorem vword_whole₁ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
+    (V : Fin m → List Bool) :
+    vword (callSegs ⟨j, .whole, [r], l₁, l₀⟩ u V) = pairEncode u (V r) := by
+  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]
+
+/-! ## The input-read fragment -/
+
+/-- The phases of the input-read fragment: the equality test of the counter with the index
+(`eC`, `eBy`, `eBn`), the read (`yes`) or advance (`no`) step, the counter increment (`iC`,
+`iB`), and, carrying the symbol read, the input rewind (`rw₁`, `rw₂`) and the counter clear
+(`cR`, `cE`). -/
+inductive RdPh where
+  | eC | eBy | eBn
+  | yes | no
+  | iC | iB
+  | rw₁ (a : Option Bool) | rw₂ (a : Option Bool)
+  | cR (a : Option Bool) | cE (a : Option Bool)
+  deriving DecidableEq, Fintype
+
+variable {m d : ℕ} {Λ : Type} {x : List Bool}
+
+/-- **The transition table of the input-read fragment** on index register `r` and counter
+register `s`, its phases embedded by `st` and its exits by `ex`. With the input head on
+position `k + 1` (input symbol `k`) and the counter holding `bits k`: compare the counter with
+the index (`eq_run`); if equal, take the symbol under the head; if not, stop at the right
+blank, or else step the input head right and increment the counter (`inc_run`). Then rewind
+the input head to position `1` (`rewind_x`) and clear the counter (`clr_run`), exiting into
+`ex a` with the symbol `a` taken. -/
+def readTr (r s : Fin m) (st : RdPh → Λ) (ex : Option Bool → Λ) :
+    RdPh → Option Bool → (Fin m → Option Bool) → Action m Bool Λ
+  | .eC, _, w => eqCAct s r (st .eC) (st .eBy) (st .eBn) (w s) (w r)
+  | .eBy, _, w => eqBAct s r (st .eBy) (st .yes) (w s)
+  | .eBn, _, w => eqBAct s r (st .eBn) (st .no) (w s)
+  | .yes, a, _ => goAct (st (.rw₁ a))
+  | .no, a, _ =>
+    match a with
+    | none => goAct (st (.rw₁ none))
+    | some _ => xAct s 1 0 (st .iC)
+  | .iC, _, w => incCAct s (st .iC) (st .iB) (w s)
+  | .iB, _, w => incBAct s (st .iB) (st .eC) (w s)
+  | .rw₁ a, _, _ => xAct s (-1) 0 (st (.rw₂ a))
+  | .rw₂ a, b, _ => rw2Act s (st (.rw₂ a)) (st (.cR a)) b
+  | .cR a, _, w => toEndAct s (st (.cR a)) (st (.cE a)) (w s)
+  | .cE a, _, w => clrEAct s (st (.cE a)) (ex a) (w s)
+
+section Read
+
+variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r s : Fin m) (hrs : r ≠ s)
+  (st : RdPh → Λ) (ex : Option Bool → Λ)
+  (htr : ∀ ph a w, P.tm.tr (st ph) a w = readTr r s st ex ph a w)
+  (hc : ∀ ph, P.call (st ph) = none)
+
+include hrs htr hc in
+/-- **The input-read fragment** (phase P4.4b; spec, fill pending): from phase `eC`, with
+`bits i` on the index register `r`, an empty counter register `s`, both heads on cell `0` and
+the input head on position `1`, the program reaches the exit `ex x[i]?` — symbol `i` of the
+input, `none` when `i ≥ |x|` — in the same configuration otherwise (registers, heads, input
+position and output restored). Throughout, only registers `s` and `r` change (the tape of `s`,
+the heads of both), both heads stay in `[-1, |bits (|x| + 1)|]`, and every state is an
+ordinary fragment state: the fragment's space is these two ranges, independently of `i`.
+A hand-built fragment: no received layer reads a general input at a register-held position
+(the `Parse` fragments assume unary-first inputs).
+
+**Proof sketch.** Induction on the counter value `k ≤ min i |x|`, the input head on position
+`k + 1`. `eq_run` (with `r₁ := s`, so both heads stay within `|bits k|`) compares `bits k`
+with `bits i`. If `k = i`, phase `yes` takes `inSym x (i + 1) = x[i]?`. Otherwise phase `no`
+reads `inSym x (k + 1)`: at the right blank (`k = |x| < i`) the symbol taken is
+`none = x[i]?`; on a letter (`k < |x|`) the head steps right and `inc_run` turns `bits k` into
+`bits (k + 1)`, `k + 1 ≤ |x|`. Then `rewind_x` returns the input head to position `1`, and
+`clr_run` empties the counter (its head within `|bits k|`). -/
+theorem readIn_run (c : Cfg m Bool Λ x) (i : ℕ)
+    (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i)) (hs : c.workTapes s = FinTM.bufferTape [])
+    (hrp : c.workTapePos r = 0) (hsp : c.workTapePos s = 0) (hip : c.inputPos.val = 1) :
+    ∃ T, rrun P oracle { c with state := some (st .eC) } T = { c with state := some (ex x[i]?) } ∧
+      ∀ t < T, ∃ (ph : RdPh) (ip : Fin (x.length + 2)) (f : ℤ → Option Bool) (q q' : ℤ),
+        rrun P oracle { c with state := some (st .eC) } t =
+          ⟨some (st ph), ip, Function.update c.workTapes s f,
+            Function.update (Function.update c.workTapePos s q) r q', c.output⟩ ∧
+        -1 ≤ q ∧ q ≤ (Nat.bits (x.length + 1)).length ∧
+        -1 ≤ q' ∧ q' ≤ (Nat.bits (x.length + 1)).length := by
+  sorry
+
+end Read
+
+end LogProg
+
+/-! ## Input access as a language pair -/
+
+/-- The bit language of the identity: `{⟨u, bits i⟩ | uᵢ = 1}` (`0`-based; `false` beyond the
+end). -/
+def inputBitLang : Language Bool := indexLang fun u i => u.getD i false = true
+
+/-- The length language of the identity: `{⟨u, bits i⟩ | i < |u|}`. -/
+def inputLenLang : Language Bool := indexLang fun u i => i < u.length
+
+/-- **Input random access is logspace** (phase P4.4b; spec, fill pending): the identity is
+implicitly logspace computable — its output bound is trivial and its two query languages,
+`Complexity.inputBitLang` and `Complexity.inputLenLang`, are in `L`. [AB09, §4.1: a pointer
+into the input] It is stated, and will be proved, as a corollary of
+`Complexity.LogProg.readIn_run`.
+
+**Proof sketch.** The bound is `|x| ≤ 1 · (|x| + 1)^1`. For the two languages, one call-free
+register program with a mode bit, compiled against the empty bank `LogProg.Dbl.nilTM` as in
+`LogProg.dblLang_mem` (`compile_space`): on `y`, validate `y = pairEncode z (bits r)` (an
+aligned two-cell scan to the first aligned `[false, true]`, then a canonical tail — empty or
+ending in `true`), reading each cell with `readIn_run`; reject otherwise. Then walk a counter
+`k` over the pairs of `dbl z`, comparing `bits k` with the tail in lockstep (the comparison
+pattern of `LogProg.cmpPlain_run`); on a match answer cell `2k` (resp. `true`), at the
+separator answer `false`. Every register stays within `|bits |y||` cells. -/
+theorem implicitlyLogspaceComputable_id : ImplicitlyLogspaceComputable id := by
+  sorry
+
+/-- `Complexity.inputBitLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
+theorem inputBitLang_mem : inputBitLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.1
+
+/-- `Complexity.inputLenLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
+theorem inputLenLang_mem : inputLenLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.2
+
+end Complexity
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean
index 20985ac5..704edcee 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Seyoon Ragavan
 -/
 import TCSlib.Complexity.SpaceComplexity.Basic
+import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -54,14 +55,19 @@ bit `j` of the product is determined by the column sums
 `∑_{p+q=j'} a_p · b_q` for `j' ≤ j` propagated through the carry — maintain
 the carry (of `O(logSpace n)` bits, since a column sum is at most the input
 length) and two index counters, re-reading `a`'s and `b`'s bits from the
-input by position arithmetic on the nested pair layout (the received
-`Machines/Parse2`/`ParseCmp` toolkit for inputs `⟨u, ⟨v, w⟩⟩`); compare each
-computed bit against the third component's bit and reject on mismatch or
-malformed shape, accept at the simultaneous end. Registers: carry, two
+input by position arithmetic on the nested pair layout (through `whole`-mode
+calls to the input-access languages `Complexity.inputBitLang` and
+`Complexity.inputLenLang` of phase P4.4b; the received
+`Machines/Parse2`/`ParseCmp` toolkit reads only unary-first inputs
+`⟨1ⁿ, ⟨u, w⟩⟩` and does not apply); compare each computed bit against the
+third component's bit and reject on mismatch or malformed shape; accept when
+every column through `|a| + |b|` matches (missing result bits read as `0`, a
+longer result field rejected) and no carry remains. Registers: carry, two
 indices, a column cursor — `O(logSpace n)` cells; assembled by the received
-`arm_decides`. Fill obligations, named: the column-sum/carry invariant; the
-position arithmetic into the nested pairs; the shape validator; the
-`DecidesInSpace` packaging. -/
+`arm_decides_poly`. Fill obligations, named: the column-sum/carry invariant;
+the position arithmetic into the nested pairs; the shape validator; the
+`DecidesInSpace` packaging. (Sketch prose corrected at phase P4.4b; the
+statement is unchanged.) -/
 theorem multLang_mem_LOGSPACE : multLang ∈ LOGSPACE := by
   sorry
 
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean
new file mode 100644
index 00000000..b2370943
--- /dev/null
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean
@@ -0,0 +1,256 @@
+/-
+Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: Seyoon Ragavan
+-/
+import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The oracle-input simulator: logspace preimages along implicit functions
+
+[AB09, proof of Lemma 4.17, Fig. 4.3]: to decide whether `f x ∈ C`, run `C`'s logspace decider
+`M` on a **virtual input** `f x` that is never written down. Whenever `M` reads its input, its
+head position (in binary) is a query `⟨x, i⟩` to the length and bit deciders of `f`. The
+received `LogProg` call protocol does not host this by itself. A call's virtual input is read
+physically, as the whole input or its leading run of `1`s followed by register words, and
+nothing serves a decider's input symbols through further calls (P0 reception audit,
+`audits/ch34-p0-findings.md`, note 10). This file adds the missing engine as a register-tape
+program on the received compiler.
+
+The **oracle-input simulator** `Complexity.LogProg.OIS.prog M` keeps `M`'s work tapes on
+registers `0, …, M.k − 1`, where they are touched only by `M`'s own transitions. It keeps `M`'s
+input position `p` as the index `p − 1` in binary on the last register `q` (with `p = 0`, the
+left blank, recorded in the control state). Each step of `M` runs as follows:
+
+1. one `whole`-mode call on `[q]` asks the length decider whether `p − 1 < |f x|`;
+2. if so, a second call asks the bit decider for the symbol;
+3. one ordinary step applies `M`'s transition to the work registers;
+4. the increment and decrement fragments move `q` as `M`'s clamped input move dictates.
+
+Phase P4.4b of `AroraBarakChapters3-4Plan.md`; `audits/ch4-p44-resolutions-addendum.md`
+records it as the route of `Complexity.mem_LOGSPACE_of_logspaceReducible`. The simulator is
+campaign-owned and lives here (decision D3), beside its only class-level corollary.
+
+## Main definitions
+
+* `Complexity.LogProg.OIS.Ph`, `OIS.tr`, `OIS.call` — the phases, ordinary transitions and
+  call nodes of the simulator.
+* `Complexity.LogProg.OIS.prog`, `OIS.start` — the simulator program and its start state.
+* `Complexity.LogProg.OIS.lo`, `OIS.hi` — its register ranges.
+
+## Main results
+
+* `Complexity.LogProg.OIS.run` — the run contract: against any oracle answering the two
+  queries truthfully, the program halts with `M`'s output on the virtual input, inside the
+  ranges, with well-formed calls (sorried; phase-P4.4b statement).
+* `Complexity.LogProg.OIS.compile_decides` — the space contract: compiled against a bank of
+  the two deciders, it computes `M`'s output on the virtual input within the ranges plus the
+  bank's space (sorried; phase-P4.4b statement).
+* `Complexity.mem_LOGSPACE_preimage` — logspace preimages along implicitly logspace
+  computable maps are in `L` (sorried; phase-P4.4b statement).
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009. (§4.3, Lemma 4.17 and its proof, Figure 4.3.)
+-/
+
+namespace Complexity
+
+open Turing
+
+namespace LogProg.OIS
+
+/-- The phases of the simulator: the length call (`ask`) and the bit call (`bit`); the
+simulated step with the symbol read (`work a lb`, `lb` marking the left blank); the zero test
+before a left move (`zt`); the increment (`iC`, `iB`) and decrement (`dD`, `dL`, `dE`, `dB`)
+of the index register. -/
+inductive Ph where
+  | ask | bit
+  | work (a : Option Bool) (lb : Bool)
+  | zt
+  | iC | iB
+  | dD | dL | dE | dB
+  deriving DecidableEq, Fintype
+
+variable (M : FinTM Bool)
+
+/-- The index register of the simulator, the last one. -/
+abbrev q : Fin (M.k + 1) := Fin.last M.k
+
+/-- The phase after a simulated step, from the decider's input move `d`, at the left blank
+(`lb`) or at the right blank (`rb`): from the left blank, a right move reaches position `1`
+(index `0`); elsewhere a left move first tests the index for zero, and a right move increments
+it unless clamped at the right blank. -/
+def nextPh (d : SignType) (lb rb : Bool) : Ph :=
+  if lb then (if d = 1 then .ask else .work none true)
+  else if d = -1 then .zt
+  else if d = 1 ∧ rb = false then .iC
+  else .ask
+
+/-- The decider's action on the work registers: input head and index register still, output
+forwarded, the next phase by `nextPh`. -/
+def liftAct (A : Action M.k Bool M.State) (lb rb : Bool) : Action (M.k + 1) Bool (M.State × Ph) :=
+  ⟨0, Fin.lastCases (none, 0) A.workTapes, A.output,
+    A.state.map fun s' => (s', nextPh A.inputTape lb rb)⟩
+
+/-- **The ordinary transitions of the simulator.** `work a lb` applies `M`'s transition at the
+symbol `a` (at the right blank exactly when `a = none` and not `lb`); `zt` reads the index
+register's cell `0` (blank iff the index is `0`); the increment and decrement fragments act on
+the index register and return to `ask`. The call phases' transitions are never used. -/
+def tr : M.State × Ph → Option Bool → (Fin (M.k + 1) → Option Bool) →
+    Action (M.k + 1) Bool (M.State × Ph)
+  | (s, .work a lb), _, w =>
+    liftAct M (M.tm.tr s a fun i => w i.castSucc) lb (a.isNone && !lb)
+  | (s, .zt), _, w =>
+    regAct (q M) none 0 (match w (q M) with
+      | none => (s, .work none true)
+      | some _ => (s, .dD))
+  | (s, .iC), _, w => incCAct (q M) (s, .iC) (s, .iB) (w (q M))
+  | (s, .iB), _, w => incBAct (q M) (s, .iB) (s, .ask) (w (q M))
+  | (s, .dD), _, w => decDAct (q M) (s, .dD) (s, .dL) (s, .dB) (w (q M))
+  | (s, .dL), _, w => decLAct (q M) (s, .dE) (s, .dB) (w (q M))
+  | (s, .dE), _, _ => decEAct (q M) (s, .dB)
+  | (s, .dB), _, w => incBAct (q M) (s, .dB) (s, .ask) (w (q M))
+  | (_, .ask), _, _ => junkAct
+  | (_, .bit), _, _ => junkAct
+
+/-- **The call nodes of the simulator.** `ask` asks decider `0` (the length language) about
+`⟨x, bits i⟩`, `i` the index register: on *yes* go on to `bit`; on *no* the symbol is the right
+blank. `bit` asks decider `1` (the bit language) and goes on to the simulated step with the
+answer. -/
+def call : M.State × Ph → Option (CallSpec (M.k + 1) 2 (M.State × Ph))
+  | (s, .ask) => some ⟨0, .whole, [q M], (s, .bit), (s, .work none false)⟩
+  | (s, .bit) => some ⟨1, .whole, [q M], (s, .work (some true) false),
+      (s, .work (some false) false)⟩
+  | _ => none
+
+/-- **The oracle-input simulator** of the decider `M`: a register-tape program over `M.k + 1`
+registers calling two deciders. A hand-built program: no received layer serves a decider's
+input from oracle calls. -/
+def prog : RProg (M.k + 1) 2 (M.State × Ph) := ⟨⟨(M.tm.q₀, .ask), tr M⟩, call M⟩
+
+/-- The start state of the simulator: `M`'s start state, about to ask for symbol `0`. -/
+def start : M.State × Ph := (M.tm.q₀, .ask)
+
+/-- The lower register bounds: `-S` on the work registers, `-1` on the index register. -/
+def lo (S : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (-1) fun _ => -(S : ℤ)
+
+/-- The upper register bounds: `S` on the work registers, `W` on the index register. -/
+def hi (S W : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (W : ℤ) fun _ => (S : ℤ)
+
+/-- **The run contract of the simulator** (phase P4.4b; spec, fill pending). Let `M` halt
+by time `t` on the virtual input `v`. Let the oracle answer every length query
+`⟨x, bits i⟩` with `i ≤ |v|`, and every bit query with `i < |v|`, truthfully. Then the
+program, started on the host input `x`:
+
+* halts with `M`'s output on `v`;
+* keeps the work registers in `[-S, S]`, with `S` the space `M` uses up to `t`;
+* keeps the index register in `[-1, |bits (|v| + 1)|]`;
+* at every call has the input head on position `1` and the index register holding some
+  `bits i`, `i ≤ |v|`, with its head on cell `0` — so the call's virtual input is
+  `⟨x, bits i⟩` (`Complexity.LogProg.vword_whole₁`).
+
+**Proof sketch.** Encode `M`'s configuration `c` on `v` as the program configuration with:
+
+* the work tapes and heads of `c` on registers `castSucc i`;
+* `bits (p − 1)` on `q`, with its head on `0` (`p` the input position of `c`; `bits 0` at
+  `p = 0`);
+* the host input head on `1`, and `c`'s output;
+* state `(s, ask)`, or `(s, work none true)` at `p = 0`.
+
+By induction on `n ≤ t`, the run reaches the encoding of `M.tm.runFrom (M.tm.initCfg v) n`
+until `M` halts. One step goes as follows.
+
+1. At most two calls fix the symbol `inSym v p`: by the oracle laws, the length call says
+   `p − 1 < |v|`.
+2. `work` applies `M.tm.tr` to the `castSucc` block (`liftAct`), so the work registers move
+   exactly as `M`'s tapes.
+3. The clamped move of `p` is realized by `nextPh`:
+   * `inc_run` only when `p − 1 < |v|`;
+   * the zero test and `dec_run` only when `p − 1 ≥ 1`;
+   * a phase change at the left blank.
+
+Intermediate configurations are those of the received fragments on `q`. The work heads are
+`M`'s, so they lie in `[-S, S]` by `Turing.MultiTapeTM.abs_pos_lt_card_visited`. Template:
+`ImplicitEnum.{round, rounds, run}`. -/
+theorem run (x v : List Bool) (o : Fin 2 → List Bool → Bool)
+    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
+    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false)
+    (t : ℕ) (ht : (M.tm.runFrom (M.tm.initCfg v) t).state = none) :
+    ∃ N, (rrun (prog M) o (Cfg.init (start M) x) N).state = none ∧
+      (rrun (prog M) o (Cfg.init (start M) x) N).output =
+        (M.tm.runFrom (M.tm.initCfg v) t).output ∧
+      (∀ n ≤ N, ∀ r,
+        lo M (M.tm.spaceUsed (M.tm.initCfg v) t) r ≤
+            (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ∧
+          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ≤
+            hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length r) ∧
+      ∀ n < N, ∀ l cs, (rrun (prog M) o (Cfg.init (start M) x) n).state = some l →
+        (prog M).call l = some cs →
+          (rrun (prog M) o (Cfg.init (start M) x) n).inputPos.val = 1 ∧
+          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos (q M) = 0 ∧
+          ∃ i ≤ v.length, (rrun (prog M) o (Cfg.init (start M) x) n).workTapes (q M) =
+            FinTM.bufferTape (Nat.bits i) := by
+  sorry
+
+/-- **The space contract of the simulator** (phase P4.4b; spec, fill pending). Let:
+
+* deciders `Ms j` decide `As j` in space `sb j`;
+* on genuine queries about the host input `x`, `As 0` be the length language and `As 1` the
+  bit language of the virtual input `v`;
+* `M` compute `w` on `v` by time `t`;
+* `B` bound the bank's clean-run radius on every query `⟨x, bits i⟩` with `i ≤ |v|`.
+
+Then the simulator, compiled against the bank of the `Ms j`, computes `w` on `x`, visiting at
+most `M.k (2S + 1) + (|bits (|v| + 1)| + 2) + kD (2B + 1)` work cells, where `S` is the space
+`M` uses up to `t` and `kD` the bank's tape count.
+
+**Proof sketch.** Take `OIS.run` with the oracle `j, V ↦ [V ∈ As j]`, whose laws are the two
+hypotheses. Then apply `compile_space` with the ranges `OIS.lo` and `OIS.hi`; their sizes sum
+to the first two terms. Each call's precondition `CallOK` comes from `OIS.run`'s call clause:
+
+* the virtual input is `⟨x, bits i⟩` by `vword_whole₁` and `tapeWord_bufferTape`;
+* the clean run of the bank is `bank_cleanRun`, weakened to `B` by `CleanRun.mono`;
+* `|bits i| ≤ |bits (|v| + 1)|` by `length_bits_mono`. -/
+theorem compile_decides (Ms : Fin 2 → FinTM Bool) (As : Fin 2 → Language Bool)
+    (sb : Fin 2 → ℕ → ℕ) (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j)) (x v w : List Bool)
+    (hA0 : ∀ i ≤ v.length, pairEncode x (Nat.bits i) ∈ As 0 ↔ i < v.length)
+    (hA1 : ∀ i < v.length, pairEncode x (Nat.bits i) ∈ As 1 ↔ v.getD i false = true)
+    (t : ℕ) (ht : M.ComputesInTime v w t) (B : ℕ)
+    (hB : ∀ j, ∀ i ≤ v.length, max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B) :
+    ∃ T, (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).ComputesInTime x w T ∧
+      (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.spaceUsed
+          ((compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.initCfg x) T ≤
+        M.k * (2 * M.tm.spaceUsed (M.tm.initCfg v) t + 1) +
+          ((Nat.bits (v.length + 1)).length + 2) + (bankK Ms + bankK Ms) * (2 * B + 1) := by
+  sorry
+
+end LogProg.OIS
+
+/-- **Logspace preimages along implicitly logspace computable maps are logspace**
+(phase P4.4b; spec, fill pending): if `f` is implicitly logspace computable and `C ∈ L`, then
+`{x | f x ∈ C} ∈ L`. [AB09, Lemma 4.17(2), in preimage form; its proof's Fig. 4.3] It is stated,
+and will be proved, as a corollary of `Complexity.LogProg.OIS.compile_decides`.
+
+**Proof sketch.** Unpack `f`'s bound `C₀ (|x| + 1)^e` and its two deciders (spaces `c₀`,
+`c₁` times `logSpace`), and `C`'s decider `M` (space `c · logSpace`). For each `x`, take the
+time `t` of `M` on `v := f x`, and apply `OIS.compile_decides` with:
+
+* the bank `![length decider, bit decider]`;
+* the laws `pairEncode_mem_indexLang`;
+* `B := (c₀ + c₁) · logSpace (2|x| + 2 + |bits (|f x| + 1)|) + 1`.
+
+The indicator `[f x ∈ C]` is `[x ∈ {x | f x ∈ C}]`. The bound is `O(logSpace |x|)`:
+`logSpace |f x|` and `|bits (|f x| + 1)|` are at most `K · logSpace |x|` by
+`LogProg.log_poly_bound`, since `|f x| ≤ C₀ (|x| + 1)^e`. The arithmetic follows
+`ImplicitlyLogspaceComputable.computesInSpace`. -/
+theorem mem_LOGSPACE_preimage {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
+    {C : Language Bool} (hC : C ∈ LOGSPACE) : ({x | f x ∈ C} : Language Bool) ∈ LOGSPACE := by
+  sorry
+
+end Complexity
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean
new file mode 100644
index 00000000..9dc13c0c
--- /dev/null
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean
@@ -0,0 +1,192 @@
+/-
+Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: Seyoon Ragavan
+-/
+import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Reshaping implicit queries
+
+To compose implicitly logspace computable functions [AB09, Lemma 4.17's proof], a query
+`⟨x, bits i⟩` about `g (f x)` is reshaped into the query `⟨f x, bits i⟩` about `g`. This is
+`Complexity.compQ f`, and it is itself implicitly logspace computable. Both query languages of
+`g ∘ f` are then preimages of `g`'s along it (`Complexity.mem_indexLang_compQ_iff`), hence in
+`L` by `Complexity.mem_LOGSPACE_preimage`.
+
+Deciding `compQ f`'s own languages needs `f`'s queries at `⟨x, bits j⟩`. An abstract register
+machine on the host `⟨⟨x, bits i⟩, bits p⟩` can only present `⟨⟨⟨x, bits i⟩, bits p⟩, bits j⟩`
+(a `whole`-mode call). The index-dropping map `Complexity.dropIdx` takes
+`⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`; applied twice it recovers `⟨x, bits j⟩`.
+
+Phase P4.4b of `AroraBarakChapters3-4Plan.md`; see `audits/ch4-p44-resolutions-addendum.md`.
+
+## Main definitions
+
+* `Complexity.dropIdx` — `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` off that shape.
+* `Complexity.compQ` — `⟨x, b⟩ ↦ ⟨f x, b⟩` for canonical `b`, and `[]` otherwise.
+
+## Main results
+
+* `Complexity.dropIdx_pairEncode`, `Complexity.dropIdx_length_le` — the map on nested pairs;
+  its length bound.
+* `Complexity.compQ_pairEncode`, `Complexity.mem_indexLang_compQ_iff`,
+  `Complexity.compQ_length_le` — the map on queries; the preimage identity; the length bound.
+* `Complexity.implicitlyLogspaceComputable_dropIdx`,
+  `Complexity.ImplicitlyLogspaceComputable.compQ` — both maps are implicitly logspace
+  computable (sorried; phase-P4.4b statements).
+
+## References
+
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17 and its proof.)
+-/
+
+namespace Complexity
+
+open Turing
+
+/-- **Dropping the middle index**: `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` on words not of that
+shape. -/
+def dropIdx (z : List Bool) : List Bool :=
+  match pairDecode z with
+  | some (u, b') =>
+    match pairDecode u with
+    | some (w, _) => pairEncode w b'
+    | none => []
+  | none => []
+
+/-- `dropIdx` on a nested pair. -/
+theorem dropIdx_pairEncode (w b b' : List Bool) :
+    dropIdx (pairEncode (pairEncode w b) b') = pairEncode w b' := by
+  simp [dropIdx, pairDecode_pairEncode]
+
+/-- `dropIdx` never lengthens a word. -/
+theorem dropIdx_length_le (z : List Bool) : (dropIdx z).length ≤ z.length := by
+  unfold dropIdx
+  split
+  · rename_i u b' hz
+    split
+    · rename_i w b hu
+      rw [eq_pairEncode_of_pairDecode _ _ _ hz, eq_pairEncode_of_pairDecode _ _ _ hu]
+      simp only [length_pairEncode]
+      omega
+    · simp
+  · simp
+
+/-- **The query reshaping of a composition**: `⟨x, b⟩ ↦ ⟨f x, b⟩` when `b` is a canonical
+binary word (some `Nat.bits i`), and `[]` otherwise. -/
+def compQ (f : List Bool → List Bool) (w : List Bool) : List Bool :=
+  match pairDecode w with
+  | some (x, b) => if Nat.bits (LogProg.bitsVal b) = b then pairEncode (f x) b else []
+  | none => []
+
+/-- `compQ f` on a genuine query. -/
+theorem compQ_pairEncode (f : List Bool → List Bool) (x : List Bool) (i : ℕ) :
+    compQ f (pairEncode x (Nat.bits i)) = pairEncode (f x) (Nat.bits i) := by
+  simp [compQ, pairDecode_pairEncode, LogProg.bitsVal_bits]
+
+/-- **The preimage identity of composition**: a word is in `{⟨x, i⟩ | p (f x) i}` iff its
+reshaping is in `{⟨y, i⟩ | p y i}`. Malformed and non-canonical queries go to `[]`, which no
+index language contains. -/
+theorem mem_indexLang_compQ_iff (f : List Bool → List Bool) (p : List Bool → ℕ → Prop)
+    (w : List Bool) :
+    w ∈ indexLang (fun x i => p (f x) i) ↔ compQ f w ∈ indexLang p := by
+  constructor
+  · rintro ⟨x, i, rfl, hp⟩
+    exact ⟨f x, i, compQ_pairEncode f x i, hp⟩
+  · rintro ⟨y, i, h, hp⟩
+    unfold compQ at h
+    split at h
+    · rename_i x b hw
+      split_ifs at h with hb
+      · have := pairEncode_injective (a₁ := (f x, b)) (a₂ := (y, Nat.bits i)) h
+        simp only [Prod.mk.injEq] at this
+        obtain ⟨rfl, rfl⟩ := this
+        exact ⟨x, i, eq_pairEncode_of_pairDecode _ _ _ hw, hp⟩
+      · exact absurd h.symm (pairEncode_ne_nil _ _)
+    · exact absurd h.symm (pairEncode_ne_nil _ _)
+
+/-- `compQ f` is polynomially bounded when `f` is: `|compQ f w| ≤ (2C + 3)(|w| + 1)^{c+1}`
+from `|f x| ≤ C (|x| + 1)^c`. -/
+theorem compQ_length_le {f : List Bool → List Bool} {C c : ℕ}
+    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c) (w : List Bool) :
+    (compQ f w).length ≤ (2 * C + 3) * (w.length + 1) ^ (c + 1) := by
+  unfold compQ
+  split
+  · rename_i x b hw
+    split_ifs
+    · have hw' := eq_pairEncode_of_pairDecode _ _ _ hw
+      have hl : w.length = 2 * x.length + 2 + b.length := by rw [hw', length_pairEncode]
+      have e1 : (w.length + 1) ^ c ≤ (w.length + 1) ^ (c + 1) :=
+        Nat.pow_le_pow_right (by omega) (by omega)
+      have e2 : w.length + 1 ≤ (w.length + 1) ^ (c + 1) := by
+        calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
+          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
+      have e3 : (f x).length ≤ C * (w.length + 1) ^ c :=
+        (hf x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
+      have e4 : C * (w.length + 1) ^ c ≤ C * (w.length + 1) ^ (c + 1) :=
+        Nat.mul_le_mul_left _ e1
+      rw [length_pairEncode]
+      have e5 : (2 * C + 3) * (w.length + 1) ^ (c + 1) =
+          2 * (C * (w.length + 1) ^ (c + 1)) + 3 * (w.length + 1) ^ (c + 1) := by ring
+      omega
+    · simp
+  · simp
+
+/-- **Dropping the middle index is implicitly logspace computable** (phase P4.4b; spec, fill
+pending).
+
+**Proof sketch.**
+
+* **Bound.** `Complexity.dropIdx_length_le`.
+* **The ARM.** Both query languages come from one abstract register machine with a mode bit
+  over the access bank `![inputBitLang, inputLenLang]` (`inputBitLang_mem`,
+  `inputLenLang_mem`), by `LogProg.arm_decides_poly`. A `whole` call on `[r]` reads the host's
+  bit at `v r` (`LogProg.vword_whole₁`, `indicator_indexLang_pairEncode`).
+* **The run, on a host `h = ⟨z, bits q⟩`.**
+  * Validate `h` and its canonical tail.
+  * Before accumulating `q`, compare the tail's length with `|bits |h||`. If longer, then
+    `q ≥ |h| ≥ |dropIdx z|` and the answer is `false`.
+  * Decode `z = ⟨u, b'⟩` and `u = ⟨w, b⟩` by aligned scans at strides 2 and 4 of `h`. A failed
+    decode means `dropIdx z = []`, and the answer is `false`.
+  * Answer by position arithmetic: positions below `2|w| + 2` come from `u`, the rest from
+    `b'`.
+* **Registers** are at most `4|h| + 4`. -/
+theorem implicitlyLogspaceComputable_dropIdx : ImplicitlyLogspaceComputable dropIdx := by
+  sorry
+
+/-- **`comp`'s query reshaping is implicitly logspace computable** (phase P4.4b; spec, fill
+pending): if `f` is, so is `compQ f`.
+
+**Proof sketch.**
+
+* **Bound.** `Complexity.compQ_length_le`.
+* **The ARM.** Both query languages come from one abstract register machine with a mode bit
+  over a four-oracle bank (`LogProg.arm_decides_poly`):
+  * `inputBitLang` and `inputLenLang`;
+  * `{z | dropIdx (dropIdx z) ∈ L}` for `L` each of `f`'s two query languages. These are in
+    `L` by `Complexity.mem_LOGSPACE_preimage` twice along
+    `Complexity.implicitlyLogspaceComputable_dropIdx`.
+
+  A `whole` call on `[j]` from the host `h = ⟨w, bits p⟩` presents
+  `⟨⟨w, bits p⟩, bits j⟩`, which two `dropIdx` turn into `⟨x, bits j⟩` (`dropIdx_pairEncode`).
+* **The run** ([AB09, Lemma 4.17's proof]; the P4.4 audit's question-2 ledger):
+  * (i) Validate `h`, with the overflow test before storing `p`.
+  * (ii) Validate `w = ⟨x, b⟩` with `b` canonical: last bit `true`, using
+    `LogProg.canon_eq_bits` and `LogProg.canon_bits`.
+  * (iii) Find `F := |f x|` by lifted length queries at `j = 0, 1, …`, below `C (|x| + 1)^e`.
+  * (iv) Answer:
+    * `p < 2F`: the lifted bit at `⌊p/2⌋`;
+    * `p ∈ {2F, 2F + 1}`: the separator `[false, true]`;
+    * otherwise: `b`'s bit at `p − 2F − 2`, read from `h` at its doubled position;
+    * length: `p < 2F + 2 + |b|`. -/
+theorem ImplicitlyLogspaceComputable.compQ {f : List Bool → List Bool}
+    (hf : ImplicitlyLogspaceComputable f) : ImplicitlyLogspaceComputable (compQ f) := by
+  sorry
+
+end Complexity
diff --git a/TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean b/TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean
index c616e3b8..471988c1 100644
--- a/TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean
@@ -6,6 +6,7 @@ Authors: Seyoon Ragavan
 import TCSlib.Complexity.SpaceComplexity.SpaceClasses
 import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
 import TCSlib.Complexity.ClassNP.Reductions
+import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -78,14 +79,19 @@ implicitly logspace computable, so is `g ∘ f`.
 `f x` — maintain the index of the cell `g`'s head would scan (logarithmic in
 `|f x|`, hence in `|x|` by `f`'s polynomial output bound), and whenever
 `g`'s machine reads, suspend it and answer with `f`'s bit/length queries on
-`⟨x, i⟩`. The received `LogProg` layer is built for exactly this shape: the
-virtual-input discipline is `Machines/Layout`, the suspended-call protocol
-is `Machines/{Program,Sim,Call,CallReturn,Compile}` (`compile_correct`/
-`compile_space`), and the decider assembly is `arm_decides` — the fill
-instantiates them rather than building machines by hand. Obligations, named:
-the polynomial bound of the composite (`f`'s and `g`'s bounds composed); the
-two `indexLang` memberships of `g ∘ f` via the call protocol; the index
-bookkeeping (binary counters within `logSpace`, the `Machines/Bin` layer). -/
+`⟨x, i⟩`. The received `LogProg` call protocol does not host this shape by
+itself: a call's virtual input is read physically (the whole input, or its
+leading run of `1`s, followed by register words), so no call can serve `g`'s
+input from `f`'s queries (P0 reception audit, note 10). Fill route (phase
+P4.4b, `audits/ch4-p44-resolutions-addendum.md`): both query languages of
+`g ∘ f` are preimages of `g`'s along `Complexity.compQ f`
+(`Complexity.mem_indexLang_compQ_iff`), hence in `L` by
+`Complexity.mem_LOGSPACE_preimage` (the Fig. 4.3 engine,
+`Complexity.LogProg.OIS`) and `Complexity.ImplicitlyLogspaceComputable.compQ`.
+Obligations, named: the polynomial bound of the composite (`f`'s and `g`'s
+bounds composed, `D (C + 1)^d (|x| + 1)^{cd}`); the two preimage memberships;
+the index bookkeeping, which lives in `compQ`'s machines. (Sketch prose
+corrected at phase P4.4b; the statement is unchanged.) -/
 theorem ImplicitlyLogspaceComputable.comp {f g : List Bool → List Bool}
     (hf : ImplicitlyLogspaceComputable f) (hg : ImplicitlyLogspaceComputable g) :
     ImplicitlyLogspaceComputable (g ∘ f) := by

## ===== audits/logs/b7-statements-axioms.log =====

'Complexity.LogProg.readIn_run' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_id' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.run' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogProg.OIS.compile_decides' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_preimage' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.implicitlyLogspaceComputable_dropIdx' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.compQ' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.pairEncode_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.indicator_indexLang_pairEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.vword_whole₁' depends on axioms: [propext]
'Complexity.dropIdx_pairEncode' depends on axioms: [propext, Quot.sound]
'Complexity.dropIdx_length_le' depends on axioms: [propext, Quot.sound]
'Complexity.compQ_pairEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.mem_indexLang_compQ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.compQ_length_le' depends on axioms: [propext, Quot.sound]
'Complexity.inputBitLang_mem' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.inputLenLang_mem' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.ImplicitlyLogspaceComputable.comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.trans' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.mem_LOGSPACE_of_logspaceReducible' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Complexity.multLang_mem_LOGSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogProg.compile_space' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.bank_cleanRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.arm_decides_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.inc_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.dec_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.eq_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.clr_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.rewind_x' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LogProg.canon_eq_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.MultiTapeTM.abs_pos_lt_card_visited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.LOGSPACE_subset_NL' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== audits/logs/b7-statements-declfreeze.log =====

# Statement freeze over the two edited chapter files (HEAD 22b6c84a -> working tree).
# The only body changes are the D5 docstring (sketch-prose) corrections, authorized by the user-approved P4.4b restructure; no statement changed.
== Logspace/Reductions
public before/after: 7 7 private before/after: 0 0
public added: []
public removed: []
authorized body change: ImplicitlyLogspaceComputable.comp
private removed: []
private added: []
private changed: []
== Logspace/Mult
public before/after: 2 2 private before/after: 0 0
public added: []
public removed: []
authorized body change: multLang_mem_LOGSPACE
private removed: []
private added: []
private changed: []

## ===== audits/logs/b7-statements-order-closure.txt =====

TCSlib/Complexity/SpaceComplexity/Machines/Bin
TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Deterministic
TCSlib/Complexity/TuringMachine/StateRenaming
TCSlib/Complexity/TuringMachine/Finite
TCSlib/Complexity/TuringMachine/Simulation
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Sweep
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/ClassP/DTIME
TCSlib/Complexity/ClassP/P
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Build/Convention
TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Embed
TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/ClassNP/PolyTime
TCSlib/Complexity/Formulas/CNF
TCSlib/Complexity/Formulas/CNFEncoding
TCSlib/Complexity/ClassNP/PolyTimePairing
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Computable
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/ClassNP/Reductions
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeFormat
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/UnaryTape
TCSlib/Complexity/TuringMachine/CounterProg
TCSlib/Complexity/TuringMachine/CounterProgRun
TCSlib/Complexity/SpaceComplexity/Machines/Layout
TCSlib/Complexity/SpaceComplexity/Machines/Program
TCSlib/Complexity/SpaceComplexity/Machines/Sim
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn
TCSlib/Complexity/SpaceComplexity/Machines/Call
TCSlib/Complexity/SpaceComplexity/Machines/Compile
TCSlib/Complexity/SpaceComplexity/Machines/Lib
TCSlib/Complexity/SpaceComplexity/Basic
TCSlib/Complexity/SpaceComplexity/ConfigCount
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep
TCSlib/Complexity/SpaceComplexity/Machines/Clean
TCSlib/Complexity/SpaceComplexity/Machines/Bank
TCSlib/Complexity/SpaceComplexity/ImplicitPoly
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
TCSlib/Complexity/TimeHierarchy/ClockMachine
TCSlib/Complexity/TimeHierarchy/ClockLoop
TCSlib/Complexity/TimeHierarchy/CodePrefix
TCSlib/Complexity/TimeHierarchy/Diagonal
TCSlib/Complexity/TuringMachine/Nondeterministic
TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/TuringMachine/NondeterministicSpace
TCSlib/Complexity/SpaceComplexity/NSPACE
TCSlib/Complexity/SpaceComplexity/SpaceClasses
TCSlib/Complexity/SpaceComplexity/Constructible
TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/Inclusions
TCSlib/Complexity/SpaceComplexity/Examples
TCSlib/Complexity/SpaceComplexity/ZeroSpace
TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity

## ===== audits/logs/b7-statements-screen-after.txt =====

declarations screened: 192; copy pairs (target reproduces >= half of source): 53; reproduced text: 14,788 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%

## ===== audits/logs/b7-statements-screen-before.txt =====

declarations screened: 177; copy pairs (target reproduces >= half of source): 53; reproduced text: 14,788 chars
   ARMKit.lean::vword_unary₂  reproduces  ARMKit.lean::vword_unary₁: 176/176 = 100%
   ARMKit.lean::vword_unary₁  reproduces  ARMKit.lean::vword_unary₂: 176/176 = 100%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.trans: 200/202 = 99%
   ARMProof.lean::AReach.trans  reproduces  DblLang.lean::Rch.trans: 200/202 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   CounterProgSim.lean::upd_rT  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rP  reproduces  CounterProgSim.lean::upd_rO: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rT: 90/91 = 99%
   CounterProgSim.lean::upd_rO  reproduces  CounterProgSim.lean::upd_rP: 90/91 = 99%
   ImplicitPoly.lean::regCfg_cfg  reproduces  DblLang.lean::regCfg_K: 121/124 = 98%
   ARMProof.lean::AReach.halt  reproduces  ARMProof.lean::AReach.trans: 197/202 = 98%
   ARMProof.lean::AReach.halt  reproduces  DblLang.lean::Rch.trans: 185/202 = 92%
   ParsePlain.lean::validPlain_iff  reproduces  ARMKit.lean::takeWhile_pairEncode_replicate: 94/105 = 90%
   CounterProgSimRun.lean::Bd  reproduces  CounterProgSim.lean::cf: 190/220 = 86%
   DblLang.lean::regCfg_K  reproduces  ImplicitPoly.lean::regCfg_cfg: 121/143 = 85%
   ARMProof.lean::AReach.trans  reproduces  ARMProof.lean::AReach.halt: 197/236 = 83%
   DblLang.lean::sym_lt  reproduces  DblLang.lean::sym_eq: 83/101 = 82%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_eq: 82/101 = 81%
   CounterProgSim.lean::pr_halt  reproduces  CounterProgSim.lean::pr_reach: 836/1033 = 81%
   ParsePlain.lean::rrun_one_x  reproduces  Frag.lean::rrun_one_eq: 67/84 = 80%
   Frag.lean::rrun_one_eq  reproduces  ParsePlain.lean::rrun_one_x: 67/85 = 79%
   DblLang.lean::Rch.trans  reproduces  ARMProof.lean::AReach.halt: 185/236 = 78%
   FragDec.lean::rrun_one_reg  reproduces  Frag.lean::rrun_one_eq: 64/84 = 76%
   FragDec.lean::decDAct  reproduces  Lib.lean::incCAct: 61/82 = 74%
   DblLang.lean::sym_eq  reproduces  DblLang.lean::sym_lt: 83/112 = 74%
   CounterProgSim.lean::cf  reproduces  CounterProgSimRun.lean::Bd: 190/257 = 74%
   Parse.lean::jeqPlain_run  reproduces  DblLang.lean::sym_lt: 81/112 = 72%
   Frag.lean::half_run  reproduces  FragDec.lean::clr_run: 375/520 = 72%
   Frag.lean::eqB_run  reproduces  Parse.lean::regBack_x: 617/864 = 71%
   CounterProgSimRun.lean::ans_append  reproduces  CounterProgSimRun.lean::ans_of_le: 60/86 = 70%
   Lib.lean::incB_run  reproduces  Frag.lean::eqB_run: 654/938 = 70%
   FragDec.lean::decD_run  reproduces  Lib.lean::incC_run: 1179/1733 = 68%
   Frag.lean::halfL_run  reproduces  FragDec.lean::clrE_run: 928/1366 = 68%
   CounterProgSimRun.lean::ans_of_le  reproduces  CounterProgSimRun.lean::ans_append: 60/90 = 67%
   ImplicitPoly.lean::rounds  reproduces  DblLang.lean::Rch.trans: 134/202 = 66%
   CounterProgSim.lean::pr_reach  reproduces  CounterProgSim.lean::pr_halt: 836/1262 = 66%
   Parse.lean::regBack_x  reproduces  Frag.lean::eqB_run: 617/938 = 66%
   FragDec.lean::clrEAct  reproduces  FragDec.lean::toEndAct: 144/229 = 63%
   Lib.lean::incB_run  reproduces  Parse.lean::regBack_x: 536/864 = 62%
   Frag.lean::eqB_run  reproduces  Lib.lean::incB_run: 654/1066 = 61%
   Lib.lean::incB_run  reproduces  FragDec.lean::toEnd_run: 582/951 = 61%
   Frag.lean::rrun_one_eq  reproduces  FragDec.lean::rrun_one_reg: 64/110 = 58%
   FragDec.lean::clr_run  reproduces  Frag.lean::half_run: 375/653 = 57%
   Lib.lean::inc_run  reproduces  FragDec.lean::dec_run: 372/670 = 56%
   CounterProgSimRun.lean::UnaryLogspace.counterProg  reproduces  UnaryLogspace.lean::ltLang_mem: 580/1051 = 55%
   Lib.lean::incCAct  reproduces  FragDec.lean::decDAct: 61/111 = 55%
   FragDec.lean::toEnd_run  reproduces  Lib.lean::incB_run: 582/1066 = 55%
   ConfigCount.lean::ComputesInTime.of_spaceUsed_le  reproduces  ConfigCount.lean::visitedByTapeHead_mono: 61/114 = 54%
   FragDec.lean::dec_run  reproduces  Lib.lean::inc_run: 372/707 = 53%
   DblLang.lean::dblLang_mem  reproduces  UnaryLogspace.lean::orc_eq: 76/150 = 51%
   Parse.lean::regBack_x  reproduces  Lib.lean::incB_run: 536/1066 = 50%
   Lib.lean::update_bufferTape_cons  reproduces  FragDec.lean::bufferTape_erase_last: 137/273 = 50%

## ===== audits/logs/b7-statements-stylelint.log =====

INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          191 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    493 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    612 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    612 lines; 16 public / 12 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  95 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       147 lines; 4 public / 1 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      234 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     115 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  116 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean           200 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  74 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  136 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean          256 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean          192 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            153 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   307 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean                93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              333 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean                551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   176 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               266 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               347 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Savitch.lean                        131 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   86 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean                      264 lines; 11 public / 2 private declarations

style_lint: 0 FAIL, 0 WARN over 45 files

## ===== audits/logs/b7-statements-sweep-after.log =====

== TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean:152:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean:191:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean:181:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean:220:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean:252:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:188:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:95:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:105:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:125:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:149:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:71:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity
exit=0

## ===== audits/logs/b7-statements-sweep-before.log =====

== TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:89:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:99:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:119:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:143:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/Path
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:104:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean:133:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity/Logspace/Mult
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:65:8: warning: declaration uses 'sorry'
exit=0
== TCSlib/Complexity/SpaceComplexity
exit=0

## ===== audits/evidence/retrofit/copy-text-screen.py =====

```
"""Text-level copy screen for retrofit deliveries (introduced after RB4).

Declaration counts can be satisfied by inlining a copy into its consumer.
This screen measures copied *text* instead. For the given Lean files it lists
every like-kind pair (proof vs proof, term vs term) in which one declaration
reproduces at least half of another's extracted body (at least 60 characters,
greedy tiling with blocks of at least 25), within a file and across the given
files. It also prints the total reproduced text. Run it before and after a
change: a pair present after but not before is new duplication; inlining a
deleted copy into a consumer shows up as such a pair.
Usage: python3 -I copy-text-screen.py <repo-root> <file.lean> [<file.lean> ...]
"""
import re, sys
root, files = sys.argv[1], sys.argv[2:]
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiled(a, b):
    c = 0
    while True:
        n, seg = lcs(a, b)
        if n < 25: return c
        c += n; a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
grams = lambda x: {x[i:i + 25] for i in range(len(x) - 24)}
decls = []
for f in files:
    t = strip(open(f'{root}/{f}', encoding='utf-8').read()); ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        if len(bd) >= 60: decls.append((f.split('/')[-1], m.group(3), kind, bd, grams(bd)))
pairs = []; total = 0
for (fa, a, ka, ta, ga) in decls:
    for (fb, b, kb, tb, gb) in decls:
        if (fa, a) == (fb, b) or ka != kb or not (ga & gb): continue
        sh = tiled(tb, ta)
        if sh >= 60 and 2 * sh >= len(tb):
            pairs.append((sh / len(tb), sh, len(tb), f'{fa}::{a}', f'{fb}::{b}')); total += sh
pairs.sort(reverse=True)
print(f"declarations screened: {len(decls)}; copy pairs (target reproduces >= half of source): {len(pairs)}; reproduced text: {total:,} chars")
for frac, sh, ln, a, b in pairs:
    print(f"   {a}  reproduces  {b}: {sh}/{ln} = {frac:.0%}")
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random access to a general input in logarithmic space

A logspace machine reads its input at a position held in binary on a work tape [AB09, §4.1:
"a pointer into the input"]. The received `LogProg` layer has no such access for a general
(non-unary) input: the input instructions of `Complexity.LogProg.ARM` presuppose inputs
`⟨1ⁿ, w⟩` or `⟨1ⁿ, ⟨u, w⟩⟩`, and a call's virtual input is the whole input or its leading run
of `1`s followed by register words (P0 reception audit, `audits/ch34-p0-findings.md`). This
file supplies the missing piece twice, at the two levels later logspace programs use:

* **as a program fragment**: `Complexity.LogProg.readIn_run` reads bit `i` of the input,
  `i` held in binary on a register, into the control state (a counter register stepped up to
  `i` in lockstep with the input head, the received equality, increment, rewind and clear
  fragments), and restores everything else;
* **as a language pair**: `Complexity.implicitlyLogspaceComputable_id` — the bit and length
  languages of the identity, `Complexity.inputBitLang` and `Complexity.inputLenLang`, are in
  `L` — so an abstract register machine reads its own input at a register-held position by a
  `whole`-mode call with that register as its one argument (`Complexity.LogProg.vword_whole₁`,
  `Complexity.indicator_indexLang_pairEncode`).

Phase P4.4b of `AroraBarakChapters3-4Plan.md` (the B7 statement mini-phase, recorded in
`audits/ch4-p44-resolutions-addendum.md`). The fragment is campaign-owned and lives here,
not in `Machines/`, by decision D3; it is built only from received fragments.

## Main definitions

* `Complexity.LogProg.RdPh`, `Complexity.LogProg.readTr` — the phases and the transition
  table of the input-read fragment.
* `Complexity.inputBitLang`, `Complexity.inputLenLang` — `{⟨u, i⟩ | uᵢ = 1}` and
  `{⟨u, i⟩ | i < |u|}`.

## Main results

* `Complexity.LogProg.vword_whole₁` — a `whole` call with one argument presents `⟨u, V r⟩`.
* `Complexity.indicator_indexLang_pairEncode` — the answer of an `indexLang` decider on a
  genuine pair.
* `Complexity.pairEncode_ne_nil` — no pair is empty (so `[]` lies in no `indexLang`).
* `Complexity.LogProg.readIn_run` — the input-read fragment (sorried; phase-P4.4b
  statement).
* `Complexity.implicitlyLogspaceComputable_id` — input random access in `L` (sorried;
  phase-P4.4b statement), with `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16.)
-/

namespace Complexity

open Turing

/-- No pair encoding is the empty word: `pairEncode x y` contains the separator. -/
theorem pairEncode_ne_nil (x y : List Bool) : pairEncode x y ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [length_pairEncode] at this

/-- **The answer of an index-language decider on a genuine pair**: the indicator of
`indexLang p` at `⟨u, bits v⟩` is the decision of `p u v`. -/
theorem indicator_indexLang_pairEncode (p : List Bool → ℕ → Prop) (u : List Bool) (v : ℕ) :
    MultiTapeTM.indicator (indexLang p : Set (List Bool)) (pairEncode u (Nat.bits v)) =
      @decide (p u v) (Classical.dec _) := by
  rw [LogProg.indicator_eq_decide]
  exact decide_eq_decide.mpr (pairEncode_mem_indexLang p u v)

namespace LogProg

/-- **A `whole`-mode call with one argument** presents the pair of the whole input and the
argument register's word: its virtual input is `⟨u, V r⟩`. -/
theorem vword_whole₁ {m d : ℕ} {Λ : Type} (u : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .whole, [r], l₁, l₀⟩ u V) = pairEncode u (V r) := by
  simp [callSegs, Mode.seg0, argSegs, vword, render, pairEncode_eq_dbl]

/-! ## The input-read fragment -/

/-- The phases of the input-read fragment: the equality test of the counter with the index
(`eC`, `eBy`, `eBn`), the read (`yes`) or advance (`no`) step, the counter increment (`iC`,
`iB`), and, carrying the symbol read, the input rewind (`rw₁`, `rw₂`) and the counter clear
(`cR`, `cE`). -/
inductive RdPh where
  | eC | eBy | eBn
  | yes | no
  | iC | iB
  | rw₁ (a : Option Bool) | rw₂ (a : Option Bool)
  | cR (a : Option Bool) | cE (a : Option Bool)
  deriving DecidableEq, Fintype

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- **The transition table of the input-read fragment** on index register `r` and counter
register `s`, its phases embedded by `st` and its exits by `ex`. With the input head on
position `k + 1` (input symbol `k`) and the counter holding `bits k`: compare the counter with
the index (`eq_run`); if equal, take the symbol under the head; if not, stop at the right
blank, or else step the input head right and increment the counter (`inc_run`). Then rewind
the input head to position `1` (`rewind_x`) and clear the counter (`clr_run`), exiting into
`ex a` with the symbol `a` taken. -/
def readTr (r s : Fin m) (st : RdPh → Λ) (ex : Option Bool → Λ) :
    RdPh → Option Bool → (Fin m → Option Bool) → Action m Bool Λ
  | .eC, _, w => eqCAct s r (st .eC) (st .eBy) (st .eBn) (w s) (w r)
  | .eBy, _, w => eqBAct s r (st .eBy) (st .yes) (w s)
  | .eBn, _, w => eqBAct s r (st .eBn) (st .no) (w s)
  | .yes, a, _ => goAct (st (.rw₁ a))
  | .no, a, _ =>
    match a with
    | none => goAct (st (.rw₁ none))
    | some _ => xAct s 1 0 (st .iC)
  | .iC, _, w => incCAct s (st .iC) (st .iB) (w s)
  | .iB, _, w => incBAct s (st .iB) (st .eC) (w s)
  | .rw₁ a, _, _ => xAct s (-1) 0 (st (.rw₂ a))
  | .rw₂ a, b, _ => rw2Act s (st (.rw₂ a)) (st (.cR a)) b
  | .cR a, _, w => toEndAct s (st (.cR a)) (st (.cE a)) (w s)
  | .cE a, _, w => clrEAct s (st (.cE a)) (ex a) (w s)

section Read

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r s : Fin m) (hrs : r ≠ s)
  (st : RdPh → Λ) (ex : Option Bool → Λ)
  (htr : ∀ ph a w, P.tm.tr (st ph) a w = readTr r s st ex ph a w)
  (hc : ∀ ph, P.call (st ph) = none)

include hrs htr hc in
/-- **The input-read fragment** (phase P4.4b; spec, fill pending): from phase `eC`, with
`bits i` on the index register `r`, an empty counter register `s`, both heads on cell `0` and
the input head on position `1`, the program reaches the exit `ex x[i]?` — symbol `i` of the
input, `none` when `i ≥ |x|` — in the same configuration otherwise (registers, heads, input
position and output restored). Throughout, only registers `s` and `r` change (the tape of `s`,
the heads of both), both heads stay in `[-1, |bits (|x| + 1)|]`, and every state is an
ordinary fragment state: the fragment's space is these two ranges, independently of `i`.
A hand-built fragment: no received layer reads a general input at a register-held position
(the `Parse` fragments assume unary-first inputs).

**Proof sketch.** Induction on the counter value `k ≤ min i |x|`, the input head on position
`k + 1`. `eq_run` (with `r₁ := s`, so both heads stay within `|bits k|`) compares `bits k`
with `bits i`. If `k = i`, phase `yes` takes `inSym x (i + 1) = x[i]?`. Otherwise phase `no`
reads `inSym x (k + 1)`: at the right blank (`k = |x| < i`) the symbol taken is
`none = x[i]?`; on a letter (`k < |x|`) the head steps right and `inc_run` turns `bits k` into
`bits (k + 1)`, `k + 1 ≤ |x|`. Then `rewind_x` returns the input head to position `1`, and
`clr_run` empties the counter (its head within `|bits k|`). -/
theorem readIn_run (c : Cfg m Bool Λ x) (i : ℕ)
    (hr : c.workTapes r = FinTM.bufferTape (Nat.bits i)) (hs : c.workTapes s = FinTM.bufferTape [])
    (hrp : c.workTapePos r = 0) (hsp : c.workTapePos s = 0) (hip : c.inputPos.val = 1) :
    ∃ T, rrun P oracle { c with state := some (st .eC) } T = { c with state := some (ex x[i]?) } ∧
      ∀ t < T, ∃ (ph : RdPh) (ip : Fin (x.length + 2)) (f : ℤ → Option Bool) (q q' : ℤ),
        rrun P oracle { c with state := some (st .eC) } t =
          ⟨some (st ph), ip, Function.update c.workTapes s f,
            Function.update (Function.update c.workTapePos s q) r q', c.output⟩ ∧
        -1 ≤ q ∧ q ≤ (Nat.bits (x.length + 1)).length ∧
        -1 ≤ q' ∧ q' ≤ (Nat.bits (x.length + 1)).length := by
  sorry

end Read

end LogProg

/-! ## Input access as a language pair -/

/-- The bit language of the identity: `{⟨u, bits i⟩ | uᵢ = 1}` (`0`-based; `false` beyond the
end). -/
def inputBitLang : Language Bool := indexLang fun u i => u.getD i false = true

/-- The length language of the identity: `{⟨u, bits i⟩ | i < |u|}`. -/
def inputLenLang : Language Bool := indexLang fun u i => i < u.length

/-- **Input random access is logspace** (phase P4.4b; spec, fill pending): the identity is
implicitly logspace computable — its output bound is trivial and its two query languages,
`Complexity.inputBitLang` and `Complexity.inputLenLang`, are in `L`. [AB09, §4.1: a pointer
into the input] It is stated, and will be proved, as a corollary of
`Complexity.LogProg.readIn_run`.

**Proof sketch.** The bound is `|x| ≤ 1 · (|x| + 1)^1`. For the two languages, one call-free
register program with a mode bit, compiled against the empty bank `LogProg.Dbl.nilTM` as in
`LogProg.dblLang_mem` (`compile_space`): on `y`, validate `y = pairEncode z (bits r)` (an
aligned two-cell scan to the first aligned `[false, true]`, then a canonical tail — empty or
ending in `true`), reading each cell with `readIn_run`; reject otherwise. Then walk a counter
`k` over the pairs of `dbl z`, comparing `bits k` with the tail in lockstep (the comparison
pattern of `LogProg.cmpPlain_run`); on a match answer cell `2k` (resp. `true`), at the
separator answer `false`. Every register stays within `|bits |y||` cells. -/
theorem implicitlyLogspaceComputable_id : ImplicitlyLogspaceComputable id := by
  sorry

/-- `Complexity.inputBitLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputBitLang_mem : inputBitLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.1

/-- `Complexity.inputLenLang` is in `L` (from `Complexity.implicitlyLogspaceComputable_id`). -/
theorem inputLenLang_mem : inputLenLang ∈ LOGSPACE := implicitlyLogspaceComputable_id.2.2

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The oracle-input simulator: logspace preimages along implicit functions

[AB09, proof of Lemma 4.17, Fig. 4.3]: to decide whether `f x ∈ C`, run `C`'s logspace decider
`M` on a **virtual input** `f x` that is never written down. Whenever `M` reads its input, its
head position (in binary) is a query `⟨x, i⟩` to the length and bit deciders of `f`. The
received `LogProg` call protocol does not host this by itself. A call's virtual input is read
physically, as the whole input or its leading run of `1`s followed by register words, and
nothing serves a decider's input symbols through further calls (P0 reception audit,
`audits/ch34-p0-findings.md`, note 10). This file adds the missing engine as a register-tape
program on the received compiler.

The **oracle-input simulator** `Complexity.LogProg.OIS.prog M` keeps `M`'s work tapes on
registers `0, …, M.k − 1`, where they are touched only by `M`'s own transitions. It keeps `M`'s
input position `p` as the index `p − 1` in binary on the last register `q` (with `p = 0`, the
left blank, recorded in the control state). Each step of `M` runs as follows:

1. one `whole`-mode call on `[q]` asks the length decider whether `p − 1 < |f x|`;
2. if so, a second call asks the bit decider for the symbol;
3. one ordinary step applies `M`'s transition to the work registers;
4. the increment and decrement fragments move `q` as `M`'s clamped input move dictates.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; `audits/ch4-p44-resolutions-addendum.md`
records it as the route of `Complexity.mem_LOGSPACE_of_logspaceReducible`. The simulator is
campaign-owned and lives here (decision D3), beside its only class-level corollary.

## Main definitions

* `Complexity.LogProg.OIS.Ph`, `OIS.tr`, `OIS.call` — the phases, ordinary transitions and
  call nodes of the simulator.
* `Complexity.LogProg.OIS.prog`, `OIS.start` — the simulator program and its start state.
* `Complexity.LogProg.OIS.lo`, `OIS.hi` — its register ranges.

## Main results

* `Complexity.LogProg.OIS.run` — the run contract: against any oracle answering the two
  queries truthfully, the program halts with `M`'s output on the virtual input, inside the
  ranges, with well-formed calls (sorried; phase-P4.4b statement).
* `Complexity.LogProg.OIS.compile_decides` — the space contract: compiled against a bank of
  the two deciders, it computes `M`'s output on the virtual input within the ranges plus the
  bank's space (sorried; phase-P4.4b statement).
* `Complexity.mem_LOGSPACE_preimage` — logspace preimages along implicitly logspace
  computable maps are in `L` (sorried; phase-P4.4b statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17 and its proof, Figure 4.3.)
-/

namespace Complexity

open Turing

namespace LogProg.OIS

/-- The phases of the simulator: the length call (`ask`) and the bit call (`bit`); the
simulated step with the symbol read (`work a lb`, `lb` marking the left blank); the zero test
before a left move (`zt`); the increment (`iC`, `iB`) and decrement (`dD`, `dL`, `dE`, `dB`)
of the index register. -/
inductive Ph where
  | ask | bit
  | work (a : Option Bool) (lb : Bool)
  | zt
  | iC | iB
  | dD | dL | dE | dB
  deriving DecidableEq, Fintype

variable (M : FinTM Bool)

/-- The index register of the simulator, the last one. -/
abbrev q : Fin (M.k + 1) := Fin.last M.k

/-- The phase after a simulated step, from the decider's input move `d`, at the left blank
(`lb`) or at the right blank (`rb`): from the left blank, a right move reaches position `1`
(index `0`); elsewhere a left move first tests the index for zero, and a right move increments
it unless clamped at the right blank. -/
def nextPh (d : SignType) (lb rb : Bool) : Ph :=
  if lb then (if d = 1 then .ask else .work none true)
  else if d = -1 then .zt
  else if d = 1 ∧ rb = false then .iC
  else .ask

/-- The decider's action on the work registers: input head and index register still, output
forwarded, the next phase by `nextPh`. -/
def liftAct (A : Action M.k Bool M.State) (lb rb : Bool) : Action (M.k + 1) Bool (M.State × Ph) :=
  ⟨0, Fin.lastCases (none, 0) A.workTapes, A.output,
    A.state.map fun s' => (s', nextPh A.inputTape lb rb)⟩

/-- **The ordinary transitions of the simulator.** `work a lb` applies `M`'s transition at the
symbol `a` (at the right blank exactly when `a = none` and not `lb`); `zt` reads the index
register's cell `0` (blank iff the index is `0`); the increment and decrement fragments act on
the index register and return to `ask`. The call phases' transitions are never used. -/
def tr : M.State × Ph → Option Bool → (Fin (M.k + 1) → Option Bool) →
    Action (M.k + 1) Bool (M.State × Ph)
  | (s, .work a lb), _, w =>
    liftAct M (M.tm.tr s a fun i => w i.castSucc) lb (a.isNone && !lb)
  | (s, .zt), _, w =>
    regAct (q M) none 0 (match w (q M) with
      | none => (s, .work none true)
      | some _ => (s, .dD))
  | (s, .iC), _, w => incCAct (q M) (s, .iC) (s, .iB) (w (q M))
  | (s, .iB), _, w => incBAct (q M) (s, .iB) (s, .ask) (w (q M))
  | (s, .dD), _, w => decDAct (q M) (s, .dD) (s, .dL) (s, .dB) (w (q M))
  | (s, .dL), _, w => decLAct (q M) (s, .dE) (s, .dB) (w (q M))
  | (s, .dE), _, _ => decEAct (q M) (s, .dB)
  | (s, .dB), _, w => incBAct (q M) (s, .dB) (s, .ask) (w (q M))
  | (_, .ask), _, _ => junkAct
  | (_, .bit), _, _ => junkAct

/-- **The call nodes of the simulator.** `ask` asks decider `0` (the length language) about
`⟨x, bits i⟩`, `i` the index register: on *yes* go on to `bit`; on *no* the symbol is the right
blank. `bit` asks decider `1` (the bit language) and goes on to the simulated step with the
answer. -/
def call : M.State × Ph → Option (CallSpec (M.k + 1) 2 (M.State × Ph))
  | (s, .ask) => some ⟨0, .whole, [q M], (s, .bit), (s, .work none false)⟩
  | (s, .bit) => some ⟨1, .whole, [q M], (s, .work (some true) false),
      (s, .work (some false) false)⟩
  | _ => none

/-- **The oracle-input simulator** of the decider `M`: a register-tape program over `M.k + 1`
registers calling two deciders. A hand-built program: no received layer serves a decider's
input from oracle calls. -/
def prog : RProg (M.k + 1) 2 (M.State × Ph) := ⟨⟨(M.tm.q₀, .ask), tr M⟩, call M⟩

/-- The start state of the simulator: `M`'s start state, about to ask for symbol `0`. -/
def start : M.State × Ph := (M.tm.q₀, .ask)

/-- The lower register bounds: `-S` on the work registers, `-1` on the index register. -/
def lo (S : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (-1) fun _ => -(S : ℤ)

/-- The upper register bounds: `S` on the work registers, `W` on the index register. -/
def hi (S W : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (W : ℤ) fun _ => (S : ℤ)

/-- **The run contract of the simulator** (phase P4.4b; spec, fill pending). Let `M` halt
by time `t` on the virtual input `v`. Let the oracle answer every length query
`⟨x, bits i⟩` with `i ≤ |v|`, and every bit query with `i < |v|`, truthfully. Then the
program, started on the host input `x`:

* halts with `M`'s output on `v`;
* keeps the work registers in `[-S, S]`, with `S` the space `M` uses up to `t`;
* keeps the index register in `[-1, |bits (|v| + 1)|]`;
* at every call has the input head on position `1` and the index register holding some
  `bits i`, `i ≤ |v|`, with its head on cell `0` — so the call's virtual input is
  `⟨x, bits i⟩` (`Complexity.LogProg.vword_whole₁`).

**Proof sketch.** Encode `M`'s configuration `c` on `v` as the program configuration with:

* the work tapes and heads of `c` on registers `castSucc i`;
* `bits (p − 1)` on `q`, with its head on `0` (`p` the input position of `c`; `bits 0` at
  `p = 0`);
* the host input head on `1`, and `c`'s output;
* state `(s, ask)`, or `(s, work none true)` at `p = 0`.

By induction on `n ≤ t`, the run reaches the encoding of `M.tm.runFrom (M.tm.initCfg v) n`
until `M` halts. One step goes as follows.

1. At most two calls fix the symbol `inSym v p`: by the oracle laws, the length call says
   `p − 1 < |v|`.
2. `work` applies `M.tm.tr` to the `castSucc` block (`liftAct`), so the work registers move
   exactly as `M`'s tapes.
3. The clamped move of `p` is realized by `nextPh`:
   * `inc_run` only when `p − 1 < |v|`;
   * the zero test and `dec_run` only when `p − 1 ≥ 1`;
   * a phase change at the left blank.

Intermediate configurations are those of the received fragments on `q`. The work heads are
`M`'s, so they lie in `[-S, S]` by `Turing.MultiTapeTM.abs_pos_lt_card_visited`. Template:
`ImplicitEnum.{round, rounds, run}`. -/
theorem run (x v : List Bool) (o : Fin 2 → List Bool → Bool)
    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false)
    (t : ℕ) (ht : (M.tm.runFrom (M.tm.initCfg v) t).state = none) :
    ∃ N, (rrun (prog M) o (Cfg.init (start M) x) N).state = none ∧
      (rrun (prog M) o (Cfg.init (start M) x) N).output =
        (M.tm.runFrom (M.tm.initCfg v) t).output ∧
      (∀ n ≤ N, ∀ r,
        lo M (M.tm.spaceUsed (M.tm.initCfg v) t) r ≤
            (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ≤
            hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length r) ∧
      ∀ n < N, ∀ l cs, (rrun (prog M) o (Cfg.init (start M) x) n).state = some l →
        (prog M).call l = some cs →
          (rrun (prog M) o (Cfg.init (start M) x) n).inputPos.val = 1 ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos (q M) = 0 ∧
          ∃ i ≤ v.length, (rrun (prog M) o (Cfg.init (start M) x) n).workTapes (q M) =
            FinTM.bufferTape (Nat.bits i) := by
  sorry

/-- **The space contract of the simulator** (phase P4.4b; spec, fill pending). Let:

* deciders `Ms j` decide `As j` in space `sb j`;
* on genuine queries about the host input `x`, `As 0` be the length language and `As 1` the
  bit language of the virtual input `v`;
* `M` compute `w` on `v` by time `t`;
* `B` bound the bank's clean-run radius on every query `⟨x, bits i⟩` with `i ≤ |v|`.

Then the simulator, compiled against the bank of the `Ms j`, computes `w` on `x`, visiting at
most `M.k (2S + 1) + (|bits (|v| + 1)| + 2) + kD (2B + 1)` work cells, where `S` is the space
`M` uses up to `t` and `kD` the bank's tape count.

**Proof sketch.** Take `OIS.run` with the oracle `j, V ↦ [V ∈ As j]`, whose laws are the two
hypotheses. Then apply `compile_space` with the ranges `OIS.lo` and `OIS.hi`; their sizes sum
to the first two terms. Each call's precondition `CallOK` comes from `OIS.run`'s call clause:

* the virtual input is `⟨x, bits i⟩` by `vword_whole₁` and `tapeWord_bufferTape`;
* the clean run of the bank is `bank_cleanRun`, weakened to `B` by `CleanRun.mono`;
* `|bits i| ≤ |bits (|v| + 1)|` by `length_bits_mono`. -/
theorem compile_decides (Ms : Fin 2 → FinTM Bool) (As : Fin 2 → Language Bool)
    (sb : Fin 2 → ℕ → ℕ) (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j)) (x v w : List Bool)
    (hA0 : ∀ i ≤ v.length, pairEncode x (Nat.bits i) ∈ As 0 ↔ i < v.length)
    (hA1 : ∀ i < v.length, pairEncode x (Nat.bits i) ∈ As 1 ↔ v.getD i false = true)
    (t : ℕ) (ht : M.ComputesInTime v w t) (B : ℕ)
    (hB : ∀ j, ∀ i ≤ v.length, max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B) :
    ∃ T, (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).ComputesInTime x w T ∧
      (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.spaceUsed
          ((compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.initCfg x) T ≤
        M.k * (2 * M.tm.spaceUsed (M.tm.initCfg v) t + 1) +
          ((Nat.bits (v.length + 1)).length + 2) + (bankK Ms + bankK Ms) * (2 * B + 1) := by
  sorry

end LogProg.OIS

/-- **Logspace preimages along implicitly logspace computable maps are logspace**
(phase P4.4b; spec, fill pending): if `f` is implicitly logspace computable and `C ∈ L`, then
`{x | f x ∈ C} ∈ L`. [AB09, Lemma 4.17(2), in preimage form; its proof's Fig. 4.3] It is stated,
and will be proved, as a corollary of `Complexity.LogProg.OIS.compile_decides`.

**Proof sketch.** Unpack `f`'s bound `C₀ (|x| + 1)^e` and its two deciders (spaces `c₀`,
`c₁` times `logSpace`), and `C`'s decider `M` (space `c · logSpace`). For each `x`, take the
time `t` of `M` on `v := f x`, and apply `OIS.compile_decides` with:

* the bank `![length decider, bit decider]`;
* the laws `pairEncode_mem_indexLang`;
* `B := (c₀ + c₁) · logSpace (2|x| + 2 + |bits (|f x| + 1)|) + 1`.

The indicator `[f x ∈ C]` is `[x ∈ {x | f x ∈ C}]`. The bound is `O(logSpace |x|)`:
`logSpace |f x|` and `|bits (|f x| + 1)|` are at most `K · logSpace |x|` by
`LogProg.log_poly_bound`, since `|f x| ≤ C₀ (|x| + 1)^e`. The arithmetic follows
`ImplicitlyLogspaceComputable.computesInSpace`. -/
theorem mem_LOGSPACE_preimage {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    {C : Language Bool} (hC : C ∈ LOGSPACE) : ({x | f x ∈ C} : Language Bool) ∈ LOGSPACE := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reshaping implicit queries

To compose implicitly logspace computable functions [AB09, Lemma 4.17's proof], a query
`⟨x, bits i⟩` about `g (f x)` is reshaped into the query `⟨f x, bits i⟩` about `g`. This is
`Complexity.compQ f`, and it is itself implicitly logspace computable. Both query languages of
`g ∘ f` are then preimages of `g`'s along it (`Complexity.mem_indexLang_compQ_iff`), hence in
`L` by `Complexity.mem_LOGSPACE_preimage`.

Deciding `compQ f`'s own languages needs `f`'s queries at `⟨x, bits j⟩`. An abstract register
machine on the host `⟨⟨x, bits i⟩, bits p⟩` can only present `⟨⟨⟨x, bits i⟩, bits p⟩, bits j⟩`
(a `whole`-mode call). The index-dropping map `Complexity.dropIdx` takes
`⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`; applied twice it recovers `⟨x, bits j⟩`.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; see `audits/ch4-p44-resolutions-addendum.md`.

## Main definitions

* `Complexity.dropIdx` — `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` off that shape.
* `Complexity.compQ` — `⟨x, b⟩ ↦ ⟨f x, b⟩` for canonical `b`, and `[]` otherwise.

## Main results

* `Complexity.dropIdx_pairEncode`, `Complexity.dropIdx_length_le` — the map on nested pairs;
  its length bound.
* `Complexity.compQ_pairEncode`, `Complexity.mem_indexLang_compQ_iff`,
  `Complexity.compQ_length_le` — the map on queries; the preimage identity; the length bound.
* `Complexity.implicitlyLogspaceComputable_dropIdx`,
  `Complexity.ImplicitlyLogspaceComputable.compQ` — both maps are implicitly logspace
  computable (sorried; phase-P4.4b statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17 and its proof.)
-/

namespace Complexity

open Turing

/-- **Dropping the middle index**: `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` on words not of that
shape. -/
def dropIdx (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, b') =>
    match pairDecode u with
    | some (w, _) => pairEncode w b'
    | none => []
  | none => []

/-- `dropIdx` on a nested pair. -/
theorem dropIdx_pairEncode (w b b' : List Bool) :
    dropIdx (pairEncode (pairEncode w b) b') = pairEncode w b' := by
  simp [dropIdx, pairDecode_pairEncode]

/-- `dropIdx` never lengthens a word. -/
theorem dropIdx_length_le (z : List Bool) : (dropIdx z).length ≤ z.length := by
  unfold dropIdx
  split
  · rename_i u b' hz
    split
    · rename_i w b hu
      rw [eq_pairEncode_of_pairDecode _ _ _ hz, eq_pairEncode_of_pairDecode _ _ _ hu]
      simp only [length_pairEncode]
      omega
    · simp
  · simp

/-- **The query reshaping of a composition**: `⟨x, b⟩ ↦ ⟨f x, b⟩` when `b` is a canonical
binary word (some `Nat.bits i`), and `[]` otherwise. -/
def compQ (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  match pairDecode w with
  | some (x, b) => if Nat.bits (LogProg.bitsVal b) = b then pairEncode (f x) b else []
  | none => []

/-- `compQ f` on a genuine query. -/
theorem compQ_pairEncode (f : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    compQ f (pairEncode x (Nat.bits i)) = pairEncode (f x) (Nat.bits i) := by
  simp [compQ, pairDecode_pairEncode, LogProg.bitsVal_bits]

/-- **The preimage identity of composition**: a word is in `{⟨x, i⟩ | p (f x) i}` iff its
reshaping is in `{⟨y, i⟩ | p y i}`. Malformed and non-canonical queries go to `[]`, which no
index language contains. -/
theorem mem_indexLang_compQ_iff (f : List Bool → List Bool) (p : List Bool → ℕ → Prop)
    (w : List Bool) :
    w ∈ indexLang (fun x i => p (f x) i) ↔ compQ f w ∈ indexLang p := by
  constructor
  · rintro ⟨x, i, rfl, hp⟩
    exact ⟨f x, i, compQ_pairEncode f x i, hp⟩
  · rintro ⟨y, i, h, hp⟩
    unfold compQ at h
    split at h
    · rename_i x b hw
      split_ifs at h with hb
      · have := pairEncode_injective (a₁ := (f x, b)) (a₂ := (y, Nat.bits i)) h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨x, i, eq_pairEncode_of_pairDecode _ _ _ hw, hp⟩
      · exact absurd h.symm (pairEncode_ne_nil _ _)
    · exact absurd h.symm (pairEncode_ne_nil _ _)

/-- `compQ f` is polynomially bounded when `f` is: `|compQ f w| ≤ (2C + 3)(|w| + 1)^{c+1}`
from `|f x| ≤ C (|x| + 1)^c`. -/
theorem compQ_length_le {f : List Bool → List Bool} {C c : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c) (w : List Bool) :
    (compQ f w).length ≤ (2 * C + 3) * (w.length + 1) ^ (c + 1) := by
  unfold compQ
  split
  · rename_i x b hw
    split_ifs
    · have hw' := eq_pairEncode_of_pairDecode _ _ _ hw
      have hl : w.length = 2 * x.length + 2 + b.length := by rw [hw', length_pairEncode]
      have e1 : (w.length + 1) ^ c ≤ (w.length + 1) ^ (c + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : w.length + 1 ≤ (w.length + 1) ^ (c + 1) := by
        calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : (f x).length ≤ C * (w.length + 1) ^ c :=
        (hf x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have e4 : C * (w.length + 1) ^ c ≤ C * (w.length + 1) ^ (c + 1) :=
        Nat.mul_le_mul_left _ e1
      rw [length_pairEncode]
      have e5 : (2 * C + 3) * (w.length + 1) ^ (c + 1) =
          2 * (C * (w.length + 1) ^ (c + 1)) + 3 * (w.length + 1) ^ (c + 1) := by ring
      omega
    · simp
  · simp

/-- **Dropping the middle index is implicitly logspace computable** (phase P4.4b; spec, fill
pending).

**Proof sketch.**

* **Bound.** `Complexity.dropIdx_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over the access bank `![inputBitLang, inputLenLang]` (`inputBitLang_mem`,
  `inputLenLang_mem`), by `LogProg.arm_decides_poly`. A `whole` call on `[r]` reads the host's
  bit at `v r` (`LogProg.vword_whole₁`, `indicator_indexLang_pairEncode`).
* **The run, on a host `h = ⟨z, bits q⟩`.**
  * Validate `h` and its canonical tail.
  * Before accumulating `q`, compare the tail's length with `|bits |h||`. If longer, then
    `q ≥ |h| ≥ |dropIdx z|` and the answer is `false`.
  * Decode `z = ⟨u, b'⟩` and `u = ⟨w, b⟩` by aligned scans at strides 2 and 4 of `h`. A failed
    decode means `dropIdx z = []`, and the answer is `false`.
  * Answer by position arithmetic: positions below `2|w| + 2` come from `u`, the rest from
    `b'`.
* **Registers** are at most `4|h| + 4`. -/
theorem implicitlyLogspaceComputable_dropIdx : ImplicitlyLogspaceComputable dropIdx := by
  sorry

/-- **`comp`'s query reshaping is implicitly logspace computable** (phase P4.4b; spec, fill
pending): if `f` is, so is `compQ f`.

**Proof sketch.**

* **Bound.** `Complexity.compQ_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over a four-oracle bank (`LogProg.arm_decides_poly`):
  * `inputBitLang` and `inputLenLang`;
  * `{z | dropIdx (dropIdx z) ∈ L}` for `L` each of `f`'s two query languages. These are in
    `L` by `Complexity.mem_LOGSPACE_preimage` twice along
    `Complexity.implicitlyLogspaceComputable_dropIdx`.

  A `whole` call on `[j]` from the host `h = ⟨w, bits p⟩` presents
  `⟨⟨w, bits p⟩, bits j⟩`, which two `dropIdx` turn into `⟨x, bits j⟩` (`dropIdx_pairEncode`).
* **The run** ([AB09, Lemma 4.17's proof]; the P4.4 audit's question-2 ledger):
  * (i) Validate `h`, with the overflow test before storing `p`.
  * (ii) Validate `w = ⟨x, b⟩` with `b` canonical: last bit `true`, using
    `LogProg.canon_eq_bits` and `LogProg.canon_bits`.
  * (iii) Find `F := |f x|` by lifted length queries at `j = 0, 1, …`, below `C (|x| + 1)^e`.
  * (iv) Answer:
    * `p < 2F`: the lifted bit at `⌊p/2⌋`;
    * `p ∈ {2F, 2F + 1}`: the separator `[false, true]`;
    * otherwise: `b`'s bit at `p − 2F − 2`, read from `h` at its doubled position;
    * length: `p < 2F + 2 + |b|`. -/
theorem ImplicitlyLogspaceComputable.compQ {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : ImplicitlyLogspaceComputable (compQ f) := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace reductions and `NL`-completeness

[AB09, §4.3, Definition 4.16 and Lemma 4.17]: reductions computed in
logarithmic space — rendered, as the book does, through *implicitly* logspace
computable functions (`Complexity.ImplicitlyLogspaceComputable`, the received
P0 surface), since a logspace machine cannot store its output. Phase P4.4 of
`AroraBarakChapters3-4Plan.md`; the composition theorem stated here is
exactly the general Lemma 4.17 that the P0 reception round recorded as *not*
delivered (its note 10) — the received `UnaryLogspace.counterProg` closure
remains the special case.

## Main definitions

* `Complexity.LogspaceReducible` (`≤ₗ`) — [AB09, Definition 4.16].
* `Complexity.NLComplete` — `NL`-membership plus `NL`-hardness under `≤ₗ`.
  [AB09, Definition 4.16]

## Main results (four phase-P4.4 statements remain sorried)

* `Complexity.ImplicitlyLogspaceComputable.comp` — the composition engine
  ([AB09, Lemma 4.17's proof], Figure 4.3's virtual input tape).
* `Complexity.LogspaceReducible.trans` — [AB09, Lemma 4.17(1)].
* `Complexity.mem_LOGSPACE_of_logspaceReducible` — [AB09, Lemma 4.17(2)].
* `Complexity.LogspaceReducible.polyTimeReducible` — `≤ₗ` refines `≤ₚ`.
* `Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` — an `NL`-complete
  language in `L` collapses `NL` to `L`. [AB09, after Lemma 4.17]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17,
  Figure 4.3.)
-/

namespace Complexity

open Turing

/-- **Logspace reducibility** [AB09, Definition 4.16]: `B ≤ₗ C` when some
implicitly logspace computable `f` satisfies `x ∈ B ↔ f x ∈ C` for every
string — the reduction is never written down whole, only queried bit by bit
(`Complexity.ImplicitlyLogspaceComputable`, with its received divergences:
`0`-based indices and the campaign polynomial normal form). -/
def LogspaceReducible (B C : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, ImplicitlyLogspaceComputable f ∧
    ∀ x, x ∈ B ↔ f x ∈ C

@[inherit_doc] scoped infix:50 " ≤ₗ " => LogspaceReducible

/-- **`NL`-completeness** [AB09, Definition 4.16]: membership in `NL`
together with `NL`-hardness under logspace reductions. (Polynomial-time
reductions would trivialize this notion — `Complexity.polyTimeReducible_of_mem_NL`,
Exercise 4.3, phase P4.2.) -/
def NLComplete (C : Language Bool) : Prop :=
  C ∈ NL ∧ ∀ B ∈ NL, B ≤ₗ C

/-- **Composition of implicitly logspace computable functions** ([AB09,
Lemma 4.17's proof]; spec, fill pending — phase P4.4, **the general
composition the P0 round recorded as undelivered**): if `f` and `g` are
implicitly logspace computable, so is `g ∘ f`.

**Proof sketch.** [AB09, Figure 4.3]: to answer a bit or length query about
`g (f x)`, run `g`'s query machine against a **virtual input tape** holding
`f x` — maintain the index of the cell `g`'s head would scan (logarithmic in
`|f x|`, hence in `|x|` by `f`'s polynomial output bound), and whenever
`g`'s machine reads, suspend it and answer with `f`'s bit/length queries on
`⟨x, i⟩`. The received `LogProg` call protocol does not host this shape by
itself: a call's virtual input is read physically (the whole input, or its
leading run of `1`s, followed by register words), so no call can serve `g`'s
input from `f`'s queries (P0 reception audit, note 10). Fill route (phase
P4.4b, `audits/ch4-p44-resolutions-addendum.md`): both query languages of
`g ∘ f` are preimages of `g`'s along `Complexity.compQ f`
(`Complexity.mem_indexLang_compQ_iff`), hence in `L` by
`Complexity.mem_LOGSPACE_preimage` (the Fig. 4.3 engine,
`Complexity.LogProg.OIS`) and `Complexity.ImplicitlyLogspaceComputable.compQ`.
Obligations, named: the polynomial bound of the composite (`f`'s and `g`'s
bounds composed, `D (C + 1)^d (|x| + 1)^{cd}`); the two preimage memberships;
the index bookkeeping, which lives in `compQ`'s machines. (Sketch prose
corrected at phase P4.4b; the statement is unchanged.) -/
theorem ImplicitlyLogspaceComputable.comp {f g : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) (hg : ImplicitlyLogspaceComputable g) :
    ImplicitlyLogspaceComputable (g ∘ f) := by
  sorry

/-- **Logspace reducibility is transitive** ([AB09, Lemma 4.17(1)]; spec,
fill pending).

**Proof sketch.** `Complexity.ImplicitlyLogspaceComputable.comp` on the two
reduction functions; the membership equivalences chain. -/
theorem LogspaceReducible.trans {B C D : Language Bool} (h₁ : B ≤ₗ C)
    (h₂ : C ≤ₗ D) : B ≤ₗ D := by
  sorry

/-- **Logspace reductions preserve `L` downward** ([AB09, Lemma 4.17(2)];
spec, fill pending): if `B ≤ₗ C` and `C ∈ LOGSPACE` then `B ∈ LOGSPACE`.

**Proof sketch.** [AB09]'s own route: `C`'s characteristic function is
implicitly logspace computable (its bit language holds at a genuine pair
`⟨x, i⟩` iff `i = 0 ∧ x ∈ C`; its length language is **exactly**
`{pairEncode x [] | x}` — a regular language, not a total one: index `1` and
every malformed string are rejected; round-1 audit, finding 1), so the
composition `χ_C ∘ f` is implicitly logspace computable by
`Complexity.ImplicitlyLogspaceComputable.comp`, and deciding `B` is its bit
query at index `0` — a `LOGSPACE` membership by a fixed-index
**paired-input** specialization (named fill obligation): the index-`0` query
string is `pairEncode x [] = dbl x ++ [false, true]`, the *doubled* word with
its separator, not `x` itself, so the specialization simulates the query
decider on that doubled virtual input directly — independent of this very
theorem, avoiding circularity (round-1 audit, finding 2). -/
theorem mem_LOGSPACE_of_logspaceReducible {B C : Language Bool} (h : B ≤ₗ C)
    (hC : C ∈ LOGSPACE) : B ∈ LOGSPACE := by
  sorry

/-- **`≤ₗ` refines `≤ₚ`**: a logspace reduction is in
particular a polynomial-time reduction.

**Proof sketch.** The received
`Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` turns the
implicit witness into a whole-output polynomial-time machine; the
equivalences carry over verbatim. -/
theorem LogspaceReducible.polyTimeReducible {B C : Language Bool}
    (h : B ≤ₗ C) : B ≤ₚ C := by
  obtain ⟨f, hf, hB⟩ := h
  exact ⟨f, hf.polyTimeComputable, hB⟩

/-- **An `NL`-complete language in `L` collapses `NL`** ([AB09, the remark
after Lemma 4.17]; spec, fill pending): if `C` is `NL`-complete and
`C ∈ LOGSPACE`, then `NL = LOGSPACE`.

**Proof sketch.** `⊇` is `Complexity.LOGSPACE_subset_NL` (phase P4.1). `⊆`:
a member of `NL` reduces to `C` (completeness) and
`Complexity.mem_LOGSPACE_of_logspaceReducible` pulls membership back along
the reduction. -/
theorem NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE {C : Language Bool}
    (h : NLComplete C) (hC : C ∈ LOGSPACE) : NL = LOGSPACE := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multiplication in logarithmic space

[AB09, Example 4.7], second language: `MULT = {⟨n, m, nm⟩}` is in `L` by the
grade-school method. Deferred from phase P4.1 to P4.4
(`AroraBarakChapters3-4Plan.md`) for the number-triple encoding conventions,
which the logspace phase fixes: binary components in nested aligned pairs,
little-endian (`Nat.bits`), membership by existential witness over genuine
encodings — the same pattern as `Complexity.PATH`'s instance encoding.

## Main definitions

* `Complexity.multLang` — the triples `⟨a, b, a·b⟩`. [AB09, Example 4.7]

## Main results (sorried; phase-P4.4 statement)

* `Complexity.multLang_mem_LOGSPACE` — grade-school multiplication runs in
  logarithmic space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The language `MULT`** [AB09, Example 4.7]: encodings of triples
`⟨a, b, a·b⟩`, components in little-endian binary, nested aligned pairs.
Strings encoding no such triple are not members. -/
def multLang : Language Bool :=
  {z | ∃ a b : ℕ,
    z = pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits (a * b)))}

/-- **Multiplication verifies in logarithmic space** ([AB09, Example 4.7];
spec, fill pending — phase P4.4): the grade-school method checks the third
component bit by bit with carry and index counters only.

**Proof sketch.** The verifier computes each bit of `a · b` on demand:
bit `j` of the product is determined by the column sums
`∑_{p+q=j'} a_p · b_q` for `j' ≤ j` propagated through the carry — maintain
the carry (of `O(logSpace n)` bits, since a column sum is at most the input
length) and two index counters, re-reading `a`'s and `b`'s bits from the
input by position arithmetic on the nested pair layout (through `whole`-mode
calls to the input-access languages `Complexity.inputBitLang` and
`Complexity.inputLenLang` of phase P4.4b; the received
`Machines/Parse2`/`ParseCmp` toolkit reads only unary-first inputs
`⟨1ⁿ, ⟨u, w⟩⟩` and does not apply); compare each computed bit against the
third component's bit and reject on mismatch or malformed shape; accept when
every column through `|a| + |b|` matches (missing result bits read as `0`, a
longer result field rejected) and no carry remains. Registers: carry, two
indices, a column cursor — `O(logSpace n)` cells; assembled by the received
`arm_decides_poly`. Fill obligations, named: the column-sum/carry invariant;
the position arithmetic into the nested pairs; the shape validator; the
`DecidesInSpace` packaging. (Sketch prose corrected at phase P4.4b; the
statement is unchanged.) -/
theorem multLang_mem_LOGSPACE : multLang ∈ LOGSPACE := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Program.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import TCSlib.Complexity.SpaceComplexity.Machines.Layout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register-tape programs with subroutine calls, and their compiled machines

A *register-tape program* (`Complexity.LogProg.RProg`) is a multi-tape machine over `m`
work tapes (its *registers*) in which some states are *call nodes*: in a call node the
program asks a fixed decider whether a *virtual input* — a part of its own input followed by
the words on some of its registers, `Complexity.LogProg.vword` — belongs to the decider's
language, and continues in one of two states. This is the "pretend there is a virtual input
tape" device of [AB09, proof of Lemma 4.17, Fig. 4.3], packaged once.

This file defines the program model and the machine `Complexity.LogProg.compileTM` that
realizes it: the registers become work tapes `0, …, m - 1`, the decider's work tapes follow,
and a call node is executed by simulating the decider step for step on the virtual input.
The virtual input head is represented by the real input head and the register heads
(`Complexity.LogProg.TPos`), so the simulation needs no extra space.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Mode` — which part of the real input opens the virtual input: all of
  it, doubled (`whole`, giving `Turing.pairEncode x _` when the call has at least one
  argument), or its leading run of `1`s, plain (`unaryFst`, giving `Turing.pairEncode 1ⁿ _`
  on inputs `Turing.pairEncode 1ⁿ _`, again with at least one argument). A call with no
  arguments has a single-segment virtual input with no separator — for `whole` on `x = []`
  it is the empty word, not a pair encoding (P0 round 1, finding 3).
* `Complexity.LogProg.CallSpec`, `Complexity.LogProg.RProg` — call nodes and programs.
* `Complexity.LogProg.callSegs` — the segments of the virtual input of a call.
* `Complexity.LogProg.CSt`, `Complexity.LogProg.ctr`, `Complexity.LogProg.compileTM` — the
  compiled machine.
* `Complexity.LogProg.seam` — the compiled configuration of a program configuration.

## Main results

* `Complexity.LogProg.step_seam_prog` — away from call nodes the compiled machine runs the
  program in lockstep.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

/-- Which part of the real input opens a virtual input. -/
inductive Mode where
  /-- the whole input, doubled: virtual inputs `pairEncode x _` (when the call has at
  least one argument; with none, the virtual input is the doubled input alone, with no
  separator) -/
  | whole
  /-- the leading run of `1`s of the input, plain: on an input `pairEncode 1ⁿ _` this is
  `1²ⁿ`, so the virtual inputs are `pairEncode 1ⁿ _` (again given at least one argument) -/
  | unaryFst
  deriving DecidableEq

/-- The first segment of a virtual input. -/
def Mode.seg0 : Mode → List Bool → Seg
  | .whole, x => (x, true)
  | .unaryFst, x => (x.takeWhile (· = true), false)

/-- The register segments: every word but the last is doubled. -/
def argSegs : List (List Bool) → List Seg
  | [] => []
  | [w] => [(w, false)]
  | w :: v :: ws => (w, true) :: argSegs (v :: ws)

/-- There is one register segment per argument word. -/
@[simp] lemma length_argSegs (ws : List (List Bool)) : (argSegs ws).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => cases ws with
    | nil => rfl
    | cons v ws => simp [argSegs] at ih ⊢; omega

/-- Segment `i` of the register segments is register word `i`, doubled unless last. -/
lemma seg_argSegs (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) :
    seg (argSegs ws) i = (ws[i], decide (i + 1 < ws.length)) := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases ws with
    | nil =>
      have : i = 0 := by simp at hi; omega
      subst this; simp [argSegs, seg]
    | cons v ws =>
      cases i with
      | zero => simp [argSegs, seg]
      | succ i =>
        simp only [argSegs, seg_cons_succ]
        rw [ih i (by simp at hi ⊢; omega)]
        simp

/-- A call node: the decider to call, the virtual-input mode, the argument registers, and
the two continuation states. -/
structure CallSpec (m d : ℕ) (Λ : Type) where
  /-- which decider -/
  dec : Fin d
  /-- the first segment of the virtual input -/
  mode : Mode
  /-- the registers whose words follow, in order -/
  args : List (Fin m)
  /-- the state after a positive answer -/
  yes : Λ
  /-- the state after a negative answer -/
  no : Λ

/-- A register-tape program over `m` registers calling `d` deciders: a machine on the
registers together with the set of call nodes (on which its transition table is ignored). -/
structure RProg (m d : ℕ) (Λ : Type) where
  /-- the transitions at the ordinary nodes -/
  tm : MultiTapeTM m Bool Λ
  /-- the call nodes -/
  call : Λ → Option (CallSpec m d Λ)

/-- The segments of the virtual input of a call on input `x` with register words `W`. -/
def callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : List Seg :=
  cs.mode.seg0 x :: argSegs (cs.args.map W)

/-- A call's virtual input has one segment per argument register plus the leading segment. -/
@[simp] lemma length_callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : (callSegs cs x W).length = cs.args.length + 1 := by
  simp [callSegs]

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
/-- The states of the compiled machine. -/
inductive CSt (Λ SD : Type) (m : ℕ) where
  /-- running the program at node `l` -/
  | prog (l : Λ)
  /-- simulating the decider (state `q`) for the call at `l`: current segment `s`, parity,
  direction of the last track move, and the decider's emitted bit so far -/
  | sim (l : Λ) (q : SD) (s : Fin (m + 1)) (par dir : Bool) (res : Option Bool)
  /-- returning: the mandatory first left move of the input rewind -/
  | ret1 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: scanning the input head left -/
  | ret2 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: restoring the head of argument register number `a` (`scan`: in its left
  scan) -/
  | retR (l : Λ) (s : Fin (m + 1)) (dir res : Bool) (a : Fin m) (scan : Bool)
  deriving DecidableEq, Fintype

/-- Track bookkeeping of one simulated step (a pure function): from the segment `s`, parity,
direction of the last move, whether the current track reads a cell, and the virtual head
move, compute the new segment, parity, direction, and the move of the current track's real
head. `dbl`: the segment is doubled; `last`/`first`: it is the last/first segment. -/
def gstep (dbl last first : Bool) (s : ℕ) (par dir isChar : Bool) :
    SignType → ℕ × Bool × Bool × SignType
  | .zero => (s, par, dir, 0)
  | .pos =>
    if isChar then (if dbl ∧ par = false then (s, true, dir, 0) else (s, false, true, .pos))
    else if dir then (if last then (s, par, dir, 0) else (s + 1, true, false, 0))
    else (s, false, true, .pos)
  | .neg =>
    if isChar then (if dbl ∧ par = true then (s, false, dir, 0) else (s, true, false, .neg))
    else if dir then (s, true, false, .neg)
    else (if first then (s, par, dir, 0) else (s - 1, false, true, 0))

/-- Clamp a natural number into `Fin (m + 1)`. -/
def toFin (m s : ℕ) : Fin (m + 1) := ⟨min s m, by omega⟩

/-- The rendering flag of segment `s` of a call (from the mode for `s = 0`). -/
def segDbl {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) : Bool :=
  if s = 0 then decide (cs.mode = .whole) else decide (s < cs.args.length)

/-- The register read by segment `s ≥ 1` (a default otherwise). -/
def segReg {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) (h : 0 < m) : Fin m :=
  cs.args.getD (s - 1) ⟨0, h⟩

/-- Whether segment `s`'s current reading is a cell of its word: a bit on a register or
on the input in `whole` mode, a `1` in `unaryFst` mode. -/
def isCharRead (mode : Mode) (s : ℕ) (rd : Option Bool) : Bool :=
  if s = 0 ∧ mode = .unaryFst then decide (rd = some true) else rd.isSome

/-- The virtual symbol presented to the decider. -/
def virtSym (mode : Mode) (s nseg : ℕ) (dir : Bool) (rd : Option Bool) : Option Bool :=
  if isCharRead mode s rd then (if s = 0 ∧ mode = .unaryFst then some true else rd)
  else if dir then (if s + 1 = nseg then none else some false)
  else (if s = 0 then none else some true)

/-- The register action of a return step on argument register `r`: move `mv`. -/
def regMove {m : ℕ} (r : Fin m) (mv : SignType) : Fin m → Option (Option Bool) × SignType :=
  fun r' => (none, if r' = r then mv else 0)

/-- The state after finishing argument register `a` of a return: the next argument register,
or back to the program. -/
def nextRet {Λ SD : Type} {m d : ℕ} (cs : CallSpec m d Λ) (l : Λ) (s : Fin (m + 1))
    (dir res : Bool) (a : ℕ) : CSt Λ SD m :=
  if h : a < cs.args.length ∧ a < m then .retR l s dir res ⟨a, h.2⟩ false
  else .prog (if res then cs.yes else cs.no)

section Compile

variable {m d kD : ℕ} {Λ SD : Type}

/-- The idle action on the decider block. -/
def dIdle : Fin kD → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- **The transition table of the compiled machine.** See the module docstring; at a call
node the setup step moves the argument heads one cell left (onto the left blanks of their
words) and starts the decider; a simulated step reads the virtual symbol from the current
track, performs the decider's work-tape actions on the decider block, moves the current
track's real head according to `gstep`, and records the decider's emission; when the decider
halts the return phase rewinds the input head and the argument heads. -/
def ctr (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    CSt Λ SD m → Option Bool → (Fin (m + kD) → Option Bool) → Action (m + kD) Bool (CSt Λ SD m)
  | .prog l, inp, w =>
    match P.call l with
    | none =>
      let a := P.tm.tr l inp (fun r => w (Fin.castAdd kD r))
      ⟨a.inputTape, Fin.append a.workTapes dIdle, a.output, a.state.map .prog⟩
    | some cs =>
      ⟨0, Fin.append (fun r => (none, if r ∈ cs.args then -1 else 0)) dIdle, none,
        some (.sim l (q0 cs.dec) 0 false true none)⟩
  | .sim l q s par dir res, inp, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let rd : Option Bool :=
        if s.val = 0 then inp
        else if hm : 0 < m then w (Fin.castAdd kD (segReg cs s hm)) else none
      let ic := isCharRead cs.mode s rd
      let vs := virtSym cs.mode s (cs.args.length + 1) dir rd
      let a := D.tr q vs (fun i => w (Fin.natAdd m i))
      let g := gstep (segDbl cs s) (decide (s.val + 1 = cs.args.length + 1))
        (decide (s.val = 0)) s par dir ic a.inputTape
      let res' := res <|> a.output
      ⟨if s.val = 0 then g.2.2.2 else 0,
        Fin.append (fun r => (none, if h : 0 < m then
            (if s.val ≠ 0 ∧ r = segReg cs s h then g.2.2.2 else 0) else 0)) a.workTapes,
        none,
        some (match a.state with
          | some q' => .sim l q' (toFin m g.1) g.2.1 g.2.2.1 res'
          | none => .ret1 l (toFin m g.1) g.2.2.1 (res'.getD false))⟩
  | .ret1 l s dir res, _, _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
  | .ret2 l s dir res, inp, _ =>
    match inp with
    | some _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
    | none =>
      match P.call l with
      | none => ⟨0, fun _ => (none, 0), none, none⟩
      | some cs => ⟨1, fun _ => (none, 0), none, some (nextRet cs l s dir res 0)⟩
  | .retR l s dir res a scan, _, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let r := cs.args.getD a a
      let rd := w (Fin.castAdd kD r)
      let leftSide : Bool := decide (s.val < a.val + 1) || (decide (s.val = a.val + 1) && !dir)
      if scan then
        match rd with
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | none => ⟨0, Fin.append (regMove r 1) dIdle, none,
            some (nextRet cs l s dir res (a.val + 1))⟩
      else
        match rd with
        | none =>
          if leftSide then
            ⟨0, Fin.append (regMove r 1) dIdle, none, some (nextRet cs l s dir res (a.val + 1))⟩
          else ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩

/-- **The compiled machine** of a program `P` with start node `l₀`, calling the deciders
`D` from the start states `q0 j`. -/
def compileTM (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    MultiTapeTM (m + kD) Bool (CSt Λ SD m) where
  q₀ := .prog l₀
  tr := ctr P D q0

/-- The compiled configuration of a program configuration: the program's registers, the
decider block blank with heads at the origin. -/
def seam {x : List Bool} (c : Cfg m Bool Λ x) : Cfg (m + kD) Bool (CSt Λ SD m) x :=
  ⟨c.state.map .prog, c.inputPos, Fin.append c.workTapes (fun _ _ => none),
    Fin.append c.workTapePos (fun _ => 0), c.output⟩

/-- The initial configuration of the compiled machine is the seam of the program's. -/
lemma seam_init (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (compileTM P l₀ D q0).initCfg x = seam (kD := kD) (Cfg.init (k := m) l₀ x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]

/-- **Lockstep away from calls**: at a non-call node the compiled machine makes exactly the
program's step.

**Proof sketch.** At a non-call program node the compiled transition is the program's
transition, relabelled (`ctr` on `prog` states), with the decider tapes untouched. Unfold one
step on both sides and compare the components of `seam`. -/
lemma step_seam_prog (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) {x : List Bool} (c : Cfg m Bool Λ x) (l : Λ) (hl : c.state = some l)
    (hcall : P.call l = none) :
    (compileTM P l₀ D q0).step (seam c) = seam (P.tm.step c) := by
  have hstate : (seam (kD := kD) (SD := SD) c).state = some (.prog l) := by
    simp [seam, hl]
  unfold MultiTapeTM.step
  rw [hstate, hl]
  have hin : (seam (kD := kD) (SD := SD) c).inputSymbol = c.inputSymbol := rfl
  have hw : (fun r => (seam (kD := kD) (SD := SD) c).workTapeSymbols (Fin.castAdd kD r)) =
      c.workTapeSymbols := by
    funext r; simp [seam, Cfg.workTapeSymbols]
  simp only [compileTM, ctr, hcall, hin, hw]
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [seam]
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp only [Action.apply, Fin.append_left, seam]
    · simp [Action.apply, seam, dIdle]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp [Action.apply, seam]
    · simp [Action.apply, seam, dIdle]

/-- A halted program configuration is a halted compiled configuration. -/
lemma seam_state_none {x : List Bool} (c : Cfg m Bool Λ x) (h : c.state = none) :
    (seam (kD := kD) (SD := SD) c).state = none := by
  simp [seam, h]

end Compile

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.SpaceComplexity.Machines.Call

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the compiled machine

The semantics of a register-tape program (`Complexity.LogProg.rstep`): ordinary nodes take
their machine step, a call node asks an oracle about the virtual input of the call
(`Complexity.LogProg.vword` of `Complexity.LogProg.callSegs`) and continues in its `yes` or
`no` state with the input head back on the first cell. If the deciders answer the oracle
cleanly, the compiled machine (`Complexity.LogProg.compileTM`) computes what the program
computes (`Complexity.LogProg.compile_correct`), in space bounded by the program's register
ranges plus the deciders' space (`Complexity.LogProg.compile_space`).

## Main definitions

* `Complexity.LogProg.tapeWord` — the word stored on a register tape.
* `Complexity.LogProg.rstep` — one step of a program, calls being atomic oracle questions.
* `Complexity.LogProg.CallOK` — the precondition of one call, required at every step
  along the run by the compilation theorems' `hcalls` hypotheses.
* `Complexity.LogProg.compileFinTM` — the compiled machine as a bundled finite machine.

## Main results

* `Complexity.LogProg.compile_correct` — the compiled machine halts with the program's
  output, all heads in the given ranges at all times.
* `Complexity.LogProg.compile_space` — its space usage is at most the sum of the register
  ranges plus `kD (2B + 1)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The word stored on a register tape (from cell `0`; `[]` if the tape is not of this
shape). -/
noncomputable def tapeWord (f : ℤ → Option Bool) : List Bool :=
  open Classical in if h : ∃ w, f = FinTM.bufferTape w then h.choose else []

/-- A stored word is read back. -/
lemma tapeWord_bufferTape (w : List Bool) : tapeWord (FinTM.bufferTape w) = w := by
  have h : ∃ w', FinTM.bufferTape w = FinTM.bufferTape w' := ⟨w, rfl⟩
  unfold tapeWord
  rw [dif_pos h]
  have hspec := h.choose_spec
  -- `bufferTape` is injective
  apply List.ext_getElem?
  intro i
  have := congrFun hspec (i : ℤ)
  simpa [FinTM.bufferTape] using this.symm

/-- The register words of a program configuration. -/
noncomputable def regWords (c : Cfg m Bool Λ x) (r : Fin m) : List Bool := tapeWord (c.workTapes r)

/-- **One step of a register-tape program**: an ordinary node takes its machine step; a call
node asks `oracle` (decider `cs.dec`) about its virtual input and moves to `yes` or `no`,
with the input head on the first cell. -/
noncomputable def rstep (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) : Cfg m Bool Λ x :=
  match c.state with
  | none => c
  | some l =>
    match P.call l with
    | none => P.tm.step c
    | some cs =>
      { c with
        state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
          else cs.no),
        inputPos := 1 }

/-- The program run: `n` steps of `rstep`. -/
noncomputable def rrun (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) (n : ℕ) : Cfg m Bool Λ x :=
  (rstep P oracle)^[n] c

/-- Running a register-tape program `n + 1` steps is one more step after `n` steps. -/
lemma rrun_succ (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rstep P oracle (rrun P oracle c n) := by
  simp [rrun, Function.iterate_succ_apply']

/-- The preconditions of a call at configuration `c` (if `c` is at a call node): distinct
argument registers holding words with their heads at the origin and within the register
ranges, input head on the first cell, and a decider answering the oracle cleanly within head
range `B`. -/
def CallOK (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ) (c : Cfg m Bool Λ x) :
    Prop :=
  ∀ l cs, c.state = some l → P.call l = some cs →
    cs.args.Nodup ∧ c.inputPos.val = 1 ∧
    (∀ r ∈ cs.args, c.workTapes r = FinTM.bufferTape (regWords c r) ∧ c.workTapePos r = 0 ∧
      lo r ≤ -1 ∧ ((regWords c r).length : ℤ) ≤ hi r) ∧
    CleanRun D (q0 cs.dec) (vword (callSegs cs x (regWords c)))
      (oracle cs.dec (vword (callSegs cs x (regWords c)))) B

/-- **Correctness of the compiled machine.** If the program halts after `N` steps with
output `w`, its register heads stay in `[lo r, hi r]`, and every call along the way meets
its preconditions, then the compiled machine halts with output `w`, and at every time its
register heads are in `[lo r, hi r]` and its decider heads in `[-B, B]`.

**Proof sketch.** Induction on the program run, keeping the compiled machine on the seam
(`Complexity.LogProg.seam`) of the program configuration: ordinary steps are simulated in
lockstep (`step_seam_prog`), calls by `call_run`. -/
theorem compile_correct (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ)
    (N : ℕ)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T =
        seam (rrun P oracle (Cfg.init l₀ x) N) ∧
      ∀ t ≤ T, (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x)
          t).workTapePos (Fin.castAdd kD r) ∧
          ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
            (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
          (Fin.natAdd m i)| ≤ B := by
  induction N with
  | zero =>
    refine ⟨0, by rw [MultiTapeTM.runFrom_zero, seam_init]; rfl, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    refine ⟨fun r => ?_, fun i => ?_⟩
    · have := hbox 0 le_rfl r
      simpa [seam_init, seam, rrun] using this
    · simp
  | succ N ih =>
    obtain ⟨T, hT, hTb⟩ := ih (fun t ht => hbox t (by omega)) (fun t ht => hcalls t (by omega))
    set c := rrun P oracle (Cfg.init l₀ x) N with hc
    have hbN := hbox N (by omega)
    have hbN1 := hbox (N + 1) le_rfl
    rw [rrun_succ, ← hc] at hbN1 ⊢
    -- one program step from `c`
    have hstep : ∃ T', (compileTM P l₀ D q0).runFrom (seam c) T' = seam (rstep P oracle c) ∧
        ∀ t ≤ T', (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
            (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
              (Fin.castAdd kD r) ≤ hi r) ∧
          ∀ i, |((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos (Fin.natAdd m i)| ≤ B := by
      cases hs : c.state with
      | none =>
        refine ⟨0, by simp [rstep, hs], fun t ht => ?_⟩
        obtain rfl : t = 0 := by omega
        exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
      | some l =>
        cases hcl : P.call l with
        | none =>
          have hst := step_seam_prog P l₀ D q0 c l hs hcl
          have hr : rstep P oracle c = P.tm.step c := by simp [rstep, hs, hcl]
          refine ⟨1, by rw [hr]; exact hst, fun t ht => ?_⟩
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
          · obtain rfl : t = 1 := by omega
            rw [show (compileTM P l₀ D q0).runFrom (seam c) 1 =
              (compileTM P l₀ D q0).step (seam c) from rfl, hst, ← hr]
            exact ⟨fun r => by simpa [seam] using hbN1 r, fun i => by simp [seam]⟩
        | some cs =>
          obtain ⟨hnd, hin, hargs, hclean⟩ := hcalls N (by omega) l cs hs hcl
          obtain ⟨T', hb', hr'⟩ := call_run P l₀ D q0 hs hcl (fun r hr => (hargs r hr).1)
            (fun r hr => (hargs r hr).2.1) hnd hin _ B hclean
          have hr : rstep P oracle c = { c with
              state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
                else cs.no), inputPos := 1 } := by simp [rstep, hs, hcl]
          refine ⟨T', by rw [hr]; exact hr', fun t ht => ⟨fun r => ?_, (hb' t ht).2⟩⟩
          obtain ⟨h1, h2⟩ := (hb' t ht).1 r
          beta_reduce at h1 h2
          by_cases hrm : r ∈ cs.args
          · obtain ⟨-, -, hlo, hhi⟩ := hargs r hrm
            have := h2 hrm
            constructor <;> omega
          · rw [h1 hrm]; exact hbN r
    obtain ⟨T', hT', hTb'⟩ := hstep
    refine ⟨T + T', by rw [MultiTapeTM.runFrom_add, hT, hT'], ?_⟩
    apply runFrom_forall_append (Q := fun g =>
      (∀ r, lo r ≤ g.workTapePos (Fin.castAdd kD r) ∧ g.workTapePos (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B) hTb
    rw [hT]
    exact hTb'

/-- The space used up to time `T` is bounded by the sizes of ranges containing every head
at every time up to `T`. -/
lemma spaceUsed_le_of_ranges {K : ℕ} {S : Type} (tm : MultiTapeTM K Bool S)
    (c : Cfg K Bool S x) (T : ℕ) (lo hi : Fin K → ℤ)
    (h : ∀ t ≤ T, ∀ i, lo i ≤ (tm.runFrom c t).workTapePos i ∧
      (tm.runFrom c t).workTapePos i ≤ hi i) :
    tm.spaceUsed c T ≤ ∑ i, (hi i - lo i + 1).toNat := by
  unfold MultiTapeTM.spaceUsed MultiTapeTM.spaceUsedByTape
  refine Finset.sum_le_sum fun i _ => ?_
  have hsub : tm.visitedByTapeHead c T i ⊆ Finset.Icc (lo i) (hi i) := by
    intro z hz
    simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact h t (by omega) i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Int.card_Icc]
  congr 1
  ring

/-- The compiled machine as a bundled finite machine. -/
def compileFinTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinTM Bool where
  k := m + kD
  State := CSt Λ SD m
  tm := compileTM P l₀ D q0

/-- **The compiled machine computes what the program computes, in the program's space plus
the deciders' space**: if the program halts after `N` steps with output `w`, register heads
in `[lo r, hi r]`, and all calls meet their preconditions with decider head range `B`, then
the compiled machine halts on `x` with output `w`, having visited at most
`∑ r (hi r - lo r + 1) + kD (2B + 1)` work cells.

**Proof sketch.** `compile_correct` gives the halting time and the head ranges;
`spaceUsed_le_of_ranges` turns ranges into space, the register tapes and the decider tapes
being the two blocks of `Fin (m + kD)`. -/
theorem compile_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B N : ℕ) (w : List Bool)
    (hhalt : (rrun P oracle (Cfg.init l₀ x) N).state = none)
    (hout : (rrun P oracle (Cfg.init l₀ x) N).output = w)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileFinTM P l₀ D q0).ComputesInTime x w T ∧
      (compileFinTM P l₀ D q0).tm.spaceUsed ((compileFinTM P l₀ D q0).tm.initCfg x) T ≤
        ∑ r, (hi r - lo r + 1).toNat + kD * (2 * B + 1) := by
  obtain ⟨T, hT, hTb⟩ := compile_correct P l₀ D q0 oracle lo hi B N hbox hcalls
  refine ⟨T, ?_, ?_⟩
  · rw [FinTM.computesInTime_iff]
    change ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).state = none ∧
      ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).output = w
    rw [hT]
    exact ⟨by show Option.map _ _ = none; rw [hhalt]; rfl, by show _ = w; exact hout⟩
  · change (compileTM P l₀ D q0).spaceUsed ((compileTM P l₀ D q0).initCfg x) T ≤ _
    have := spaceUsed_le_of_ranges (compileTM P l₀ D q0) ((compileTM P l₀ D q0).initCfg x) T
      (Fin.append lo (fun _ => -(B : ℤ))) (Fin.append hi (fun _ => (B : ℤ))) (by
        intro t ht i
        refine Fin.addCases (fun r => ?_) (fun j => ?_) i
        · simpa using (hTb t ht).1 r
        · have := (hTb t ht).2 j
          simp only [Fin.append_right]
          rw [abs_le] at this
          exact this)
    refine this.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    congr 1
    omega

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Call.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A whole subroutine call of the compiled machine

From a program configuration at a call node, the compiled machine moves the argument
heads onto their left blanks (*setup*), simulates the decider on the virtual input step for
step (`Complexity.LogProg.sim_step`), and when the decider halts rewinds the input head and
the argument heads (*return*). For a *clean* decider — one that halts with blank work tapes
and heads at the origin — this ends in the compiled configuration of the program
configuration after the call (`Complexity.LogProg.call_run`), with every head in a known
range at every intermediate time.

Compiled configurations (`mkCfg`) and the return phase are in
`TCSlib.Complexity.SpaceComplexity.Machines.CallReturn`, which this file re-exports.

## Main definitions

* `Complexity.LogProg.mkCfg` — a compiled configuration from its register and decider
  blocks.
* `Complexity.LogProg.CleanRun` — the decider halts from a start state cleanly, with heads
  in a given range, answering a given bit.

## Main results

* `Complexity.LogProg.call_run` — a call runs to completion.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-! ## The whole call -/

/-- The decider started in state `q` on `V` halts — at time `T` — with output `[b]`, blank
work tapes and heads at the origin, its heads staying within `[-B, B]`. -/
def CleanRun (D : MultiTapeTM kD Bool SD) (q : SD) (V : List Bool) (b : Bool) (B : ℕ) : Prop :=
  ∃ T, (D.runFrom (Cfg.init q V) T).state = none ∧ (D.runFrom (Cfg.init q V) T).output = [b] ∧
    (D.runFrom (Cfg.init q V) T).workTapes = (fun _ _ => none) ∧
    (D.runFrom (Cfg.init q V) T).workTapePos = (fun _ => 0) ∧
    ∀ t ≤ T, ∀ i, |(D.runFrom (Cfg.init q V) t).workTapePos i| ≤ B

/-- Properties of all configurations along two consecutive run segments. -/
lemma runFrom_forall_append {K : ℕ} {S : Type} {tm : MultiTapeTM K Bool S}
    {c : Cfg K Bool S x} {T₁ T₂ : ℕ} {Q : Cfg K Bool S x → Prop}
    (h₁ : ∀ t ≤ T₁, Q (tm.runFrom c t)) (h₂ : ∀ t ≤ T₂, Q (tm.runFrom (tm.runFrom c T₁) t)) :
    ∀ t ≤ T₁ + T₂, Q (tm.runFrom c t) := by
  intro t ht
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact h₁ t h.le
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [MultiTapeTM.runFrom_add]
    exact h₂ t' (by omega)

/-- The first segment of a virtual input starts at offset `0`. -/
@[simp] lemma off_zero (segs : List Seg) : off segs 0 = 0 := by cases segs <;> rfl

section Whole

variable {l : Λ} {cs : CallSpec m d Λ} {W : Fin m → List Bool} {c0 : Cfg m Bool Λ x}

/-- During a call the register positions stay in the call's range. -/
lemma regPos_box (_hnd : cs.args.Nodup) (s : ℕ) (tp : TPos)
    (hval : tp.Valid (callSegs cs x W) s) (_hs : s < cs.args.length + 1) :
    RegBox cs c0.workTapePos W (regPos c0 cs W s tp) := by
  intro r
  refine ⟨fun hr => by simp [regPos, hr], fun hr => ?_⟩
  have hidx := List.idxOf_lt_length_of_mem hr
  have hget : cs.args[cs.args.idxOf r] = r := List.getElem_idxOf hidx
  have hw : wlen (callSegs cs x W) (cs.args.idxOf r + 1) = (W r).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ hidx, hget]
  simp only [regPos, hr, ↓reduceIte]
  split_ifs with h1 h2
  · rw [hw]; omega
  · omega
  · have hs' : s = cs.args.idxOf r + 1 := by omega
    have := trackPos_bounds _ s tp hval
    rw [hs'] at this ⊢
    rw [hw] at this
    exact this

/-- The side tests of the return phase agree with the register positions at the halt.

**Proof sketch.** A register head is at `-1` or at `|W r|` only when the track position sits at
the left or right blank of that register's segment. Consistency of the track position with the
segment parity and direction (`Consistent`) then fixes which side the return phase's test
`leftSide` reports. -/
lemma regPos_side (hnd : cs.args.Nodup) (s : Fin (m + 1)) (par dir : Bool) (tp : TPos)
    (hcons : Consistent (callSegs cs x W) s par dir tp)
    (hval : tp.Valid (callSegs cs x W) s) (a : ℕ) (ha : a < cs.args.length) (hm : a < m) :
    (regPos c0 cs W s tp cs.args[a] = -1 → leftSide s dir ⟨a, hm⟩ = true) ∧
      (regPos c0 cs W s tp cs.args[a] = (W cs.args[a]).length →
        leftSide s dir ⟨a, hm⟩ = false) := by
  have hidx : cs.args.idxOf cs.args[a] = a := List.idxOf_getElem hnd a ha
  have hw : wlen (callSegs cs x W) (a + 1) = (W cs.args[a]).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ ha]
  simp only [regPos, List.getElem_mem, ↓reduceIte, hidx, leftSide]
  split_ifs with h1 h2
  · rw [hw]
    have e1 : ¬ (s : ℕ) < a + 1 := by omega
    have e2 : ¬ (s : ℕ) = a + 1 := by omega
    simp only [e1, e2, decide_false, Bool.false_and, Bool.or_false, Bool.false_eq_true]
    constructor <;> intro h <;> first | rfl | omega
  · simp only [h2, decide_true, Bool.true_or]
    exact ⟨fun _ => trivial, fun h => h.elim⟩
  · have hs' : (s : ℕ) = a + 1 := by omega
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, hs']
    | cell c p =>
      simp only [TPos.Valid, hs'] at hval
      simp only [trackPos]
      rw [hw] at hval
      constructor <;> intro h <;> omega
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, hs', hw]
      constructor <;> intro h <;> simp; omega

/-- **A whole call.** From a program configuration at a call node whose argument registers
hold `W` with their heads at the origin, input head on the first cell, and a decider that
answers `b` cleanly within head range `B`, the compiled machine reaches the compiled
configuration of the program configuration after the call — state `yes` or `no` by `b`,
input head on the first cell, everything else unchanged. Throughout, the registers stay in
the call's range and the decider block in `[-B, B]`.

**Proof sketch.** One setup step (`apply_moves`) establishes the simulation relation with
the decider's initial configuration; `sim_step` carries it to the decider's first halting
time; there the decider's tapes are clean, and the return phase (`ret2_run`, `regs_run`)
restores the input head and the argument heads (`regPos_side` checks the side tests). -/
theorem call_run (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (hl : c0.state = some l) (hcall : P.call l = some cs)
    (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r))
    (hW0 : ∀ r ∈ cs.args, c0.workTapePos r = 0) (hnd : cs.args.Nodup)
    (hin : c0.inputPos.val = 1) (b : Bool) (B : ℕ)
    (hD : CleanRun D (q0 cs.dec) (vword (callSegs cs x W)) b B) :
    ∃ T, (∀ t ≤ T, RegBox cs c0.workTapePos W (fun r => ((compileTM P l₀ D q0).runFrom
          (seam c0) t).workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom (seam c0) t).workTapePos (Fin.natAdd m i)| ≤ B) ∧
      (compileTM P l₀ D q0).runFrom (seam c0) T =
        seam { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
  classical
  obtain ⟨T, hTh, hTo, hTt, hTp, hTb⟩ := hD
  set V := vword (callSegs cs x W) with hV
  set dc0 : Cfg kD Bool SD V := Cfg.init (q0 cs.dec) V with hdc0
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  -- the setup step
  have hsetup : (compileTM P l₀ D q0).step (seam c0) =
      mkCfg (some (.sim l (q0 cs.dec) 0 false true none)) c0.inputPos c0.workTapes
        (fun r => c0.workTapePos r + ((if r ∈ cs.args then -1 else 0 : SignType) : ℤ))
        (fun _ _ => none) (fun _ => 0) c0.output := by
    rw [seam_eq_mkCfg]
    unfold MultiTapeTM.step
    simp only [mkCfg_state, hl, Option.map_some]
    simp only [compileTM, ctr, hcall]
    rw [apply_moves, moveInputPos_zero]
  -- the first halting time of the decider
  have hex : ∃ t, (D.runFrom dc0 t).state = none := ⟨T, hTh⟩
  set T0 := Nat.find hex with hT0def
  have hT0 : (D.runFrom dc0 T0).state = none := Nat.find_spec hex
  have hT0le : T0 ≤ T := Nat.find_min' hex hTh
  have hlive : ∀ t < T0, (D.runFrom dc0 t).state ≠ none := fun t ht => Nat.find_min hex ht
  have hfin : D.runFrom dc0 T = D.runFrom dc0 T0 := by
    rw [show T = T0 + (T - T0) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hT0]
  have hT0pos : 0 < T0 := by
    rcases Nat.eq_zero_or_pos T0 with h | h
    · rw [h] at hT0; simp [dc0] at hT0
    · exact h
  -- the simulation relation at the start
  have hsim0 : SimRel c0 l cs W ((compileTM P l₀ D q0).step (seam c0)) dc0 := by
    have hw0 := wlen_zero_le cs x W
    let tp : TPos := if wlen (callSegs cs x W) 0 = 0 then .right else .cell 0 false
    refine ⟨q0 cs.dec, 0, false, true, tp, ?_, rfl, ?_⟩
    · rw [hsetup]; rfl
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tp]; split_ifs with h <;> simp [TPos.Valid]; omega
    · simp only [tp]; split_ifs <;> simp [Consistent]
    · simp only [tp, dc0, Cfg.init]
      split_ifs with h
      · simp only [vpos, wlen, rlen] at h ⊢; split <;> simp_all
      · simp [vpos, off_zero, cellOff]
    · rw [hsetup]
      simp only [mkCfg, tp, inPos, Fin.val_zero, ↓reduceIte, hin]
      split_ifs with h <;> simp [trackPos, h]
    · intro r; rw [hsetup]; simp [mkCfg]
    · intro r
      rw [hsetup]
      simp only [mkCfg, Fin.append_left, regPos]
      by_cases hr : r ∈ cs.args
      · simp [hr, hW0 r hr]
      · simp [hr]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · rw [hsetup]; rfl
  -- the simulation, up to the halt
  have hsim : ∀ t ≤ T0, (t < T0 → SimRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
        (D.runFrom dc0 t)) ∧
      (t = T0 → HaltRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t) (D.runFrom dc0 t)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨fun _ => hsim0, fun h => absurd h (by omega)⟩
    | succ t ih =>
      intro ht
      have h := (ih (by omega)).1 (by omega)
      have hs := sim_step l P D q0 hcall hW hnd h (l₀ := l₀)
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step']
      constructor
      · intro hlt
        apply hs.1
        rw [← MultiTapeTM.runFrom_succ_eq_step']
        exact hlive _ hlt
      · intro heq
        apply hs.2
        rw [← MultiTapeTM.runFrom_succ_eq_step', heq]
        exact hT0
  -- the halt
  obtain ⟨s, par, dir, tp, hgst, -, R⟩ := (hsim T0 le_rfl).2 rfl
  have hout0 : (D.runFrom dc0 T0).output = [b] := by rw [← hfin]; exact hTo
  have hb : ((D.runFrom dc0 T0).output.head?.getD false) = b := by rw [hout0]; rfl
  set gH := (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0 with hgH
  have hgHeq : gH = mkCfg (some (.ret1 l s dir b)) gH.inputPos c0.workTapes
      (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    refine Cfg.ext (by rw [hgst, hb]; rfl) rfl ?_ ?_ R.out
    · funext i z
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regTape]
      · simp only [mkCfg, Fin.append_right, R.dTape]
        rw [← hfin, hTt]
    · funext i
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regPos]
      · simp only [mkCfg, Fin.append_right, R.dPos]
        rw [← hfin, hTp]
  -- the return: input rewind
  have hret1 : (compileTM P l₀ D q0).step gH =
      mkCfg (some (.ret2 l s dir b)) (moveInputPos gH.inputPos (-1)) c0.workTapes
        (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    conv_lhs => rw [hgHeq]
    unfold MultiTapeTM.step
    simp only [mkCfg_state]
    simp only [compileTM, ctr]
    rw [apply_inputOnly]
  have hj : (moveInputPos gH.inputPos (-1)).val ≤ x.length := by
    rw [show (-1 : SignType) = .neg from rfl, FinTM.moveInputPos_neg_val]
    have := gH.inputPos.isLt; omega
  obtain ⟨hb2, hr2⟩ := ret2_run P l₀ D q0 l cs hcall s dir b c0.workTapes (regPos c0 cs W s tp)
    (fun _ _ => none) (fun _ => 0) c0.output _ _ rfl hj
  -- the return: argument registers
  have hbox0 := regPos_box (c0 := c0) hnd s tp R.valid R.hs
  have hret0 : retPos cs (regPos c0 cs W s tp) 0 = regPos c0 cs W s tp := by
    funext r; simp [retPos]
  obtain ⟨T₃, hb3, hr3⟩ := regs_run P l₀ D q0 l cs hcall hnd s dir b W c0.workTapes hW
    (fun _ _ => none) (fun _ => 0) c0.output 1 c0.workTapePos (regPos c0 cs W s tp) hbox0
    (fun a ha hm => regPos_side hnd s par dir tp R.cons R.valid a ha hm)
    cs.args.length 0 (by omega)
  rw [hret0] at hb3 hr3
  have hretL : retPos cs (regPos c0 cs W s tp) cs.args.length = c0.workTapePos := by
    funext r
    unfold retPos
    by_cases hr : r ∈ cs.args
    · simp [hr, List.idxOf_lt_length_of_mem hr, hW0 r hr]
    · simp [hr, regPos]
  rw [hretL] at hr3
  -- assemble
  have hfinal : (mkCfg (some (CSt.prog (if b then cs.yes else cs.no))) 1 c0.workTapes
      c0.workTapePos (fun _ _ => none) (fun _ => 0) c0.output : Cfg (m + kD) Bool (CSt Λ SD m) x) =
      seam (kD := kD) (SD := SD)
        { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
    rw [seam_eq_mkCfg]; rfl
  refine ⟨1 + (T0 + (1 + ((moveInputPos gH.inputPos (-1)).val + 1 + T₃))), ?_, ?_⟩
  · -- the box along the whole call
    have hregBoxSeam : RegBox cs c0.workTapePos W c0.workTapePos := by
      intro r
      refine ⟨fun _ => rfl, fun hr => ?_⟩
      rw [hW0 r hr]; simp
    let Q : Cfg (m + kD) Bool (CSt Λ SD m) x → Prop := fun g =>
      RegBox cs c0.workTapePos W (fun r => g.workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B
    show ∀ t ≤ _, Q ((compileTM P l₀ D q0).runFrom (seam c0) t)
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        refine ⟨by simpa [seam] using hregBoxSeam, fun i => by simp [seam]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = ((compileTM P l₀ D q0).step (seam c0)) from rfl]
        obtain ⟨_, _, _, _, _, _, _, R0⟩ := hsim0
        refine ⟨?_, fun i => ?_⟩
        · intro r; simp only [R0.regPos]; exact regPos_box hnd _ _ R0.valid R0.hs r
        · rw [R0.dPos]; simp [dc0, Cfg.init]
    rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = (compileTM P l₀ D q0).step (seam c0)
      from rfl]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      have hTR : ∃ s par dir tp, TrackRel c0 cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
          (D.runFrom dc0 t) s par dir tp := by
        rcases Nat.lt_or_ge t T0 with h | h
        · obtain ⟨_, s', par', dir', tp', -, -, R'⟩ := (hsim t ht).1 h
          exact ⟨s', par', dir', tp', R'⟩
        · obtain ⟨s', par', dir', tp', -, -, R'⟩ := (hsim t ht).2 (by omega)
          exact ⟨s', par', dir', tp', R'⟩
      obtain ⟨s', par', dir', tp', R'⟩ := hTR
      refine ⟨?_, fun i => ?_⟩
      · intro r; simp only [R'.regPos]; exact regPos_box hnd s' tp' R'.valid R'.hs r
      · rw [R'.dPos]; exact hTb t (by omega) i
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        rw [MultiTapeTM.runFrom_zero, ← hgH, hgHeq]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
          (compileTM P l₀ D q0).step gH from rfl, hret1]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
    rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
      (compileTM P l₀ D q0).step gH from rfl, hret1]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      dsimp only [Q]
      rw [hb2 t ht]
      exact ⟨fun r => by simpa using hbox0 r, fun i => by simp⟩
    rw [hr2]
    intro t ht
    dsimp only [Q]
    obtain ⟨h1, h2⟩ := hb3 t ht
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    simp only [Function.comp_apply] at this
    rw [this]; simp
  · rw [MultiTapeTM.runFrom_add]
    change (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) _ = _
    rw [MultiTapeTM.runFrom_add, ← hgH, MultiTapeTM.runFrom_add]
    rw [show (compileTM P l₀ D q0).runFrom gH 1 = (compileTM P l₀ D q0).step gH from rfl, hret1,
      MultiTapeTM.runFrom_add, hr2, hr3, hfinal]


end Whole

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Clean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A bank of clean deciders

The compiled machine of a register-tape program calls its deciders through one machine
with several start states (`Complexity.LogProg.compileTM` takes a single decider block).
This file builds that machine from finitely many space-bounded deciders: each decider is
padded to the largest number of work tapes, the padded machines are run side by side in one
state space (the start state selects the decider), and the whole is cleaned
(`Complexity.LogProg.cleanTM`).

## Main definitions

* `Complexity.LogProg.padTM` — a machine with extra, unused work tapes.
* `Complexity.LogProg.bankTM`, `Complexity.LogProg.bankStart` — the bank and its start states.

## Main results

* `Complexity.LogProg.bank_cleanRun` — started in `bankStart j` on `V`, the bank answers
  whether `V` belongs to decider `j`'s language, cleanly, with heads in
  `[-max (s j |V|) 1, max (s j |V|) 1]`, where decider `j` runs in space `s j`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Padding with unused tapes -/

section Pad

variable {k K : ℕ} {S : Type}

/-- The machine `M` with `K ≥ k` work tapes, the extra ones unused. -/
def padTM (M : MultiTapeTM k Bool S) (K : ℕ) : MultiTapeTM K Bool S where
  q₀ := M.q₀
  tr q a w :=
    let act := M.tr q a (fun i => if h : i.val < K then w ⟨i.val, h⟩ else none)
    ⟨act.inputTape, fun i => if h : i.val < k then act.workTapes ⟨i.val, h⟩ else (none, 0),
      act.output, act.state⟩

/-- The padded configuration. -/
def padCfg {x : List Bool} (K : ℕ) (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos, fun i z => if h : i.val < k then c.workTapes ⟨i.val, h⟩ z else none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- One step of the padded machine on a padded configuration is the padding of one step of the
original machine.

**Proof sketch.** Unfold one step on both sides: the padded transition reads the original tapes'
symbols (the padding tapes are never read), applies the original action to them, and leaves the
padding tapes and heads unchanged. Compare componentwise, splitting tape indices into original
and padding ones. -/
lemma padTM_step {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x) :
    (padTM M K).step (padCfg K c) = padCfg K (M.step c) := by
  unfold MultiTapeTM.step
  simp only [padCfg]
  cases hs : c.state with
  | none => simp [hs]
  | some q =>
    simp only
    have hw : (fun i : Fin k => if h : i.val < K then
        (padCfg K c : Cfg K Bool S x).workTapeSymbols ⟨i.val, h⟩ else none) =
          c.workTapeSymbols := by
      funext i
      simp [padCfg, Cfg.workTapeSymbols, show i.val < K by omega]
    have hin : (padCfg K c : Cfg K Bool S x).inputSymbol = c.inputSymbol := rfl
    change ((padTM M K).tr q (padCfg K c).inputSymbol (padCfg K c).workTapeSymbols).apply
      (padCfg K c) = padCfg K ((M.tr q c.inputSymbol c.workTapeSymbols).apply c)
    simp only [padTM, hin, hw]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k
      · simp only [h, ↓reduceDIte]
      · simp [h]
    · funext i
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k <;> simp [h]

/-- Runs of the padded machine on padded configurations are the paddings of the original runs. -/
lemma padTM_runFrom {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x)
    (n : ℕ) : (padTM M K).runFrom (padCfg K c) n = padCfg K (M.runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (padCfg K) (padTM_step M hk) c n

end Pad

/-! ## Machines side by side -/

section Sigma

variable {d K : ℕ} {S : Fin d → Type}

/-- The machines `Ms j` in one state space; the dummy state `none` halts. -/
def sigmaTM (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) :
    MultiTapeTM K Bool (Option (Σ j, S j)) where
  q₀ := none
  tr
    | none, _, _ => ⟨0, fun _ => (none, 0), none, none⟩
    | some ⟨j, q⟩, a, w =>
      let act := (Ms j).tr q a w
      ⟨act.inputTape, act.workTapes, act.output, act.state.map fun q' => some ⟨j, q'⟩⟩

/-- The configuration of machine `j` inside the side-by-side machine. -/
def sigCfg {x : List Bool} (j : Fin d) (c : Cfg K Bool (S j) x) :
    Cfg K Bool (Option (Σ j, S j)) x :=
  ⟨c.state.map fun q => some ⟨j, q⟩, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- One step of the disjoint union of machines on a configuration of component `j` is that
component's step. -/
lemma sigmaTM_step {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) : (sigmaTM Ms).step (sigCfg j c) = sigCfg j ((Ms j).step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [sigCfg, hs]
  | some q =>
    simp only [sigCfg, hs, Option.map_some]
    rfl

/-- Runs of the disjoint union of machines on configurations of component `j` are that
component's runs. -/
lemma sigmaTM_runFrom {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) (n : ℕ) :
    (sigmaTM Ms).runFrom (sigCfg j c) n = sigCfg j ((Ms j).runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (sigCfg j) (sigmaTM_step Ms j) c n

end Sigma

/-! ## The bank -/

section Bank

variable {d : ℕ} (Ms : Fin d → FinTM Bool)

/-- The common number of work tapes. -/
def bankK : ℕ := Finset.univ.sup fun j => (Ms j).k

/-- Every machine of the bank has at most `bankK Ms` work tapes. -/
lemma le_bankK (j : Fin d) : (Ms j).k ≤ bankK Ms :=
  Finset.le_sup (f := fun j => (Ms j).k) (Finset.mem_univ j)

/-- The raw state type of the bank. -/
abbrev BankS : Type := Option (Σ j, (Ms j).State)

/-- **The bank of deciders**: the deciders padded to `bankK` tapes, side by side, cleaned. -/
def bankTM : MultiTapeTM (bankK Ms + bankK Ms) Bool (CleanSt (BankS Ms) (bankK Ms)) :=
  cleanTM (sigmaTM fun j => padTM (Ms j).tm (bankK Ms)) none

/-- The start state of decider `j` in the bank. -/
def bankStart (j : Fin d) : CleanSt (BankS Ms) (bankK Ms) := .init (some ⟨j, (Ms j).tm.q₀⟩)

/-- **The bank answers cleanly.** If decider `j` decides `A j` in space `s j`, then the bank
started in `bankStart j` on any `V` halts with output `[V ∈ A j]`, blank work tapes and heads
at the origin, all heads within `[-B, B]` for `B = max (s j |V|) 1`.

**Proof sketch.** Padding (`padTM_runFrom`) and the side-by-side union (`sigmaTM_runFrom`)
run decider `j` unchanged; its tapes visit at most `s j |V|` cells each and the padding
tapes only the origin; `cleanTM_run` does the rest. -/
theorem bank_cleanRun (A : Fin d → Language Bool) (s : Fin d → ℕ → ℕ)
    (hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j)) (j : Fin d) (V : List Bool) :
    CleanRun (bankTM Ms) (bankStart Ms j) V
      (MultiTapeTM.indicator (A j : Set (List Bool)) V) (max (s j V.length) 1) := by
  obtain ⟨T, hT, hsp⟩ := hMs j V
  rw [FinTM.computesInTime_iff] at hT
  obtain ⟨hhalt, hout⟩ := hT
  set K := bankK Ms
  have hk : (Ms j).k ≤ K := le_bankK Ms j
  -- the side-by-side padded run
  have hrun : ∀ t, (sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) t =
      sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.runFrom ((Ms j).tm.initCfg V) t)) := by
    intro t
    have e : (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V : Cfg K Bool (BankS Ms) V) =
        sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.initCfg V)) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i z; simp [sigCfg, padCfg, Cfg.init]
      · funext i; simp [sigCfg, padCfg, Cfg.init]
    rw [e, sigmaTM_runFrom, padTM_runFrom _ hk]
  have hhalt' : ((sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T).state = none := by
    rw [hrun]; simp only [sigCfg, padCfg]; rw [hhalt]; rfl
  -- visited cells per tape
  have hvis : ∀ i : Fin K, ((sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i).card ≤ max (s j V.length) 1 := by
    intro i
    by_cases hi : i.val < (Ms j).k
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i =
          (Ms j).tm.visitedByTapeHead ((Ms j).tm.initCfg V) T ⟨i.val, hi⟩ := by
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte]
      rw [hsub]
      exact ((Ms j).tm.spaceUsedByTape_le_spaceUsed _ T _).trans (hsp.trans (le_max_left _ _))
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i ⊆ {0} := by
        intro z hz
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte,
          Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨_, _, rfl⟩ := hz
        simp
      exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨T', h1, h2, h3, h4, h5⟩ := cleanTM_run (sigmaTM fun j => padTM (Ms j).tm K) none
    (some ⟨j, (Ms j).tm.q₀⟩) V T hhalt' _ hvis
  unfold CleanRun bankStart bankTM
  refine ⟨T', h1, ?_, h3, h4, fun t ht i => by exact_mod_cast h5 t ht i⟩
  rw [h2, hrun]
  simp only [sigCfg, padCfg]
  exact hout

end Bank

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: binary counters

Reusable pieces of register-tape programs (`Complexity.LogProg.RProg`), each specified by the
transitions it needs at a few states and proved once against the program semantics
`Complexity.LogProg.rstep`. The increment fragment adds one to the binary counter
(`Nat.bits n`, from cell `0`) on a register and returns its head to cell `0`.

## Main definitions

* `Complexity.LogProg.regCfg` — a program configuration with one register changed.
* `Complexity.LogProg.incCAct`, `Complexity.LogProg.incBAct` — the transitions of the
  increment fragment.

## Main results

* `Complexity.LogProg.inc_run` — the increment fragment turns `Nat.bits n` into
  `Nat.bits (n + 1)`, its head staying in `[-1, |Nat.bits (n + 1)|]`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A non-call step of a program is a machine step. -/
lemma rstep_noncall (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (l : Λ) (hl : c.state = some l) (hc : P.call l = none) :
    rstep P oracle c = P.tm.step c := by
  simp [rstep, hl, hc]

/-- Running a program one step is `rstep`. -/
lemma rrun_one (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 1 = rstep P oracle c := rfl

/-- Running a program zero steps leaves the configuration unchanged. -/
lemma rrun_zero (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 0 = c := rfl

/-- Running `a + b` steps is running `a` steps, then `b` steps. -/
lemma rrun_add (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (a b : ℕ) : rrun P oracle c (a + b) = rrun P oracle (rrun P oracle c a) b := by
  simp only [rrun]
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- A configuration with state `s` and register `r` holding tape `f` with its head at `p`,
everything else as in `c`. -/
def regCfg (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, Function.update c.workTapes r f, Function.update c.workTapePos r p,
    c.output⟩

/-- The register view `regCfg c s …` is in state `s`. -/
@[simp] lemma regCfg_state (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool)
    (p : ℤ) : (regCfg c s r f p).state = some s := rfl

/-- An action touching only register `r`. -/
def regAct (r : Fin m) (w : Option (Option Bool)) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r' => if r' = r then (w, mv) else (none, 0), none, some s⟩

/-- Applying a register action to a register view writes the register cell (if asked), moves
the register head by `mv`, and enters `s'`.

**Proof sketch.** Unfold the action's application on a register view: only register `r`'s cell
under the head is written and only its head moves. Compare the tape and head families pointwise
(`Function.update_apply`). -/
lemma apply_regAct (c : Cfg m Bool Λ x) (s s' : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ)
    (w : Option (Option Bool)) (mv : SignType) :
    (regAct r w mv s').apply (regCfg c s r f p) =
      regCfg c s' r (match w with | none => f | some b => Function.update f p b) (p + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [regAct, regCfg])
  · funext r' z
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h
      cases w with
      | none => simp
      | some b =>
        simp only [Function.update_self, ↓reduceIte]
        rw [Function.update_self]
    · simp [h]
  · funext r'
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/-- The register view reads register `r` at its head position `p`. -/
lemma regCfg_read (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    (regCfg c s r f p).workTapeSymbols r = f p := by
  simp [regCfg, Cfg.workTapeSymbols]

/-- Overwriting the cell right after a prefix. -/
lemma update_bufferTape_cons (pre w : List Bool) (b b' : Bool) :
    Function.update (FinTM.bufferTape (pre ++ b :: w)) (pre.length : ℤ) (some b') =
      FinTM.bufferTape (pre ++ b' :: w) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · have hne : z.toNat ≠ pre.length := by omega
      rw [List.getElem?_append, List.getElem?_append]
      split_ifs with h3
      · rfl
      · obtain ⟨j, hj⟩ : ∃ j, z.toNat - pre.length = j + 1 :=
          ⟨z.toNat - pre.length - 1, by omega⟩
        rw [hj]; rfl
    · rfl

/-- Writing past the end of a stored word appends. -/
lemma update_bufferTape_end (w : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape w) (w.length : ℤ) (some b) = FinTM.bufferTape (w ++ [b]) :=
  (FinTM.bufferTape_append w b).symm

/-! ## The increment fragment -/

/-- The carry state of the increment: flip `1`s to `0` moving right; at a `0` or the end
write `1`, step back, and return. -/
def incCAct (r : Fin m) (cC cB : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some true => regAct r (some (some false)) 1 cC
  | _ => regAct r (some (some true)) (-1) cB

/-- The return state: walk left to the left blank, then step onto cell `0` and continue. -/
def incBAct (r : Fin m) (cB next : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none (-1) cB
  | none => regAct r none 1 next

section Inc

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m) (cC cB next : Λ)
  (hC : ∀ a w, P.tm.tr cC a w = incCAct r cC cB (w r))
  (hB : ∀ a w, P.tm.tr cB a w = incBAct r cB next (w r))
  (hCc : P.call cC = none) (hBc : P.call cB = none)

include hC hCc in
/-- **The carry phase** of the increment: from `cC` at the start of the suffix `w`, the program
reaches `cB` with `w` replaced by its increment `incW w`, the head in range throughout.

**Proof sketch.** Induction on `w`. A `1` becomes `0` and the carry moves right; a `0`, or the
blank after the word, becomes `1` and ends the carry, entering `cB`. The head stays within
`[|pre|, |pre ++ w|]`. -/
lemma incC_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ incW w).length ∧
      rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c cB r (FinTM.bufferTape (pre ++ incW w)) p ∧
      ∀ t < T, ∃ f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c cC r f q ∧ (pre.length : ℤ) ≤ q ∧ q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
    · rw [rrun_one]
      rw [rstep_noncall P oracle _ cC rfl hCc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hC, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [incCAct]
      rw [apply_regAct]
      dsimp only
      simp only [List.append_nil, incW]
      rw [update_bufferTape_end]
      simp only [SignType.coe_neg_one, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre
    cases b with
    | false =>
      refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
      · rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        simp only [incW]
        rw [update_bufferTape_cons]
        simp only [SignType.coe_neg_one, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
    | true =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [false])
      have hstep : rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ true :: w)) pre.length) 1 =
          regCfg c cC r (FinTM.bufferTape (pre ++ [false] ++ w)) (pre ++ [false]).length := by
        rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [incW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [incW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨f, q, hq, h1, h2⟩ := hmid t' (by omega)
          exact ⟨f, q, hq, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩

include hB hBc in
/-- **The return phase** of the increment: from `cB` at position `p < |w|`, the head walks left to
the left blank and back onto cell `0`, entering `next`.

**Proof sketch.** Induction on `n = p + 1`: on a letter the head moves left; at the left blank
`-1` it moves right onto cell `0` and the state becomes `next`. -/
lemma incB_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w.length →
      rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c next r (FinTM.bufferTape w) 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) t =
        regCfg c cB r (FinTM.bufferTape w) q ∧ -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one]
    rw [rstep_noncall P oracle _ cB rfl hBc]
    unfold MultiTapeTM.step
    simp only [regCfg_state]
    rw [hB, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [incBAct]
    rw [apply_regAct]
    try congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) 1 =
        regCfg c cB r (FinTM.bufferTape w) (p - 1) := by
      rw [rrun_one]
      rw [rstep_noncall P oracle _ cB rfl hBc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hB, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [incBAct]
      rw [apply_regAct]
      try congr 1
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, h1, by omega⟩

include hC hB hCc hBc in
/-- **The increment fragment**: from `cC` with `Nat.bits n` on register `r` and its head on
cell `0`, the program reaches `next` with `Nat.bits (n + 1)` there and its head on cell `0`,
everything else unchanged; on the way it is only in the fragment's (non-call) states, with
the head of `r` in `[-1, |Nat.bits (n + 1)|]`.

**Proof sketch.** Run the carry phase (`incC_run`) from cell `0`, which turns `bits n` into
`incW (bits n) = bits (n + 1)` (`bits_succ`). Then run the return phase (`incB_run`) back to
cell `0`; the head ranges of the two phases combine. -/
lemma inc_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n + 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ (s = cC ∨ s = cB) ∧ -1 ≤ q ∧ q ≤ (Nat.bits (n + 1)).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := incC_run P oracle r cC cB hC hCc c (Nat.bits n) []
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_succ] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r cB next hB hBc c (Nat.bits (n + 1)) (p + 1).toNat p
    (by omega) hp2
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨f, q, hq, h1, h2⟩ := hm1 t h
    have hl : (Nat.bits n).length ≤ (Nat.bits (n + 1)).length := by
      rw [bits_succ]
      generalize Nat.bits n = w
      induction w with
      | nil => simp [incW]
      | cons b w ih => cases b <;> simp [incW, ih]
    exact ⟨cC, f, q, hq, Or.inl rfl, by omega, by omega⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨cB, _, q, hq, Or.inr rfl, h1, by omega⟩

end Inc

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement and clear

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Frag`: words without trailing
`0`, the decrement fragment, the walk to the right end of a register word and the clear
fragment.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.toEnd_run` — the walk to the right end of a word.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Words -/

/-- The decrement of a little-endian word (borrow propagation, dropping a final `0`). -/
def decW : List Bool → List Bool
  | [] => []
  | false :: w => true :: decW w
  | [true] => []
  | true :: b :: w => false :: b :: w

/-- A word without a trailing `0`. -/
def Canon (w : List Bool) : Prop := ∀ h : w ≠ [], w.getLast h = true

/-- The binary word of a number has no trailing `0`. -/
lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := fun h => bits_getLast n h

/-- A word without trailing `0` keeps that property when its first letter is dropped. -/
lemma canon_tail {b : Bool} {w : List Bool} (h : Canon (b :: w)) : Canon w := by
  intro hw
  have := h (by simp)
  rwa [List.getLast_cons hw] at this

/-- Decrementing the increment of a word without trailing `0` gives the word back. -/
lemma decW_incW (w : List Bool) (h : Canon w) : decW (incW w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      cases w with
      | nil => have := h (by simp); simp at this
      | cons c w => rfl
    | true => simp only [incW, decW]; rw [ih (canon_tail h)]

/-- The binary word of `n - 1` is the decrement of that of `n`. -/
lemma bits_pred (n : ℕ) : Nat.bits (n - 1) = decW (Nat.bits n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits, decW]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, bits_succ, decW_incW _ (canon_bits k)]

/-- The binary word of `n / 2` is the tail of that of `n`. -/
lemma bits_half (n : ℕ) : Nat.bits (n / 2) = (Nat.bits n).tail := by
  rw [← Nat.div2_val, Nat.div2_bits_eq_tail]

/-- The parity of `n` is its first binary digit. -/
lemma bits_head_odd (n : ℕ) : (Nat.bits n).head? = if n = 0 then none else some (decide (n % 2 = 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits]
  · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
    have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by intro h0; simp; omega
    have e := bits_two_mul_add (n / 2) _ hb
    rw [← hdecomp] at e
    rw [e]; simp [show n ≠ 0 by omega]

/-- Erasing the last cell of a buffer tape holding `pre ++ [b]` leaves a buffer tape holding
`pre`. -/
lemma bufferTape_erase_last (pre : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ [b])) (pre.length : ℤ) none =
      FinTM.bufferTape pre := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · by_cases h1 : z.toNat < pre.length
      · rw [List.getElem?_append_left h1]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · rfl

/-! ## The decrement fragment -/

/-- The borrow state: `0`s become `1`s moving right; the first `1` becomes `0` and the next
cell decides whether it was the last bit. -/
def decDAct {m : ℕ} {Λ : Type} (r : Fin m) (dD dL dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some false => regAct r (some (some true)) 1 dD
  | some true => regAct r (some (some false)) 1 dL
  | none => regAct r none (-1) dB

/-- The lookahead after the borrow: a blank means the new `0` is a trailing zero. -/
def decLAct {m : ℕ} {Λ : Type} (r : Fin m) (dE dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | none => regAct r none (-1) dE
  | some _ => regAct r none (-1) dB

/-- Erase the trailing zero. -/
def decEAct {m : ℕ} {Λ : Type} (r : Fin m) (dB : Λ) : Action m Bool Λ :=
  regAct r (some none) (-1) dB

section Dec

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (dD dL dE dB next : Λ)
  (hD : ∀ a w, P.tm.tr dD a w = decDAct r dD dL dB (w r))
  (hL : ∀ a w, P.tm.tr dL a w = decLAct r dE dB (w r))
  (hE : ∀ a w, P.tm.tr dE a w = decEAct r dB)
  (hB : ∀ a w, P.tm.tr dB a w = incBAct r dB next (w r))
  (hDc : P.call dD = none) (hLc : P.call dL = none) (hEc : P.call dE = none)
  (hBc : P.call dB = none)

/-- Peel the first step off a run. -/
lemma rrun_succ_left (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rrun P oracle (rrun P oracle c 1) n := by
  rw [Nat.add_comm, rrun_add]

/-- One ordinary step of a program from a `regCfg`. -/
lemma rrun_one_reg (c : Cfg m Bool Λ x) (s : Λ) (f : ℤ → Option Bool) (p : ℤ)
    (hs : P.call s = none) :
    rrun P oracle (regCfg c s r f p) 1 =
      (P.tm.tr s (regCfg c s r f p).inputSymbol (regCfg c s r f p).workTapeSymbols).apply
        (regCfg c s r f p) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  simp only [regCfg_state]

include hD hL hE hDc hLc hEc in
/-- **The borrow phase** of the decrement: from `dD` with the head at the start of the suffix `w`
(no trailing `0`), the program reaches `dB` with `w` replaced by its decrement `decW w`, the
head in range throughout.

**Proof sketch.** Induction on `w`. A leading `0` becomes `1` and the borrow moves right; a
leading `1` becomes `0` and ends the borrow. If that `1` was the last letter, the trailing `0`
is erased through `dL`/`dE`. The head stays within `[|pre|, |pre ++ w|]`. -/
lemma decD_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), Canon w → ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ decW w).length ∧
      rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c dB r (FinTM.bufferTape (pre ++ decW w)) p ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c s r f q ∧ (s = dD ∨ s = dL ∨ s = dE) ∧ (pre.length : ℤ) ≤ q ∧
          q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre _
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
    · rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [decDAct]
      rw [apply_regAct]
      simp [decW, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre hcan
    cases b with
    | false =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [true]) (canon_tail hcan)
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ false :: w))
          pre.length) 1 =
          regCfg c dD r (FinTM.bufferTape (pre ++ [true] ++ w)) (pre ++ [true]).length := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by
          simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [decW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [decW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hmid t' (by omega)
          exact ⟨s, f, q, hq, hs, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩
    | true =>
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ true :: w))
          pre.length) 1 =
          regCfg c dL r (FinTM.bufferTape (pre ++ false :: w)) ((pre.length : ℤ) + 1) := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      cases w with
      | nil =>
        -- the last bit: erase it
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ [false]))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dE r (FinTM.bufferTape (pre ++ [false])) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ [false]) ((pre.length : ℤ) + 1) = none := by
            simp [FinTM.bufferTape]
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        have hstep3 : rrun P oracle (regCfg c dE r (FinTM.bufferTape (pre ++ [false]))
            pre.length) 1 = regCfg c dB r (FinTM.bufferTape pre) ((pre.length : ℤ) - 1) := by
          rw [rrun_one_reg P oracle r c dE _ _ hEc, hE]
          simp only [decEAct]
          rw [apply_regAct]
          dsimp only
          rw [bufferTape_erase_last]
          simp [sub_eq_add_neg]
        refine ⟨1 + (1 + 1), (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
        · rw [rrun_add, hstep, rrun_add, hstep2, hstep3]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
          rw [show t = 1 + (t - 1) by omega, rrun_add, hstep]
          rcases Nat.lt_or_ge (t - 1) 1 with h' | h'
          · rw [show t - 1 = 0 by omega]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp⟩
          · rw [show t - 1 = 1 + 0 by omega, rrun_add, hstep2]
            exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl), le_rfl, by simp⟩
      | cons b' w' =>
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ false :: b' :: w'))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dB r (FinTM.bufferTape (pre ++ false :: b' :: w')) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ false :: b' :: w') ((pre.length : ℤ) + 1) =
              some b' := by
            simp only [FinTM.bufferTape]
            rw [if_pos (by omega), show ((pre.length : ℤ) + 1).toNat = pre.length + 1 by omega]
            simp
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        refine ⟨1 + 1, pre.length, by omega, by simp [decW]; omega, ?_, ?_⟩
        · rw [rrun_add, hstep, hstep2]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
          · obtain rfl : t = 1 := by omega
            rw [hstep]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp; omega⟩

include hD hL hE hB hDc hLc hEc hBc in
/-- **The decrement fragment**: `Nat.bits n ↦ Nat.bits (n - 1)` on register `r`, head back on
cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** For `n = 0` the word is empty and the fragment returns at once. Otherwise run
the borrow phase (`decD_run`), which replaces `bits n` by `decW (bits n) = bits (n - 1)`
(`decW_incW`, `bits_succ`). Then run the return walk to cell `0`; the head ranges combine. -/
lemma dec_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n - 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := decD_run P oracle r dD dL dE dB hD hL hE hDc hLc hEc c
    (Nat.bits n) [] (canon_bits n)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_pred] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r dB next hB hBc c (Nat.bits (n - 1)) (p + 1).toNat p
    (by omega) hp2
  have hlen : (Nat.bits (n - 1)).length ≤ (Nat.bits n).length := by
    exact length_bits_mono (by omega)
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hm1 t h
    exact ⟨s, f, q, hq, by rcases hs with rfl | rfl | rfl <;> assumption, by omega, h2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨dB, _, q, hq, hBc, h1, by omega⟩

end Dec

/-! ## Walking to the right end -/

/-- Walk right over the word; at its right end step back and continue in `nx`. -/
def toEndAct {m : ℕ} {Λ : Type} (r : Fin m) (cR nx : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none 1 cR
  | none => regAct r none (-1) nx

section ToEnd

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR nx : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR nx (w r)) (hRc : P.call cR = none)

include hR hRc in
/-- **The walk to the right end** of a register word: from `cR` at position `p ≥ 0` the head moves
right to the blank after `w`, then back onto the last letter, entering `nx`.

**Proof sketch.** Induction on `n = |w| - p`: on a letter the head moves right; on the blank at
`|w|` it moves left and the state becomes `nx`. The head stays in `[p, |w|]`. -/
lemma toEnd_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), (w.length : ℤ) - p = n → 0 ≤ p →
      rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c nx r (FinTM.bufferTape w) ((w.length : ℤ) - 1) ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) t =
        regCfg c cR r (FinTM.bufferTape w) q ∧ p ≤ q ∧ q ≤ w.length := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hpw : p = w.length := by omega
    refine ⟨?_, fun t ht => ⟨p, by obtain rfl : t = 0 := by omega
                                   rfl, le_rfl, by omega⟩⟩
    rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [hpw]; simp
    rw [hrd]
    simp only [toEndAct]
    rw [apply_regAct]
    simp [hpw, sub_eq_add_neg]
  | succ n ih =>
    intro p hp h0
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) 1 =
        regCfg c cR r (FinTM.bufferTape w) (p + 1) := by
      rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [toEndAct]
      rw [apply_regAct]
      simp
    obtain ⟨ihr, ihm⟩ := ih (p + 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, le_rfl, by omega⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, by omega, h2⟩

end ToEnd

/-! ## The clear fragment -/

/-- Erase walking left; at the left blank step onto cell `0` and continue. -/
def clrEAct {m : ℕ} {Λ : Type} (r : Fin m) (cE next : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some _ => regAct r (some none) (-1) cE
  | none => regAct r none 1 next

section Clr

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR cE next : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR cE (w r))
  (hE : ∀ a w, P.tm.tr cE a w = clrEAct r cE next (w r))
  (hRc : P.call cR = none) (hEc : P.call cE = none)

include hE hEc in
/-- **The erasing walk** of the clear fragment: from `cE` on the last letter of `w.take k`, the
program erases the word right to left and reaches `next` on cell `0` of a blank register.

**Proof sketch.** Induction on `k`. Each step erases the cell under the head and moves left; at
the left blank `-1` the head moves right onto cell `0` and the state becomes `next`. -/
lemma clrE_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape []) 0 ∧
      ∀ t < k + 1, ∃ f q, rrun P oracle
        (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) t =
          regCfg c cE r f q ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ⟨_, _, by obtain rfl : t = 0 := by omega
                                      rfl, by omega, le_rfl⟩⟩
    rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0) (((0 : ℕ) : ℤ) - 1) = none := by simp
    rw [hrd]
    simp only [clrEAct]
    rw [apply_regAct]
    simp
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hstep : rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take (k + 1)))
        (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
      have hrd : FinTM.bufferTape (w.take (k + 1)) (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [htake]; simp only [FinTM.bufferTape]
        rw [if_pos (by omega), show (((k + 1 : ℕ) : ℤ) - 1).toNat = (w.take k).length by
          rw [hlen]; omega]
        simp only [List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      rw [hrd]
      simp only [clrEAct]
      rw [apply_regAct]
      dsimp only
      rw [show (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) by rw [hlen]; push_cast; ring,
        htake, bufferTape_erase_last, hlen]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show k + 1 + 1 = 1 + (k + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨f, q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨f, q, hq, h1, by push_cast at h2 ⊢; omega⟩

include hR hE hRc hEc in
/-- **The clear fragment**: `Nat.bits n ↦ Nat.bits 0` on register `r`, head back on cell `0`,
head in `[-1, |Nat.bits n|]` throughout. -/
lemma clr_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits 0)) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r cR cE hR hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := clrE_run P oracle r cE next hE hEc c w w.length le_rfl
  rw [List.take_length] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, h2, Nat.zero_bits]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨cR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨f, q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨cE, f, q, hq, hEc, hq1, by omega⟩

end Clr

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement, clear, halve

More single-register fragments of register-tape programs, in the style of
`Complexity.LogProg.inc_run`: each is specified by its transitions and proved once against
the program semantics. Counters are the words `Nat.bits n` from cell `0`.

The decrement and clear fragments are in
`TCSlib.Complexity.SpaceComplexity.Machines.FragDec`, which this file re-exports; this file
has the halving and equality fragments.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.
* `Complexity.LogProg.half_run` — `Nat.bits n ↦ Nat.bits (n / 2)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## The halving fragment -/

/-- The left walk of the halving: write the carried symbol (the cell to the right), carry the
current one; at the left blank step onto cell `0` and continue. -/
def halfLAct {m : ℕ} {Λ : Type} (r : Fin m) (carry : Option Bool) (hF hT next : Λ)
    (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some b => regAct r (some carry) (-1) (if b then hT else hF)
  | none => regAct r none 1 next

section Half

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (hR h0 hF hT next : Λ)
  (hRt : ∀ a w, P.tm.tr hR a w = toEndAct r hR h0 (w r))
  (h0t : ∀ a w, P.tm.tr h0 a w = halfLAct r none hF hT next (w r))
  (hFt : ∀ a w, P.tm.tr hF a w = halfLAct r (some false) hF hT next (w r))
  (hTt : ∀ a w, P.tm.tr hT a w = halfLAct r (some true) hF hT next (w r))
  (hRc : P.call hR = none) (h0c : P.call h0 = none) (hFc : P.call hF = none)
  (hTc : P.call hT = none)

/-- The left-walk state carrying a given optional symbol. -/
def halfSt (h0 hF hT : Λ) : Option Bool → Λ
  | none => h0
  | some false => hF
  | some true => hT

include h0t hFt hTt h0c hFc hTc in
/-- **The shifting walk** of the halving fragment: from the position `k - 1` after the first `k`
letters have been shifted, carrying `w[k]` in the state, the program shifts the remaining
letters one cell left and returns to cell `0` with `w.tail` written.

**Proof sketch.** Induction on `k`. Each step writes the carried letter, picks up the letter
under the head and moves left. At the left blank the head moves right onto cell `0`, and the
tape holds `w` with its first letter dropped. -/
lemma halfL_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape w.tail) 0 ∧
      ∀ t < k + 1, ∃ s f q, rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r
          (FinTM.bufferTape (w.take k ++ w.drop (k + 1))) ((k : ℤ) - 1)) t =
          regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  have htr : ∀ (cr : Option Bool) a ww, P.tm.tr (halfSt h0 hF hT cr) a ww =
      halfLAct r cr hF hT next (ww r) := by
    intro cr a ww; rcases cr with _ | _ | _
    · exact h0t a ww
    · exact hFt a ww
    · exact hTt a ww
  have hc : ∀ cr, P.call (halfSt h0 hF hT cr) = none := by
    intro cr; rcases cr with _ | _ | _
    · exact h0c
    · exact hFc
    · exact hTc
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
    rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0 ++ w.drop (0 + 1)) (((0 : ℕ) : ℤ) - 1) = none := by
      simp
    rw [hrd]
    simp only [halfLAct]
    rw [apply_regAct]
    simp [List.drop_one]
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hsplit : w.take (k + 1) ++ w.drop (k + 1 + 1) = w.take k ++ w[k] :: w.drop (k + 2) := by
      have h1 : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
      rw [h1, List.append_assoc]; rfl
    have hstep : rrun P oracle (regCfg c (halfSt h0 hF hT w[k + 1]?) r
        (FinTM.bufferTape (w.take (k + 1) ++ w.drop (k + 1 + 1))) (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read, hsplit]
      have hpos : (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) := by
        rw [hlen]; push_cast; ring
      have hrd : FinTM.bufferTape (w.take k ++ w[k] :: w.drop (k + 2))
          (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [hpos]; simp
      rw [hrd]
      simp only [halfLAct]
      rw [apply_regAct]
      dsimp only
      rw [List.getElem?_eq_getElem hkw]
      congr 1
      · cases w[k] <;> rfl
      · rw [hpos]
        rcases hk2 : w[k + 1]? with _ | v
        · -- `k + 1 = |w|`: erase the last cell
          have hkl : k + 1 = w.length := by
            by_contra hne; rw [List.getElem?_eq_getElem (by omega)] at hk2; simp at hk2
          have hd1 : w.drop (k + 2) = [] := List.drop_eq_nil_of_le (by omega)
          have hd2 : w.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd1, hd2, bufferTape_erase_last]; simp
        · have hd : w.drop (k + 1) = v :: w.drop (k + 2) := by
            rw [List.drop_eq_getElem_cons (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)]
            congr 1
            rw [List.getElem?_eq_getElem (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)] at hk2
            simpa using hk2
          rw [hd, update_bufferTape_cons]
      · simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [rrun_succ_left, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨s', f, q, hq, hs', h1, h2⟩ := ihm t' (by omega)
        exact ⟨s', f, q, hq, hs', h1, by push_cast at h2 ⊢; omega⟩

include hRt hRc h0t hFt hTt h0c hFc hTc in
/-- **The halving fragment**: `Nat.bits n ↦ Nat.bits (n / 2)` on register `r` (drop the
first binary digit), head back on cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** Walk to the right end of `bits n` (`toEnd_run`), then shift every letter one
cell left while walking back (`halfL_run`), which drops the first letter. Since `bits (n / 2)`
is the tail of `bits n` (`bits_half`), the register holds `bits (n / 2)`. -/
lemma half_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n / 2))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r hR h0 hRt hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := halfL_run P oracle r h0 hF hT next h0t hFt hTt h0c hFc hTc c w w.length
    le_rfl
  have he : w.take w.length ++ w.drop (w.length + 1) = w := by simp
  have hn : w[w.length]? = none := by simp
  rw [he, hn] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1]
    convert h2 using 3
    · rw [bits_half]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨hR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨s', f, q, hq, hs', hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨s', f, q, hq, hs', hq1, by omega⟩

end Half

/-! ## The equality test of two registers -/

section Eq

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A configuration with state `s` and the heads of registers `r₁`, `r₂` at `k`. -/
def eqCfg (c : Cfg m Bool Λ x) (s : Λ) (r₁ r₂ : Fin m) (k : ℤ) : Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, c.workTapes,
    Function.update (Function.update c.workTapePos r₁ k) r₂ k, c.output⟩

/-- Move the heads of `r₁` and `r₂` together. -/
def mv2Act (r₁ r₂ : Fin m) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r => if r = r₁ ∨ r = r₂ then (none, mv) else (none, 0), none, some s⟩

/-- Applying the two-register move action moves both register heads by `mv` and enters `s'`. -/
lemma apply_mv2Act (c : Cfg m Bool Λ x) (s s' : Λ) (r₁ r₂ : Fin m) (k : ℤ) (mv : SignType) :
    (mv2Act r₁ r₂ mv s').apply (eqCfg c s r₁ r₂ k) = eqCfg c s' r₁ r₂ (k + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [mv2Act, eqCfg])
  · funext r z
    simp only [mv2Act, eqCfg, Action.apply]
    split_ifs <;> rfl
  · funext r
    simp only [mv2Act, eqCfg, Action.apply, Function.update_apply]
    by_cases h2 : r = r₂
    · simp [h2]
    · by_cases h1 : r = r₁
      · simp [h1]
      · simp [h1, h2]

/-- The comparison step. -/
def eqCAct (r₁ r₂ : Fin m) (eC eBy eBn : Λ) (a b : Option Bool) : Action m Bool Λ :=
  if a = b then (if a = none then mv2Act r₁ r₂ (-1) eBy else mv2Act r₁ r₂ 1 eC)
  else mv2Act r₁ r₂ (-1) eBn

/-- The return step (reading register `r₁`). -/
def eqBAct (r₁ r₂ : Fin m) (eB l : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some _ => mv2Act r₁ r₂ (-1) eB
  | none => mv2Act r₁ r₂ 1 l

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r₁ r₂ : Fin m)
  (hne : r₁ ≠ r₂) (eC eBy eBn yes no : Λ)
  (hC : ∀ a w, P.tm.tr eC a w = eqCAct r₁ r₂ eC eBy eBn (w r₁) (w r₂))
  (hBy : ∀ a w, P.tm.tr eBy a w = eqBAct r₁ r₂ eBy yes (w r₁))
  (hBn : ∀ a w, P.tm.tr eBn a w = eqBAct r₁ r₂ eBn no (w r₁))
  (hCc : P.call eC = none) (hByc : P.call eBy = none) (hBnc : P.call eBn = none)

include hne in
/-- The two-register view reads register `r₁` at its head position `k`. -/
lemma eqCfg_read₁ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₁ = c.workTapes r₁ k := by
  simp [eqCfg, Cfg.workTapeSymbols, hne]

/-- The two-register view reads register `r₂` at its head position `k`. -/
lemma eqCfg_read₂ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₂ = c.workTapes r₂ k := by
  simp [eqCfg, Cfg.workTapeSymbols]

/-- One step of the program from a two-register view at a non-call state is the transition's
action applied to it. -/
lemma rrun_one_eq (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) (hs : P.call s = none) :
    rrun P oracle (eqCfg c s r₁ r₂ k) 1 =
      (P.tm.tr s (eqCfg c s r₁ r₂ k).inputSymbol (eqCfg c s r₁ r₂ k).workTapeSymbols).apply
        (eqCfg c s r₁ r₂ k) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  rfl

include hne hC hCc in
/-- **The comparison walk** of the equality test: from `eC` with both heads after the common prefix
`pre` of `w₁` and `w₂`, the program reaches `eBy` if `w₁ = w₂` and `eBn` otherwise, the heads
within `w₁`'s range.

**Proof sketch.** Induction on `u₁`. Equal letters move both heads right and extend the common
prefix. A mismatch, or one word ending before the other, enters `eBn`; both words ending
together enters `eBy`. -/
lemma eqC_run (c : Cfg m Bool Λ x) (w₁ w₂ : List Bool)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁) (h₂ : c.workTapes r₂ = FinTM.bufferTape w₂) :
    ∀ (u₁ u₂ pre : List Bool), w₁ = pre ++ u₁ → w₂ = pre ++ u₂ →
      ∃ (T : ℕ) (p : ℤ), (pre.length : ℤ) - 1 ≤ p ∧ p < w₁.length ∧
        rrun P oracle (eqCfg c eC r₁ r₂ pre.length) T =
          eqCfg c (if w₁ = w₂ then eBy else eBn) r₁ r₂ p ∧
        ∀ t < T, ∃ q, rrun P oracle (eqCfg c eC r₁ r₂ pre.length) t = eqCfg c eC r₁ r₂ q ∧
          (pre.length : ℤ) ≤ q ∧ q ≤ w₁.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre e1 e2
    refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp, ?_, ?_⟩
    · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂]
      have ha : FinTM.bufferTape w₁ pre.length = none := by rw [e1]; simp
      rw [ha]
      cases u₂ with
      | nil =>
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, ↓reduceIte]
        rw [apply_mv2Act]
        simp [e1, e2, sub_eq_add_neg]
      | cons b u₂' =>
        have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, rfl, le_rfl, by rw [e1]; simp⟩
  | cons a u₁' ih =>
    intro u₂ pre e1 e2
    have ha : FinTM.bufferTape w₁ pre.length = some a := by rw [e1]; simp
    cases u₂ with
    | nil =>
      refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
      · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂,
          ha]
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
    | cons b u₂' =>
      have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
      by_cases hab : a = b
      · subst hab
        obtain ⟨T, p, hp1, hp2, hr, hm⟩ := ih u₂' (pre ++ [a]) (by rw [e1]; simp)
          (by rw [e2]; simp)
        have hstep : rrun P oracle (eqCfg c eC r₁ r₂ pre.length) 1 =
            eqCfg c eC r₁ r₂ (pre ++ [a]).length := by
          rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          simp only [eqCAct, reduceCtorEq, ↓reduceIte]
          rw [apply_mv2Act]
          simp
        refine ⟨1 + T, p, by simp at hp1; omega, hp2, by rw [rrun_add, hstep, hr], ?_⟩
        intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨q, hq, hq1, hq2⟩ := hm t' (by omega)
          exact ⟨q, hq, by simp at hq1; omega, hq2⟩
      · refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
        · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          have hab' : (some a : Option Bool) ≠ some b := by simpa using hab
          simp only [eqCAct, hab', ↓reduceIte]
          rw [apply_mv2Act]
          have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp; intro h; exact absurd h hab
          simp [hneq, sub_eq_add_neg]
        · intro t ht
          obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩

include hne in
/-- The return walk of the equality test (reading register `r₁`, whose cells left of the
start are nonblank).

**Proof sketch.** Induction on `n = p + 1`: on a letter of `w₁` both heads move left; at the
left blank both move right onto cell `0` and the state becomes `l`. The heads stay in `[-1, p]`. -/
lemma eqB_run (c : Cfg m Bool Λ x) (w₁ : List Bool) (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁)
    (eB l : Λ) (hBt : ∀ a w, P.tm.tr eB a w = eqBAct r₁ r₂ eB l (w r₁))
    (hBc : P.call eB = none) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w₁.length →
      rrun P oracle (eqCfg c eB r₁ r₂ p) (n + 1) = eqCfg c l r₁ r₂ 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (eqCfg c eB r₁ r₂ p) t = eqCfg c eB r₁ r₂ q ∧
        -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
    have hrd : FinTM.bufferTape w₁ p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [eqBAct]
    rw [apply_mv2Act]
    congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w₁.length := by omega
    have hstep : rrun P oracle (eqCfg c eB r₁ r₂ p) 1 = eqCfg c eB r₁ r₂ (p - 1) := by
      rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
      have hrd : FinTM.bufferTape w₁ p = some w₁[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [eqBAct]
      rw [apply_mv2Act]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      rw [rrun_add, hstep]
      obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
      exact ⟨q, hq, h1, by omega⟩

include hne hC hBy hBn hCc hByc hBnc in
/-- **The equality test**: from `eC` with `Nat.bits a` on `r₁` and `Nat.bits b` on `r₂`, both
heads on cell `0`, the program reaches `yes` if `a = b` and `no` otherwise, heads back on
cell `0`, tapes unchanged; both heads stay in `[-1, |Nat.bits a|]`.

**Proof sketch.** Run the comparison walk (`eqC_run`) from the empty common prefix, reaching
`eBy` or `eBn` according to `bits a = bits b`, which is `a = b` by injectivity of `Nat.bits`.
Then run the return walk (`eqB_run`) back to cell `0`, ending in `yes` or `no`. -/
lemma eq_run (c : Cfg m Bool Λ x) (a b : ℕ)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape (Nat.bits a))
    (h₂ : c.workTapes r₂ = FinTM.bufferTape (Nat.bits b)) :
    ∃ T, rrun P oracle (eqCfg c eC r₁ r₂ 0) T = eqCfg c (if a = b then yes else no) r₁ r₂ 0 ∧
      ∀ t < T, ∃ s q, rrun P oracle (eqCfg c eC r₁ r₂ 0) t = eqCfg c s r₁ r₂ q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits a).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := eqC_run P oracle r₁ r₂ hne eC eBy eBn hC hCc c _ _ h₁ h₂
    (Nat.bits a) (Nat.bits b) [] rfl rfl
  simp only [List.length_nil, Nat.cast_zero] at hp1 hr1 hm1
  have hiff : (Nat.bits a = Nat.bits b) ↔ a = b :=
    ⟨fun h => bits_injective h, fun h => by rw [h]⟩
  by_cases hab : a = b
  · have hw : Nat.bits a = Nat.bits b := hiff.mpr hab
    rw [if_pos hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBy yes hBy hByc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_pos hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBy, q, hq, hByc, hq1, by omega⟩
  · have hw : Nat.bits a ≠ Nat.bits b := fun h => hab (hiff.mp h)
    rw [if_neg hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBn no hBn hBnc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_neg hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBn, q, hq, hBnc, hq1, by omega⟩

end Eq

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary counters as words

Register-tape programs keep counters in little-endian binary, as the words `Nat.bits n`
(least significant bit first, no redundant zeros). This file collects the word-level facts the
counter machines need: the value of a word, injectivity of `Nat.bits`, the carry rule of
the increment (`Complexity.LogProg.bits_succ`), and length bounds.

## Main definitions

* `Complexity.LogProg.bitsVal` — the value of a little-endian word.
* `Complexity.LogProg.incW` — the increment of a little-endian word (carry propagation).

## Main results

* `Complexity.LogProg.bitsVal_bits`, `Complexity.LogProg.bits_injective`.
* `Complexity.LogProg.bits_succ` — `Nat.bits (n + 1) = incW (Nat.bits n)`.
* `Complexity.LogProg.length_bits_le` — `|Nat.bits n| ≤ m` when `n < 2^m`;
  `Complexity.LogProg.length_bits_mono` — `|Nat.bits n|` is monotone in `n`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: counters in logarithmic space.)
-/

namespace Complexity.LogProg

/-- The value of a little-endian binary word. (Duplicates `BoolCircuit.bitsVal` of
`TCSlib.Complexity.CircuitComplexity.Adder`; to be unified.) -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * bitsVal w

/-- The increment of a little-endian binary word: flip the leading `1`s to `0` and the
first `0` (or the end) to `1`. -/
def incW : List Bool → List Bool
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incW w

/-- `Nat.bits` of an even and an odd number. -/
lemma bits_two_mul_add (n : ℕ) (b : Bool) (h : n = 0 → b = true) :
    Nat.bits (2 * n + b.toNat) = b :: Nat.bits n := by
  cases b with
  | false =>
    have hn : n ≠ 0 := fun h0 => by simpa using h h0
    simpa using Nat.bit0_bits n hn
  | true => simp

/-- The value of `Nat.bits n` is `n`. -/
lemma bitsVal_bits (n : ℕ) : bitsVal (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitsVal, Nat.zero_bits]
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      rw [hdecomp, bits_two_mul_add _ _ hb]
      simp only [bitsVal]
      rw [ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]; omega

/-- `Nat.bits` is injective. -/
lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← bitsVal_bits a, ← bitsVal_bits b, h]

/-- **The carry rule**: the binary word of `n + 1` is the increment of that of `n`. -/
lemma bits_succ (n : ℕ) : Nat.bits (n + 1) = incW (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits, Nat.one_bits, incW]
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · -- `n = 2m`, `m ≠ 0`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
        have hm : m ≠ 0 := by omega
        rw [Nat.bit0_bits m hm, show 2 * m + 1 = 2 * m + (true).toNat by rfl,
          bits_two_mul_add m true (fun _ => rfl)]
        rfl
      · -- `n = 2m + 1`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) + (false).toNat by simp; ring,
          bits_two_mul_add (m + 1) false (by omega), ih m (by omega)]
        rfl

/-- The binary word of `n` has at most `m` letters when `n < 2^m`. -/
lemma length_bits_le {n m : ℕ} (h : n < 2 ^ m) : (Nat.bits n).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- Binary words of larger numbers are not shorter. -/
lemma length_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

/-- The binary word of `n` has at most `⌊log₂ n⌋ + 1` letters. -/
lemma length_bits_le_log (n : ℕ) : (Nat.bits n).length ≤ Nat.log 2 n + 1 :=
  length_bits_le (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- Every letter of `Nat.bits n` is followed by more letters or is a `1`: the word has no
trailing `0`. (The last letter is `true`.) -/
lemma bits_getLast (n : ℕ) (h : Nat.bits n ≠ []) : (Nat.bits n).getLast h = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits] at h
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      have e := bits_two_mul_add (n / 2) _ hb
      rw [← hdecomp] at e
      simp only [e]
      by_cases h0 : Nat.bits (n / 2) = []
      · simp only [h0, List.getLast_singleton]
        have : n / 2 = 0 := by
          have := bitsVal_bits (n / 2); rw [h0] at this; simp [bitsVal] at this; omega
        exact hb this
      · rw [List.getLast_cons h0]
        exact ih (n / 2) (by omega) h0

end Complexity.LogProg

namespace Complexity.LogProg

/-- `n + 1 ≤ 2^(⌊log₂ n⌋ + 1)`. -/
lemma succ_le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) n

/-- **Logarithms of polynomials are logarithmic**: `⌊log₂ (A (n+1)^c + B)⌋ + 1` is at most a
constant times `⌊log₂ n⌋ + 1`.

**Proof sketch.** With `L = ⌊log₂ n⌋`, `n + 1 ≤ 2^{L+1}`, `A < 2^A` and `B < 2^B`, so
`A (n+1)^c + B < 2^{A + B + c(L+1) + 1}`; take `K = A + B + c + 2`. -/
lemma log_poly_bound (A c B : ℕ) :
    ∃ K, ∀ n, Nat.log 2 (A * (n + 1) ^ c + B) + 1 ≤ K * (Nat.log 2 n + 1) := by
  refine ⟨A + B + c + 2, fun n => ?_⟩
  set L := Nat.log 2 n
  have h1 : (n + 1) ^ c ≤ 2 ^ (c * (L + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (succ_le_two_pow_log n) c
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hB : B < 2 ^ B := Nat.lt_two_pow_self
  have hy : A * (n + 1) ^ c + B < 2 ^ (A + B + c * (L + 1) + 1) := by
    have e1 : A * (n + 1) ^ c ≤ 2 ^ A * 2 ^ (c * (L + 1)) :=
      Nat.mul_le_mul hA.le h1
    have e2 : 2 ^ A * 2 ^ (c * (L + 1)) ≤ 2 ^ (A + B + c * (L + 1)) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 2 ^ B ≤ 2 ^ (A + B + c * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega
  have hlog : Nat.log 2 (A * (n + 1) ^ c + B) < A + B + c * (L + 1) + 1 := by
    rcases Nat.eq_zero_or_pos (A * (n + 1) ^ c + B) with h | h
    · rw [h]; simp
    · exact Nat.log_lt_of_lt_pow (by omega) hy
  have hle : A + B + 2 ≤ (A + B + 2) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have heq : (A + B + c + 2) * (L + 1) = (A + B + 2) * (L + 1) + c * (L + 1) := by ring
  rw [heq]
  generalize c * (L + 1) = P at hlog ⊢
  generalize (A + B + 2) * (L + 1) = Q at hle ⊢
  omega

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines

Logspace algorithms are usually described with a constant number of counters of logarithmic
size [AB09, §4.1]. An *abstract register machine* (`Complexity.LogProg.ARM`) is a flowchart
over finitely many labels whose registers hold natural numbers, with the instructions:
increment, decrement, clear, halve, zero/parity/equality tests, the input-format checks and
index comparisons of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`, subroutine calls,
and `ret b` (answer `b`). Its semantics (`Complexity.LogProg.astep`) is over values; the
compilation `Complexity.LogProg.armProg` into a register-tape program stores each register
in binary (`Nat.bits`) and implements each instruction by the fragment proved for it.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Ins`, `Complexity.LogProg.ARM` — instructions and machines.
* `Complexity.LogProg.astep` — the value semantics.
* `Complexity.LogProg.armProg` — the compiled register-tape program.
* `Complexity.LogProg.aseam` — the program configuration of an abstract configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The instructions of an abstract register machine over `m` registers calling `d` deciders,
with labels `Λ`. -/
inductive Ins (m d : ℕ) (Λ : Type) where
  /-- `r := r + 1` -/
  | inc (r : Fin m) (l : Λ)
  /-- `r := r - 1` (truncated) -/
  | dec (r : Fin m) (l : Λ)
  /-- `r := 0` -/
  | clr (r : Fin m) (l : Λ)
  /-- `r := r / 2` -/
  | half (r : Fin m) (l : Λ)
  /-- branch on `r = 0` -/
  | jz (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r` odd -/
  | jodd (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r = s` (distinct registers) -/
  | jeq (r s : Fin m) (l₁ l₀ : Λ)
  /-- call decider `j` on the virtual input of `mode` and `args` -/
  | call (j : Fin d) (mode : Mode) (args : List (Fin m)) (l₁ l₀ : Λ)
  /-- answer `b` and halt -/
  | ret (b : Bool)
  /-- check that the input is `⟨1ⁿ, w⟩` with `w` a canonical binary payload (a `Nat.bits`
  word — `pairEncode [] [false]` has the pair shape but is rejected); else answer `0`;
  `r` is any register -/
  | valP (r : Fin m) (l : Λ)
  /-- check that the input is `⟨1ⁿ, ⟨u, w⟩⟩` with both inner payloads canonical binary
  words (else answer `0`) -/
  | valQ (r : Fin m) (l : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, w⟩` -/
  | jeqIn (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = u` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqFst (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqSnd (r : Fin m) (l₁ l₀ : Λ)

/-- An abstract register machine: an instruction at every label. -/
abbrev ARM (m d : ℕ) (Λ : Type) := Λ → Ins m d Λ

/-- The word `w` of an input `⟨1ⁿ, w⟩`. -/
def plainWord (x : List Bool) : List Bool := x.drop (tRun x + 2)

/-- The words `u`, `w` of an input `⟨1ⁿ, ⟨u, w⟩⟩`. -/
def pairWords (x : List Bool) : List Bool × List Bool :=
  (pairDecode (x.drop (tRun x + 2))).getD ([], [])

/-- The word of the input `⟨1ⁿ, w⟩` is `w`. -/
lemma plainWord_pairEncode (n : ℕ) (w : List Bool) :
    plainWord (pairEncode (List.replicate n true) w) = w := by
  unfold plainWord
  rw [tRun_pairEncode]
  simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]

/-- The words of the input `⟨1ⁿ, ⟨u, w⟩⟩` are `u` and `w`. -/
lemma pairWords_pairEncode (n : ℕ) (u w : List Bool) :
    pairWords (pairEncode (List.replicate n true) (pairEncode u w)) = (u, w) := by
  have : (pairEncode (List.replicate n true) (pairEncode u w)).drop
      (tRun (pairEncode (List.replicate n true) (pairEncode u w)) + 2) = pairEncode u w := by
    rw [tRun_pairEncode]; simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]
  simp [pairWords, this, pairDecode_pairEncode]

/-- An abstract configuration: the current label (`none` when halted), the register values,
and the answer once halted. -/
abbrev AConf (m : ℕ) (Λ : Type) := Option Λ × (Fin m → ℕ) × Option Bool

open Classical in
/-- **One step of an abstract register machine** on input `x`, deciders answering `oracle`. -/
noncomputable def astep {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) : AConf m Λ → AConf m Λ
  | (none, v, res) => (none, v, res)
  | (some l, v, res) =>
    match A l with
    | .inc r l' => (some l', Function.update v r (v r + 1), res)
    | .dec r l' => (some l', Function.update v r (v r - 1), res)
    | .clr r l' => (some l', Function.update v r 0, res)
    | .half r l' => (some l', Function.update v r (v r / 2), res)
    | .jz r l₁ l₀ => (some (if v r = 0 then l₁ else l₀), v, res)
    | .jodd r l₁ l₀ => (some (if v r % 2 = 1 then l₁ else l₀), v, res)
    | .jeq r s l₁ l₀ => (some (if v r = v s then l₁ else l₀), v, res)
    | .call j md args l₁ l₀ =>
      (some (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))
        then l₁ else l₀), v, res)
    | .ret b => (none, v, some b)
    | .valP _ l' => if ValidPlain x then (some l', v, res) else (none, v, some false)
    | .valQ _ l' => if ValidPair x then (some l', v, res) else (none, v, some false)
    | .jeqIn r l₁ l₀ => (some (if Nat.bits (v r) = plainWord x then l₁ else l₀), v, res)
    | .jeqFst r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).1 then l₁ else l₀), v, res)
    | .jeqSnd r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).2 then l₁ else l₀), v, res)

/-- The run of an abstract register machine. -/
noncomputable def arun {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (a : AConf m Λ) (n : ℕ) : AConf m Λ :=
  (astep A oracle x)^[n] a

/-! ## Compilation -/

/-- The phases of the instruction fragments. -/
inductive Ph where
  | start
  | incB
  | decL | decE | decB
  | clrE
  | h0 | hF | hT
  | eqBy | eqBn
  | vU1 | vS | vW0 | vWF | vWT | vrw1 | vrw2
  | vP1 (l : Option Bool) | vP2 (b : Bool) (l : Option Bool)
  | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool)
  | jP1 | jP2F | jP2T | jD1 | jD2F | jD2T
  deriving DecidableEq, Fintype

/-- A control action: change state, move nothing. -/
def goAct {m : ℕ} {S : Type} (s : S) : Action m Bool S := ⟨0, fun _ => (none, 0), none, some s⟩

/-- Halt with output `b`. -/
def retAct {m : ℕ} {S : Type} (b : Bool) : Action m Bool S := ⟨0, fun _ => (none, 0), some b, none⟩

/-- The input rewind scan (moving nothing else): left over symbols, then right into `nx`. -/
def rw2Act {m : ℕ} {S : Type} (r : Fin m) (s₀ nx : S) (a : Option Bool) : Action m Bool S :=
  match a with
  | some _ => xAct r (-1) 0 s₀
  | none => xAct r 1 0 nx

/-- The halting junk action. -/
def junkAct {m : ℕ} {S : Type} : Action m Bool S := ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition table of one instruction's fragment**: phase `start` is the fragment's
first state. -/
def insTr {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  match i with
  | .inc r l' =>
    match ph with
    | .start => incCAct r (l, .start) (l, .incB) (w r)
    | .incB => incBAct r (l, .incB) (l', .start) (w r)
    | _ => junkAct
  | .dec r l' =>
    match ph with
    | .start => decDAct r (l, .start) (l, .decL) (l, .decB) (w r)
    | .decL => decLAct r (l, .decE) (l, .decB) (w r)
    | .decE => decEAct r (l, .decB)
    | .decB => incBAct r (l, .decB) (l', .start) (w r)
    | _ => junkAct
  | .clr r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .clrE) (w r)
    | .clrE => clrEAct r (l, .clrE) (l', .start) (w r)
    | _ => junkAct
  | .half r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .h0) (w r)
    | .h0 => halfLAct r none (l, .hF) (l, .hT) (l', .start) (w r)
    | .hF => halfLAct r (some false) (l, .hF) (l, .hT) (l', .start) (w r)
    | .hT => halfLAct r (some true) (l, .hF) (l, .hT) (l', .start) (w r)
    | _ => junkAct
  | .jz r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = none then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jodd r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = some true then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jeq r s l₁ l₀ =>
    match ph with
    | .start => eqCAct r s (l, .start) (l, .eqBy) (l, .eqBn) (w r) (w s)
    | .eqBy => eqBAct r s (l, .eqBy) (l₁, .start) (w r)
    | .eqBn => eqBAct r s (l, .eqBn) (l₀, .start) (w r)
    | _ => junkAct
  | .call _ _ _ _ _ => junkAct
  | .ret b =>
    match ph with
    | .start => retAct b
    | _ => junkAct
  | .valP r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vW0) a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .valQ r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vP1 none) a
    | .vP1 lst => valP1Act r (fun b => (l, .vP2 b lst)) a
    | .vP2 b lst => valP2Act r (l, .vP1 (some false)) (l, .vP1 (some true)) (l, .vW0) lst b a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .jeqIn r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jC)
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqSnd r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jP1)
    | .jP1 => pskip1Act r (l, .jP2F) (l, .jP2T) a
    | .jP2F => pskip2Act r (l, .jP1) (l, .jC) false a
    | .jP2T => pskip2Act r (l, .jP1) (l, .jC) true a
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqFst r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jD1)
    | .jD1 => dcmp1Act r (l, .jD2F) (l, .jD2T) a
    | .jD2F => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) false a (w r)
    | .jD2T => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) true a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct

/-- The transition table of the compiled program. -/
def armTr {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  insTr (A l) l ph a w

/-- The call node of one instruction. -/
def insCall {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (ph : Ph) : Option (CallSpec m d (Λ × Ph)) :=
  match i with
  | .call j md args l₁ l₀ =>
    match ph with
    | .start => some ⟨j, md, args, (l₁, .start), (l₀, .start)⟩
    | _ => none
  | _ => none

/-- The call nodes of the compiled program. -/
def armCall {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (q : Λ × Ph) :
    Option (CallSpec m d (Λ × Ph)) :=
  insCall (A q.1) q.2

/-- **The compiled register-tape program** of an abstract register machine. -/
def armProg {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l₀ : Λ) : RProg m d (Λ × Ph) where
  tm := ⟨(l₀, .start), fun q a w => armTr A q.1 q.2 a w⟩
  call := armCall A

/-- The program configuration representing the abstract configuration at label `l` with
values `v`, having written `out`. -/
def aseam {m : ℕ} {Λ : Type} (x : List Bool) (l : Λ) (v : Fin m → ℕ) (out : List Bool) :
    Cfg m Bool (Λ × Ph) x :=
  ⟨some (l, .start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)), fun _ => 0, out⟩

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proving abstract register machines correct

Reasoning about abstract register machines (`Complexity.LogProg.ARM`) happens on values: runs
`Complexity.LogProg.AReach` between abstract configurations through configurations satisfying
an invariant, composed sequentially. `Complexity.LogProg.arm_decides` turns a correct
abstract machine — one answering membership in a language on every input, with values of
logarithmically many binary digits — into a logspace decider.

## Main definitions

* `Complexity.LogProg.AReach`, `Complexity.LogProg.AHalt` — runs of abstract machines.

## Main results

* `Complexity.LogProg.arm_decides` — a correct abstract machine with logarithmic register
  values, calling logspace deciders on short virtual inputs, decides its language in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A run of an abstract machine from `a` to `a'` through configurations satisfying `G`. -/
def AReach (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a a' : AConf m Λ) : Prop :=
  ∃ T, arun A oracle x a T = a' ∧ ∀ t < T, G (arun A oracle x a t)

/-- A run of an abstract machine from `a` answering `b`, through configurations satisfying `G`. -/
def AHalt (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (b : Bool) : Prop :=
  ∃ T, (arun A oracle x a T).1 = none ∧ (arun A oracle x a T).2.2 = some b ∧
    ∀ t < T, G (arun A oracle x a t)

section Combinators

variable {A : ARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- Running `s + t` steps is running `s` steps, then `t` steps. -/
lemma arun_add (a : AConf m Λ) (s t : ℕ) :
    arun A oracle x a (s + t) = arun A oracle x (arun A oracle x a s) t := by
  simp only [arun]; rw [Nat.add_comm, Function.iterate_add_apply]

/-- Every configuration reaches itself (in zero steps). -/
lemma AReach.refl (a : AConf m Λ) : AReach A oracle x G a a := ⟨0, rfl, fun t h => by omega⟩

/-- Runs compose: a run from `a` to `b` followed by one from `b` to `c` is a run from `a` to `c`. -/
lemma AReach.trans {a b c : AConf m Λ} (h₁ : AReach A oracle x G a b)
    (h₂ : AReach A oracle x G b c) : AReach A oracle x G a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A run from `a` to `b` followed by a halting run from `b` is a halting run from `a`, with
the same answer. -/
lemma AReach.halt {a b : AConf m Λ} {r : Bool} (h₁ : AReach A oracle x G a b)
    (h₂ : AHalt A oracle x G b r) : AHalt A oracle x G a r := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1]; exact f1, by rw [arun_add, e1]; exact f2, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A configuration satisfying the guard reaches its successor in one step. -/
lemma AReach.single {a : AConf m Λ} (hG : G a) :
    AReach A oracle x G a (astep A oracle x a) := ⟨1, rfl, fun t ht => by
  obtain rfl : t = 0 := by omega
  exact hG⟩

/-- A step followed by a run. -/
lemma AReach.step {a c : AConf m Λ} (hG : G a) (h : AReach A oracle x G (astep A oracle x a) c) :
    AReach A oracle x G a c := (AReach.single hG).trans h

/-- A step followed by a halting run. -/
lemma AHalt.step {a : AConf m Λ} {r : Bool} (hG : G a)
    (h : AHalt A oracle x G (astep A oracle x a) r) : AHalt A oracle x G a r :=
  (AReach.single hG).halt h

/-- Answering in one step. -/
lemma AHalt.ret {l : Λ} {v : Fin m → ℕ} {r : Bool} (hA : A l = .ret r)
    (hG : G (some l, v, none)) : AHalt A oracle x G (some l, v, none) r :=
  ⟨1, by simp [arun, astep, hA], by simp [arun, astep, hA], fun t ht => by
    obtain rfl : t = 0 := by omega
    exact hG⟩

/-- A run through configurations satisfying `G` also runs through configurations satisfying any
weaker `G'`. -/
lemma AReach.mono {G' : AConf m Λ → Prop} {a b : AConf m Λ} (h : AReach A oracle x G a b)
    (hG : ∀ c, G c → G' c) : AReach A oracle x G' a b := by
  obtain ⟨T, e, hm⟩ := h; exact ⟨T, e, fun t ht => hG _ (hm t ht)⟩

/-- A halting run through configurations satisfying `G` also runs through configurations
satisfying any weaker `G'`. -/
lemma AHalt.mono {G' : AConf m Λ → Prop} {a : AConf m Λ} {r : Bool} (h : AHalt A oracle x G a r)
    (hG : ∀ c, G c → G' c) : AHalt A oracle x G' a r := by
  obtain ⟨T, e1, e2, hm⟩ := h; exact ⟨T, e1, e2, fun t ht => hG _ (hm t ht)⟩

end Combinators

/-! ## From abstract machines to `L` -/

/-- A clean run within a head range is a clean run within any larger range. -/
lemma cleanRun_mono {kD : ℕ} {SD : Type} {D : MultiTapeTM kD Bool SD} {q : SD}
    {V : List Bool} {b : Bool} {B B' : ℕ} (h : CleanRun D q V b B) (hB : B ≤ B') :
    CleanRun D q V b B' := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, fun t ht i => (h5 t ht i).trans (by exact_mod_cast hB)⟩

/-- The syntactic preconditions of an abstract step (the decider part of `Pre` is discharged
by `arm_decides`). -/
def PreS (A : ARM m d Λ) (x : List Bool) : AConf m Λ → Prop
  | (some l, _, _) =>
    match A l with
    | .jeq r s _ _ => r ≠ s
    | .jeqIn _ _ _ => ValidPlain x
    | .jeqFst _ _ _ => ValidPair x
    | .jeqSnd _ _ _ => ValidPair x
    | .call _ _ args _ _ => args.Nodup
    | _ => True
  | _ => True

/-- A virtual input is at most as long as its segments' renderings plus two separator symbols
per segment. -/
lemma length_vword_le (segs : List Seg) :
    (vword segs).length ≤ (segs.map rlen).sum + 2 * segs.length := by
  induction segs with
  | nil => simp [vword]
  | cons s rest ih =>
    cases rest with
    | nil => simp [vword]
    | cons t rest' =>
      simp only [vword, List.length_append, length_render, List.length_cons, List.length_nil,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Every register segment of a call comes from one of the argument words. -/
lemma mem_argSegs {ws : List (List Bool)} {sg : Seg} (h : sg ∈ argSegs ws) : sg.1 ∈ ws := by
  induction ws with
  | nil => simp [argSegs] at h
  | cons w ws ih =>
    cases ws with
    | nil => simp [argSegs] at h; simp [h]
    | cons v ws' =>
      simp only [argSegs, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- The renderings of the register segments of argument words of length at most `W` have total
length at most `2W` per word. -/
lemma sum_rlen_argSegs_le (ws : List (List Bool)) (W : ℕ) (h : ∀ w ∈ ws, w.length ≤ W) :
    ((argSegs ws).map rlen).sum ≤ ws.length * (2 * W) := by
  have hle : ∀ y ∈ (argSegs ws).map rlen, y ≤ 2 * W := by
    intro y hy
    obtain ⟨sg, hs, rfl⟩ := List.mem_map.mp hy
    have := h _ (mem_argSegs hs)
    obtain ⟨w', bb⟩ := sg
    cases bb <;> simp [rlen] at this ⊢ <;> omega
  have := List.sum_le_card_nsmul _ _ hle
  simpa using this

/-- The virtual input of a call is short when the registers are.

**Proof sketch.** The virtual input is the leading segment (the input doubled, or its leading
run of `1`s, of rendered length at most `2|x|`) and one segment per argument register. There are
at most `m` arguments since they are distinct (`hnd`), each rendered with length at most `2W`,
plus two separator symbols per segment (`length_vword_le`, `sum_rlen_argSegs_le`). -/
lemma length_callSegs_le (cs : CallSpec m d Λ) (W : ℕ) (V : Fin m → List Bool)
    (hV : ∀ r, (V r).length ≤ W) (hnd : cs.args.Nodup) :
    (vword (callSegs cs x V)).length ≤ 2 * x.length + 2 + m * (2 * W + 2) := by
  have h1 := length_vword_le (callSegs cs x V)
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  have h0 : rlen (cs.mode.seg0 x) ≤ 2 * x.length := by
    cases cs.mode
    · simp [Mode.seg0, rlen]
    · simp only [Mode.seg0, rlen, Bool.false_eq_true, ↓reduceIte]
      have := (List.takeWhile_prefix (fun b => decide (b = true)) (l := x)).length_le; omega
  have h2 := sum_rlen_argSegs_le (cs.args.map V) W (by simp; intro r _; exact hV r)
  simp only [callSegs, List.map_cons, List.sum_cons, List.length_cons, length_argSegs,
    List.length_map] at h1 h2 ⊢
  have h3 : cs.args.length * (2 * W) ≤ m * (2 * W) := Nat.mul_le_mul_right _ hlen
  have h4 : m * (2 * W + 2) = m * (2 * W) + 2 * m := by ring
  rw [h4]
  generalize m * (2 * W) = P at h3 ⊢
  generalize cs.args.length * (2 * W) = Q at h2 h3
  omega

/-- **Abstract register machines with logarithmic registers decide languages in `L`**: if, on
every input `x`, the abstract machine `A` (calling deciders for languages in `L`) answers
`x ∈ L`, through configurations meeting the syntactic preconditions with every register value
of at most `K · logSpace |x|` binary digits (counting one increment), then `L ∈ L`.

**Proof sketch.** The deciders are collected in a clean bank (`bank_cleanRun`). Virtual inputs
of calls have length at most `2|x| + 2 + m (2W + 2)` (`length_callSegs_le`), linear in `|x|`,
so the deciders' head ranges are `O(log |x|)` (`log_poly_bound`). `arm_space` then gives a
machine answering `x ∈ L` within `m (W + 2) + kD (2B + 1) = O(log |x|)` cells. -/
theorem arm_decides {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (K : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ K * logSpace x.length)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  let c : Fin d → ℕ := fun j => Classical.choose (hc j)
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (Classical.choose_spec (hc j))
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) fun n => c j * logSpace n :=
    fun j => Classical.choose_spec (Classical.choose_spec (hc j))
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Q := 4 + 2 * m + 2 * m * K with hQ
  obtain ⟨K2, hK2⟩ := log_poly_bound Q 1 0
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  refine ⟨m * K + 2 * m + kD * (2 * cs * K2 + 3),
    compileFinTM (armProg A l₀) (l₀, .start) (bankTM Ms) (bankStart Ms), fun x => ?_⟩
  set n := x.length with hn
  set Ls := logSpace n with hLs
  have hL1 : 1 ≤ Ls := by simp [hLs, logSpace]
  have hLn : Ls ≤ n + 1 := by
    simp only [hLs, logSpace]
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · have := Nat.log_lt_self 2 (show n ≠ 0 by omega); omega
  set W := K * Ls with hW
  set B := cs * K2 * Ls + 1 with hB
  obtain ⟨N, h1, h2, hm⟩ := hcorr x
  have hpre : ∀ t < N, Pre A oracle (bankTM Ms) (bankStart Ms) B x
      (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ)
        ≤ (W : ℤ) := by
    intro t ht
    obtain ⟨hps, hbd⟩ := hm t ht
    refine ⟨?_, fun r => by exact_mod_cast hbd r⟩
    generalize hat : arun A oracle x (some l₀, fun _ => 0, none) t = a at hps hbd
    rcases a with ⟨_ | l, v, res⟩
    · trivial
    · simp only [Pre]
      cases hA : A l with
      | jeq r s' l₁ l₀' => simpa [PreS, hA] using hps
      | jeqIn r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqFst r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqSnd r l₁ l₀' => simpa [PreS, hA] using hps
      | inc => trivial
      | dec => trivial
      | clr => trivial
      | half => trivial
      | jz => trivial
      | jodd => trivial
      | ret => trivial
      | valP => trivial
      | valQ => trivial
      | call j md args l₁ l₀' =>
      simp only [PreS, hA] at hps
      refine ⟨hps, ?_⟩
      refine cleanRun_mono (bank_cleanRun Ms As (fun j n => c j * logSpace n) hMs j _) ?_
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ W (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ W
          have h0 : (Nat.bits (v r + 1)).length ≤ W := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length := by
            exact length_bits_mono (by omega)
          omega) hps
      have hVQ : (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length ≤
          Q * (n + 1) ^ 1 + 0 := by
        have : W ≤ K * (n + 1) := Nat.mul_le_mul_left K hLn
        have e : Q * (n + 1) ^ 1 + 0 = (4 + 2 * m) * (n + 1) + 2 * m * (K * (n + 1)) := by
          simp only [hQ]; ring
        rw [e]
        have h5 : m * (2 * W + 2) ≤ 2 * m * (K * (n + 1)) + 2 * m := by
          have := Nat.mul_le_mul_left (2 * m) this
          calc m * (2 * W + 2) = 2 * m * W + 2 * m := by ring
            _ ≤ 2 * m * (K * (n + 1)) + 2 * m := by omega
        have h6 : 2 * m ≤ 2 * m * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h7 : (4 + 2 * m) * (n + 1) = 4 * (n + 1) + 2 * m * (n + 1) := by ring
        omega
      have hlog : logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length
          ≤ K2 * Ls := by
        have h := hK2 n
        have hm' := Nat.log_mono_right (b := 2) hVQ
        simp only [logSpace, hLs] at h hm' ⊢
        omega
      have hcm : c j * logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
          fun r => Nat.bits (v r))).length ≤ cs * K2 * Ls := by
        calc _ ≤ c j * (K2 * Ls) := Nat.mul_le_mul_left _ hlog
          _ ≤ cs * (K2 * Ls) := Nat.mul_le_mul_right _ (hcj j)
          _ = cs * K2 * Ls := by ring
      simp only [hB]
      exact max_le (by omega) (by omega)
  obtain ⟨T, hT, hsp⟩ := arm_space A l₀ oracle (bankTM Ms) (bankStart Ms) B W N
    (MultiTapeTM.indicator (L : Set (List Bool)) x) h1 h2 hpre
  refine ⟨T, hT, hsp.trans ?_⟩
  · -- the arithmetic
    show _ ≤ (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls
    have e1 : m * (W + 2) = m * K * Ls + 2 * m := by simp only [hW]; ring
    have e2 : kD * (2 * B + 1) = 2 * kD * cs * K2 * Ls + 3 * kD := by simp only [hB]; ring
    have e3 : (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls =
        m * K * Ls + 2 * m * Ls + 2 * kD * cs * K2 * Ls + 3 * kD * Ls := by ring
    rw [e1, e2, e3]
    have f1 : 2 * m ≤ 2 * m * Ls := Nat.le_mul_of_pos_right _ (by omega)
    have f2 : 3 * kD ≤ 3 * kD * Ls := Nat.le_mul_of_pos_right _ (by omega)
    omega

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A toolkit for abstract register machines

Conveniences for writing logspace algorithms as abstract register machines
(`Complexity.LogProg.ARM`) on inputs `⟨1ⁿ, w⟩`: the virtual inputs of calls in `unaryFst`
mode with one or two register arguments are `⟨1ⁿ, bits r⟩` and `⟨1ⁿ, ⟨bits r, bits s⟩⟩`,
and `Complexity.LogProg.arm_decides_poly` restates `Complexity.LogProg.arm_decides` with
register values bounded by a polynomial in the input length.

## Main results

* `Complexity.LogProg.vword_unary₁`, `Complexity.LogProg.vword_unary₂` — virtual inputs
  of `unaryFst` calls.
* `Complexity.LogProg.arm_decides_poly` — abstract register machines with polynomially
  bounded register values decide languages in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type}

/-- The leading run of `1`s of `⟨1ⁿ, w⟩` is `1²ⁿ`. -/
lemma takeWhile_pairEncode_replicate (n : ℕ) (w : List Bool) :
    (pairEncode (List.replicate n true) w).takeWhile (· = true) =
      List.replicate (2 * n) true := by
  simp only [pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
  rw [List.takeWhile_append_of_pos (by simp)]
  simp

/-- The virtual input of a `unaryFst` call with one argument on `⟨1ⁿ, w⟩` is `⟨1ⁿ, V r⟩`. -/
lemma vword_unary₁ (n : ℕ) (w : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (V r) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The virtual input of a `unaryFst` call with two arguments on `⟨1ⁿ, w⟩` is
`⟨1ⁿ, ⟨V r, V s⟩⟩`. -/
lemma vword_unary₂ (n : ℕ) (w : List Bool) (j : Fin d) (r s : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r, s], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (pairEncode (V r) (V s)) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The indicator of a set at a point, as a decision. -/
lemma indicator_eq_decide {α : Type} (S : Set α) (a : α) :
    MultiTapeTM.indicator S a = @decide (a ∈ S) (Classical.dec _) := by
  unfold MultiTapeTM.indicator; split <;> simp_all

/-- **Abstract register machines with polynomially bounded registers decide languages in
`L`**: the form of `arm_decides` with register values at most `C₀ (|x| + 1)^{c₀}`.

**Proof sketch.** A value `v ≤ C₀ (|x|+1)^{c₀}` has `|bits (v + 1)| ≤ ⌊log₂ (v + 1)⌋ + 1`,
which `log_poly_bound` bounds by `K · logSpace |x|`. -/
theorem arm_decides_poly {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  obtain ⟨K, hK⟩ := log_poly_bound C₀ c₀ 1
  refine arm_decides A l₀ As hAs K fun x => (hcorr x).mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => ?_⟩
  have e1 := length_bits_le_log (a.2.1 r + 1)
  have e2 : Nat.log 2 (a.2.1 r + 1) ≤ Nat.log 2 (C₀ * (x.length + 1) ^ c₀ + 1) :=
    Nat.log_mono_right (by have := h2 r; omega)
  have e3 := hK x.length
  simp only [logSpace]
  omega

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading the unary length in logarithmic space

The abstract register machines of `TCSlib.Complexity.SpaceComplexity.Machines.ARM` see their
input `⟨1ⁿ, w⟩` only through comparisons with `w` and through calls to logspace deciders on
`⟨1ⁿ, …⟩`; none of their instructions measures `n`. This file supplies the missing base
decider, written directly as a register-tape program: it counts the leading run `1²ⁿ` of
`⟨1ⁿ, w⟩ = 1²ⁿ 0 1 w` into a binary register and compares the register with `w`
[AB09, §4.1: a logspace machine keeps a counter of `O(log n)` bits].

The decider is generic logspace material; its first client is [AB09, Thm 6.15]
(`TCSlib.Complexity.CircuitComplexity.LogspaceTableau`).

## Main definitions

* `Complexity.LogProg.dblLang` — the inputs `⟨1ⁿ, bits (2n)⟩`.
* `Complexity.LogProg.Dbl.prog` — the register-tape program deciding it.

## Main results

* `Complexity.LogProg.dblLang_mem` — `dblLang ∈ L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The inputs `⟨1ⁿ, bits (2n)⟩`: the index on the input is twice the unary length. -/
def dblLang : Language Bool :=
  {y | ∃ n, y = pairEncode (List.replicate n true) (Nat.bits (2 * n))}

namespace Dbl

/-- The states of the counting program. -/
inductive St where
  | vU0 | vU1 | vS | vW0 | vWF | vWT | rw1 | rw2 | cnt | iC | iB | sw1 | sw2
  | jK | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool) | yes | no
  deriving DecidableEq, Fintype

/-- The transitions: the format check (`vU0` … `rw2`), the count of the leading `1`s
(`cnt`, with the increment fragment `iC`, `iB`), the rewind (`sw1`, `sw2`), and the
comparison of the counter with the index (`jK` … `jI2`). -/
def tr : St → Option Bool → (Fin 1 → Option Bool) → Action 1 Bool St
  | .vU0, a, _ => valUAct 0 .vU0 .vU1 .vS false a
  | .vU1, a, _ => valUAct 0 .vU0 .vU1 .vS true a
  | .vS, a, _ => valSAct 0 .vW0 a
  | .vW0, a, _ => valWAct 0 .vWF .vWT .rw1 none a
  | .vWF, a, _ => valWAct 0 .vWF .vWT .rw1 (some false) a
  | .vWT, a, _ => valWAct 0 .vWF .vWT .rw1 (some true) a
  | .rw1, _, _ => xAct 0 (-1) 0 .rw2
  | .rw2, a, _ => rw2Act 0 .rw2 .cnt a
  | .cnt, a, _ => if a = some true then xAct 0 1 0 .iC else xAct 0 0 0 .sw1
  | .iC, _, w => incCAct 0 .iC .iB (w 0)
  | .iB, _, w => incBAct 0 .iB .cnt (w 0)
  | .sw1, _, _ => xAct 0 (-1) 0 .sw2
  | .sw2, a, _ => rw2Act 0 .sw2 .jK a
  | .jK, a, _ => skipAct 0 .jK .jK2 a
  | .jK2, _, _ => xAct 0 1 0 .jC
  | .jC, a, w => cmpAct 0 .jC St.jRB a (w 0)
  | .jRB b, _, w => backAct 0 (.jRB b) (.jI1 b) (w 0)
  | .jI1 b, _, _ => xAct 0 (-1) 0 (.jI2 b)
  | .jI2 b, a, _ => rewAct 0 (.jI2 b) (if b then .yes else .no) a
  | .yes, _, _ => retAct true
  | .no, _, _ => retAct false

/-- **The counting program** (one register, no calls). -/
def prog : RProg 1 0 St where
  tm := ⟨.vU0, tr⟩
  call := fun _ => none

/-- The (empty) oracle. -/
def o : Fin 0 → List Bool → Bool := fun j => j.elim0

variable {y : List Bool}

/-- The configuration in state `s`, input head `ip`, register holding `bits v` with its head at
`q`, nothing written. -/
def K (s : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) : Cfg 1 Bool St y :=
  ⟨some s, ip, fun _ => FinTM.bufferTape (Nat.bits v), fun _ => q, []⟩

/-- The input-scanning view of a counting configuration is a counting configuration. -/
lemma xCfg_K (s s' : St) (ip ip' : Fin (y.length + 2)) (v : ℕ) (q q' : ℤ) :
    xCfg (K s' ip' v q') s ip 0 q = K s ip v q := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r; rw [Fin.fin_one_eq_zero r]; simp [xCfg, K]

/-- The register view of a counting configuration is a counting configuration. -/
lemma regCfg_K (s s' : St) (ip : Fin (y.length + 2)) (v v' : ℕ) (q q' : ℤ) :
    regCfg (K s' ip v q') s 0 (FinTM.bufferTape (Nat.bits v')) q = K s ip v' q := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]

/-- A run from `c` to `c'` with the register head in `[-1, W]`. -/
def Rch (W : ℕ) (c c' : Cfg 1 Bool St y) : Prop :=
  ∃ T, rrun prog o c T = c' ∧ ∀ t < T, -1 ≤ (rrun prog o c t).workTapePos 0 ∧
    (rrun prog o c t).workTapePos 0 ≤ W

/-- Runs compose. -/
lemma Rch.trans {W : ℕ} {a b c : Cfg 1 Bool St y} (h₁ : Rch W a b) (h₂ : Rch W b c) :
    Rch W a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- One input-scanning step. -/
lemma step_x (s s' : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) (mvI : SignType)
    (h : ∀ w, tr s (inSym y ip.val) w = xAct 0 mvI 0 s') :
    rrun prog o (K s ip v q) 1 = K s' (moveInputPos ip mvI) v q := by
  rw [← xCfg_K s s ip ip v q q, rrun_one_x prog o _ s ip 0 q rfl]
  change (tr s (inSym y ip.val) _).apply _ = _
  rw [h, apply_xAct]
  simp only [SignType.coe_zero, add_zero]
  exact xCfg_K _ _ _ _ _ _ _

/-- The symbols of `⟨1ⁿ, w⟩`: `1` before position `2n`, `0` at `2n`. -/
lemma sym_lt {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) {k : ℕ}
    (hk : k < 2 * n) : y[k]? = some true := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- The separator `0` of `⟨1ⁿ, w⟩` sits at position `2n`. -/
lemma sym_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y[2 * n]? = some false := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_right (by simp)]
  simp

/-- The length of `⟨1ⁿ, w⟩` is `2n + 2 + |w|`. -/
lemma length_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y.length = 2 * n + 2 + w.length := by
  subst hy; simp [pairEncode_eq_dbl, dbl_replicate]; omega

/-- **The counting loop**: from `cnt` at input position `1` with counter `0`, the program
reaches `cnt` at position `1 + j` with counter `j`, for every `j ≤ 2n`.

**Proof sketch.** Induction on `j`: one `cnt` step reads a `1` and moves right, then the
increment fragment (`inc_run`) adds one to the counter; the register head stays within
`|bits (2n)|` since `j + 1 ≤ 2n` (`length_bits_mono`). -/
lemma count {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    ∀ j (hj : j ≤ 2 * n), Rch (Nat.bits (2 * n)).length
      (K (y := y) .cnt ⟨1, by have := length_eq hy; omega⟩ 0 0)
      (K (y := y) .cnt ⟨1 + j, by have := length_eq hy; omega⟩ j 0) := by
  have hl := length_eq hy
  intro j
  induction j with
  | zero => intro _; exact ⟨0, rfl, fun t ht => by omega⟩
  | succ j ih =>
    intro hj
    refine (ih (by omega)).trans ?_
    have h1 : rrun prog o (K .cnt ⟨1 + j, by omega⟩ j 0) 1 =
        K (y := y) .iC ⟨2 + j, by omega⟩ j 0 := by
      rw [step_x .cnt .iC _ j 0 1 (fun w => by
        simp only [tr, show 1 + j = j + 1 by omega, inSym_succ, sym_lt hy (by omega : j < 2 * n),
          ↓reduceIte])]
      congr 1; exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    obtain ⟨T, h2, hm2⟩ := inc_run prog o 0 .iC .iB .cnt (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (K (y := y) .iC ⟨2 + j, by omega⟩ j 0) j
    rw [regCfg_K, regCfg_K] at h2
    refine ⟨1 + T, ?_, fun t ht => ?_⟩
    · rw [rrun_add, h1, h2]; congr 1; exact Fin.ext (by simp; omega)
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        simp [rrun_zero, K]
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, h1]
        obtain ⟨s, f, q, hq, -, hq1, hq2⟩ := hm2 t' (by omega)
        rw [regCfg_K] at hq
        rw [hq]
        have := length_bits_mono (show j + 1 ≤ 2 * n by omega)
        simp only [regCfg, Function.update_self]
        omega

/-- The initial configuration. -/
lemma init_eq : (Cfg.init (k := 1) St.vU0 y) = K .vU0 ⟨1, by omega⟩ 0 0 := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext r z; simp [K, Nat.zero_bits]

/-- **The run on a well-formed input** `⟨1ⁿ, w⟩`: the program answers whether `w = bits (2n)`,
the register head staying in `[-1, |bits (2n)|]`.

**Proof sketch.** The format check (`valPlain_run`) returns to position `1`; the counting
loop (`count`) leaves `bits (2n)` in the register at the separator; the rewind
(`rewind_x`) and the comparison (`jeqPlain_run`) decide `w = bits (2n)`; one step answers. -/
lemma run_valid {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w)
    (hw : Canon w) :
    Rch (Nat.bits (2 * n)).length (K .vU0 ⟨1, by omega⟩ 0 0)
      (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
  have hl := length_eq hy
  set W := (Nat.bits (2 * n)).length
  -- the format check
  have h1 : Rch W (K .vU0 ⟨1, by omega⟩ 0 0) (K (y := y) .cnt ⟨1, by omega⟩ 0 0) := by
    obtain ⟨T, e, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0) (vU0 := .vU0)
      (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT) (rw₁ := .rw1)
      (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
      (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).1 ⟨n, w, hy, hw⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the count
  have h2 := count hy (2 * n) le_rfl
  -- the separator
  have h3 : Rch W (K (y := y) .cnt ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) := by
    refine ⟨1, ?_, fun t ht => ?_⟩
    · rw [step_x .cnt .sw1 _ _ 0 0 (fun _ => by
        simp only [tr, show 1 + 2 * n = 2 * n + 1 by omega, inSym_succ, sym_eq hy]; rfl)]
      rw [moveInputPos_zero]
    · obtain rfl : t = 0 := by omega
      simp [rrun_zero, K]
  -- the rewind
  have h4 : Rch W (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .jK ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := rewind_x prog o (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) 0 0
      .sw1 .sw2 .jK (fun _ _ => rfl) (fun a _ => by cases a <;> rfl) rfl rfl
      ⟨1 + 2 * n, by omega⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the comparison
  have h5 : Rch W (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0)
      (K (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := jeqPlain_run (P := prog) (oracle := o) (r := 0) (jK := .jK)
      (jK2 := .jK2) (jC := .jC) (jRB := St.jRB) (jI1 := St.jI1) (jI2 := St.jI2) (yes := .yes)
      (no := .no) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0) n w hy (2 * n) rfl
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, q, hs, -, hq1, hq2⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp only [K]; exact ⟨hq1, hq2⟩
  exact (((h1.trans h2).trans h3).trans h4).trans h5

/-- The answering step. -/
lemma ret_step (b : Bool) (ip : Fin (y.length + 2)) (v : ℕ) :
    (rrun prog o (K (if b then .yes else .no) ip v 0) 1).state = none ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).output = [b] ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).workTapePos 0 = 0 := by
  rw [rrun_one, rstep_noncall prog o _ _ rfl rfl]
  cases b <;> simp [MultiTapeTM.step, K, prog, tr, retAct, Action.apply]

/-- The trivial decider bank (no deciders are called). -/
def nilTM : MultiTapeTM 0 Bool Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩

end Dbl

open Dbl in
/-- **`dblLang` is in `L`**: the counting program decides it with one binary counter.

**Proof sketch.** On a well-formed input `⟨1ⁿ, w⟩` the run is `Dbl.run_valid` followed by the
answering step; on any other input the format check rejects (`valPlain_run`) with the
register untouched. The register head stays in `[-1, |bits |y||]`, so `compile_space` bounds
the space by `|bits |y|| + 2 ≤ 3 logSpace |y|` (there are no deciders). -/
theorem dblLang_mem : dblLang ∈ LOGSPACE := by
  refine ⟨3, compileFinTM prog .vU0 nilTM (fun _ => ()), fun y => ?_⟩
  set W := (Nat.bits y.length).length with hW
  have key : ∃ N, (rrun prog o (Cfg.init .vU0 y) N).state = none ∧
      (rrun prog o (Cfg.init .vU0 y) N).output =
        [MultiTapeTM.indicator (dblLang : Set (List Bool)) y] ∧
      ∀ t ≤ N, -1 ≤ (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ∧
        (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ≤ W := by
    rw [init_eq]
    by_cases hv : ValidPlain y
    · obtain ⟨n, w, hy, hw⟩ := hv
      have hl := length_eq hy
      obtain ⟨T, e, hm⟩ := run_valid hy hw
      obtain ⟨r1, r2, r3⟩ := ret_step (y := y) (decide (w = Nat.bits (2 * n))) ⟨1, by omega⟩
        (2 * n)
      have hW' : (Nat.bits (2 * n)).length ≤ W := length_bits_mono (by omega)
      have hind : MultiTapeTM.indicator (dblLang : Set (List Bool)) y =
          decide (w = Nat.bits (2 * n)) := by
        rw [indicator_eq_decide]
        refine decide_eq_decide.mpr ⟨fun ⟨n', h⟩ => ?_, fun h => ⟨n, by rw [hy, h]⟩⟩
        have := pairEncode_injective (a₁ := (List.replicate n true, w))
          (a₂ := (List.replicate n' true, Nat.bits (2 * n'))) (hy.symm.trans h)
        simp only [Prod.mk.injEq] at this
        obtain ⟨h1, h2⟩ := this
        have : n = n' := by simpa using congrArg List.length h1
        subst this; exact h2
      simp only [decide_eq_true_eq] at r1 r2 r3
      refine ⟨T + 1, ?_, ?_, fun t ht => ?_⟩
      · rw [rrun_add, e]; convert r1 using 4
      · rw [rrun_add, e, hind]; convert r2 using 4
      · rcases Nat.lt_or_ge t T with h | h
        · have := hm t h; omega
        · rcases Nat.lt_or_ge t (T + 1) with h' | h'
          · obtain rfl : t = T := by omega
            rw [e]; simp [K]
          · obtain rfl : t = T + 1 := by omega
            rw [rrun_add, e]
            have : (rrun prog o (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no)
                ⟨1, by omega⟩ (2 * n) 0) 1).workTapePos 0 = 0 := by
              convert r3 using 4
            rw [this]; omega
    · obtain ⟨T, e1, e2, e3, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0)
        (vU0 := .vU0) (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT)
        (rw₁ := .rw1) (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
        (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).2 hv
      rw [xCfg_K] at e1 e2 e3 hm
      have hn : MultiTapeTM.indicator (dblLang : Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        simp only [decide_eq_false_iff_not]
        rintro ⟨n, rfl⟩
        exact hv ⟨n, _, rfl, canon_bits _⟩
      refine ⟨T, e1, by rw [e2, hn]; rfl, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t T with h | h
      · obtain ⟨s, ip, hs, -⟩ := hm t h
        rw [xCfg_K] at hs
        rw [hs]; simp [K]
      · obtain rfl : t = T := by omega
        rw [e3]; simp [K]
  obtain ⟨N, h1, h2, hbox⟩ := key
  obtain ⟨T, hT, hsp⟩ := compile_space prog .vU0 nilTM (fun _ => ()) o (fun _ => -1)
    (fun _ => (W : ℤ)) 0 N _ h1 h2
    (fun t ht r => by rw [Fin.fin_one_eq_zero r]; exact hbox t ht)
    (fun t _ l cs _ hcs => by simp [prog] at hcs)
  refine ⟨T, hT, hsp.trans ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, zero_mul,
    add_zero]
  have e1 := length_bits_le_log y.length
  have : ((W : ℤ) - -1 + 1).toNat = W + 2 := by omega
  rw [this]
  simp only [logSpace]
  omega

end Complexity.LogProg
```

## ===== TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implicitly logspace computable functions are computable in logspace and in polynomial time

[AB09, Def 4.16 and p. 112]: an implicitly logspace computable function can be computed by a
machine with a write-once output tape in logarithmic space — for `i = 0, 1, 2, …` ask the
length language whether `i` is a position of `f(x)` and, if so, ask the bit language for
`f(x)ᵢ` and write it — and logspace computations run in polynomial time, so the function is
polynomial-time computable.

The enumeration is a register-tape program (`Complexity.LogProg.RProg`) with one register,
the binary counter `i`, calling the two deciders on the virtual input `⟨x, i⟩`; it is
compiled with `Complexity.LogProg.compile_space` against the decider bank
`Complexity.LogProg.bankTM`.

## Main results

* `Complexity.ImplicitlyLogspaceComputable.computesInSpace` — some machine computes `f` in
  space `O(log n)`. [AB09, Def 4.16; Exercise 4.8, one direction]
* `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` — `f` is polynomial-time
  computable. [AB09, p. 112: "logspace computations run in polynomial time"]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16; §6.2.1, p. 112.)
-/

namespace Complexity

open Turing LogProg

/-- Membership of a pair in an index language. -/
lemma pairEncode_mem_indexLang (p : List Bool → ℕ → Prop) (x : List Bool) (i : ℕ) :
    pairEncode x (Nat.bits i) ∈ indexLang p ↔ p x i := by
  constructor
  · rintro ⟨x', i', h, hp⟩
    have := pairEncode_injective (a₁ := (x, Nat.bits i)) (a₂ := (x', Nat.bits i')) h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, hb⟩ := this
    rw [bits_injective hb]; exact hp
  · intro h; exact ⟨x, i, rfl, h⟩

namespace ImplicitEnum

/-- The states of the enumeration program. -/
inductive St where
  | ask | bit | emitT | emitF | incC | incB | done
  deriving DecidableEq, Fintype

/-- The ordinary transitions: emit a bit, increment the counter, halt. -/
def tm : MultiTapeTM 1 Bool St where
  q₀ := .ask
  tr
    | .emitT, _, _ => ⟨0, fun _ => (none, 0), some true, some .incC⟩
    | .emitF, _, _ => ⟨0, fun _ => (none, 0), some false, some .incC⟩
    | .incC, _, w => incCAct 0 .incC .incB (w 0)
    | .incB, _, w => incBAct 0 .incB .ask (w 0)
    | _, _, _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The enumeration program**: at `ask`, ask decider `0` (the length language) about
`⟨x, i⟩`; at `bit`, ask decider `1` (the bit language); emit the answer; increment `i`. -/
def prog : RProg 1 2 St where
  tm := tm
  call
    | .ask => some ⟨0, .whole, [0], .bit, .done⟩
    | .bit => some ⟨1, .whole, [0], .emitT, .emitF⟩
    | _ => none

/-- The program configuration at the start of round `i`, having written `out`. -/
def cfg (x out : List Bool) (s : St) (i : ℕ) : Cfg 1 Bool St x :=
  ⟨some s, 1, fun _ => FinTM.bufferTape (Nat.bits i), fun _ => 0, out⟩

/-- The virtual input of both calls in round `i` is `⟨x, i⟩`. -/
lemma vword_call (x out : List Bool) (s : St) (i : ℕ) (dec : Fin 2) (yes no : St) :
    vword (callSegs ⟨dec, .whole, [0], yes, no⟩ x (regWords (cfg x out s i))) =
      pairEncode x (Nat.bits i) := by
  simp [callSegs, argSegs, regWords, cfg, tapeWord_bufferTape, vword, Mode.seg0, render,
    pairEncode_eq_dbl]

/-- The enumerator configuration `cfg x out s i` is in state `s`. -/
@[simp] lemma cfg_state (x out : List Bool) (s : St) (i : ℕ) : (cfg x out s i).state = some s :=
  rfl

/-- The call at `ask`. -/
lemma rstep_ask (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .ask i) =
      cfg x out (if o 0 (pairEncode x (Nat.bits i)) then .bit else .done) i := by
  have h := vword_call x out .ask i 0 .bit .done
  have hc : prog.call .ask = some ⟨0, .whole, [0], .bit, .done⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

/-- The call at `bit`. -/
lemma rstep_bit (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .bit i) =
      cfg x out (if o 1 (pairEncode x (Nat.bits i)) then .emitT else .emitF) i := by
  have h := vword_call x out .bit i 1 .emitT .emitF
  have hc : prog.call .bit = some ⟨1, .whole, [0], .emitT, .emitF⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

section Run

variable (f : List Bool → List Bool) (o : Fin 2 → List Bool → Bool)
  (ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length))
  (ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false)

/-- The configurations met along the run: a call configuration of some round, or an ordinary
configuration with the counter head in `[-1, W]`. -/
def Shape (x : List Bool) (F W : ℕ) (c : Cfg 1 Bool St x) : Prop :=
  (∃ out s i, i ≤ F ∧ (s = .ask ∨ s = .bit) ∧ c = cfg x out s i) ∨
  ((∀ l, c.state = some l → prog.call l = none) ∧ -1 ≤ c.workTapePos 0 ∧
    c.workTapePos 0 ≤ W)

/-- Writing the binary word of `n` on the counter of an enumerator configuration gives the
enumerator configuration with counter `n`. -/
lemma regCfg_cfg (x out : List Bool) (s s' : St) (i : ℕ) (n : ℕ) :
    regCfg (cfg x out s i) s' 0 (FinTM.bufferTape (Nat.bits n)) 0 = cfg x out s' n := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]

include ho0 ho1 in
/-- **One round**: from round `i < |f x|` with `f(x)₀ … f(x)ᵢ₋₁` written, the program
writes `f(x)ᵢ` and reaches round `i + 1`.

**Proof sketch.** The round asks the bit decider (a call on `⟨x, bits i⟩`), emits the answer
`f(x)ᵢ` (`rstep_bit`), then increments the counter `i` with the increment fragment (`inc_run`).
Every intermediate configuration has the counter in binary of length at most `W` and output a
prefix of `f x`, which is `Shape`. -/
lemma round (x : List Bool) (i : ℕ) (hi : i < (f x).length) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : (Nat.bits (i + 1)).length ≤ W) :
    ∃ T, rrun prog o (cfg x ((f x).take i) .ask i) T = cfg x ((f x).take (i + 1)) .ask (i + 1) ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x ((f x).take i) .ask i) t) := by
  set b := (f x)[i] with hb
  have h1 : rrun prog o (cfg x ((f x).take i) .ask i) 1 = cfg x ((f x).take i) .bit i := by
    rw [rrun_one, rstep_ask, ho0]
    simp [hi]
  have h2 : rrun prog o (cfg x ((f x).take i) .bit i) 1 =
      cfg x ((f x).take i) (if b then .emitT else .emitF) i := by
    rw [rrun_one, rstep_bit, ho1]
    simp [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have h3 : rrun prog o (cfg x ((f x).take i) (if b then .emitT else .emitF) i) 1 =
      cfg x ((f x).take (i + 1)) .incC i := by
    rw [rrun_one, rstep_noncall prog o _ (if b then .emitT else .emitF) rfl (by cases b <;> rfl)]
    unfold MultiTapeTM.step
    simp only [cfg]
    have ht : (f x).take (i + 1) = (f x).take i ++ [b] := by
      rw [hb, List.take_succ, List.getElem?_eq_getElem hi]; rfl
    rw [ht]
    cases b <;> (refine Cfg.ext rfl ?_ ?_ ?_ ?_) <;> simp [prog, tm, Action.apply]
  obtain ⟨T₄, h4, hm4⟩ := inc_run prog o 0 .incC .incB .ask (fun _ _ => rfl) (fun _ _ => rfl)
    rfl rfl (cfg x ((f x).take (i + 1)) .incC i) i
  rw [regCfg_cfg, regCfg_cfg] at h4
  refine ⟨1 + (1 + (1 + T₄)), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2, rrun_add, h3, h4]
  · rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .ask, i, by omega, Or.inl rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .bit, i, by omega, Or.inr rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h2]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      refine Or.inr ⟨fun l hl => ?_, by simp [rrun_zero, cfg], by simp [rrun_zero, cfg]⟩
      simp only [rrun_zero, cfg, Option.some.injEq] at hl
      subst hl; cases b <;> rfl
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h3]
    obtain ⟨s', f', q, hq, hs', hq1, hq2⟩ := hm4 t (by omega)
    rw [regCfg_cfg] at hq
    rw [hq]
    refine Or.inr ⟨fun l hl => ?_, ?_, ?_⟩
    · simp only [regCfg, Option.some.injEq] at hl
      subst hl; rcases hs' with rfl | rfl <;> rfl
    · simpa [regCfg] using hq1
    · simp only [regCfg, Function.update_self]; omega

include ho0 ho1 in
/-- All rounds: from the start the program reaches round `i ≤ |f x|`. -/
lemma rounds (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∀ i ≤ (f x).length, ∃ T, rrun prog o (cfg x [] .ask 0) T = cfg x ((f x).take i) .ask i ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x [] .ask 0) t) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨0, by simp [rrun_zero], fun t ht => absurd ht (by omega)⟩
  | succ i ih =>
    intro hi
    obtain ⟨T₁, h1, hm1⟩ := ih (by omega)
    obtain ⟨T₂, h2, hm2⟩ := round f o ho0 ho1 x i (by omega) F W hF (hW i (by omega))
    refine ⟨T₁ + T₂, by rw [rrun_add, h1, h2], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, h1]; exact hm2 t' (by omega)

include ho0 ho1 in
/-- **The whole run**: the program halts with output `f x`, every configuration before the
halt having the shape `Shape`.

**Proof sketch.** Induction on the number of rounds: `round` takes round `i` to round `i + 1`
for `i < |f x|`; at `i = |f x|` the length decider answers no and the program halts with output
`f x` and counter head home. The shape invariant is collected round by round. -/
lemma run (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∃ N, (rrun prog o (Cfg.init .ask x) N).state = none ∧
      (rrun prog o (Cfg.init .ask x) N).output = f x ∧
      (rrun prog o (Cfg.init .ask x) N).workTapePos 0 = 0 ∧
      ∀ t < N, Shape x F W (rrun prog o (Cfg.init .ask x) t) := by
  have hinit : (Cfg.init .ask x : Cfg 1 Bool St x) = cfg x [] .ask 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext r z; simp [cfg, Nat.zero_bits]
  rw [hinit]
  obtain ⟨T, h1, hm1⟩ := rounds f o ho0 ho1 x F W hF hW (f x).length le_rfl
  rw [List.take_length] at h1
  have h2 : rrun prog o (cfg x (f x) .ask (f x).length) 1 = cfg x (f x) .done (f x).length := by
    rw [rrun_one, rstep_ask, ho0]; simp
  have h3 : (rrun prog o (cfg x (f x) .done (f x).length) 1).state = none ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).output = f x ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).workTapePos 0 = 0 := by
    rw [rrun_one, rstep_noncall prog o _ .done rfl rfl]
    simp [MultiTapeTM.step, cfg, prog, tm, Action.apply]
  refine ⟨T + (1 + 1), ?_, ?_, ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.2
  · rcases Nat.lt_or_ge t T with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T + t' := ⟨t - T, by omega⟩
      rw [rrun_add, h1]
      rcases Nat.lt_or_ge t' 1 with h' | h'
      · obtain rfl : t' = 0 := by omega
        exact Or.inl ⟨_, .ask, _, hF, Or.inl rfl, rfl⟩
      · obtain rfl : t' = 1 := by omega
        rw [h2]
        refine Or.inr ⟨fun l hl => ?_, by simp [cfg], by simp [cfg]⟩
        simp only [cfg_state, Option.some.injEq] at hl
        subst hl; rfl

end Run

end ImplicitEnum

/-- **Implicitly logspace computable functions are computable in logspace** [AB09, Def 4.16;
one direction of Exercise 4.8]: some machine computes `f` visiting `O(log n)` work cells.

**Proof sketch.** The enumeration program `ImplicitEnum.prog` keeps `i` in binary on one
register and, for `i = 0, 1, …`, asks the length language and the bit language about `⟨x, i⟩`
and writes the answer (`ImplicitEnum.run`). `i ≤ |f(x)| ≤ C (n+1)^e`, so the counter has
`O(log n)` bits, and the deciders run on inputs of length `2n + 2 + O(log n)`, in space
`O(log n)`. `compile_space` turns the program into a machine computing `f` within the
register range plus `kD (2B + 1)` cells, which `log_poly_bound` shows to be `O(log n)`. -/
theorem ImplicitlyLogspaceComputable.computesInSpace {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesInSpace f fun n => c * logSpace n := by
  classical
  obtain ⟨⟨C, e, hlen⟩, ⟨c1, M1, hM1⟩, ⟨c0, M0, hM0⟩⟩ := hf
  let Ms : Fin 2 → FinTM Bool := fun j => if j = 0 then M0 else M1
  let A : Fin 2 → Language Bool := fun j => if j = 0 then
    indexLang (fun x i => i < (f x).length) else indexLang (fun x i => (f x).getD i false = true)
  let s : Fin 2 → ℕ → ℕ := fun j n => if j = 0 then c0 * logSpace n else c1 * logSpace n
  have hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simpa [Ms, A, s] using hM0
    · have hj1 : j = 1 := Fin.ext (by
        have := j.isLt; have : j.val ≠ 0 := fun h => hj (Fin.ext h); simp; omega)
      subst hj1; simpa [Ms, A, s] using hM1
  let o : Fin 2 → List Bool → Bool := fun j V => MultiTapeTM.indicator (A j : Set (List Bool)) V
  have ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length) := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => i < (f x).length) x i
    by_cases h : i < (f x).length <;>
      simp_all [o, A, MultiTapeTM.indicator]
  have ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => (f x).getD i false = true) x i
    cases h : (f x).getD i false <;> simp_all [o, A, MultiTapeTM.indicator]
  obtain ⟨K1, hK1⟩ := LogProg.log_poly_bound C e 1
  obtain ⟨K2, hK2⟩ := LogProg.log_poly_bound (C + 2) (e + 1) 2
  set kD := bankK Ms + bankK Ms with hkD
  refine ⟨compileFinTM ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms),
    K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1), fun x => ?_⟩
  set n := x.length with hn
  set F := C * (n + 1) ^ e with hFdef
  set W := Nat.log 2 (F + 1) + 1 with hWdef
  set B := (c0 + c1) * logSpace (2 * n + 2 + W) + 1 with hBdef
  have hF : (f x).length ≤ F := hlen x
  have hbitsW : ∀ i ≤ F + 1, (Nat.bits i).length ≤ W := fun i hi =>
    (LogProg.length_bits_le_log i).trans (by have := Nat.log_mono_right (b := 2) hi; omega)
  obtain ⟨N, hN1, hN2, hN3, hNs⟩ := ImplicitEnum.run f o ho0 ho1 x F W hF
    (fun i hi => hbitsW (i + 1) (by omega))
  have hbox : ∀ t ≤ N, ∀ r : Fin 1, (-1 : ℤ) ≤ (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ∧
      (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ≤ (W : ℤ) := by
    intro t ht r
    rw [Fin.fin_one_eq_zero r]
    rcases Nat.lt_or_ge t N with h | h
    · rcases hNs t h with ⟨out, s', i, -, -, hc⟩ | ⟨-, h1, h2⟩
      · rw [hc]; simp [ImplicitEnum.cfg]
      · exact ⟨h1, h2⟩
    · obtain rfl : t = N := by omega
      rw [hN3]; simp
  have hcalls : ∀ t < N, CallOK ImplicitEnum.prog (bankTM Ms) (bankStart Ms) o (fun _ => -1)
      (fun _ => (W : ℤ)) B (rrun ImplicitEnum.prog o (Cfg.init .ask x) t) := by
    intro t ht l cs hl hcs
    rcases hNs t ht with ⟨out, s', i, hi, hs', hc⟩ | ⟨hnc, -, -⟩
    · rw [hc] at hl ⊢
      simp only [ImplicitEnum.cfg_state, Option.some.injEq] at hl
      subst hl
      have hreg : regWords (ImplicitEnum.cfg x out s' i) = fun _ => Nat.bits i := by
        funext r; simp [regWords, ImplicitEnum.cfg, tapeWord_bufferTape]
      have hV : vword (callSegs cs x (regWords (ImplicitEnum.cfg x out s' i))) =
          pairEncode x (Nat.bits i) := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; exact ImplicitEnum.vword_call _ _ _ _ _ _ _)
      have hargs : cs.args = [0] := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; rfl)
      refine ⟨by rw [hargs]; simp, rfl, ?_, ?_⟩
      · intro r hr
        rw [hargs] at hr
        simp only [List.mem_singleton] at hr
        subst hr
        rw [hreg]
        refine ⟨rfl, rfl, le_rfl, ?_⟩
        beta_reduce
        exact_mod_cast hbitsW i (by omega)
      · rw [hV]
        refine (bank_cleanRun Ms A s hMs cs.dec _).mono ?_
        have hlenV : (pairEncode x (Nat.bits i)).length ≤ 2 * n + 2 + W := by
          have := hbitsW i (by omega)
          simp [pairEncode, hn]; omega
        have hsj : s cs.dec (pairEncode x (Nat.bits i)).length ≤
            (c0 + c1) * logSpace (2 * n + 2 + W) := by
          have hm := logSpace_mono hlenV
          simp only [s]
          split_ifs
          · exact (Nat.mul_le_mul_left c0 hm).trans (Nat.mul_le_mul_right _ (by omega))
          · exact (Nat.mul_le_mul_left c1 hm).trans (Nat.mul_le_mul_right _ (by omega))
        simp only [hBdef]
        omega
    · exact absurd hcs (by rw [hnc l hl]; simp)
  obtain ⟨T, hT, hTs⟩ := compile_space ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms) o
    (fun _ => -1) (fun _ => (W : ℤ)) B N (f x) hN1 hN2 hbox hcalls
  refine ⟨T, hT, hTs.trans ?_⟩
  -- the arithmetic
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  have hW2 : (((W : ℤ) - -1 + 1).toNat) = W + 2 := by omega
  rw [hW2]
  set L := logSpace n with hL
  have hL1 : 1 ≤ L := by simp [hL, logSpace]
  have hWL : W + 2 ≤ (K1 + 2) * L := by
    have := hK1 n
    simp only [hWdef, hFdef]
    have : (K1 + 2) * L = K1 * L + 2 * L := by ring
    simp only [logSpace] at hL
    rw [hL] at *
    omega
  have hlogW : logSpace (2 * n + 2 + W) ≤ K2 * L := by
    have hWle : W ≤ F + 2 := by
      have := Nat.log_le_self 2 (F + 1); omega
    have hle : 2 * n + 2 + W ≤ (C + 2) * (n + 1) ^ (e + 1) + 2 := by
      have h1 : n + 1 ≤ (n + 1) ^ (e + 1) := by
        calc n + 1 = (n + 1) ^ 1 := by ring
          _ ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : F ≤ C * (n + 1) ^ (e + 1) := Nat.mul_le_mul_left C h2
      have : (C + 2) * (n + 1) ^ (e + 1) = C * (n + 1) ^ (e + 1) + 2 * (n + 1) ^ (e + 1) := by
        ring
      omega
    have := hK2 n
    have hm := logSpace_mono hle
    simp only [logSpace] at hm this ⊢
    simp only [hL, logSpace]
    omega
  have hBL : 2 * B + 1 ≤ (2 * ((c0 + c1) * K2 + 1) + 1) * L := by
    have h1 : (c0 + c1) * logSpace (2 * n + 2 + W) ≤ (c0 + c1) * (K2 * L) :=
      Nat.mul_le_mul_left _ hlogW
    have e1 : (2 * ((c0 + c1) * K2 + 1) + 1) * L = 2 * ((c0 + c1) * (K2 * L)) + 3 * L := by ring
    rw [e1]
    simp only [hBdef]
    omega
  calc W + 2 + kD * (2 * B + 1) ≤ (K1 + 2) * L + kD * ((2 * ((c0 + c1) * K2 + 1) + 1) * L) :=
        Nat.add_le_add hWL (Nat.mul_le_mul_left _ hBL)
    _ = (K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1)) * L := by ring

/-- **Implicitly logspace computable functions are polynomial-time computable**
[AB09, p. 112: "logspace computations run in polynomial time"].

**Proof sketch.** `ImplicitlyLogspaceComputable.computesInSpace` gives a machine computing
`f` in logarithmic space; by configuration counting
(`Complexity.polyTimeComputable_of_computesInSpace`) it runs in polynomial time. -/
theorem ImplicitlyLogspaceComputable.polyTimeComputable {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : PolyTimeComputable f := by
  obtain ⟨M, c, hM⟩ := hf.computesInSpace
  exact polyTimeComputable_of_computesInSpace hM

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

* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.
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

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

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

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

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
