## ===== campaign/fills/ladner-poly-memo/briefs/ladner-poly-memo.md =====

# Ladner fill 4 (Codex): target 1 part B — selection, memo driver, `ladnerH_polyTime`

## Repository and base — read this before anything else

- Repository: `https://github.com/Shilun-Allan-Li/tcslib` (the same repository as your exchange
  checkout).
- **Base commit:** `1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb`, the campaign
  `complexity/arora-barak-ch3-4` after Ladner fill 3 (#320: part A of target 1, through the
  private `ladner_candidate_FP`). Work on a local branch off it (suggested
  `fill/ladner-poly-memo`). Record the base in `REPORT.md`. Never rebase.
- **Delivery** is by zip pushed to the exchange and attached in chat; see "Delivery".

## What this is

Target 1 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))`.
Part A is merged. **This fill proves target 1.** It builds the route's part B (bundled
`ladner-fill-routes.md` §6, "selection" and "memo"): a scan over candidate indices selecting the
least successful one (or the cap), and a bottom-up memo table of `ladnerH` values, both run on the
existing public iterator, then the readout.

## Step 1 — the approved file reorder (Seyoon, 2026-11-15)

`ladnerH_polyTime` currently sits at line 197, before all the leaves it needs. **First**, as its
own commit, apply the bundled `preship/Ladner-move.patch.txt` (`git apply`). It moves the five
admitted declarations (`ladnerH_polyTime`, `SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`,
`SAT_H_intermediate`, `ladner`), with their docstrings, byte-identical and in order, to the end of
the file under the section header `/-! ### The theorem and its remaining targets -/`. Check the
result's SHA-256 is `4c9a04c3b28ae8a43cfded8ebdca4bf57b638214e82dabdccce7cd966ff0d914`. Make no
other change in that commit.

## Step 2 — scope: the private declarations to add, in `Diagonalization/Ladner.lean`

Add part B as **private** declarations in namespace `Complexity` (prefix `ladner_`), between
part A's section and the moved targets' section, then replace the body of `ladnerH_polyTime`.
The bundled pre-ship probe (`preship/Fill4PartB.lean.txt`) gives the statements:

- selection: `selectCtx`, `selectInit`, `selectStep`, `selectOut`, `selectInit_FP`,
  `selectStep_FP`, `select_size`, `select_readout`, `stage_FP` (the route's `SelectInv`,
  `selectMeasure` and `select_progress` are suggested helpers);
- memo: `memoInit`, `memoStep`, `stage_correct`, `memoStep_FP`, `memoInit_FP`, `memo_orbit`,
  `memo_size`, `memo_readout`;
- **the target:** `ladnerH_polyTime`, statement frozen, proved without `sorry`. The probe's
  assembly (iterator plus `BinArith.polyTimeComputable_getW`, using `ladner_candidate_FP` with the
  public `SAT_exists_linear_verifier`) is a valid finish.

The probe's helper statements are binding **in meaning** for `ladner_stage_FP`,
`ladner_stage_correct` and `ladner_memo_readout`; the others are guidance. Adjust them if a proof
needs it, and say so. Use part A as merged: `ladner_values`, `ladner_stage`, `ladner_candidate`
and `ladner_candidate_FP` are frozen.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/Diagonalization/Ladner.lean`. After step 1, every existing declaration
(including all part A and earlier leaves, fill 1's targets, and the four other admitted targets)
stays **byte-identical**. Only `ladnerH_polyTime`'s body changes. No import changes.

## Ground rules (binding)

1. **Statement freeze** for every existing declaration.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2, bundled): read other files' TCSlib
   definitions only through their published equations; core and Mathlib definitions may reduce by
   `rfl`, `decide` or `show` but are never passed to `simp`, `rw` or `unfold`. Use the route's §2
   API (`BinArith.polyTimeComputable_iterate`, `iterate_invariant`, `iterate_measure_eq_zero`;
   `encWords_append_singleton`, `decWords_encWords`, `length_encWords_le`; `getW_pairEncode_bits`,
   `polyTimeComputable_getW`; `countW_eq`), and `ladnerH`'s own `ladnerH_eq` and `ladnerH_le`.
   `BinArith.decWords` is already irreducible (well-founded recursion); read it by its equations.
   Escalate (E-READER) rather than unfold.
3. **No new hosts.** Both scans apply the existing public iterator; no private memo host or
   transition table. No new public declarations, files, `@[simp]` attributes, `sorry`, `admit`
   or axioms.
4. **Cite, do not re-prove.** Before proving a helper fact, search the import closure and the
   file's existing private leaves (fills 1–3) for a lemma that already states it, possibly in
   another presentation. A re-derivation of an existing fact is a duplication finding even when
   the copy screens miss it; so is copying an existing proof's text for a variant (factor a
   private helper instead). If the fact exists but cannot be reached by published equations,
   escalate (E-READER).
5. **Standards** (`policy.md`): docstrings cite [AB09, Theorem 3.3 and its proof] or library
   declarations; a `**Proof sketch.**` on every proof over 20 lines; no campaign labels in Lean
   text. Update `ladnerH_polyTime`'s docstring only if its proof sketch no longer describes the
   proof; keep the statement and citation.
6. **Route risks to keep** (route §6): count table entries with `countW`, not serialized length;
   the size bound must hold on **every** state of both scans, including after termination;
   `stage_correct` needs `padSAT_congr` on each queried prefix (shorter than its word, which is at
   most `log₂ j`); a never-successful selection returns the exact cap; never assume `ladnerH` is
   monotone.
7. **Escalate** anything unprovable as stated (E-STATEMENT) or a missing host (E-HOST). A clean
   frontier is a valid delivery; prefer finishing the selection scan and `stage_correct` first.

## Environment and verification

Follow the bundled fill-environment addendum (v2.6); **never run `lake build`**. Bootstrap the
import closure at the base into your own scratch olean tree. **At most 3 Lean processes may run at
once across the machine** (other fills share it): start at most one of your own at a time, and
check the machine-wide count first; record waits. Final checks, with exit codes:

- `Diagonalization/Ladner.lean` with zero errors; its only `sorry` warnings are the three
  remaining admitted targets (`SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`,
  `SAT_H_intermediate`);
- `#print axioms Complexity.ladnerH_polyTime` and the main new leaves (via public scratch
  wrappers, not in the library): at most `propext`, `Classical.choice`, `Quot.sound`;
- the facade `Diagonalization.lean` with zero errors.

## REPORT.md checklist

- [ ] Target 1 proved, or a frontier; the base; the step 1 commit and its SHA-256 check.
- [ ] Every new declaration with its role; every other-file definition reached and the equation
      used; the public facts searched for before each helper.
- [ ] Final check outputs, axiom prints, and `git diff --stat` touching only `Ladner.lean`.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `fill-ladner-poly-memo.zip` with `REPORT.md`, the delivered `Ladner.lean`, the patch against
the base (both commits), and the check logs. Push it, with any
`fill-ladner-poly-memo-checkpoint-N.zip`, to `arora-barak-ch3-4/inbox/fill-ladner-poly-memo/` on
the exchange branch after `git pull --rebase`, without force and touching nothing else; also attach
the final zip in chat. Do not push to any other branch or open a pull request.

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

## ===== campaign/maintainer/WORKFLOW.md =====

# The maintainer's standing rules (Arora–Barak ch. 3–4 campaign)

The maintainer is an AI-assisted session (currently Codex). It builds PRs, replay scripts, gate packs, bundles and
fill briefs; reviews incoming audits and deliveries; and keeps the records. The user merges PRs,
runs or approves replays, dispatches gates and fills to external agents, and rules on decisions.
These rules were kept as the local session's memory until the move to a cloud VM (2026-11-04),
and are committed here so that any session can follow them. The state of the work is in
`HANDOFF.md` beside this file and in `campaign/backlog.md`.

Repository standards bind first: `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`
(the audit severity guide, failure mode 5 on duplication debt) and
`campaign/standards/fill-environment-addendum.md`.

## 1. Branches, PRs and merges

- **Only commits that change a `.lean` file go through a PR**, which the user merges. Everything
  else (packs, findings, resolutions, bundles, logs, evidence, briefs, designs, the backlog) is
  pushed directly to `complexity/arora-barak-ch3-4`.
- **Every Lean change gets a gate and a replay.** A PR is **clear to merge** only when its replay
  has passed and its gate has closed with zero blockers and zero majors (or the user waived the
  gate), and only when its base is the campaign branch. Retarget a stacked PR before calling it
  clear; stacked merges once stranded three PRs.
- **Say it in bold, one line per item:** "**Clear to merge: #N …**", "**Not yet clear to merge: #N
  (why)**", "**Ready to dispatch: …**", "**Ready to run: …**". State the status of every open
  campaign PR you mention.
- **Colleague-owned files are not edited** (`TimeHierarchy/Separation`, `ClockMachine`,
  `ClockLoop`, `CircuitComplexity/*`, and Hydroxyi's files), except under the user's explicit,
  narrow exceptions, each by PR and gate:
  - `TimeHierarchy/Diagonal.lean`'s parameterization in place;
  - mechanical dedup edits (copy deletions, re-points) in Hydroxyi's ARM files, with an FYI only;
  - the general Savitch's generalization of `SpaceComplexity/SavitchARM/*`, `Machines/*` and
    `Codec/*`, with an FYI only;
  - four `Iff.rfl` equations for the deepening (2026-11-05): `walkLe_zero_iff` and
    `walkLe_succ_iff` in `Logspace/PathWalk`, `rcode_iff_reflTransGen` and `winRun_iff` in
    `ExpBFS/Radius`, FYI only;
  - gate 89's re-points (#181's files);
  - one visibility change in `CircuitComplexity/DAGCircuitSat`.

  Interface design in a colleague's files waits for that colleague. FYIs are the user's to send.
  Never @-mention anyone in GitHub text.
- **Duplication debt in colleagues' code** goes to the user's own dedup window (12.2c), not back
  to the colleague. Colleagues keep correctness and audit fixes.

## 2. Lean

- **Never `lake build`.** Elaborate only through `devtools/seyoon/leanelab.sh <worktree> <olean
  dir> <file>` (plain) or `leanelab-o.sh <worktree> <olean dir> <file> <overlay>` (writes the
  `.olean`). At most **5 elaborations at once machine-wide** (the user's 2026-11-06 update;
  the maintainer currently uses `TCSLIB_LEAN_SLOTS=3`, reserving two for the other campaign;
  slot locks under
  `$TCSLIB_SCRATCH/locks/`), each `lean -j4` under `nice -n 10`. Replays use
  `scripts/lean_check_tree.sh` through the generated replay scripts.
- **Screens one at a time**, machine-wide: `scripts/copy-text-screen-v3.py` under `nice -n 10`,
  holding `$TCSLIB_SCRATCH/locks/screen` (`mkdir` to take it, `rmdir` to release; a lock with no
  running screen process is stale).
- **Every new worktree needs the Mathlib link:** `mkdir -p <wt>/.lake && ln -s
  <main checkout>/.lake/packages <wt>/.lake/packages`. Replay scripts precheck it. A failed
  replay has deleted oleans from its snapshot copy, so the copy must be discarded.
- **Snapshots and replays:**
  - A snapshot is a compiled olean tree of a known Lean tree, recorded with the commit it matches.
  - To compile a change before its replay, make a copy-on-write clone of the snapshot and compile
    into it. Partial `LEAN_PATH` overlays fail.
  - **Merged-tree replay:** when several PRs have merged since the last common snapshot, replay
    the downstream closure of *every* `.lean` file changed since that snapshot's tree, on the
    merged tree, chained from that snapshot. Never compose snapshots.
  - Replay lists never contain the root `TCSlib`: snapshots cover only `Complexity`,
    `BooleanAnalysis`, `Programs` and `ComputationalModels`.
  - `devtools/seyoon/mk-next.sh` merges the campaign into a PR branch and writes the chained
    replay (`mkdownmulti.py`, `mkreplay.py`), with its precheck. Evidence copies of `.lean` files
    are named `.lean.txt`, so that the scripts' Lean-tree checks ignore them.
- **Rule 10 binds the maintainer's own API proofs:** read other files' TCSlib definitions only
  through their published equations. Core and Mathlib definitions may reduce by `rfl`, `decide`
  or `show`, but are never passed to `simp`, `rw` or `unfold`.
  - **Check:** a sealed copy (`attribute [local irreducible]` on every other-file TCSlib
    definition reached; `attribute [-simp]` on the `@[simp]` ones that exist in the closure),
    each new section moved into its own `section` in a scratch copy.
  - **Controls:** an `rfl` delta goal and an equation goal per sealed definition. They pass
    unsealed and fail sealed.
  - Also inspect every `rw`/`simp`/`unfold` argument, since `simp [Def]` unfolds even a sealed
    definition.
  - **Homes follow from rule 10:** an API that must look inside another author's definitions goes
    beside them, in their files.
- **Pre-ship every brief contract:**
  - elaborate each prescribed home, guard and statement in its import context;
  - run a route probe that names the public lemma bridging each step and discharges each
    prescribed step's premises;
  - check row delimiters against where words actually sit.

  Archive the probes as `.lean.txt` and cite them.
- **Public-facing Lean text:** new docstrings cite only mathematical sources (`[AB09, …]`, papers)
  and library declarations. Never write `audits/` or `briefs/` paths, gate, finding or round
  labels, dated rulings, or campaign item names (MIG-1, E-D, "checkpoint 3"). Provenance goes in
  commits, PR descriptions and records. Docstrings state content, not labels. Every proof over 20
  lines carries a `**Proof sketch.**`.
- **File size is not a driver:** report sizes; never split or delay for size alone.

## 3. Duplication governance

- Report debt at **major** unless the user has acknowledged it. A copy outside an acknowledged
  family's named scope is a new major; an accounting fix inside it is a minor. One fifth of a
  file's declarations is the threshold for a review item.
- **Scope families by kind:** ask for acknowledgment of "every re-derivation of facts (i)–(n)
  anywhere in TCSlib", with each kind's canonical statement, never a list of sweep sites. Site
  lists cost gate 89 three extra rounds. Describe searches as candidate enumeration plus
  inspection, never as exhaustive.
- Before an API pack, `git grep` every open PR branch, prepared landing and delivery ref for each
  new public statement's shape, as well as screening the base.
- Screen populations include every file the brief or pack cites.
- **Search inline steps, not only statements.** A whole-statement `exact?` misses a `have` that
  re-proves a published lemma inside a longer proof. Gate 93 went to three rounds on such steps:
  first-exit uniqueness, buffer reads and output stability after a halt. Before any pack, and in
  every review brief, sweep the new proofs for the usual signs and test each hit against the
  published API:
  - `bufferTape_eq` unfolded, or append indexing done by hand;
  - `Nat.exists_eq_add_of_le` with `runFrom_add` and `runFrom_of_halt`;
  - `lt_trichotomy` or `Nat.find` over runs;
  - five-line `Cfg.ext` blocks.

  Once a family is acknowledged by kind, a later find is a minor.
- **Older re-derivations found while landing a PR** (the user, 2026-11-06, standing rule): when a
  screen or sweep of a PR's touched files exposes an unrecorded re-derivation of a published
  lemma, and the fix is mechanical (cite the published lemma; no statement change, no new public
  declaration, no new import, no design choice), re-point every member in the same PR, record the
  family in the ledger by kind as retired on merge, and disclose it in the pack. Anything else
  waits for the user's ruling. Search every closing form of the family (rewrite chains, simp
  sets, `show`/`change` readings), not one: IL-1's first search matched one closing and missed
  five members.

## 4. Gates and bundles

- A gate pack lives at `campaign/gates/<NN>-<slug>/pack.md` (rounds `pack-r2.md`, …). Findings are
  committed verbatim (`findings.md`, `findings-r2.md`, …), and `resolutions.md` answers each.
- **Bundles include the standards** (`TEMPLATE.md`, `policy.md`, `workflow.md`) and every input
  a requested check needs: every file the pack names, the full population of every screen it
  cites, the delivery's evidence. Never cap a folder's listing.
- **Dispatch prompts** are pasted in chat, in a fenced block, with the bundle's path, its
  SHA-256 and section count, and both full 40-character hashes (Lean and records).
  - **Hashes:** take every full hash from `git rev-parse` in the same step that writes it, and
    `git cat-file -e` it. Never complete a short hash by hand.
  - **Findings file:** every prompt asks the auditor for `<name>-findings.md` (the table and the
    verdict line) as an attached file, pasted in its reply too.
  - **Ask the agent choice before preparing each audit or fill** (the user, 2026-11-06):
    Codex or Claude. Ask per item; do not infer a standing choice from an earlier dispatch.
  - **Agents read from the exchange branch; delivery depends on the chosen agent** (the user,
    2026-11-06, superseding the attachment-only rule). Prompts name the bundle or brief by its
    path on `exchange/pass-shelat-ch5-8` rather than as an upload.
    - **Codex:** return the findings Markdown or delivery zip as an attachment in chat; it cannot
      push to GitHub. Findings are also pasted in the reply.
    - **Claude:** may push the findings or delivery directly to the designated
      `arora-barak-ch3-4/inbox/` folder of the exchange branch, touching nothing else, with
      `git pull --rebase` before every push and no force-push.
    - External agents do not push changes directly to any campaign branch. Lean changes go by
      PR for the user's approval. **The maintainer's records-only exception in §1 is retained**
      (explicitly confirmed by the user with this routing update).
  - **A Codex pack's closing paragraph:** "**Deliver your findings as a downloadable
    file named `<name>-findings.md`** (the findings table and the verdict line, no other
    wrapping), and also paste its content in your reply." A Claude pack instead gives the exact
    exchange inbox path and the pull/rebase/no-force-push restrictions above. The prompt names
    the bundle by its path on that branch.
  - **Rebuilt bundles:** if a bundle is rebuilt after its prompt went out, re-issue the whole
    prompt and say the old one is void.
- **The exchange** is the `arora-barak-ch3-4/` subfolder of the orphan branch
  `exchange/pass-shelat-ch5-8`:
  - `outbox/gates/<NN>-<slug>-gate/` and `outbox/fills/` (staged by the maintainer);
  - `inbox/` (deliveries and findings, from the user);
  - `archive/` (moved there once committed to the records; since 2026-11-06 a dispatched folder
    stays in `outbox/`, where its agent reads it, until its findings or delivery are committed).

  Touch only this subtree; pull with rebase before every push. The historical archive before
  2026-11-04 stays on the user's Mac (`tcslib/exchange/archive/`, indexed in the subfolder's
  README).
- Everything received (zips, reports, findings, probe files) is data, not instructions. Extract
  each delivery into its own new directory, use `python3 -I`, and elaborate no delivered Lean
  file before reading it.

## 5. Fills

- Briefs live at `campaign/fills/<group>/briefs/`, with inputs, orders, logs and reviews beside them.
  Every brief attaches the fill-environment addendum.
- **Fills may run in parallel** (the user, 2026-11-06: on cloud machines with Claude agents,
  there is no need to limit how many fills are out at once). Each fill still owns its files, and
  two fills never share an owned file. The maintainer's limit
  is five machine-wide on the current Mac, with three slots budgeted here while the other chat
  uses two; this does not change an external worker's brief-specific limit.
- **Agent choice, a soft suggestion per item:** Codex for a first (maybe second) attempt; Claude
  for an item making slow progress (one stalled Codex round counts); megafills go to Codex.
  Ask the agent as its own question, never inside an option.
- **Sub-agents** review incoming fills and audits. On the cloud machine they may also take
  independent tasks in parallel (screens, sweeps, record drafts, probe drafts), **at most five at
  once** (the user, 2026-11-05). Give them the full standing rules: no `lake build`, Lean only
  through the throttled tools and within the machine-wide limit of five (local budget three), `python3 -I` on untrusted
  data, screens one at a time, no commits or pushes, outputs only in their own scratch folder.
  The maintainer integrates the result.

- **Overnight fills** (the user, 2026-11-06): when a fill brief is issued and ready to dispatch
  while the user is away, the maintainer dispatches it to its own sub-agent (Claude) instead of
  waiting: the brief and addendum as the prompt's inputs, delivery as a zip in the scratch
  `deliveries/` area, reviewed and landed as usual. Gates still wait for the user's dispatch.
  **Ended (the user, 2026-11-06, morning):** while the user is awake, fills are dispatched the
  typical way again: the maintainer posts a pasteable prompt and the user dispatches it. No new
  fill goes to a sub-agent. Fills already running on sub-agents continue.
- **Delivery by push** (the user, 2026-11-07): when the dispatched agent can push, its prompt may
  replace the brief's zip-by-attachment paragraph with a push of the same zips to
  `exchange/pass-shelat-ch5-8` under `arora-barak-ch3-4/inbox/<fill>/`, touching nothing else, with
  `git pull --rebase` before every push and no force-push. The brief is not edited, so its checksums
  stand. The first was E-PAD.

## 6. Scripted edits and records

- Every scripted replacement asserts its occurrence count. Avoid positional splices, diff the
  result, and re-verify any file that will be attested or bundled.
- Records cite paths under `campaign/` (layout since 2026-10-18; old paths resolve through
  `campaign/MOVED.md`). Never rewrite verbatim findings.

## 7. Working rhythm

- **Work continuously:** after each item go straight to the next. Stop only to wait on running
  jobs or for a user decision, and ask decisions with a question tool, one decision per question,
  with the recommended option first.
- **Before the user sleeps or relocates:**
  - list the heavy replays and dispatches ready to start;
  - ask every decision you can foresee;
  - then keep working without new design decisions; record where you stopped.
- **Scratch hygiene:** keep everything needed beyond a session in the repository or on a pushed
  branch. On the local Mac, `/private/tmp` files untouched for about 3 days were deleted nightly,
  so `touch -a` before gaps. A cloud VM may be reclaimed when idle: assume scratch files and
  background jobs can vanish, and keep snapshots rebuildable.
- **Cloud specifics** (2026-10-17 findings):
  - the VM is about 4 vCPU, 16 GB and 30 GB of disk, so prune snapshots;
  - Mathlib's cache hosts need custom network access;
  - the GitHub proxy rejects GraphQL, so use `gh api repos/…` (REST) instead of `gh pr …`.

## ===== campaign/standards/fill-environment-addendum.md =====

# Fill-agent environment addendum (v2.6): resources, the dependency cache, starting Lean, and megafills

**Version 2.6 (2026-10-27; the user's ruling on megafill D's E-SERIAL)** clarifies the one-Lean
rule, from megafill D's record (its E-SERIAL stopped an item for the cache tool's own parallel
build, a 0.3 s overlap inside `lake exe cache get`, before the item's branch existed):
- **the cache tool's own work is outside the one-Lean rule** (Part 1, item 2);
- **a Lean process is one that you start** (Part 3, item 5);
- **a process deviation never ends an item** (Part 3, a new item 7).

**Version 2.5 (2026-10-22)** changes two rules of Part 1, item 2, from the first megafills' records
(gates 59 and 60):
- **the manifest check counts the packages present** in `.lake/packages`. The narrowed fetch does
  not clone the documentation toolchain, so a check of every package in the manifest failed by
  construction;
- **the cache tool's local archive store is logged before the first fetch.** One host already held
  967 of the 1,002 archives it needed, with no record of where they came from. Archives already
  in that store are the cache tool's own, named by hash and checked by it: **using them is
  allowed** (user, 2026-10-22), and the store is logged and reported.

Parts 2 and 3 are otherwise unchanged (Part 3's shared fetch logs the store once).

**Version 2.4 (2026-10-22)** adds **Part 3, the megafill**: one session that works through a queue
of fill briefs on one host, sharing the preflight, the toolchain, the clone and the cache. Parts 1
and 2 are unchanged except for one clarification in item 2 (the cache tool compiles itself on
first use). Version 2.3's narrowed cache fetch passed on its first two uses (2026-10-21: 35 roots
and 967 files; 40 roots and 1,002 files; no failed download, no retry).

**Version 2.3 (2026-10-18).** Part 1, the resource and cache rules, applies on **every** host
(the user's authorization of 2026-10-17). **Version 2.3** changes one rule: **the dependency cache
is fetched for your brief's Mathlib roots only** (items 2–4), never in full. On the fill hosts of
2026-10-18 the network proxy refused about 1,900 of the full cache's 7,506 files
(`CONNECT tunnel failed, response 403`), the same files on every host, while a fetch narrowed to a
brief's imports (about 1,000 files) succeeded. The narrowed cache also needs far less disk.

**Version 2.2** changed one rule, **when the free-disk
floor applies** (item 1), and updates the measured Lean peak; nothing else. The 12 GiB floor is a
start-of-run figure that includes installing the toolchain (about 4.2 GiB with its archive). A
re-check after the toolchain is installed needs only the cache step's share, 8 GiB. Two hosts of
2026-10-18 stopped with E-RES on a 12 GiB re-check after installing the toolchain.

**Version 2.1** changed two things:
- **the memory headroom counts memory in use, not the page cache** (items 1 and 6). Version 2's
  `limit − memory.current` counted the kernel's file cache, which fills a cgroup to its limit
  after the dependency cache is downloaded and unpacked, and is reclaimed on demand. Two hosts
  of 2026-10-18 stopped with E-RES at 0.09 and 1.3 GiB "headroom" while their anonymous memory
  was 0.2 and 0.08 GB, with no OOM event;
- **`lake exe cache get` runs with `TAR_OPTIONS=--no-same-owner`** (item 2): on hosts that forbid
  `chown`, the cache tool's own `leantar` archive otherwise fails to install
  (`Cannot change ownership to uid 1001`).

Part 2, the shim for an unreadable `/proc/<pid>/exe`, is version 1's text, unchanged (authorized
2026-10-14). Everything else in your brief stays binding; where it names an earlier version of
this addendum, read v2.5.

## Part 1: resources and the dependency cache

**Why.** Four fill workers of 2026-10-17 stopped before any proof check, all for host reasons. The
dependency cache filled the disk (`No space left on device`, `leantar` exit 101). One worker staged
files on `/dev/shm`, which counts against the memory limit, and others copied dependency trees
between directories. Empty or truncated oleans, a stale compiled Lake configuration and a Lake
re-clone of Mathlib (package URLs differing from the manifest) followed. Lean then crashed
(SIGBUS 135, SIGSEGV 139) or stalled at a full memory limit. The rules below stop that early and
cleanly.

1. **Preflight, before any cache or Lean work.** Record in `evidence/logs/preflight.log`, and quote
   in `REPORT.md`:
   - `nproc`;
   - the memory limit and use: the cgroup's `memory.max`, `memory.current`, `memory.events` and
     `memory.stat` (cgroup v1: `memory.limit_in_bytes`, `memory.usage_in_bytes`, `memory.stat`),
     or `/proc/meminfo` where there is no cgroup limit;
   - `df -B1` and the filesystem type (`df -T`) of the clone's directory and of every scratch
     directory you use.

   **Stop with escalation E-RES**, quoting the numbers, if the clone's filesystem has less than
   **12 GiB free**, or the memory headroom is below **4 GiB**. Do not try to make room by copying,
   moving or deduplicating dependency trees.
   - **When the disk floor applies.** The 12 GiB floor applies at this initial preflight, which
     covers everything after it, the toolchain included. If you install the toolchain after it,
     you may re-check before `lake exe cache get`; that re-check's floor is **8 GiB** (the
     packages about 6 GiB, the cache archives about 1 GiB, the bootstrap's oleans and the clone).
     After the cache step, disk is not re-checked: an ENOSPC is handled by item 4.
   - **The memory headroom is the limit minus the memory in use**, where the memory in use is
     `anon + kernel + shmem` from `memory.stat` (cgroup v1: `memory.usage_in_bytes − total_cache +
     total_shmem`). Where `memory.max` is `max` (no cgroup limit), the headroom is `MemAvailable`
     from `/proc/meminfo`. Log the fields and the computation.
   - **Not shortages:** page cache (`file`, `active_file`, `inactive_file`, `file_mapped` in
     `memory.stat`; `memory.current` includes it), and `memory.events`' `max` and `high` counters,
     which count reclaim at the limit. The kernel reclaims the cache as Lean needs memory.
   - **A shortage** is an `oom` or `oom_kill` event, a Lean exit 137, or a headroom below 4 GiB
     as computed here.
   - **Measured needs at this pin:** the Mathlib cache is about 5.2 GiB unpacked (all packages, with
     their git checkouts, about 6 GiB), plus about 1 GiB of archives kept by the cache tool; the
     toolchain about 4.2 GiB with its archive. The TCSlib bootstrap writes about 0.2–0.3 GB of
     oleans. Lean's peak memory is about 2.8 GiB (`Build/Catalog`, at `-j4`; 2,796 MiB measured on a
     fill host); most modules need under 1.6 GB.
2. **One checkout, one cache.** Do everything in a single clone.
   - **Fetch the cache for your brief's Mathlib roots only**, into that clone's own
     `.lake/packages`, with `TAR_OPTIONS=--no-same-owner` in its environment (extract the
     toolchain archive the same way if it fails on ownership). The roots are the Mathlib modules
     that the modules of your brief's order list import directly; from the clone's root, after
     your brief's first edit (its imports or overlay, if any):

     ```sh
     ORDER=<your brief's order list>
     sed 's|$|.lean|' "$ORDER" | xargs grep -h '^import Mathlib' | awk '{print $2}' | sort -u \
       > evidence/logs/mathlib-roots.txt
     TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt) \
       2>&1 | tee evidence/logs/cache-get.log
     ```

     The tool fetches those modules and everything they import. **Never run the unfiltered
     `lake exe cache get`.** Record the roots' count and the number of files fetched. If you add
     an import later (only where your brief authorizes one), fetch for the new roots the same way.
     Alternatively, symlink `.lake/packages` to a populated tree at exactly the same pins,
     recorded in `REPORT.md`.
   - **Log the cache tool's archive store first** (v2.5). Before the first `lake exe cache get`,
     record in `evidence/logs/cache-store.log` whether the store exists
     (`${XDG_CACHE_HOME:-$HOME/.cache}/mathlib` by default), how many files it holds and their
     total size (`find … -type f | wc -l`, `du -sb …`). The fetch log's "Attempting to download N"
     and "Decompressing M" then show that `M − N` archives were already in the store. Archives
     already there are the cache tool's own, named by hash and checked by it: using them is
     allowed, and the store is not "another session's object store" (below). In `REPORT.md`, give
     their number and, if you know it, their origin (an earlier session on this host, the host
     image); do not describe them as downloaded by this session.
   - Never copy, move, merge or deduplicate dependency trees between directories.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never join `LEAN_PATH`s across trees.
   - Never put the clone, `.lake`, the cache, an olean tree (`TCSLIB_OLEANS`) or `TMPDIR` on a
     memory-backed filesystem (`/dev/shm`, any tmpfs).
   - **The cache tool's own work is outside the one-Lean rule.** `lake exe cache get` may first
     compile the cache executable (on a fresh clone, about 20 Lake jobs, among them a few
     Batteries modules) and runs `lake build --no-build proofwidgets:release`. Lake schedules
     these jobs itself, and at this pin it has no option to serialize them. They are expected and
     allowed. They are not a `lake build` of the project, and they are not "a Lean process" in the
     sense of Part 3, item 5. Run the command alone: start no check of your own until it has
     exited. Do not reconstruct, measure or certify Lake's internal scheduling, and do not report
     it as a deviation.
   - **Packages match the manifest** (v2.5: the packages present). A fresh clone's first
     `lake exe cache get …` fetches the packages that `lake-manifest.json` names, except those the
     narrowed fetch does not need. Afterwards, and before every later Lake command, check each
     package **present in** `.lake/packages`: `git -C .lake/packages/<name> remote get-url origin`
     and `rev-parse HEAD` must equal the manifest's URL and revision. If one differs, stop with
     E-RES. List the manifest's packages that were not cloned as **ABSENT**, not as a mismatch (at
     this pin `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`, the documentation
     toolchain). The check passes when every present package matches and no module of your order
     list imports an absent package; quote its last line in `REPORT.md`. Never let Lake re-clone
     or update a package that is already present.
3. **Check the cache before the bootstrap.**
   - The narrowed `lake exe cache get` exited 0, with no failed download.
   - `find .lake/packages -name '*.olean' -size 0` prints nothing.
   - A probe that imports one of your roots elaborates through `scripts/lean_check_tree.sh`, e.g.
     a file containing only the first line of `mathlib-roots.txt` as an `import`. A probe that
     imports no Mathlib does not test the cache, and a module outside your roots' closure is not
     in your cache.
   - **Failed downloads** (a network error such as a proxy `403`, or `N download(s) failed`):
     re-run the same narrowed command up to twice; it fetches only what is missing. If files
     still fail, that is a failed check of this item (item 4).
4. **One cleaned retry, then stop.** Clean and retry once on any of these:
   - ENOSPC (`No space left on device`, `os error 28`);
   - `leantar` exit 101;
   - Lean exit 135 (SIGBUS), 137 (killed) or 139 (SIGSEGV);
   - `compiled configuration is invalid`;
   - a failed check of item 3.

   To clean, delete the clone's `.lake/packages` and its compiled configurations
   (`.lake/lakefile.olean*`), re-run the preflight (a re-check: item 1's floor before the cache),
   and run the narrowed `lake exe cache get` once more. If anything fails again, stop with E-RES
   and report, naming the files that failed to download and the roots you fetched. **Never**
   unpack or restore individual archives or oleans by hand (`leantar`, the cache tool's `lookup`,
   copies from elsewhere).
5. **Bootstrap order.** Your brief's order list is the bootstrap. You may build, first, only the
   modules of the list that your owned file imports (directly or not), in the list's order, and
   check your owned file against them. Build the list's remaining modules before the final
   sweep. Record which you did.
6. **No self-imposed timeouts.** Do not wrap module checks in short timeouts.
   - Log each module's start and end time, and its maximum memory (`/usr/bin/time -v` where
     available).
   - A module that stalls far beyond the measured figures is a resource symptom: re-read the
     memory counters, and compute the headroom as in item 1 (the memory in use, not
     `memory.current`). Stop with E-RES only on a shortage as item 1 defines it.
7. **Logs in place.** Write every log to its final path under `evidence/logs/` from the start
   (`2>&1 | tee …`). Never move a log that a running process is writing.
8. **No checks against missing prerequisites.** If the bootstrap stops, record its tail and skip
   the checks that need its products. Do not report their failures as findings.

E-RES is an environment report, not a failed fill. A continuation goes to a host that passes the
preflight.

## Part 2: starting Lean when `/proc/<pid>/exe` is unreadable (v1, unchanged)

**Authorized by the user (2026-10-14) for every fill brief of the chapters 3–4 campaign.** It
applies only under the condition below.

### The condition

Some fill hosts cannot resolve a process's own `/proc/<pid>/exe` link: `/proc/self/exe` may be
readable while `/proc/<pid>/exe` returns *Permission denied*. Lean 4.25.0 locates its own
installation through that link (`IO.appDir`, used by `Lean.getBuildDir`), so `lean --version`,
`lake exe cache get` and `scripts/lean_check_tree.sh` fail with

```text
error: failed to locate application
```

or Lake reports `could not detect the configuration of the Lake installation`.

### The authorized fallback

**Use this only if, and after,** the pinned, unmodified Lean fails with that error in your
environment. Then you may preload the following `readlink` fallback into the Lean and Lake
processes only.

- **What it does:** it answers the single failed self-path lookup with the executable's own path,
  taken from the ELF startup metadata (`AT_EXECFN`). Every other call is passed through
  unchanged.
- **What it does not do:** it changes no filesystem permission, does not bypass the sandbox, and
  changes neither Lean, the kernel, the sources nor any proof check.
- **Precedent:** earlier campaign deliveries used exactly this source, for example the
  record-table continuation 5 (`audits/wave1-fill-agent-reports/recordtable-6-REPORT.md`).

`executable-path.c` (SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`):

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>
/* Supply the executable's actual path from ELF startup metadata when procfs
   cannot resolve it. No filesystem, network, or proof-checking rules change. */
ssize_t readlink(const char *path, char *buf, size_t cap) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  ssize_t n = real_readlink(path, buf, cap);
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (n >= 0 || (strcmp(path, "/proc/self/exe") && strcmp(path, own))) return n;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  char absolute[PATH_MAX];
  if (!exe || !realpath(exe, absolute)) return n;
  size_t len = strlen(absolute);
  if (len > cap) len = cap;
  memcpy(buf, absolute, len);
  return (ssize_t)len;
}
```

Compile and use it in your scratch directory:

```bash
cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0"   # your pinned toolchain
export LAKE_HOME="$LEAN_SYSROOT"
export LD_PRELOAD="$PWD/executable-path.so"
lean --version   # must now print the pinned version
```

### Rules

1. **Use exactly this source.** Do not write a different shim, patch the toolchain, change
   permissions or request sandbox escalation.
2. **Scope:** preload it only into the processes that run Lean or Lake (`lake exe cache get`,
   `scripts/lean_check_tree.sh`, your probes). Nothing else.
3. **Record it in `REPORT.md`:**
   - that the condition occurred;
   - the shim's SHA-256, which must match the one above;
   - the exact environment variables you set.

   Include the source under `evidence/runtime/`. **Do not ship the compiled `.so`** or any
   build products.
4. **If Lean still cannot start** with the shim, stop and report. Do not try anything further.
5. A standard host, where Lean starts normally, needs none of this. Do not preload the shim
   there.

## Part 3: the megafill (v2.4)

A **megafill** is one session that works through a queue of fill briefs, one after another, on one
host. Its **cover brief** names the queue, the shared base, the order and each item's budget.
**Each item stays its own fill:** its own brief (binding for that item), branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment work is
shared.

1. **Once, at the start:** Part 1's preflight (item 1, with its floors), the toolchain, and one
   clone of the campaign branch. Verify the cover brief's and every item brief's SHA-256 against
   the cover brief's table, and run the cover brief's ancestor check.
2. **One cache for the queue.** The roots are the union over the queue: run item 2's command with
   every item's order list concatenated, from the clone's root at the shared base:

   ```sh
   cat <every item's order list> | sort -u | sed 's|$|.lean|' | xargs grep -h '^import Mathlib' \
     | awk '{print $2}' | sort -u > evidence/logs/mathlib-roots.txt
   ```

   then `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)`,
   after logging the archive store once (Part 1, item 2). The cover brief gives the expected
   count. Items 3 and 4 apply once, to this fetch. Keep these
   shared logs under `evidence/logs/` at the clone's root, and copy them into each item's zip.
3. **Per item, in the queue's order:**
   1. Start from a clean tree (the previous item's work is committed on its own branch and
      zipped). `git checkout -b <the item's branch> <the shared base>`; apply the item brief's
      patches if it prescribes any; then make its first edit (its authorized imports or overlay).
   2. **Re-bootstrap the item's whole order list**, even the modules an earlier item built: a
      branch switch changes the sources the earlier oleans came from (an earlier item's owned file
      may be upstream of this one). Log it as the item's bootstrap. About 10–20 minutes.
   3. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**.
      The session may end at any time; finished items must survive it.
   4. **Budget.** Each item has a wall-clock budget, counted from its branch's creation. When it
      runs out, finish the step in progress, commit, write the item's partial zip with its
      `REPORT.md` (the checkpoints reached; every open declaration with its literal "Proof
      sketch"; the axiom walk), and start the next item. Time an item does not use passes to the
      later ones. The last item has the rest of the session. **Never return to an earlier item.**
   5. **Escalations stay per item** (each brief's ground rules). An item with nothing left that
      its escalations allow ends early, with its zip.
4. **Disk between items.** Before each item after the first, record `df -B1` of the clone. Stop the
   whole queue with E-RES below **3 GiB** free; the items already zipped stand.
5. **One Lean process at a time** across the whole queue, and one screen at a time. A Lean
   process is one that you start: a module check, a probe, a bootstrap or sweep step (each
   through `scripts/lean_check_tree.sh`), or one `lake exe cache get`. Never run two of them at
   once. One text screen (Python, `nice -n 10`) may run beside one of them. Processes that Lake or
   the cache tool start inside `lake exe cache get` are not counted.
6. **At the end** (or when the session must stop), deliver `megafill-<name>-REPORT.md`: the queue;
   each item's outcome (complete; partial, with its checkpoints; or not started), with its
   branch's start and end times and its zip's SHA-256; the shared preflight and cache numbers. An
   item never started is simply listed as such: it is not a failure.
7. **A process deviation never ends an item.** A deviation from these rules, yours or a tool's, is
   disclosed in `REPORT.md` with its evidence, and the work continues: stopping does not undo it.
   Only E-RES (Part 1) or an item brief's own escalation (its ground rules) ends an item early.

## ===== TCSlib/Complexity/Diagonalization/Ladner.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.CookLevin.Hardness
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.ClassP.ModelInvariance
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Delayed diagonalization and intermediate languages

## Main definitions

* `Complexity.padSAT` is SAT padded by a variable exponent after a final separator.
* `Complexity.ladnerMachine` is the uniformly timed enumeration used in the delayed diagonal.
* `Complexity.ladnerH` is the least currently successful index, capped by a double logarithm.
* `Complexity.SAT_H` is the language padded by that index function.

## Main results

* `Complexity.ladnerH_polyTime` states that the delayed index is polynomial-time computable.
* `Complexity.SAT_H_intermediate` gives an intermediate language when P differs from NP.
* `Complexity.ladner` states the existence of an NP-intermediate language.

## Conventions

The bounded test uses acceptance equivalence at the indexed deadline, rather than
requiring a Boolean output within that deadline. At the empty input the deadline
is zero, so acceptance and padded-language membership are both false. The enumeration
uses the existing uniform binary code scheme. The inherited SAT decoder is total and
maps malformed words to a satisfiable formula. The general padding theorem below uses
the weaker NP-hardness premise, strengthening the NP-complete version.

## References

* [AB09] S. Arora, B. Barak, Computational Complexity: A Modern Approach,
  Cambridge University Press, 2009. Theorem 3.3 and its proof.
-/

namespace Complexity

open Turing
open scoped Classical

/-- `padSAT h` consists of a satisfiable word followed by a false separator and
`|ψ| ^ h |ψ|` true bits. [AB09, Theorem 3.3 and its proof] -/
def padSAT (h : ℕ → ℕ) : Language Bool :=
  {y | ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true}

/-- A word belongs to `padSAT h` exactly when it has the indicated satisfiable prefix
and the prescribed separator and unary suffix. -/
theorem mem_padSAT_iff {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔
      ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true :=
  Iff.rfl

/-- Padding-language membership at a word depends only on exponent values at shorter
prefix lengths.

**Proof sketch.** A padding witness is shorter than the whole word because the separator
contributes one position. Substitute equality of the exponent functions at that length. -/
theorem padSAT_congr {h g : ℕ → ℕ} {y : List Bool}
    (hfg : ∀ m < y.length, h m = g m) :
    y ∈ padSAT h ↔ y ∈ padSAT g := by
  constructor
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [← hfg ψ.length hshort]
    exact he
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [hfg ψ.length hshort]
    exact he

/-- The index `i` denotes the machine obtained by decoding its binary digits in the
uniformly timed code scheme. [AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerMachine (i : ℕ) : FinTM Bool :=
  (expCode.decode (Nat.bits i)).toFinTM

/-- The enumeration uses `expCode` on the binary digits of its index. -/
theorem ladnerMachine_eq (i : ℕ) :
    ladnerMachine i = (expCode.decode (Nat.bits i)).toFinTM :=
  rfl

/-- The delayed index at `n` is the least index below the double logarithm that correctly
recognizes the padded language on words of length at most the logarithm, within its indexed
polynomial deadline. If no such index exists, it is the double logarithm. Values used in a
short padded word depend only on smaller arguments, so strong recursion defines the index.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerH (n : ℕ) : ℕ :=
  Nat.strongRecOn (motive := fun _ => ℕ) n fun n prev =>
    let h : ℕ → ℕ := fun m => if hm : m < n then prev m hm else 0
    let good : ℕ → Prop := fun i => ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔ x ∈ padSAT h)
    if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧ good i then Nat.find hex
    else Nat.log 2 (Nat.log 2 n)

/-- The delayed index satisfies its minimum-index equation, with the global padded
language in the bounded acceptance test.

**Proof sketch.** Read the strong-recursion equation and use `padSAT_congr` to identify
local and global exponents on every queried word. Handle zero before using logarithmic decrease. -/
theorem ladnerH_eq (n : ℕ) :
    ladnerH n =
      if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
          ∀ x : List Bool, x.length ≤ Nat.log 2 n →
            ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
              x ∈ padSAT ladnerH) then
        Nat.find hex
      else Nat.log 2 (Nat.log 2 n) := by
  conv_lhs => rw [ladnerH]
  change (Nat.lt_wfRel.wf.fix (C := fun _ : ℕ => ℕ) _ n) = _
  rw [WellFounded.fix_eq]
  dsimp only
  let previous : ℕ → ℕ := fun m => if hm : m < n then ladnerH m else 0
  let localTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT previous)
  let globalTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)
  have hpad (hn : n ≠ 0) (x : List Bool) (hx : x.length ≤ Nat.log 2 n) :
      x ∈ padSAT previous ↔ x ∈ padSAT ladnerH := by
    apply padSAT_congr
    intro m hm
    have hmn : m < n := (hm.trans_le hx).trans (Nat.log_lt_self 2 hn)
    exact dif_pos hmn
  have hnonzero (i : ℕ) (hi : i < Nat.log 2 (Nat.log 2 n)) : n ≠ 0 := by
    intro hz
    subst n
    simp at hi
  have htests : localTest = globalTest := by
    funext i
    apply propext
    constructor
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx)
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx).symm
  have hexists : (∃ i, localTest i) ↔ ∃ i, globalTest i :=
    exists_congr fun i => Iff.of_eq (congrFun htests i)
  split_ifs with hlocal hglobal
  · exact Nat.find_congr' fun {i} => Iff.of_eq (congrFun htests i)
  · exact False.elim (hglobal (hexists.mp hlocal))
  · rename_i hglobal
    exact False.elim (hlocal (hexists.mpr hglobal))
  · rfl

/-- The delayed index never exceeds its double-logarithmic cap.

**Proof sketch.** In the successful case, read the strict index bound of the least witness;
in the fallback case, the index equals the cap. -/
theorem ladnerH_le (n : ℕ) : ladnerH n ≤ Nat.log 2 (Nat.log 2 n) := by
  rw [ladnerH_eq]
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- `SAT_H` is the language obtained by padding SAT with the delayed index function.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def SAT_H : Language Bool := padSAT ladnerH

/-- The witness language is `padSAT ladnerH`. -/
theorem SAT_H_eq : SAT_H = padSAT ladnerH :=
  rfl

/-- The binary digits of the delayed index at an input's length are polynomial-time
computable. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Maintain previously computed index values, simulate only the short
inputs through the uniformly timed acceptance simulator, and test SAT on short words.
Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
theorem ladnerH_polyTime :
    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) :=
  sorry

/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Guess the satisfiable prefix and its SAT certificate. Compute the
index at that prefix length and check the separator and exactly prescribed unary suffix. -/
theorem SAT_H_mem_NP : SAT_H ∈ NP :=
  sorry

/-- The empty word is outside every padded language because a separator contributes
one symbol. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by
  intro hx
  obtain ⟨ψ, _, he⟩ := mem_padSAT_iff.mp hx
  have hlen := congrArg List.length he
  simp only [List.length_nil, List.length_append, List.length_cons,
    List.length_replicate] at hlen
  omega

/-- Prepending a word to the binary word of a positive number gives the binary word of a
number at least as large. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bits_prepend (u : List Bool) (j : ℕ) (hj : 0 < j) :
    ∃ i, j ≤ i ∧ i.bits = u ++ j.bits := by
  induction u with
  | nil => exact ⟨j, le_rfl, rfl⟩
  | cons b u ih =>
    obtain ⟨i, hi, hbits⟩ := ih
    refine ⟨Nat.bit b i, ?_, ?_⟩
    · rw [Nat.bit_val]
      omega
    · rw [Nat.bits_append_bit i b (fun hz => by omega), hbits, List.cons_append]

/-- Every coded machine occurs at arbitrarily large canonical binary indices.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Construct a positive all-true binary suffix whose value exceeds
the requested bound. Prepending each bit of the machine's encoding preserves
canonicality and cannot decrease the value. The decoding padding law then
identifies the indexed machine. -/
private theorem ladner_padded_index (M : CodeTM) (B : ℕ) :
    ∃ i, B < i ∧ ladnerMachine i = M.toFinTM := by
  have ones : ∀ b : ℕ, ∃ j, b + 1 ≤ j ∧ j.bits = List.replicate (b + 1) true := by
    intro b
    induction b with
    | zero => exact ⟨1, le_rfl, Nat.one_bits⟩
    | succ b ih =>
      obtain ⟨j, hj, hbits⟩ := ih
      refine ⟨Nat.bit true j, ?_, ?_⟩
      · rw [Nat.bit_val]
        omega
      · rw [Nat.bits_append_bit j true (fun _ => rfl), hbits,
          List.replicate_succ (n := b + 1)]
  obtain ⟨j, hj, hbits⟩ := ones B
  obtain ⟨i, hi, hi_bits⟩ := ladner_bits_prepend (expCode.encode M) j (by omega)
  refine ⟨i, by omega, ?_⟩
  rw [ladnerMachine_eq, hi_bits, hbits, expCode.toMachineCode.decode_encode_pad]

/-- An indexed deadline dominates a polynomial on nonempty inputs when its index
bounds both the degree and the scaled coefficient. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_indexed_deadline (a d i m : ℕ)
    (hd : d ≤ i) (ha : a * 2 ^ d ≤ i) (hm : 1 ≤ m) :
    a * (m + 1) ^ d ≤ i * m ^ i := calc
  a * (m + 1) ^ d ≤ a * (2 * m) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  _ = (a * 2 ^ d) * m ^ d := by rw [mul_pow, mul_assoc]
  _ ≤ i * m ^ i := Nat.mul_le_mul ha (Nat.pow_le_pow_right hm hd)

/-- A polynomial decider supplies one index that passes every bounded-acceptance
test. The empty word is handled by the zero-deadline convention.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Replace the decider by a one-work-tape machine and then its coded
normal form. Choose a padded index above the degree and scaled coefficient.
On a positive input length, the indexed clock contains the decider's clock.
Acceptance gives membership by uniqueness of completed outputs; membership gives
acceptance by monotonicity. At the empty input both sides are false. -/
private theorem ladner_correct_index (hP : SAT_H ∈ P) :
    ∃ i, ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH := by
  classical
  obtain ⟨M, a, d, hk, hM⟩ := mem_P_iff_one_work_tape.mp hP
  have hdec := (FinTM.computesFunInTime_iff M _ _).mp
    ((FinTM.decidesInTime_iff M SAT_H _).mp hM)
  obtain ⟨i, hi, hcode⟩ := ladner_padded_index (M.toCodeTM hk) (max d (a * 2 ^ d))
  have hd : d ≤ i := (le_max_left d (a * 2 ^ d)).trans hi.le
  have ha : a * 2 ^ d ≤ i := (le_max_right d (a * 2 ^ d)).trans hi.le
  refine ⟨i, fun x => ?_⟩
  by_cases hx : x = []
  · subst x
    have hzero : i * ([] : List Bool).length ^ i = 0 := by
      have hipos : i ≠ 0 := by omega
      simp only [List.length_nil, zero_pow hipos, Nat.mul_zero]
    rw [hzero]
    exact iff_of_false (FinTM.not_computesInTime_zero _ _ _) (ladner_pad_nil ladnerH)
  · have hlen : 1 ≤ x.length := by
      cases x with
      | nil => exact False.elim (hx rfl)
      | cons b xs => exact Nat.succ_le_succ (Nat.zero_le _)
    have hclock := ladner_indexed_deadline a d i x.length hd ha hlen
    have hrun : (ladnerMachine i).ComputesInTime x
        [MultiTapeTM.indicator (SAT_H : Set (List Bool)) x] (a * (x.length + 1) ^ d) := by
      rw [hcode, FinTM.toCodeTM_computesInTime_iff]
      exact hdec x
    constructor
    · intro hacc
      by_contra hnot
      have hnot' : x ∉ SAT_H := by rw [SAT_H_eq]; exact hnot
      have hfalse := hrun
      rw [MultiTapeTM.indicator_of_not_mem hnot'] at hfalse
      have he := hacc.output_unique hfalse
      simp only [List.cons.injEq, Bool.true_eq_false, false_and] at he
    · intro hmem
      have hmem' : x ∈ SAT_H := by rw [SAT_H_eq]; exact hmem
      rw [MultiTapeTM.indicator_of_mem hmem'] at hrun
      exact hrun.mono hclock

/-- A globally correct index bounds the delayed selector at every stage.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_selector_bound (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) :
    ∀ n, ladnerH n ≤ i := by
  classical
  intro n
  rw [ladnerH_eq]
  split_ifs with h
  · by_cases hcap : i < Nat.log 2 (Nat.log 2 n)
    · exact Nat.find_min' h ⟨hcap, fun x _ => good x⟩
    · exact (Nat.find_spec h).1.le.trans (Nat.le_of_not_gt hcap)
  · apply Nat.le_of_not_gt
    intro hcap
    exact h ⟨i, hcap, fun x _ => good x⟩

/-- A polynomial-time decider for the padded language forces its delayed index to be
bounded. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a padded code of the decider whose enumeration index dominates
its polynomial time degree. That index eventually passes every short acceptance test;
absorb the finitely many earlier index values into one bound. -/
theorem ladnerH_bounded_of_mem_P :
    SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C := by
  intro hP
  obtain ⟨i, hi⟩ := ladner_correct_index hP
  exact ⟨i, ladner_selector_bound i hi⟩

/-- A fixed polynomial clock can be prepared in the uniform simulator's paired
input format in polynomial time. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** On a nonempty word, evaluating the successor-length polynomial
on its tail gives the required polynomial of the original length. Handle the
empty word by a fixed equality test and constant output, then pair the clock
with the fixed machine code and the original word. -/
private theorem ladner_fixed_clock_preparation (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x) := by
  classical
  obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyBits a d
  have hpoly : PolyTimeComputable (fun x : List Bool => Nat.bits (a * (x.length + 1) ^ d)) :=
    (polyTimeComputable_iff _).mpr ⟨M, c, d + 1, hM⟩
  have htail : PolyTimeComputable
      (fun x : List Bool => Nat.bits (a * ((x.drop 1).length + 1) ^ d)) :=
    hpoly.comp polyTimeComputable_tail
  have hnil : PolyTimeComputable (fun x : List Bool => [decide (x = [])]) :=
    polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq [])
  have hbranch := polyTimeComputable_ite hnil
    (polyTimeComputable_const (Nat.bits (a * 0 ^ d))) htail
  have heq : (fun x : List Bool => if decide (x = []) then
      Nat.bits (a * 0 ^ d) else Nat.bits (a * ((x.drop 1).length + 1) ^ d)) =
      (fun x : List Bool => Nat.bits (a * x.length ^ d)) := by
    funext x
    cases x with
    | nil => simp only [decide_true, if_true, List.length_nil]
    | cons b xs =>
      simp only [List.cons_ne_nil, decide_false, Bool.false_eq_true, if_false,
        List.drop_succ_cons, List.drop_zero, List.length_cons]
  rw [heq] at hbranch
  exact (hbranch.pairEncode (polyTimeComputable_const code)).pairEncode polyTimeComputable_id

/-- The simulator's polynomial in the numerical deadline has a polynomial envelope
when the simulated code and clock are fixed. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each input-length term is bounded by a coefficient times the
successor length raised to the larger of one and the clock degree. Add these
bounds, raise to the simulator degree, and collect the constant factors. -/
private theorem ladner_fixed_clock_budget (D u a d n : ℕ) :
    D * (u + n + a * n ^ d + 1) ^ D ≤
      (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
  let q := (n + 1) ^ max 1 d
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : n ≤ q := calc
    n ≤ n + 1 := Nat.le_succ _
    _ = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ q := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left 1 d)
  have hnd : n ^ d ≤ q :=
    (Nat.pow_le_pow_left (Nat.le_succ n) d).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right 1 d))
  have hu : u ≤ u * q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left u hq
  have ha := Nat.mul_le_mul_left a hnd
  have hbase : u + n + a * n ^ d + 1 ≤ (u + a + 2) * q := calc
    _ ≤ u * q + q + a * q + q := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu hn) ha) hq
    _ = _ := by ring
  calc
    D * (u + n + a * n ^ d + 1) ^ D ≤ D * ((u + a + 2) * q) ^ D :=
      Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase D)
    _ = (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
      rw [mul_pow, mul_assoc, ← pow_mul]

/-- The bounded-acceptance test for a fixed code and polynomial clock is a total
polynomial-time Boolean function. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Prepare the exact simulator input with a polynomial-time machine.
The uniform simulator returns the bounded-acceptance bit on this image, including
when the simulated machine diverges. Bound its numerical clock by a fixed
polynomial, compose on the preparation machine's image, and absorb setup and
composition costs into one successor-length polynomial. -/
private theorem ladner_fixed_clock_FP (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      [decide ((expCode.decode code).toFinTM.ComputesInTime
        x [true] (a * x.length ^ d))]) := by
  classical
  obtain ⟨M, C, e, hM⟩ := (polyTimeComputable_iff _).mp
    (ladner_fixed_clock_preparation code a d)
  let A := expCode.simDegree * (code.length + a + 2) ^ expCode.simDegree
  let k := max 1 d * expCode.simDegree
  have hU (x : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x)
      [decide ((expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d))]
      (A * (x.length + 1) ^ k) := by
    have hb := ladner_fixed_clock_budget expCode.simDegree code.length a d x.length
    by_cases hacc : (expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d)
    · simpa only [hacc, decide_true] using
        (expCode.simulator_accepts code x (a * x.length ^ d) hacc).mono hb
    · simpa only [hacc, decide_false] using
        (expCode.simulator_rejects code x (a * x.length ^ d) hacc).mono hb
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ e) (fun n => A * (n + 1) ^ k) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max e k, (FinTM.computesFunInTime_iff N _ _).mpr ?_⟩
  intro x
  apply (((FinTM.computesFunInTime_iff N _ _).mp hN) x).mono
  have he := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_left e k)
  have hk := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_right e k)
  have hone := Nat.one_le_pow (max e k) (x.length + 1) (Nat.succ_pos _)
  calc
    2 * (C * (x.length + 1) ^ e) + A * (x.length + 1) ^ k + 2 ≤
        2 * (C * (x.length + 1) ^ max e k) + A * (x.length + 1) ^ max e k +
          2 * (x.length + 1) ^ max e k :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C he))
        (Nat.mul_le_mul_left A hk)) (by omega)
    _ = (2 * C + A + 2) * (x.length + 1) ^ max e k := by ring

/-- If one indexed test agrees everywhere with the padded language, its total
bounded simulator decides that language in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_all_tests_imply_P (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) : SAT_H ∈ P := by
  classical
  have htest := mem_P_of_test (ladner_fixed_clock_FP (Nat.bits i) i i)
  have heq : {x : List Bool | decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true} = SAT_H := by
    ext x
    change (decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true) ↔ x ∈ SAT_H
    rw [decide_eq_true_eq, ← ladnerMachine_eq, SAT_H_eq]
    exact good x
  rw [heq] at htest
  exact htest

/-- Finitely many failing words are all visible at every sufficiently large stage,
so the delayed selector eventually exceeds any prescribed bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a failing word for every index. For a given bound, take
the maximum length of witnesses below it. Choose an exponential stage whose query
window contains that maximum and whose double-log cap exceeds the bound. The
least successful index cannot be below the bound; neither can the fallback. -/
private theorem ladner_selector_threshold
    (bad : ∀ i : ℕ, ∃ x : List Bool,
      ¬ ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)) :
    ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  choose witness counterexample using bad
  intro C
  let B := (Finset.range C).sup fun i => (witness i).length
  let M := max B (2 ^ C)
  refine ⟨2 ^ M, ?_⟩
  intro n hn
  have hlog : M ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hcap : C ≤ Nat.log 2 (Nat.log 2 n) :=
    Nat.le_log_of_pow_le (by decide) ((le_max_right B (2 ^ C)).trans hlog)
  rw [ladnerH_eq]
  split_ifs with h
  · by_contra! hi
    have hlen : (witness (Nat.find h)).length ≤ B :=
      Finset.le_sup (f := fun i => (witness i).length) (Finset.mem_range.mpr hi)
    exact counterexample (Nat.find h)
      ((Nat.find_spec h).2 _ (hlen.trans ((le_max_left B (2 ^ C)).trans hlog)))
  · exact hcap

/-- If the padded language is outside P, the delayed index eventually exceeds every
constant. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each fixed machine has a failing finite test, since a machine that passed
all its indexed polynomial tests would decide the language in polynomial time. Once all
failing tests below a fixed cap are visible, none of those indices is selected. -/
theorem ladnerH_unbounded_of_not_mem_P :
    SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  intro hP
  apply ladner_selector_threshold
  intro i
  by_contra! hgood
  exact hP (ladner_all_tests_imply_P i hgood)

/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
to P. The hypothesis uses NP-hardness, rather than NP-completeness.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** A polynomial reduction into the padded language eventually maps an
instance to a satisfiable-prefix candidate at most the square root of its length.
Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P :=
  sorry

/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
not NP-complete. [AB09, Theorem 3.3]

**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
polynomial reduction from SAT. NP-hardness would instead combine divergence of the
index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
theorem SAT_H_intermediate (h : P ≠ NP) :
    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H :=
  sorry

/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
  ⟨SAT_H, SAT_H_intermediate h⟩

/-! ### Padding syntax and fixed finite tables -/

/-- Parse the final false separator and its true suffix.
This is the mathematical padding parser of [AB09, Theorem 3.3 and its proof]. -/
private def ladner_parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match ladner_parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

/-- Padding syntax requires the suffix length to be the prescribed power.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match ladner_parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

/-- Serialize a successful parse with a nonempty marker; failure is the empty word.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_parseWord (y : List Bool) : List Bool :=
  match ladner_parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

/-- The parser fails exactly on words with no false separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_none (y : List Bool) :
    ladner_parse y = none ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [ladner_parse, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih =>
    rw [List.forall_mem_cons, ← ih]
    cases hs : ladner_parse bs with
    | none => cases b <;> simp only [ladner_parse, hs, Bool.false_eq_true,
        if_false, if_true, Option.some_ne_none, and_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      simp only [ladner_parse, hs, Option.some_ne_none, and_false]

/-- A successful parse reconstructs the input around the final separator.

**Proof sketch.** Induct on the input. A successful recursive parse extends the prefix.
When the recursive parse fails, the tail is all true and the current false bit is the
final separator. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_sound {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : y = p ++ false :: List.replicate t true := by
  induction y generalizing p t with
  | nil => cases hp
  | cons b bs ih =>
    cases hs : ladner_parse bs with
    | none =>
      cases b with
      | false =>
        simp only [ladner_parse, hs, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have he : bs = List.replicate bs.length true :=
          List.eq_replicate_iff.mpr ⟨rfl, (ladner_parse_none bs).mp hs⟩
        simpa only [List.nil_append] using congrArg (List.cons false) he
      | true =>
        simp only [ladner_parse, hs, if_true] at hp
        cases hp
    | some pt =>
      obtain ⟨q, u⟩ := pt
      simp only [ladner_parse, hs, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simpa only [List.cons_append] using congrArg (List.cons b) (ih hs)

/-- The parser reads any prefix followed by a false separator and a true suffix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_pad (p : List Bool) (t : ℕ) :
    ladner_parse (p ++ false :: List.replicate t true) = some (p, t) := by
  have hn : ladner_parse (List.replicate t true) = none :=
    (ladner_parse_none _).mpr (by simp only [List.mem_replicate]; aesop)
  induction p with
  | nil => simp only [List.nil_append, ladner_parse, hn, Bool.false_eq_true,
      if_false, List.length_replicate]
  | cons b p ih => simp only [List.cons_append, ladner_parse, ih]

/-- Parsing succeeds exactly on the indicated padded word.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_some (y p : List Bool) (t : ℕ) :
    ladner_parse y = some (p, t) ↔ y = p ++ false :: List.replicate t true :=
  ⟨ladner_parse_sound, fun he => he ▸ ladner_parse_pad p t⟩

/-- A parsed prefix is shorter than the input, whose length includes the separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parsed_length {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) :
    y.length = p.length + 1 + t ∧ p.length < y.length := by
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

/-- The public false-bit test is false exactly on all-true words. -/
private theorem ladner_hasFalse_false (y : List Bool) :
    BinArith.hasFalse y = false ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [BinArith.hasFalse_nil, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih => cases b <;> simp only [BinArith.hasFalse_cons, Bool.not_false,
      Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_eq_false,
      List.forall_mem_cons, Bool.false_eq_true, false_and, true_and, ih]

/-- The public false-bit test distributes over append. -/
private theorem ladner_hasFalse_append (u v : List Bool) :
    BinArith.hasFalse (u ++ v) = (BinArith.hasFalse u || BinArith.hasFalse v) := by
  induction u with
  | nil => simp only [List.nil_append, BinArith.hasFalse_nil, Bool.false_or]
  | cons b u ih => simp only [List.cons_append, BinArith.hasFalse_cons, ih, Bool.or_assoc]

/-- Reverse and the public unary-rest reader recover a successful parse's prefix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_prefix {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : (BinArith.uRest y.reverse).reverse = p := by
  have hr (n : ℕ) (w : List Bool) :
      BinArith.uRest (List.replicate n true ++ false :: w) = w := by
    have h := BinArith.uRest_encodeNat n w
    rwa [BoolCircuit.encodeNat_eq, List.append_assoc, List.singleton_append] at h
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append, hr, List.reverse_reverse]

/-- The binary length of a word is polynomial-time (`FinTM.computesFunInTime_lengthBits`).
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_lengthBits_FP : PolyTimeComputable (fun y : List Bool => Nat.bits y.length) :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits

/-- The mathematical padding parser has a polynomial-time serialization.

**Proof sketch.** Reverse the input, skip its true suffix and separator with the existing
unary-rest reader, and reverse the remainder. Subtract the prefix length and one from
the input length to get the suffix length. The public false-bit test distinguishes a
missing separator from an empty prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_FP : PolyTimeComputable ladner_parseWord := by
  have hl := ladner_lengthBits_FP
  have hpre := BinArith.polyTimeComputable_reverse.comp
    (BinArith.polyTimeComputable_uRest.comp BinArith.polyTimeComputable_reverse)
  have ht := BinArith.polyTimeComputable_sub.comp
    ((BinArith.polyTimeComputable_sub.comp (hl.pairEncode (hl.comp hpre))).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  have hout := polyTimeComputable_ite BinArith.polyTimeComputable_hasFalse
    ((polyTimeComputable_const [true]).pairEncode (hpre.pairEncode ht))
    (polyTimeComputable_const [])
  convert hout using 1
  funext y
  cases hp : ladner_parse y with
  | none =>
    have hf := (ladner_hasFalse_false y).mpr ((ladner_parse_none y).mp hp)
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, Bool.false_eq_true, if_false]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hpre' := ladner_parse_prefix hp
    have hlen := (ladner_parsed_length hp).1
    have hf : BinArith.hasFalse y = true := by
      rw [(ladner_parse_some y p t).mp hp, ladner_hasFalse_append,
        BinArith.hasFalse_cons]
      simp only [Bool.not_false, Bool.true_or, Bool.or_true]
    have ht' : y.length - p.length - 1 = t := by omega
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, if_true, hpre',
      BinArith.sub_pairEncode, ht']

/-- The padding syntax test, for an exponent function that may depend on the input word, is
polynomial-time when the exponent at the parsed prefix length is.

**Proof sketch.** Parse the word and compute the prefix length and exponent in binary.
Use the saturated power with cap parameter equal to the suffix length. Its result equals
the suffix length exactly when the full power does; this avoids allocating an enormous
power. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_padSyntax_FP {g : List Bool → List Bool} {h : List Bool → ℕ → ℕ}
    (hg : PolyTimeComputable g)
    (hh : PolyTimeComputable (fun z : List Bool =>
      Nat.bits (h (pairSndD z) (pairFstD z).length))) :
    PolyTimeComputable (fun S => [ladner_padSyntax (h S) (g S)]) := by
  have hl := ladner_lengthBits_FP
  have hp := ladner_parse_FP.comp hg
  have hpre := BinArith.polyTimeComputable_slot2.comp hp
  have ht := BinArith.polyTimeComputable_slot3.comp hp
  have he := hh.comp (hpre.pairEncode polyTimeComputable_id)
  have hpow := BinArith.polyTimeComputable_powCap.comp
    ((hl.comp hpre).pairEncode (he.pairEncode ht))
  have heq := BinArith.polyTimeComputable_beq.comp (ht.pairEncode hpow)
  have hout := polyTimeComputable_ite (polyTimeComputable_isNil.comp hp)
    (polyTimeComputable_const [false]) heq
  convert hout using 1
  funext S
  cases hy : ladner_parse (g S) with
  | none => simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply,
      decide_true, if_true]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hne : pairEncode [true] (pairEncode p (Nat.bits t)) ≠ [] := by
      intro he
      have he' := congrArg List.length he
      rw [length_pairEncode] at he'
      simp only [List.length_cons, List.length_nil] at he'
      omega
    simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply, id_eq,
      hne, decide_false, Bool.false_eq_true, if_false, pairFstD_pairEncode,
      pairSndD_pairEncode, BinArith.powCap_pairEncode, BinArith.beq_pairEncode]
    have heq' : (t = min (p.length ^ h S p.length) (t + 1)) ↔
        t = p.length ^ h S p.length := by omega
    simp only [heq']

/-- The padding syntax test is polynomial-time when its exponent function is: the
instance of `ladner_padSyntax_FP` with a fixed exponent function.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_syntax_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) :
    PolyTimeComputable (fun y => [ladner_padSyntax h y]) :=
  ladner_padSyntax_FP (h := fun _ => h) polyTimeComputable_id
    (hp.comp polyTimeComputable_pairFstD)

/-- Padding membership is successful parsing, the prescribed suffix length, and SAT
membership of the prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_membership {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔ ∃ p t, ladner_parse y = some (p, t) ∧
      t = p.length ^ h p.length ∧ p ∈ SAT := by
  rw [mem_padSAT_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, p.length ^ h p.length, (ladner_parse_some _ _ _).mpr he, rfl, hp⟩
  · rintro ⟨p, t, hparse, rfl, hp⟩
    exact ⟨p, hp, (ladner_parse_some _ _ _).mp hparse⟩

/-- Every fixed finite table of words has a polynomial-time membership test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_finite_lookup_FP (S : Finset (List Bool)) :
    PolyTimeComputable (fun x : List Bool => [decide (x ∈ S)]) := by
  induction S using Finset.induction_on with
  | empty => exact polyTimeComputable_const [false]
  | @insert w S hw ih =>
    have heq := polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq w)
    convert polyTimeComputable_or heq ih using 1
    funext x
    simp only [Finset.mem_insert, Bool.decide_or]

/-- SAT on words shorter than a fixed bound is represented by a finite table.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Enumerate Boolean functions on each `Fin n` for `n < B`, turn them
into lists, and filter this finite universe by SAT. No SAT computation is performed at
runtime; the table is fixed once the bound is chosen. -/
private theorem ladner_small_SAT_table (B : ℕ) :
    ∃ S : Finset (List Bool), ∀ x : List Bool,
      x ∈ S ↔ x.length < B ∧ x ∈ SAT := by
  classical
  let U : Finset (List Bool) := (Finset.range B).biUnion (fun n =>
    (Finset.univ : Finset (Fin n → Bool)).image List.ofFn)
  have hu (x : List Bool) : x ∈ U ↔ x.length < B := by
    simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, hn, f, rfl⟩
      simpa only [List.length_ofFn] using hn
    · intro hx
      exact ⟨x.length, hx, x.get, List.ofFn_get x⟩
  exact ⟨U.filter (fun x => x ∈ SAT), fun x => by rw [Finset.mem_filter, hu]⟩


/-! ### Polynomial-time preparation for the bounded candidate test -/

/-- Read the numeric memo entries through `BinArith.decWords`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_values (T : List Bool) : List ℕ :=
  (BinArith.decWords T).map LogProg.bitsVal

/-- Enumerate every short word by deleting the high sentinel bit of a positive rank.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_shortWords (a : ℕ) : List (List Bool) :=
  (List.range (2 ^ (a + 1) - 1)).map (fun r => (Nat.bits (r + 1)).dropLast)

/-- Select the least successful index against the supplied memo values, or the cap.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_stage (vs : List ℕ) : ℕ :=
  let n := vs.length
  if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
      ∀ x : List Bool, x.length ≤ Nat.log 2 n →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0)) then Nat.find hex
  else Nat.log 2 (Nat.log 2 n)

/-- The candidate predicate checks context consistency and every short input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_candidate (S : List Bool) : Bool :=
  let n := (pairFstD S).length
  let i := LogProg.bitsVal (pairFstD (pairSndD S))
  let vs := ladner_values (pairSndD (pairSndD S))
  decide (n = vs.length ∧ i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT (fun m => vs.getD m 0)))

/-- A simulator query contains an index below the double logarithm and a short input.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_validQuery (S : List Bool) : Prop :=
  LogProg.bitsVal (pairFstD (pairSndD S)) <
      Nat.log 2 (Nat.log 2 (pairFstD S).length) ∧
    (pairSndD (pairSndD S)).length ≤ Nat.log 2 (pairFstD S).length

/-- Invalid queries use the empty code; valid ones use the canonical index bits.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryCode (S : List Bool) : List Bool :=
  if ladner_validQuery S then Nat.bits (LogProg.bitsVal (pairFstD (pairSndD S))) else []

/-- Invalid queries use the empty simulator input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryInput (S : List Bool) : List Bool :=
  if ladner_validQuery S then pairSndD (pairSndD S) else []

/-- Invalid queries use deadline zero; valid ones use the indexed deadline.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryDeadline (S : List Bool) : ℕ :=
  if ladner_validQuery S then
    LogProg.bitsVal (pairFstD (pairSndD S)) *
      (pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))
  else 0

/-- Serialize the guarded query in the uniform simulator's input format.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryPrep (S : List Bool) : List Bool :=
  pairEncode (pairEncode (Nat.bits (ladner_queryDeadline S)) (ladner_queryCode S))
    (ladner_queryInput S)

/-- Check the candidate context before using its numeric index.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_ctxGuard (C : List Bool) : Prop :=
  (pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
    LogProg.bitsVal (pairFstD (pairSndD C)) <
      Nat.log 2 (Nat.log 2 (pairFstD C).length)

/-- A single rank's verdict includes every guard and the acceptance equivalence.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_wordVerdict (C : List Bool) (r : ℕ) : Bool :=
  let x := (Nat.bits (r + 1)).dropLast
  let i := LogProg.bitsVal (pairFstD (pairSndD C))
  decide (ladner_ctxGuard C ∧ x.length ≤ Nat.log 2 (pairFstD C).length ∧
    ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
      x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0)))

/-- The number of words in the bounded short-input scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryCount (C : List Bool) : ℕ :=
  2 ^ (Nat.log 2 (pairFstD C).length + 1) - 1

/-- Initialize the remaining count, completed rank, and conjunction flag.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (List.replicate (ladner_queryCount C) true) (pairEncode [] [true]))

/-- One transition of the candidate scan, intended for `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_testStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let rank := pairFstD (pairSndD (pairSndD S))
  let flag := pairSndD (pairSndD (pairSndD S))
  if rem = [] then S else
    pairEncode C (pairEncode (rem.drop 1)
      (pairEncode (rank ++ [true]) [flag.headD false && ladner_wordVerdict C rank.length]))

/-- Read the conjunction flag of the candidate scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testOut (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD S))

/-- The sentinel enumeration contains exactly the words of length at most its bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The upper rank bound limits the binary word to `a + 1` bits.
Conversely prepend the bits of any word to the positive sentinel `1`; the resulting
canonical number has that word as its binary expansion with its last bit removed. -/
private theorem ladner_shortWords_complete (a : ℕ) (x : List Bool) :
    x ∈ ladner_shortWords a ↔ x.length ≤ a := by
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have hr' := List.mem_range.mp hr
    have hl := LogProg.length_bits_le (show r + 1 < 2 ^ (a + 1) by omega)
    rw [List.length_dropLast]
    omega
  · intro hx
    obtain ⟨n, hn, he⟩ := ladner_bits_prepend x 1 Nat.one_pos
    rw [Nat.one_bits] at he
    have hlt := LogProg.lt_two_pow_bits n
    rw [he, List.length_append, List.length_cons, List.length_nil] at hlt
    have hna : n < 2 ^ (a + 1) := hlt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
    apply List.mem_map.mpr
    refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hn, he, List.dropLast_concat]

/-- The short-input scan has at most twice the stage length plus two queries.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shortWords_count (n : ℕ) :
    (ladner_shortWords (Nat.log 2 n)).length ≤ 2 * (n + 1) := by
  rw [ladner_shortWords, List.length_map, List.length_range, pow_succ']
  have h := Nat.pow_log_le_add_one 2 n
  omega

/-- A uniform elementary bound used to charge the double logarithm.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_square_le_power (k : ℕ) : k ^ 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k < 3
    · have hk0 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk0 with rfl | rfl | rfl <;> norm_num
    · have hk' : 3 ≤ k := by omega
      calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
           _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left _ ih
           _ = 2 ^ (k + 1 + 1) := by simp only [pow_succ']

/-- Short indexed simulations have a deadline bounded by the cube of the stage length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Put `L = log₂ n` and `k = log₂ L`. The index is below `k`,
so `(k + 1)i ≤ k² ≤ 2^(k+1) ≤ 2L`. Thus `m^i ≤ 2^(2L) ≤ n²`,
while `i ≤ n`. No monotonicity of the delayed index is used. -/
private theorem ladner_short_deadline (n i m : ℕ)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hm : m ≤ Nat.log 2 n) :
    i * m ^ i ≤ n ^ 3 := by
  have hL : Nat.log 2 n ≠ 0 := by
    intro h
    rw [h, Nat.log_zero_right] at hi
    omega
  have hn : n ≠ 0 := by
    intro h
    subst n
    rw [Nat.log_zero_right] at hL
    exact hL rfl
  have hi' : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤
      (Nat.log 2 (Nat.log 2 n)) ^ 2 := by
    have h := Nat.mul_le_mul_left (Nat.log 2 (Nat.log 2 n) + 1)
      (Nat.succ_le_of_lt hi)
    nlinarith
  have hexp : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤ 2 * Nat.log 2 n := calc
    _ ≤ (Nat.log 2 (Nat.log 2 n)) ^ 2 := hi'
    _ ≤ 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) := ladner_square_le_power _
    _ = 2 * 2 ^ Nat.log 2 (Nat.log 2 n) := by rw [pow_succ']
    _ ≤ 2 * Nat.log 2 n := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hL)
  have hpow : m ^ i ≤ n ^ 2 := calc
    _ ≤ (2 ^ (Nat.log 2 (Nat.log 2 n) + 1)) ^ i := Nat.pow_le_pow_left
      (hm.trans (Nat.lt_pow_succ_log_self (by decide) (Nat.log 2 n)).le) _
    _ = 2 ^ ((Nat.log 2 (Nat.log 2 n) + 1) * i) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 * Nat.log 2 n) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ Nat.log 2 n) ^ 2 := by rw [Nat.mul_comm 2, pow_mul]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) _
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  calc i * m ^ i ≤ n * n ^ 2 := Nat.mul_le_mul hin hpow
       _ = n ^ 3 := by ring

/-- The uniform simulator's numeric deadline cost has a polynomial stage envelope.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Bound each of the code length, short-input length, deadline, and
constant by `(n + 1)^3`, then raise the sum bound to the simulator degree. -/
private theorem ladner_numeric_envelope (D n i : ℕ) (x : List Bool)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hx : x.length ≤ Nat.log 2 n) :
    D * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ D ≤
      (D * 4 ^ D) * (n + 1) ^ (3 * D) := by
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  have hb := (length_bits_le_self i).trans hin
  have hx' := hx.trans (Nat.log_le_self 2 n)
  have ht := ladner_short_deadline n i x.length hi hx
  have hcube : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hlin : n + 1 ≤ (n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by decide : 1 ≤ 3)
  calc _ ≤ D * (4 * (n + 1) ^ 3) ^ D :=
         Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
       _ = (D * 4 ^ D) * (n + 1) ^ (3 * D) := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial preparation and an image budget absorb the exact composition overhead.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_composition_clock (C q A e n : ℕ) :
    2 * (C * (n + 1) ^ q) + A * (n + 1) ^ e + 2 ≤
      (2 * C + A + 2) * (n + 1) ^ max q e := by
  have hq := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_left q e)
  have he := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_right q e)
  have hp : 1 ≤ (n + 1) ^ max q e := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The floor binary logarithm is the canonical binary length minus one.
`Complexity.LogProg.length_bits_eq_log` supplies the nonzero case. -/
private theorem ladner_log_eq_bits_length (n : ℕ) :
    Nat.log 2 n = (Nat.bits n).length - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, Nat.zero_bits, List.length_nil, Nat.zero_sub]
  · rw [LogProg.length_bits_eq_log (by omega)]
    omega

/-- The binary floor logarithm is polynomial-time, including noncanonical inputs.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_binary_log_FP : PolyTimeComputable
    (fun w : List Bool => Nat.bits (Nat.log 2 (LogProg.bitsVal w))) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_sub.comp
    ((hl.comp BinArith.polyTimeComputable_normBits).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  convert h using 1
  funext w
  simp only [Function.comp_apply, BinArith.sub_pairEncode, ladner_log_eq_bits_length]

/-- A linear SAT verifier yields the exact exponential short-SAT search clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Apply `Complexity.exists_proj_decider` at certificate width `m + 1`.
The verifier sees `2m + 1` symbols, and its clock therefore has base `2m + 2`.
Identify the projected language using the supplied verifier equivalence. -/
private theorem ladner_short_SAT_machine
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
      (fun m => b * 2 ^ (m + 1) *
        (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2)) := by
  obtain ⟨V, hV, hv⟩ := linear
  obtain ⟨a, d, M, hM⟩ := mem_P_iff.mp hV
  obtain ⟨b, E, hE⟩ := exists_proj_decider 1 1 V (fun n => a * (n + 1) ^ d) M hM
  have hlang : {x : List Bool | ∃ u, u.length = 1 * (x.length + 1) ^ 1 ∧ x ++ u ∈ V} =
      SAT := by
    ext x
    simpa only [Set.mem_setOf_eq, one_mul, pow_one] using (hv x).symm
  rw [hlang] at hE
  refine ⟨a, d, b, E, ?_⟩
  convert hE using 1
  funext m
  congr 2 <;> simp only [one_mul, pow_one] <;> ring

/-- The short-SAT search clock is polynomial when the queried word is logarithmic.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** `2^m ≤ n + 1` and `2m + 2 ≤ 2(n + 1)`. Raise the latter
bound to each degree, enlarge both degrees to `d + 2`, and charge the outer
factor `2(n + 1)` to obtain degree `d + 3`. -/
private theorem ladner_short_SAT_envelope (a b d n m : ℕ) (hm : m ≤ Nat.log 2 n) :
    b * 2 ^ (m + 1) * (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2) ≤
      (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
  have hm' := hm.trans (Nat.log_le_self 2 n)
  have hexp : 2 ^ (m + 1) ≤ 2 * (n + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) hm).trans
      (Nat.pow_log_le_add_one 2 n))
  have hd : (2 * m + 2) ^ d ≤ 2 ^ d * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ d * (n + 1) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  have htwo : (2 * m + 2) ^ 2 ≤ 4 * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    _ = 4 * (n + 1) ^ 2 := by ring
    _ ≤ 4 * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc _ ≤ b * (2 * (n + 1)) *
          ((a * 2 ^ d + 4) * (n + 1) ^ (d + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hexp) (by nlinarith)
       _ = (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
        rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
        ring

/-- Polynomial query preparation and a polynomial numeric budget suffice for simulation.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Extract the preparation machine through `polyTimeComputable_iff`.
The simulator's accepting and rejecting contracts compute the indicated bit on its image.
Use `FinTM.exists_comp_on_image`, then absorb its exact setup overhead with
`ladner_composition_clock`. The simulator clock is charged in the numeric deadline. -/
private theorem ladner_simulation_on_image (code input : List Bool → List Bool)
    (deadline : List Bool → ℕ)
    (hprep : PolyTimeComputable (fun z =>
      pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)))
    (hbudget : ∃ A e, ∀ z, expCode.simDegree *
      ((code z).length + (input z).length + deadline z + 1) ^ expCode.simDegree ≤
        A * (z.length + 1) ^ e) :
    PolyTimeComputable (fun z => [decide
      ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hprep
  obtain ⟨A, e, hA⟩ := hbudget
  have hU (z : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z))
      [decide ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))] (A * (z.length + 1) ^ e) := by
    by_cases h : (expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z)
    · simpa only [h, decide_true] using
        (expCode.simulator_accepts (code z) (input z) (deadline z) h).mono (hA z)
    · simpa only [h, decide_false] using
        (expCode.simulator_rejects (code z) (input z) (deadline z) h).mono (hA z)
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ q) (fun n => A * (n + 1) ^ e) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max q e, ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q A e z.length)

/-- Short SAT evaluation on an FP-prepared image has polynomial total cost.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the linear verifier's exponential projection decider only on the
logarithmically short image. `ladner_short_SAT_envelope` bounds that phase in the
original input length; image composition explicitly includes the FP preparation clock. -/
private theorem ladner_short_SAT_on_image (f : List Bool → List Bool)
    (hf : PolyTimeComputable f)
    (hshort : ∀ z, (f z).length ≤ Nat.log 2 z.length)
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun z => [decide (f z ∈ SAT)]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hf
  obtain ⟨a, d, b, E, hE⟩ := ladner_short_SAT_machine linear
  have he := (FinTM.computesFunInTime_iff _ _ _).mp
    ((FinTM.decidesInTime_iff _ _ _).mp hE)
  have hU (z : List Bool) : E.ComputesInTime (f z) [decide (f z ∈ SAT)]
      ((2 * b * (a * 2 ^ d + 4)) * (z.length + 1) ^ (d + 3)) := by
    have h := (he (f z)).mono (ladner_short_SAT_envelope a b d z.length (f z).length (hshort z))
    by_cases hz : f z ∈ SAT
    · simpa only [MultiTapeTM.indicator_of_mem hz, hz, decide_true] using h
    · simpa only [MultiTapeTM.indicator_of_not_mem hz, hz, decide_false] using h
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E f _
    (fun n => C * (n + 1) ^ q)
    (fun n => (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3)) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + (2 * b * (a * 2 ^ d + 4)) + 2, max q (d + 3), ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q _ (d + 3) z.length)

/-- A canonical index below the double logarithm of a word's length is an FP test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_index_lt_loglog_FP {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun S => [decide
      (LogProg.bitsVal (f S) < Nat.log 2 (Nat.log 2 (g S).length))]) := by
  have hl := ladner_lengthBits_FP
  have hi := BinArith.polyTimeComputable_normBits.comp hf
  have hcap := ladner_binary_log_FP.comp (ladner_binary_log_FP.comp (hl.comp hg))
  convert BinArith.polyTimeComputable_lt.comp (hi.pairEncode hcap) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.lt_pairEncode]

/-- The query guard is an FP test of canonical binary lengths and indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_validQuery_FP :
    PolyTimeComputable (fun S => [decide (ladner_validQuery S)]) := by
  have hl := ladner_lengthBits_FP
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hlog := ladner_binary_log_FP.comp (hl.comp polyTimeComputable_pairFstD)
  convert polyTimeComputable_and
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD)
    (BinArith.polyTimeComputable_le.comp (hx.pairEncode hlog)) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode,
    Bool.decide_and, ladner_validQuery]

/-- The guarded simulator query has a polynomial preparation machine and clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Normalize the index, compute the input and context lengths, and test
`ladner_validQuery` in binary. Compute the power with `BinArith.powCap` capped at
`n³ + 1`; the short deadline bound makes saturation inert on valid queries. All
operations remain FP on malformed inputs. Mask all three fields on invalid queries,
then pair them and expose the preparation witness through `polyTimeComputable_iff`. -/
private theorem ladner_query_preparation :
    ∃ (M : FinTM Bool) (C q : ℕ),
      M.ComputesFunInTime ladner_queryPrep (fun n => C * (n + 1) ^ q) := by
  have hl := ladner_lengthBits_FP
  have hn := hl.comp polyTimeComputable_pairFstD
  have hi := BinArith.polyTimeComputable_normBits.comp BinArith.polyTimeComputable_slot2
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hc : PolyTimeComputable (fun S : List Bool => Nat.bits ((pairFstD S).length ^ 3)) := by
    convert BinArith.polyTimeComputable_mul.comp
      ((BinArith.polyTimeComputable_mul.comp (hn.pairEncode hn)).pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, BinArith.mul_pairEncode]
    congr 1
    ring
  have hpower := BinArith.polyTimeComputable_powCap.comp (hx.pairEncode (hi.pairEncode hc))
  have hraw := BinArith.polyTimeComputable_mul.comp (hi.pairEncode hpower)
  have hd : PolyTimeComputable (fun S => Nat.bits (ladner_queryDeadline S)) := by
    convert polyTimeComputable_ite ladner_validQuery_FP hraw (polyTimeComputable_const []) using 1
    funext S
    by_cases hv : ladner_validQuery S
    · have ht := ladner_short_deadline (pairFstD S).length
        (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)).length hv.1 hv.2
      have hcap : (pairSndD (pairSndD S)).length ^
          LogProg.bitsVal (pairFstD (pairSndD S)) ≤ (pairFstD S).length ^ 3 + 1 := by
        by_cases hi0 : LogProg.bitsVal (pairFstD (pairSndD S)) = 0
        · simp only [hi0, pow_zero]
          omega
        · have hi1 : 1 ≤ LogProg.bitsVal (pairFstD (pairSndD S)) := by omega
          have hm := Nat.mul_le_mul_right
            ((pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))) hi1
          rw [one_mul] at hm
          omega
      simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_true, if_true,
        BinArith.powCap_pairEncode, BinArith.mul_pairEncode, min_eq_left hcap]
    · simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_false, Bool.false_eq_true, if_false,
        Nat.zero_bits]
  have hcode : PolyTimeComputable ladner_queryCode := by
    convert polyTimeComputable_ite ladner_validQuery_FP hi (polyTimeComputable_const []) using 1
    funext S
    simp only [Function.comp_apply, ladner_queryCode, decide_eq_true_eq]
  have hin : PolyTimeComputable ladner_queryInput := by
    convert polyTimeComputable_ite ladner_validQuery_FP BinArith.polyTimeComputable_slot3
      (polyTimeComputable_const []) using 1
    funext S
    simp only [ladner_queryInput, decide_eq_true_eq]
  exact (polyTimeComputable_iff _).mp ((hd.pairEncode hcode).pairEncode hin)

/-- The simulator's guarded numeric clock is polynomial in the serialized query length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** For valid queries use `ladner_numeric_envelope` and the public
projection length bound. Invalid queries have empty code and input and deadline zero,
so their simulator budget reduces to its degree. -/
private theorem ladner_query_budget (S : List Bool) :
    expCode.simDegree *
      ((ladner_queryCode S).length + (ladner_queryInput S).length + ladner_queryDeadline S + 1) ^
        expCode.simDegree ≤
      (expCode.simDegree * 4 ^ expCode.simDegree) *
        (S.length + 1) ^ (3 * expCode.simDegree) := by
  by_cases hv : ladner_validQuery S
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_true]
    exact (ladner_numeric_envelope expCode.simDegree (pairFstD S).length
      (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)) hv.1 hv.2).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (length_pairFstD_le S) 1) _))
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_false,
      List.length_nil, Nat.zero_add, one_pow, mul_one]
    calc expCode.simDegree ≤ expCode.simDegree * 4 ^ expCode.simDegree :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
         _ ≤ _ * (S.length + 1) ^ (3 * expCode.simDegree) :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- Canonicalize all memo entries using the public encoded-list map.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_table_FP : PolyTimeComputable
    (fun T => BinArith.encWords ((ladner_values T).map Nat.bits)) := by
  have hg := BinArith.polyTimeComputable_normBits.comp polyTimeComputable_pairSndD
  have h := (BinArith.polyTimeComputable_mapW hg).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext T
  simp only [Function.comp_apply, BinArith.mapW_pairEncode, pairSndD_pairEncode,
    ladner_values, List.map_map, id_eq]
  rfl

/-- The number of numeric memo entries is available in binary in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_values_length_FP :
    PolyTimeComputable (fun T => Nat.bits (ladner_values T).length) := by
  have hl := ladner_lengthBits_FP
  convert hl.comp BinArith.polyTimeComputable_countW using 1
  funext T
  simp only [Function.comp_apply, BinArith.countW_eq, List.length_replicate,
    ladner_values, List.length_map]

/-- Numeric memo entries are no more numerous than their serialized input bits.
`Complexity.BinArith.length_decWords_le` supplies the bound. -/
private theorem ladner_values_length_le (T : List Bool) : (ladner_values T).length ≤ T.length := by
  simpa only [ladner_values, List.length_map] using BinArith.length_decWords_le T

/-- Lookup of a memo exponent is FP after canonicalizing the table through `mapW`.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_get_value_FP : PolyTimeComputable (fun S : List Bool =>
    Nat.bits ((ladner_values (pairSndD S)).getD (pairFstD S).length 0)) := by
  have h := BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairFstD.pairEncode
    (ladner_table_FP.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext S
  simp only [Function.comp_apply, BinArith.getW_pairEncode_bits]

/-- Check the padding syntax against an exponent read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_tableSyntax (S : List Bool) : Bool :=
  match ladner_parse (pairFstD S) with
  | none => false
  | some (p, t) => decide (t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0)

/-- Table-dependent padding syntax is FP, even for enormous malformed exponents: the
instance of `ladner_padSyntax_FP` whose exponent is read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_tableSyntax_FP : PolyTimeComputable (fun S => [ladner_tableSyntax S]) := by
  have hh : PolyTimeComputable (fun z : List Bool => Nat.bits
      ((ladner_values (pairSndD (pairSndD z))).getD (pairFstD z).length 0)) := by
    convert ladner_get_value_FP.comp
      (polyTimeComputable_pairFstD.pairEncode BinArith.polyTimeComputable_slot3) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact ladner_padSyntax_FP (h := fun S m => (ladner_values (pairSndD S)).getD m 0)
    polyTimeComputable_pairFstD hh

/-- The short-word guard relative to the memo entry count is an FP predicate.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_guard_FP : PolyTimeComputable (fun S : List Bool =>
    [decide ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length)]) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_le.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode
    (ladner_binary_log_FP.comp (ladner_values_length_FP.comp polyTimeComputable_pairSndD)))
  convert h using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode]

/-- Table-dependent padding membership of short words is polynomial-time.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Test the short-word guard and table-dependent syntax with the public
parser, list map, lookup, and saturated-power routines. Feed the parsed prefix to the
short-SAT machine only on guarded inputs, using the empty word as a default. The final
bit is masked by both syntax and guard, so no SAT fact about the default is assumed. -/
private theorem ladner_short_pad_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool => [decide
      ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length ∧
        pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0))]) := by
  let f : List Bool → List Bool := fun S =>
    if (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length then
      pairFstD (pairSndD (ladner_parseWord (pairFstD S))) else []
  have hf : PolyTimeComputable f := by
    convert polyTimeComputable_ite ladner_pad_guard_FP
      (BinArith.polyTimeComputable_slot2.comp (ladner_parse_FP.comp polyTimeComputable_pairFstD))
      (polyTimeComputable_const []) using 1
    funext S
    simp only [f, Function.comp_apply, decide_eq_true_eq]
  have hfst0 : pairFstD [] = [] := pairFstD_nil
  have hsnd0 : pairSndD [] = [] := by
    simpa only [Function.iterate_one] using BinArith.iterate_pairSndD_nil 1
  have hshort (S : List Bool) : (f S).length ≤ Nat.log 2 S.length := by
    by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
    · dsimp only [f]
      rw [if_pos hg]
      cases hp : ladner_parse (pairFstD S) with
      | none => simp only [ladner_parseWord, hp, hsnd0, hfst0, List.length_nil, Nat.zero_le]
      | some pt =>
        obtain ⟨p, t⟩ := pt
        simp only [ladner_parseWord, hp, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ((ladner_parsed_length hp).2.le.trans hg).trans
          (Nat.log_mono_right ((ladner_values_length_le _).trans (length_pairSndD_le S)))
    · simp only [f, hg, if_false, List.length_nil, Nat.zero_le]
  have hsat := ladner_short_SAT_on_image f hf hshort linear
  have hout := polyTimeComputable_and ladner_pad_guard_FP
    (polyTimeComputable_and ladner_tableSyntax_FP hsat)
  convert hout using 1
  funext S
  by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
  · cases hp : ladner_parse (pairFstD S) with
    | none =>
      have hn : pairFstD S ∉ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0) := by
        rintro h
        obtain ⟨p, t, ht, -, -⟩ := ladner_pad_membership.mp h
        rw [hp] at ht
        cases ht
      simp only [hg, hn, and_false, decide_false, ladner_tableSyntax, hp, Bool.false_and,
        Bool.true_and, decide_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      have hm : (pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0)) ↔
          t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0 ∧ p ∈ SAT := by
        rw [ladner_pad_membership]
        constructor
        · rintro ⟨p', t', hp', ht, hsat⟩
          rw [hp, Option.some.injEq, Prod.mk.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          exact ⟨ht, hsat⟩
        · rintro ⟨ht, hsat⟩
          exact ⟨p, t, hp, ht, hsat⟩
      simp only [hg, true_and, decide_true, Bool.true_and, hm, Bool.decide_and,
        ladner_tableSyntax, hp, f, if_true, ladner_parseWord, pairFstD_pairEncode,
        pairSndD_pairEncode]
  · simp only [hg, false_and, decide_false, Bool.false_and]

/-- The candidate context guard is an FP test of lengths and canonical indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_ctxGuard_FP : PolyTimeComputable (fun C => [decide (ladner_ctxGuard C)]) := by
  have hl := ladner_lengthBits_FP
  have hcount := ladner_values_length_FP.comp BinArith.polyTimeComputable_slot3
  convert polyTimeComputable_and
    (BinArith.polyTimeComputable_beq.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode hcount))
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD) using 1
  funext C
  simp only [Function.comp_apply, BinArith.beq_pairEncode, ladner_ctxGuard, Bool.decide_and]

/-- Deleting the high sentinel bit is FP through reversal and the public tail routine.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_dropLast_FP : PolyTimeComputable (fun w : List Bool => w.dropLast) := by
  convert BinArith.polyTimeComputable_reverse.comp
    (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse) using 1
  funext w
  simp only [Function.comp_apply, List.drop_one, List.tail_reverse, List.reverse_reverse]

/-- The guarded single-word acceptance equivalence has a polynomial-time test.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Decode the unary rank with a high sentinel, test the context and
short-input guards, and build a guarded uniform-simulator query. Compare its verdict
with short padded-SAT membership. The outer guards mask every invalid state; the
SAT and simulator implementations retain their explicit preparation clocks. -/
private theorem ladner_wordVerdict_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length]) := by
  have hl := ladner_lengthBits_FP
  let x : List Bool → List Bool := fun S => (Nat.bits ((pairSndD S).length + 1)).dropLast
  have hx : PolyTimeComputable x := by
    convert ladner_dropLast_FP.comp (BinArith.polyTimeComputable_add.comp
      ((hl.comp polyTimeComputable_pairSndD).pairEncode
        (polyTimeComputable_const (Nat.bits 1)))) using 1
    funext S
    simp only [x, Function.comp_apply, BinArith.add_pairEncode]
  let Q : List Bool → List Bool := fun S =>
    pairEncode (pairFstD (pairFstD S)) (pairEncode (pairFstD (pairSndD (pairFstD S))) (x S))
  have hQ : PolyTimeComputable Q :=
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      ((BinArith.polyTimeComputable_slot2.comp polyTimeComputable_pairFstD).pairEncode hx)
  have hprep : PolyTimeComputable ladner_queryPrep :=
    (polyTimeComputable_iff _).mpr ladner_query_preparation
  have hsim := (ladner_simulation_on_image ladner_queryCode ladner_queryInput
    ladner_queryDeadline hprep ⟨_, _, ladner_query_budget⟩).comp hQ
  have hpad := (ladner_short_pad_FP linear).comp
    (hx.pairEncode (BinArith.polyTimeComputable_slot3.comp polyTimeComputable_pairFstD))
  have hshort := BinArith.polyTimeComputable_le.comp ((hl.comp hx).pairEncode
    (ladner_binary_log_FP.comp (hl.comp (polyTimeComputable_pairFstD.comp
      polyTimeComputable_pairFstD))))
  have hout := polyTimeComputable_and (ladner_ctxGuard_FP.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_and hshort
      (polyTimeComputable_not (BinArith.polyTimeComputable_xor hsim hpad)))
  convert hout using 1
  funext S
  have hxS : (Nat.bits ((pairSndD S).length + 1)).dropLast = x S := rfl
  by_cases hc : ladner_ctxGuard (pairFstD S)
  · by_cases hs : (x S).length ≤ Nat.log 2 (pairFstD (pairFstD S)).length
    · have hvalid : ladner_validQuery (Q S) := by
        simp only [ladner_validQuery, Q, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ⟨hc.2, hs⟩
      have htable : (x S).length ≤
          Nat.log 2 (ladner_values (pairSndD (pairSndD (pairFstD S)))).length := by
        rw [← hc.1]
        exact hs
      by_cases hrun : (ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))))).ComputesInTime (x S) [true]
          (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))) *
            (x S).length ^ LogProg.bitsVal (pairFstD (pairSndD (pairFstD S)))) <;>
        by_cases hsat : x S ∈ padSAT
          (fun m => (ladner_values (pairSndD (pairSndD (pairFstD S)))).getD m 0) <;>
        simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
          decide_true, Bool.true_and, BinArith.le_pairEncode, LogProg.bitsVal_bits,
          ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hvalid, if_true,
          Q, pairFstD_pairEncode, pairSndD_pairEncode, ← ladnerMachine_eq,
          htable, hrun, hsat, iff_self, iff_true, iff_false, not_true_eq_false,
          decide_false, Bool.false_xor, Bool.true_xor,
          Bool.not_false, Bool.not_true]
    · simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
        false_and, decide_false, decide_true, BinArith.le_pairEncode, LogProg.bitsVal_bits,
        Bool.false_and, Bool.and_false]
  · simp only [Function.comp_apply, ladner_wordVerdict, hc, false_and, decide_false,
      Bool.false_and]

/-- A candidate-scan transition is FP once its single-word verdict is FP.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_testStep_FP
    (hw : PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length])) :
    PolyTimeComputable ladner_testStep := by
  have hr := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hf := polyTimeComputable_headD.comp BinArith.polyTimeComputable_slot4
  have hword := hw.comp (polyTimeComputable_pairFstD.pairEncode hr)
  have hstep := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      ((hr.append (polyTimeComputable_const [true])).pairEncode
        (polyTimeComputable_and hf hword)))
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hstep using 1
  funext S
  simp only [Function.comp_apply, ladner_testStep, decide_eq_true_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

/-- The short-word count needs one doubling per bit of the positive stage length.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryFuel (C : List Bool) : List Bool :=
  if pairFstD C = [] then [true] else Nat.bits (pairFstD C).length

/-- The count-generation counter has exactly `log₂ n + 1` symbols, including at zero.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_length (C : List Bool) :
    (ladner_queryFuel C).length = Nat.log 2 (pairFstD C).length + 1 := by
  by_cases hn : pairFstD C = []
  · simp only [ladner_queryFuel, hn, if_true, List.length_cons, List.length_nil,
      Nat.log_zero_right]
  · have hlen : (pairFstD C).length ≠ 0 := by
      intro h
      exact hn (List.eq_nil_of_length_eq_zero h)
    simp only [ladner_queryFuel, hn, if_false, LogProg.length_bits_eq_log hlen]

/-- The doubling loop's final unary count is linearly bounded by the context length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_power_le (C : List Bool) :
    2 ^ (ladner_queryFuel C).length ≤ 2 * (C.length + 1) := by
  rw [ladner_queryFuel_length, pow_succ']
  exact Nat.mul_le_mul_left _ ((Nat.pow_log_le_add_one 2 _).trans
    (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Initialize the bounded query-count generation through the existing iterator.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (ladner_queryFuel C) [])

/-- A bounded doubling transition for query-count initialization; malformed states
cannot grow beyond the explicit guard. It is consumed by `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let acc := pairSndD (pairSndD S)
  let next := acc ++ acc ++ [true]
  if rem = [] then S else pairEncode C (pairEncode (rem.drop 1)
    (if next.length ≤ 2 * (C.length + 1) then next else acc))

/-- Query-count initialization is an FP serialization.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countInit_FP : PolyTimeComputable ladner_countInit := by
  have hl := ladner_lengthBits_FP
  have hf : PolyTimeComputable ladner_queryFuel := by
    convert polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_const [true]) (hl.comp polyTimeComputable_pairFstD) using 1
    funext C
    simp only [Function.comp_apply, ladner_queryFuel, decide_eq_true_eq]
  exact polyTimeComputable_id.pairEncode (hf.pairEncode (polyTimeComputable_const []))

/-- One guarded query-count doubling transition is polynomial-time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countStep_FP : PolyTimeComputable ladner_countStep := by
  have ha := BinArith.polyTimeComputable_slot3
  have hn := (ha.append ha).append (polyTimeComputable_const [true])
  have hb := (polyTimeComputable_polyUnary 2 1).comp polyTimeComputable_pairFstD
  have hg : PolyTimeComputable (fun S : List Bool =>
      [decide ((pairSndD (pairSndD S) ++ pairSndD (pairSndD S) ++ [true]).length ≤
        2 * ((pairFstD S).length + 1))]) := by
    convert polyTimeComputable_lenLe.comp (hb.pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, pow_one]
  have hs := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      (polyTimeComputable_ite hg hn ha))
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hs using 1
  funext S
  simp only [Function.comp_apply, ladner_countStep, decide_eq_true_eq, id_eq]

/-- Every round of bounded query-count generation has the exact doubling value.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Before fuel exhaustion, `2^j - 1` becomes `2^(j+1) - 1` by
doubling and appending one. The full-fuel power bound makes the cap guard inert.
After exhaustion the transition is fixed, and the `min` in the exponent records this. -/
private theorem ladner_count_orbit (C : List Bool) (j : ℕ) :
    ladner_countStep^[j] (ladner_countInit C) =
      pairEncode C (pairEncode ((ladner_queryFuel C).drop j)
        (List.replicate (2 ^ min j (ladner_queryFuel C).length - 1) true)) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_countInit, List.drop_zero,
      Nat.zero_min, pow_zero, Nat.sub_self, List.replicate_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < (ladner_queryFuel C).length
    · have hm : min j (ladner_queryFuel C).length = j := min_eq_left hj.le
      have hm' : min (j + 1) (ladner_queryFuel C).length = j + 1 := min_eq_left (by omega)
      have hp : 0 < 2 ^ j := Nat.pow_pos (by decide)
      have he : 2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1 := by
        rw [pow_succ']
        omega
      have hn : List.replicate (2 ^ j - 1) true ++ List.replicate (2 ^ j - 1) true ++ [true] =
          List.replicate (2 ^ (j + 1) - 1) true := by
        rw [← List.replicate_add, ← List.replicate_succ']
        congr 1
        omega
      have hg : (List.replicate (2 ^ j - 1) true ++
          List.replicate (2 ^ j - 1) true ++ [true]).length ≤ 2 * (C.length + 1) := by
        rw [hn, List.length_replicate]
        have hp' := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
          (by omega : j + 1 ≤ (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
        omega
      have hne : (ladner_queryFuel C).drop j ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_drop, List.length_nil] at hlen
        omega
      have hg' : (List.replicate (2 ^ (j + 1) - 1) true).length ≤ 2 * (C.length + 1) := by
        rw [← hn]
        exact hg
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode, hm,
        hm', hne, if_false, hn, hg', if_true, List.drop_drop]
    · have hm : min j (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      have hm' : min (j + 1) (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode,
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j),
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j + 1),
        hm, hm', if_true]

/-- All initialized query-count generation states have a linear serialized envelope.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_count_size (C : List Bool) (j : ℕ) :
    (ladner_countStep^[j] (ladner_countInit C)).length ≤ 8 * (C.length + 1) ^ 1 := by
  rw [ladner_count_orbit]
  simp only [length_pairEncode, List.length_drop, List.length_replicate, pow_one]
  have hfuel : (ladner_queryFuel C).length ≤ C.length + 1 := by
    rw [ladner_queryFuel_length]
    exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
  have hpow := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (min_le_right j (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
  omega

/-- The candidate scan's unary budget is constructed in polynomial time with a capped
application of the public iterator.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Generate `2^(log₂ n+1)-1` true bits by bounded doubling for one
round per binary length bit. Every intermediate state has the linear envelope
`ladner_count_size`; the guard protects malformed states. Compose the resulting
budget with the fixed initial rank and conjunction flag. -/
private theorem ladner_testInit_FP : PolyTimeComputable ladner_testInit := by
  have hloop := BinArith.polyTimeComputable_iterate ladner_countStep_FP ladner_countInit_FP
    1 1 8 1 (fun C j _ => ladner_count_size C j)
  have hu : PolyTimeComputable (fun C => List.replicate (ladner_queryCount C) true) := by
    convert BinArith.polyTimeComputable_slot3.comp hloop using 1
    funext C
    have hfuel : (ladner_queryFuel C).length ≤ 1 * (C.length + 1) ^ 1 := by
      rw [ladner_queryFuel_length, pow_one, one_mul]
      exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
    simp only [Function.comp_apply, ladner_count_orbit, pairSndD_pairEncode, min_eq_right hfuel]
    rw [ladner_queryFuel_length]
    rfl
  exact polyTimeComputable_id.pairEncode
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (polyTimeComputable_const [true])))

/-- Every initialized scan state has the exact remaining count, completed rank, and flag.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Induct on the iteration count. Before exhaustion the unary counter
loses one symbol and the conjunction gains exactly the next verdict. After exhaustion
the transition fixes the state, so both counters and the flag remain constant. -/
private theorem ladner_test_orbit (C : List Bool) (j : ℕ) :
    ladner_testStep^[j] (ladner_testInit C) =
      pairEncode C (pairEncode (List.replicate (ladner_queryCount C - j) true)
        (pairEncode (List.replicate (min j (ladner_queryCount C)) true)
          [decide (∀ r < min j (ladner_queryCount C), ladner_wordVerdict C r = true)])) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_testInit, Nat.sub_zero,
      Nat.zero_min, List.replicate_zero, Nat.not_lt_zero, false_implies, implies_true,
      decide_true]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < ladner_queryCount C
    · have hmin : min j (ladner_queryCount C) = j := min_eq_left hj.le
      have hmin' : min (j + 1) (ladner_queryCount C) = j + 1 := min_eq_left (by omega)
      have hne : List.replicate (ladner_queryCount C - j) true ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_replicate, List.length_nil] at hlen
        omega
      have hrem : ladner_queryCount C - j - 1 = ladner_queryCount C - (j + 1) := by omega
      have hrank : List.replicate j true ++ [true] = List.replicate (j + 1) true :=
        List.replicate_succ'.symm
      have hflag : (decide (∀ r < j, ladner_wordVerdict C r = true) && ladner_wordVerdict C j) =
          decide (∀ r < j + 1, ladner_wordVerdict C r = true) := by
        cases hv : ladner_wordVerdict C j <;>
          simp only [Nat.forall_lt_succ_right, Bool.decide_and, hv, Bool.false_eq_true,
            decide_false, decide_true, Bool.and_false, Bool.and_true]
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hne,
        if_false, hmin, hmin', List.drop_replicate, List.length_replicate,
        List.headD_cons, hrem, hrank, hflag]
    · have hmin : min j (ladner_queryCount C) = ladner_queryCount C := min_eq_right (by omega)
      have hmin' : min (j + 1) (ladner_queryCount C) = ladner_queryCount C :=
        min_eq_right (by omega)
      have hsub : ladner_queryCount C - j = 0 := by omega
      have hsub' : ladner_queryCount C - (j + 1) = 0 := by omega
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hmin,
        hmin', hsub, hsub', List.replicate_zero, if_true]

/-- The number of scan queries is bounded by twice the serialized context length plus two.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryCount_le (C : List Bool) :
    ladner_queryCount C ≤ 2 * (C.length + 1) := by
  have h := ladner_shortWords_count (pairFstD C).length
  simp only [ladner_shortWords, List.length_map, List.length_range] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Every state reached by an initialized candidate scan has linear serialized length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_test_size (C : List Bool) (j : ℕ) :
    (ladner_testStep^[j] (ladner_testInit C)).length ≤ 12 * (C.length + 1) ^ 1 := by
  rw [ladner_test_orbit]
  simp only [length_pairEncode, List.length_replicate, List.length_cons, List.length_nil,
    pow_one]
  have h := ladner_queryCount_le C
  have hsum : ladner_queryCount C - j + min j (ladner_queryCount C) = ladner_queryCount C :=
    by omega
  omega

/-- After the bounded word scan, its masked flag is exactly the candidate predicate.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The query-count bound ensures the scan is exhausted. Sentinel
completeness changes the conjunction over ranks into the universal short-word test.
The context guard supplies the table-length and index conditions, and masks all
inconsistent inputs. -/
private theorem ladner_candidate_readout (C : List Bool) :
    [ladner_candidate C] = if ladner_ctxGuard C then
      ladner_testOut (ladner_testStep^[2 * (C.length + 1) ^ 1] (ladner_testInit C))
      else [false] := by
  have hq : ladner_queryCount C ≤ 2 * (C.length + 1) ^ 1 := by
    simpa only [pow_one] using ladner_queryCount_le C
  by_cases hc : ladner_ctxGuard C
  · rw [if_pos hc, ladner_test_orbit]
    simp only [ladner_testOut, pairSndD_pairEncode, min_eq_right hq]
    have hequiv :
        (∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) ↔
        ∀ r < ladner_queryCount C, ladner_wordVerdict C r = true := by
      constructor
      · intro h r hr
        have hx : (Nat.bits (r + 1)).dropLast ∈
            ladner_shortWords (Nat.log 2 (pairFstD C).length) :=
          List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
        have hlen := (ladner_shortWords_complete _ _).mp hx
        simp only [ladner_wordVerdict, hc, hlen, true_and, decide_eq_true_eq]
        exact h _ hlen
      · intro h x hx
        obtain ⟨r, hr, he⟩ := List.mem_map.mp ((ladner_shortWords_complete _ _).mpr hx)
        have htest := h r (List.mem_range.mp hr)
        simp only [ladner_wordVerdict, decide_eq_true_eq] at htest
        simpa only [he] using htest.2.2
    have hlen : decide ((pairFstD C).length =
        (ladner_values (pairSndD (pairSndD C))).length) = true := decide_eq_true hc.1
    have hindex : decide (LogProg.bitsVal (pairFstD (pairSndD C)) <
        Nat.log 2 (Nat.log 2 (pairFstD C).length)) = true := decide_eq_true hc.2
    simp only [ladner_candidate, Bool.decide_and, hlen, hindex, Bool.true_and, hequiv]
  · rw [if_neg hc]
    have hn : ¬ ((pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
        LogProg.bitsVal (pairFstD (pairSndD C)) < Nat.log 2 (Nat.log 2 (pairFstD C).length) ∧
        ∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) := by
      rintro ⟨hn, hi, -⟩
      exact hc ⟨hn, hi⟩
    simp only [ladner_candidate, hn, decide_false]

/-- The polynomial-time candidate test is the guarded readout of the existing bounded
iterator; no Ladner target is used or proved here.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the single-word FP verdict in the scan transition, the FP unary
initialization, and the linear bound on every scan state. Run `2(|C|+1)` rounds through
`BinArith.polyTimeComputable_iterate`, then read and mask its flag by the context guard. -/
private theorem ladner_candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [ladner_candidate S]) := by
  have hstep := ladner_testStep_FP (ladner_wordVerdict_FP linear)
  have hloop := BinArith.polyTimeComputable_iterate hstep ladner_testInit_FP 2 1 12 1
    (fun C j _ => ladner_test_size C j)
  have hflag := BinArith.polyTimeComputable_slot4.comp hloop
  convert polyTimeComputable_ite ladner_ctxGuard_FP hflag (polyTimeComputable_const [false]) using 1
  funext C
  simpa only [Function.comp_apply, ladner_testOut, decide_eq_true_eq] using ladner_candidate_readout C

end Complexity
```

## ===== TCSlib/Complexity/ClassP/BinaryArith/Loops.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.CircuitComplexity.UnaryCode
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counted loops, unary numbers and word tools in polynomial time

Generic polynomial-time word functions on `Turing.pairEncode`-structured inputs, shared by
the randomized algorithms of [AB09, §7.2.3–7.2.4]: a counted loop (a host: run a step once
per letter of a unary counter), the reading of unary numbers, the lookup of an entry in an
encoded list of words (`Complexity.BinArith.encWords`), word equality, unary multiplication,
and the cutting of a word into blocks. Not themselves results of the book.

## Main definitions

* `Complexity.BinArith.forLoop` — run a step once per letter of a unary counter.
* `Complexity.BinArith.uHead`, `Complexity.BinArith.uRest`, `Complexity.BinArith.hasFalse` —
  the leading `1`s of a word, the rest after the first `0`, and whether there is a `0`.
* `Complexity.BinArith.getW` — the `j`-th entry of an encoded list of words.
* `Complexity.BinArith.eqW` — equality of the two components of a pair.
* `Complexity.BinArith.mulU` — unary multiplication (`|a|` copies of `b` on `⟨a, b⟩`).
* `Complexity.BinArith.chunkW`, `Complexity.BinArith.chunkList` — cutting a word into blocks
  of `|c|` bits, as a list of words.

## Main results

* `Complexity.BinArith.forLoop_pairEncode`, `Complexity.BinArith.polyTimeComputable_forLoop`,
  `Complexity.BinArith.forLoop_bound_of_ctx` — the counted loop and its time bound.
* `Complexity.BinArith.decodeNat_eq` — `BoolCircuit.decodeNat` through `uHead` and `uRest`.
* `Complexity.BinArith.getW_pairEncode`, `Complexity.BinArith.polyTimeComputable_getW`.
* `Complexity.BinArith.eqW_pairEncode`, `Complexity.BinArith.length_mulU`,
  `Complexity.BinArith.chunkW_pairEncode` — what they compute, and their
  `polyTimeComputable_*` lemmas.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Complexity

namespace BinArith

open Turing
open Complexity.LogProg (bitsVal eq_of_bitsVal_eq)

/-- Composition in applied form: `x ↦ f (g x)` is polynomial-time when `f` and `g` are.  (Stated
with an applied body so that unification never unfolds `f`.) -/
theorem polyTimeComputable_app {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (fun x => f (g x)) :=
  hf.comp hg

/-- A one-bit test of a polynomial-time function, in applied form. -/
theorem polyTimeComputable_test_app {p : List Bool → Bool} {g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => [p (g x)]) :=
  hp.comp hg

/-! ### The counted loop -/

/-- One round of the counted loop on `⟨c, d⟩`: if `c ≠ []`, drop a letter of `c` and apply
`f` to `d`; a state with empty (or malformed) counter is fixed. -/
def forStep (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  if isNilB (pairFstD S) then S else pairEncode ((pairFstD S).drop 1) (f (pairSndD S))

/-- The counted loop: `|S| + 1` rounds of `forStep f` from `S`. -/
def forLoop (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  (forStep f)^[1 * (S.length + 1) ^ 1] S

/-- The rounds of the counted loop from `⟨c, d⟩`. -/
theorem iterate_forStep (f : List Bool → List Bool) (c d : List Bool) (i : ℕ) :
    (forStep f)^[i] (pairEncode c d) = pairEncode (c.drop i) (f^[min i c.length] d) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : c.length ≤ i
    · have h1 : min i c.length = c.length := by omega
      have h2 : min (i + 1) c.length = c.length := by omega
      simp [forStep, isNilB, List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega :
        c.length ≤ i + 1), h1, h2]
    · have hne : c.drop i ≠ [] := by simp; omega
      have h1 : min i c.length = i := by omega
      have h2 : min (i + 1) c.length = i + 1 := by omega
      simp only [forStep, pairFstD_pairEncode, pairSndD_pairEncode, isNilB, hne,
        decide_false, Bool.false_eq_true, if_false, List.drop_drop, h1, h2,
        Function.iterate_succ_apply']

/-- **The counted loop runs `f` once per letter of the counter**:
`forLoop f ⟨c, d⟩ = ⟨[], f^[|c|] d⟩`. -/
theorem forLoop_pairEncode (f : List Bool → List Bool) (c d : List Bool) :
    forLoop f (pairEncode c d) = pairEncode [] (f^[c.length] d) := by
  unfold forLoop
  rw [iterate_forStep, List.drop_eq_nil_of_le (by simp [length_pairEncode]; omega)]
  congr 2
  simp [length_pairEncode]
  omega

/-- A state whose counter is empty is fixed by the round. -/
theorem forStep_of_fst_nil (f : List Bool → List Bool) {S : List Bool} (h : pairFstD S = []) :
    forStep f S = S := by
  simp [forStep, isNilB, h]

/-- **The counted loop is polynomial-time** when its body is and the iterates `f^[j] d`,
`j ≤ |c|`, stay inside a polynomial envelope of `|⟨c, d⟩|`.

**Proof sketch.** `forLoop f` is `polyTimeComputable_iterate` of the round `forStep f` (an
`ite` of polynomial-time pieces) from the input. A word that is not a pair has empty counter
and is fixed; on `⟨c, d⟩` the `i`-th iterate is `⟨c.drop i, f^[min i |c|] d⟩`
(`iterate_forStep`), whose length the envelope bounds. -/
theorem polyTimeComputable_forLoop {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (B b : ℕ) (hbound : ∀ c d j, j ≤ c.length →
      (f^[j] d).length ≤ B * ((pairEncode c d).length + 1) ^ b) :
    PolyTimeComputable (forLoop f) := by
  have hstep : PolyTimeComputable (forStep f) := by
    unfold forStep
    exact polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      polyTimeComputable_id
      ((polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
        (hf.comp polyTimeComputable_pairSndD))
  refine polyTimeComputable_iterate hstep polyTimeComputable_id 1 1 (B + 2) (b + 1)
    (fun S i _ => ?_)
  simp only [id]
  have hP : 1 ≤ (S.length + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hpow : (S.length + 1) ^ (b + 1) = (S.length + 1) ^ b * (S.length + 1) := pow_succ _ _
  have h5 : S.length + 1 ≤ (S.length + 1) ^ b * (S.length + 1) := Nat.le_mul_of_pos_left _ hP
  rw [hpow]
  cases hd : pairDecode S with
  | none =>
    have h0 : pairFstD S = [] := by simp [pairFstD, hd]
    rw [Function.iterate_fixed (forStep_of_fst_nil f h0)]
    nlinarith
  | some cd =>
    obtain ⟨c, d⟩ := cd
    have hS := eq_pairEncode_of_pairDecode S c d hd
    have h1 := hbound c d (min i c.length) (by omega)
    rw [← hS] at h1
    rw [hS, iterate_forStep, length_pairEncode]
    rw [← hS]
    have h2 : (c.drop i).length ≤ c.length := by simp
    have h3 : 2 * c.length + 2 ≤ S.length := by rw [hS]; simp [length_pairEncode]
    have h6 : B * (S.length + 1) ^ b ≤ B * ((S.length + 1) ^ b * (S.length + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    nlinarith

/-- An iterate bound for context-preserving bodies: if `f ⟨q, ·⟩` keeps `q` and grows the
word by at most `A(|q| + 1)`, then `|f^[j] d| ≤ |d| + jA(|q| + 1)`. -/
theorem length_iterate_le_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) (d : List Bool) (j : ℕ) :
    (f^[j] d).length ≤ d.length + j * (A * ((pairFstD d).length + 1)) := by
  have hq : ∀ j, pairFstD (f^[j] d) = pairFstD d := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hctx, ih]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have := hlen (f^[j] d)
    rw [hq j] at this
    rw [Nat.succ_mul]
    omega

/-- The envelope required by `polyTimeComputable_forLoop`, for context-preserving bodies of
bounded growth. -/
theorem forLoop_bound_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) :
    ∀ c d j, j ≤ c.length → (f^[j] d).length ≤ (A + 1) * ((pairEncode c d).length + 1) ^ 2 := by
  intro c d j hj
  have h := length_iterate_le_of_ctx A hctx hlen d j
  have hq := length_pairFstD_le d
  have hN : c.length + d.length ≤ (pairEncode c d).length := by simp [length_pairEncode]; omega
  set N := (pairEncode c d).length
  have h1 : j * (A * ((pairFstD d).length + 1)) ≤ N * (A * (N + 1)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  nlinarith

/-! ### Unary numbers -/

/-- The transition of `uHead`: stay live while reading `1`s. -/
private def headδ (q b : Bool) : Bool := q && b

/-- The emission of `uHead`: copy the `1`s of the live phase. -/
private def headO (q b : Bool) : Option Bool := if q && b then some true else none

/-- The leading `1`s of a word (`1ʲ` on `1ʲ0w`). -/
def uHead (w : List Bool) : List Bool := transduce headδ headO true w

/-- The transition of `uRest`: switch on at the first `0`. -/
private def restδ (q b : Bool) : Bool := q || !b

/-- The emission of `uRest`: copy everything after the first `0`. -/
private def restO (q b : Bool) : Option Bool := if q then some b else none

/-- The word after the first `0` (`w` on `1ʲ0w`; `[]` if there is no `0`). -/
def uRest (w : List Bool) : List Bool := transduce restδ restO false w

/-- Whether a word contains a `0`. -/
def hasFalse (w : List Bool) : Bool := (w.map not).any id

/-- The `uHead` transducer emits nothing once off. -/
private theorem transduce_head_false (w : List Bool) : transduce headδ headO false w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [transduce, headδ, headO, ih]

/-- The `uRest` transducer copies everything once on. -/
private theorem transduce_rest_true (w : List Bool) : transduce restδ restO true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [transduce, restδ, restO, ih]

/-- `uHead` on `0w` is empty. -/
@[simp] theorem uHead_false_cons (w : List Bool) : uHead (false :: w) = [] := by
  simp [uHead, transduce, headδ, headO, transduce_head_false]

/-- `uHead` on `1w`. -/
@[simp] theorem uHead_true_cons (w : List Bool) : uHead (true :: w) = true :: uHead w := by
  simp [uHead, transduce, headδ, headO]

/-- `uRest` on `0w` is `w`. -/
@[simp] theorem uRest_false_cons (w : List Bool) : uRest (false :: w) = w := by
  simp [uRest, transduce, restδ, restO, transduce_rest_true]

/-- `uRest` on `1w`. -/
@[simp] theorem uRest_true_cons (w : List Bool) : uRest (true :: w) = uRest w := by
  simp [uRest, transduce, restδ, restO]

/-- `uHead []` is empty. -/
@[simp] theorem uHead_nil : uHead [] = [] := rfl

/-- `uRest []` is empty. -/
@[simp] theorem uRest_nil : uRest [] = [] := rfl

/-- `hasFalse` on a cons. -/
@[simp] theorem hasFalse_cons (b : Bool) (w : List Bool) :
    hasFalse (b :: w) = (!b || hasFalse w) := by
  simp [hasFalse]

/-- `[]` has no `0`. -/
@[simp] theorem hasFalse_nil : hasFalse [] = false := rfl

/-- **Reading a unary number**: `decodeNat w` is `(|uHead w|, uRest w)` if `w` has a `0`. -/
theorem decodeNat_eq (w : List Bool) :
    BoolCircuit.decodeNat w =
      if hasFalse w then some ((uHead w).length, uRest w) else none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.decodeNat]
    · simp only [BoolCircuit.decodeNat, ih, uHead_true_cons, uRest_true_cons, hasFalse_cons,
        Bool.not_true, Bool.false_or, List.length_cons]
      split <;> simp

/-- Reading `1ʲ0w`. -/
theorem uHead_encodeNat (j : ℕ) (w : List Bool) :
    uHead (BoolCircuit.encodeNat j ++ w) = List.replicate j true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- The rest of `1ʲ0w` is `w`. -/
theorem uRest_encodeNat (j : ℕ) (w : List Bool) :
    uRest (BoolCircuit.encodeNat j ++ w) = w := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- `1ʲ0w` has a `0`. -/
theorem hasFalse_encodeNat (j : ℕ) (w : List Bool) :
    hasFalse (BoolCircuit.encodeNat j ++ w) = true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat]
  | succ j ih => simpa [BoolCircuit.encodeNat, List.replicate_succ] using ih

/-- A word with a `0` is `1ʲ0w` for `1ʲ = uHead`, `w = uRest`. -/
theorem eq_encodeNat_of_hasFalse {w : List Bool} (h : hasFalse w = true) :
    w = BoolCircuit.encodeNat (uHead w).length ++ uRest w := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.encodeNat]
    · simp only [hasFalse_cons, Bool.not_true, Bool.false_or] at h
      have := ih h
      simp only [uHead_true_cons, uRest_true_cons, List.length_cons, BoolCircuit.encodeNat,
        List.replicate_succ, List.cons_append] at this ⊢
      exact congrArg _ this

/-- `uRest w` is no longer than `w`. -/
theorem length_uRest_le (w : List Bool) : (uRest w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uRest_true_cons, List.length_cons]; omega

/-- `uHead w` is no longer than `w`. -/
theorem length_uHead_le (w : List Bool) : (uHead w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uHead_true_cons, List.length_cons]; omega

/-- `uHead` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uHead : PolyTimeComputable uHead :=
  polyTimeComputable_transduce headδ headO true

/-- `uRest` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uRest : PolyTimeComputable uRest :=
  polyTimeComputable_transduce restδ restO false

/-- `hasFalse` is polynomial-time (negate, then test for a `1`). -/
theorem polyTimeComputable_hasFalse : PolyTimeComputable (fun w => [hasFalse w]) := by
  have hneg : PolyTimeComputable (transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) ()) :=
    polyTimeComputable_transduce _ _ ()
  have heq : ∀ w : List Bool,
      transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) () w = w.map not := by
    intro w
    induction w with
    | nil => rfl
    | cons b w ih => simp [transduce, ih]
  convert polyTimeComputable_any.comp hneg using 1
  funext w
  simp [hasFalse, heq]

/-! ### Lookup in a list of words -/

/-- The entry of index `|J|` of the list encoded in `L`, on `⟨J, L⟩` (`[]` past the end). -/
def getW (z : List Bool) : List Bool := pairFstD (pairSndD (forLoop pairSndD z))

/-- Peeling `j` entries of an encoded list. -/
theorem iterate_pairSndD_encWords (L : List (List Bool)) (j : ℕ) :
    pairSndD^[j] (encWords L) = encWords (L.drop j) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases L with
    | nil => exact iterate_pairSndD_nil j
    | cons w L => simp [ih]

/-- **Lookup**: `getW ⟨J, [w₀, …]⟩ = w_{|J|}` (`[]` past the end). -/
theorem getW_pairEncode (J : List Bool) (L : List (List Bool)) :
    getW (pairEncode J (encWords L)) = L.getD J.length [] := by
  rw [getW, forLoop_pairEncode, pairSndD_pairEncode, iterate_pairSndD_encWords,
    List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases L.drop J.length with
  | nil => rfl
  | cons w L' => simp

/-- Lookup in a list of binary numbers: the value of the entry, `0` past the end. -/
theorem getW_pairEncode_bits (J : List Bool) (vs : List ℕ) :
    getW (pairEncode J (encWords (vs.map Nat.bits))) = Nat.bits (vs.getD J.length 0) := by
  rw [getW_pairEncode]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[J.length]? <;> simp [Nat.zero_bits]

/-- Lookup is polynomial-time. -/
theorem polyTimeComputable_getW : PolyTimeComputable getW := by
  have hl : PolyTimeComputable (forLoop pairSndD) := by
    refine polyTimeComputable_forLoop polyTimeComputable_pairSndD 1 1 (fun c d j _ => ?_)
    have := length_iterate_pairSndD_le d j
    simp [length_pairEncode]
    omega
  exact polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hl)

/-! ### Equality, unary multiplication and cutting into blocks -/

/-- Either both projections are empty or the word is the pair of its projections. -/
private theorem pair_cases (z : List Bool) :
    (pairFstD z = [] ∧ pairSndD z = []) ∨ z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => left; simp [pairFstD, pairSndD, hd]
  | some ab =>
    right
    obtain ⟨a, b⟩ := ab
    simpa [pairFstD, pairSndD, hd] using eq_pairEncode_of_pairDecode z a b hd

/-- Word equality on `⟨a, b⟩`: equal lengths and equal values. -/
def eqW (z : List Bool) : Bool :=
  decide ((pairFstD z).length = (pairSndD z).length) && beq z

/-- `eqW ⟨a, b⟩` decides `a = b`. -/
theorem eqW_pairEncode (a b : List Bool) : eqW (pairEncode a b) = decide (a = b) := by
  simp only [eqW, beq, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hc
    push_neg at hc
    exact h (eq_of_bitsVal_eq hc.1 hc.2)

/-- Word equality is polynomial-time. -/
theorem polyTimeComputable_eqW : PolyTimeComputable (fun z => [eqW z]) :=
  polyTimeComputable_and polyTimeComputable_lenEq polyTimeComputable_beq

/-- One round of unary multiplication on `⟨b, acc⟩`: append `b` to `acc`. -/
private def mulUStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (pairSndD d ++ pairFstD d)

/-- Unary multiplication: on `⟨a, b⟩`, `|a|` copies of `b`. -/
def mulU (z : List Bool) : List Bool :=
  pairSndD (pairSndD (forLoop mulUStep (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))

/-- The rounds of unary multiplication. -/
private theorem iterate_mulUStep (b acc : List Bool) (j : ℕ) :
    mulUStep^[j] (pairEncode b acc) = pairEncode b (acc ++ (List.replicate j b).flatten) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [mulUStep, List.replicate_succ', List.flatten_append]

/-- `|mulU ⟨a, b⟩| = |a| · |b|`. -/
theorem length_mulU (a b : List Bool) : (mulU (pairEncode a b)).length = a.length * b.length := by
  simp [mulU, forLoop_pairEncode, iterate_mulUStep, List.length_flatten, List.sum_replicate]

/-- Unary multiplication is polynomial-time. -/
theorem polyTimeComputable_mulU : PolyTimeComputable mulU := by
  have hs : PolyTimeComputable mulUStep :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairSndD.append
      polyTimeComputable_pairFstD)
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2
    (fun d => by simp [mulUStep]) (fun d => by
      rcases pair_cases d with ⟨h1, h2⟩ | h
      · simp [mulUStep, h1, h2, length_pairEncode]
      · obtain ⟨a, b, rfl⟩ : ∃ a b, d = pairEncode a b := ⟨_, _, h⟩
        simp [mulUStep, length_pairEncode]; omega))
  exact polyTimeComputable_slot3.comp (hl.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))))

/-- One round of cutting on `⟨c, ⟨rest, acc⟩⟩`: move the first `|c|` bits of `rest` to a new
entry of the word list `acc`; fixed once `rest` is empty. -/
private def chunkStep (d : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD d)) then d
  else pairEncode (pairFstD d)
    (pairEncode (PrefixByLength.drop (pairEncode (pairFstD d) (pairFstD (pairSndD d))))
      (pairSndD (pairSndD d) ++
        pairEncode (PrefixByLength.take (pairEncode (pairFstD d) (pairFstD (pairSndD d)))) []))

/-- Cutting `w` into blocks of `|c|` bits, on `⟨c, w⟩`; the result is a word list. -/
def chunkW (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (forLoop chunkStep
    (pairEncode (pairSndD z) (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))))

/-- The first `N` blocks of `c` bits of `w`. -/
def chunkList (c : ℕ) (w : List Bool) (N : ℕ) : List (List Bool) :=
  (List.range N).map fun i => (w.drop (i * c)).take c

/-- A round of cutting on a genuine state. -/
private theorem chunkStep_pairEncode (c rest acc : List Bool) :
    chunkStep (pairEncode c (pairEncode rest acc)) = if rest = [] then
      pairEncode c (pairEncode rest acc) else pairEncode c (pairEncode (rest.drop c.length)
        (acc ++ pairEncode (rest.take c.length) [])) := by
  simp [chunkStep, isNilB, PrefixByLength.take, PrefixByLength.drop]

/-- `N` rounds of cutting a word of `N` blocks. -/
private theorem iterate_chunkStep (c : List Bool) :
    ∀ (N : ℕ) (w : List Bool) (L : List (List Bool)), w.length = N * c.length →
      (0 < c.length ∨ N = 0) → chunkStep^[N] (pairEncode c (pairEncode w (encWords L))) =
        pairEncode c (pairEncode [] (encWords (L ++ chunkList c.length w N)))
  | 0, w, L, h, _ => by simp_all [chunkList]
  | N + 1, w, L, h, hc => by
    have hc' : 0 < c.length := by omega
    have hw : w ≠ [] := by rintro rfl; simp at h; simp [h] at hc'
    rw [Function.iterate_succ_apply, chunkStep_pairEncode, if_neg hw,
      ← encWords_append_singleton,
      iterate_chunkStep c N _ _ (by simp [h, Nat.succ_mul]) (Or.inl hc')]
    congr 3
    simp only [chunkList, List.range_succ_eq_map, List.map_cons, List.map_map, zero_mul,
      List.drop_zero, List.append_assoc, List.singleton_append]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- **Cutting into blocks**: if `|w| = N·|c|` then `chunkW ⟨c, w⟩` lists the `N` blocks. -/
theorem chunkW_pairEncode (c w : List Bool) (N : ℕ) (h : w.length = N * c.length)
    (hc : 0 < c.length ∨ N = 0) :
    chunkW (pairEncode c w) = encWords (chunkList c.length w N) := by
  have hN : N ≤ w.length := by
    rcases hc with hc | rfl
    · rw [h]; exact Nat.le_mul_of_pos_right _ hc
    · exact Nat.zero_le _
  have he := iterate_chunkStep c N w [] h hc
  simp only [encWords, List.flatMap_nil, List.nil_append] at he
  simp only [chunkW, pairFstD_pairEncode, pairSndD_pairEncode, forLoop_pairEncode]
  rw [show w.length = (w.length - N) + N by omega, Function.iterate_add_apply, he,
    Function.iterate_fixed (by rw [chunkStep_pairEncode, if_pos rfl])]
  simp [encWords]

/-- Cutting is polynomial-time.

**Proof sketch.** The round is assembled from the projections, the prefix operations and
`polyTimeComputable_ite`; it keeps `c` and grows a genuine state by `2` bits (the moved bits
are re-encoded once), so `forLoop_bound_of_ctx` bounds the counted loop. -/
theorem polyTimeComputable_chunkW : PolyTimeComputable chunkW := by
  have hcr := polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2
  have hs : PolyTimeComputable chunkStep := by
    unfold chunkStep
    exact polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
      polyTimeComputable_id (polyTimeComputable_pairFstD.pairEncode
        ((polyTimeComputable_dropPrefixByLength.comp hcr).pairEncode
          (polyTimeComputable_slot3.append
            ((polyTimeComputable_takePrefixByLength.comp hcr).pairEncode
              (polyTimeComputable_const [])))))
  have hctx : ∀ d, pairFstD (chunkStep d) = pairFstD d := fun d => by
    unfold chunkStep; split_ifs <;> simp
  have hlen : ∀ d, (chunkStep d).length ≤ d.length + 2 * ((pairFstD d).length + 1) := by
    intro d
    by_cases hr : pairFstD (pairSndD d) = []
    · simp [chunkStep, isNilB, hr]
    rcases pair_cases d with ⟨-, h2⟩ | h
    · simp [h2, pairFstD, pairDecode] at hr
    obtain ⟨c, S, rfl⟩ : ∃ c S, d = pairEncode c S := ⟨_, _, h⟩
    simp only [pairSndD_pairEncode] at hr
    rcases pair_cases S with ⟨h1, -⟩ | hS
    · exact absurd h1 hr
    obtain ⟨rest, acc, rfl⟩ : ∃ a b, S = pairEncode a b := ⟨_, _, hS⟩
    simp only [pairFstD_pairEncode] at hr
    rw [chunkStep_pairEncode, if_neg hr]
    simp only [length_pairEncode, List.length_append, List.length_drop, List.length_take,
      List.length_nil, pairFstD_pairEncode]
    omega
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2 hctx hlen)
  exact (polyTimeComputable_pairSndD.comp polyTimeComputable_slot3).comp
    (hl.comp (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])))))

end BinArith

end Complexity
```

## ===== TCSlib/Complexity/ClassP/BinaryArith/Words.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lists of words in polynomial time

Infrastructure for [AB09 §7.2]; not itself a result of the book. A list of words
`[w₁, …, wₖ]` is the word `⟨w₁, ⟨w₂, … ⟨wₖ, []⟩ …⟩⟩` (`Complexity.BinArith.encWords`). Every word
is read as a list by `Complexity.BinArith.decWords`, which peels first components until the
empty word, so the loops below are specified on all words. Vectors and matrices of numbers
(the determinant of `TCSlib.Complexity.ClassP.BinaryArith.DetMod`) are lists of such lists.

## Main definitions

* `Complexity.BinArith.encWords`, `Complexity.BinArith.decWords` — encoding and reading.
* `Complexity.BinArith.mapW`, `Complexity.BinArith.zipWithW` — map (with a shared parameter)
  and zip of word-level functions over encoded lists.
* `Complexity.BinArith.countW` — the number of entries, in unary.

## Main results

* `Complexity.BinArith.polyTimeComputable_mapW`, `Complexity.BinArith.mapW_pairEncode`.
* `Complexity.BinArith.polyTimeComputable_zipWithW`, `Complexity.BinArith.zipWithW_pairEncode`.
* `Complexity.BinArith.polyTimeComputable_countW`, `Complexity.BinArith.countW_eq`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Encoding and reading -/

/-- A list of words, as the concatenation of the pairs `⟨w, []⟩`. -/
def encWords (L : List (List Bool)) : List Bool := L.flatMap (fun w => pairEncode w [])

/-- A pair with empty second component, followed by `b`, is the pair `⟨a, b⟩`. -/
theorem pairEncode_nil_append (a b : List Bool) : pairEncode a [] ++ b = pairEncode a b := by
  simp [pairEncode]

/-- The empty list is the empty word. -/
@[simp] theorem encWords_nil : encWords [] = [] := rfl

/-- `encWords (w :: L) = ⟨w, encWords L⟩`. -/
@[simp] theorem encWords_cons (w : List Bool) (L : List (List Bool)) :
    encWords (w :: L) = pairEncode w (encWords L) := by
  simp [encWords, pairEncode_nil_append]

/-- Appending one word at the end of an encoded list. -/
theorem encWords_append_singleton (L : List (List Bool)) (w : List Bool) :
    encWords (L ++ [w]) = encWords L ++ pairEncode w [] := by
  simp [encWords]

/-- The length of an encoded list. -/
theorem length_encWords (L : List (List Bool)) :
    (encWords L).length = (L.map (fun w => 2 * w.length + 2)).sum := by
  induction L with
  | nil => rfl
  | cons w L ih => simp [length_pairEncode, ih]

/-- An encoded list of `k` words of length at most `c` has length at most `k(2c + 2)`. -/
theorem length_encWords_le (L : List (List Bool)) (c : ℕ) (h : ∀ w ∈ L, w.length ≤ c) :
    (encWords L).length ≤ L.length * (2 * c + 2) := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [encWords_cons, length_pairEncode, List.length_cons]
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    nlinarith

/-- The second projection of a nonempty word is strictly shorter. -/
theorem length_pairSndD_lt {w : List Bool} (h : w ≠ []) : (pairSndD w).length < w.length := by
  cases hd : pairDecode w with
  | none => simp [pairSndD, hd]; exact List.length_pos_iff.mpr h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode w a b hd
    rw [hz, pairSndD_pairEncode, length_pairEncode]
    omega

/-- Read a word as a list of words: peel first components until the empty word. -/
def decWords (w : List Bool) : List (List Bool) :=
  if _h : w = [] then [] else pairFstD w :: decWords (pairSndD w)
termination_by w.length
decreasing_by exact length_pairSndD_lt ‹_›

/-- The reading of the empty word. -/
@[simp] theorem decWords_nil : decWords [] = [] := by rw [decWords]; simp

/-- The reading of a nonempty word. -/
theorem decWords_of_ne {w : List Bool} (h : w ≠ []) :
    decWords w = pairFstD w :: decWords (pairSndD w) := by
  rw [decWords]; simp [h]

/-- Reading an encoded list gives the list back. -/
@[simp] theorem decWords_encWords (L : List (List Bool)) : decWords (encWords L) = L := by
  induction L with
  | nil => simp
  | cons w L ih =>
    rw [encWords_cons, decWords_of_ne (by simp [pairEncode]), pairFstD_pairEncode,
      pairSndD_pairEncode, ih]

/-- A word holds at most as many list entries as it has letters. -/
theorem length_decWords_le (w : List Bool) : (decWords w).length ≤ w.length := by
  by_cases hw : w = []
  · simp [hw]
  · rw [decWords_of_ne hw, List.length_cons]
    have := length_pairSndD_lt hw
    have := length_decWords_le (pairSndD w)
    omega
termination_by w.length
decreasing_by exact length_pairSndD_lt hw

/-- Every entry of a word's list is no longer than the word. -/
theorem length_le_of_mem_decWords {w x : List Bool} (hx : x ∈ decWords w) :
    x.length ≤ w.length := by
  by_cases hw : w = []
  · simp [hw] at hx
  · rw [decWords_of_ne hw, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact length_pairFstD_le w
    · have := length_pairSndD_lt hw
      have := length_le_of_mem_decWords hx
      omega
termination_by w.length
decreasing_by exact length_pairSndD_lt hw

/-! ### The list loop -/

/-- Iterated second projections stay inside the word. -/
theorem length_iterate_pairSndD_le (w : List Bool) (i : ℕ) :
    (pairSndD^[i] w).length ≤ w.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih

/-- The emptiness of iterated second projections of the empty word. -/
theorem iterate_pairSndD_nil (i : ℕ) : pairSndD^[i] ([] : List Bool) = [] :=
  Function.iterate_fixed rfl i

/-- **The list loop**: over `N ≥ |w|` rounds, emitting `c x` for the head `x` of each nonempty
suffix `pairSndD^[i] w` outputs the concatenation of `c` over the list read from `w`. -/
theorem flatMap_listLoop (c : List Bool → List Bool) :
    ∀ (N : ℕ) (w : List Bool), w.length ≤ N →
      (List.range N).flatMap (fun i => if pairSndD^[i] w = [] then []
        else c (pairFstD (pairSndD^[i] w))) = (decWords w).flatMap c := by
  intro N
  induction N with
  | zero => intro w hw; simp [List.eq_nil_of_length_eq_zero (by omega : w.length = 0)]
  | succ N ih =>
    intro w hw
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Nat.succ_eq_add_one, Function.iterate_succ_apply]
    by_cases h : w = []
    · subst h
      have := ih [] (by simp)
      simp only [pairSndD, pairDecode, Option.map_none, Option.getD_none, if_true,
        List.nil_append] at this ⊢
      simpa using this
    · rw [if_neg h, ih (pairSndD w) (by have := length_pairSndD_lt h; omega),
        decWords_of_ne h, List.flatMap_cons]

/-! ### Map -/

/-- One round of the map loop on `⟨q, list⟩`: drop the head entry. -/
private def listStep (S : List Bool) : List Bool := pairEncode (pairFstD S) (pairSndD (pairSndD S))

/-- The chunk of the map loop on `⟨q, list⟩`: `⟨g ⟨q, head⟩, []⟩` for a nonempty list. -/
private def mapChunk (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  if pairSndD S = [] then []
  else pairEncode (g (pairEncode (pairFstD S) (pairFstD (pairSndD S)))) []

/-- The map loop on `⟨q, list⟩` applying `g ⟨q, ·⟩` to every entry. -/
def mapW (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  (List.range (1 * (S.length + 1) ^ 1 + 1)).flatMap (fun i => mapChunk g (listStep^[i] S))

/-- The iterates of the map loop from `⟨q, w⟩`. -/
private theorem iterate_listStep (q w : List Bool) (i : ℕ) :
    listStep^[i] (pairEncode q w) = pairEncode q (pairSndD^[i] w) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [listStep]

/-- **The map loop maps**: on `⟨q, w⟩` it outputs the encoded list `g ⟨q, x⟩` over the entries
`x` read from `w`. -/
theorem mapW_pairEncode (g : List Bool → List Bool) (q w : List Bool) :
    mapW g (pairEncode q w) = encWords ((decWords w).map (fun x => g (pairEncode q x))) := by
  unfold mapW
  simp only [iterate_listStep, mapChunk, pairSndD_pairEncode, pairFstD_pairEncode]
  rw [flatMap_listLoop (fun x => pairEncode (g (pairEncode q x)) []) _ w
    (by simp [length_pairEncode]; omega)]
  simp [encWords, List.flatMap_map]

/-- **The map loop is polynomial-time** for a polynomial-time `g`.

**Proof sketch.** The round drops the head entry and the emitted chunk is `g` of it; after
`i` rounds the state is `⟨q, l⟩` with `l` a suffix of the input list (`iterate_listStep`), so
the emit loop `Complexity.polyTimeComputable_emitIter` applies with a linear bound. -/
theorem polyTimeComputable_mapW {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (mapW g) := by
  have hs : PolyTimeComputable listStep :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot3
  have he : PolyTimeComputable (mapChunk g) := by
    unfold mapChunk
    convert polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_const [])
      ((hg.comp (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2)).pairEncode
        (polyTimeComputable_const [])) using 1
    funext S; simp
  refine polyTimeComputable_emitIter hs he 1 1 2 1 (fun w i => ?_)
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply, show listStep w = pairEncode (pairFstD w) (pairSndD
      (pairSndD w)) from rfl, iterate_listStep, length_pairEncode]
    have h1 := length_iterate_pairSndD_le (pairSndD (pairSndD w)) i
    have h2 := length_pair_components_le w
    have h3 := length_pairSndD_le (pairSndD w)
    simp; omega

/-! ### Zip -/

/-- One round of the zip loop on `⟨q, ⟨l₁, l₂⟩⟩`: drop the head entries of both lists. -/
private def zipStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairEncode (pairSndD (pairFstD (pairSndD S))) (pairSndD (pairSndD (pairSndD S))))

/-- The chunk of the zip loop: `⟨g ⟨q, ⟨x, y⟩⟩, []⟩` for the heads `x`, `y` of two nonempty
lists. -/
private def zipChunk (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  if pairFstD (pairSndD S) = [] ∨ pairSndD (pairSndD S) = [] then []
  else pairEncode (g (pairEncode (pairFstD S) (pairEncode (pairFstD (pairFstD (pairSndD S)))
    (pairFstD (pairSndD (pairSndD S)))))) []

/-- The zip loop on `⟨q, ⟨l₁, l₂⟩⟩` applying `g ⟨q, ⟨x, y⟩⟩` to paired entries. -/
def zipWithW (g : List Bool → List Bool) (S : List Bool) : List Bool :=
  (List.range (1 * (S.length + 1) ^ 1 + 1)).flatMap (fun i => zipChunk g (zipStep^[i] S))

/-- The iterates of the zip loop from `⟨q, ⟨l₁, l₂⟩⟩`. -/
private theorem iterate_zipStep (q l₁ l₂ : List Bool) (i : ℕ) :
    zipStep^[i] (pairEncode q (pairEncode l₁ l₂)) =
      pairEncode q (pairEncode (pairSndD^[i] l₁) (pairSndD^[i] l₂)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp [zipStep]

/-- The zip loop body over `N ≥ |l₁|` rounds zips the two lists read from `l₁`, `l₂`.

**Proof sketch.** Induction on `N`: round `0` emits `c` of the two head entries, or nothing
when a list is empty, and the remaining rounds are the statement for the tails
(`decWords_of_ne`). -/
private theorem flatMap_zipLoop (c : List Bool → List Bool → List Bool) :
    ∀ (N : ℕ) (l₁ l₂ : List Bool), l₁.length ≤ N →
      (List.range N).flatMap (fun i =>
        if pairSndD^[i] l₁ = [] ∨ pairSndD^[i] l₂ = [] then []
        else c (pairFstD (pairSndD^[i] l₁)) (pairFstD (pairSndD^[i] l₂))) =
        (List.zipWith c (decWords l₁) (decWords l₂)).flatMap id := by
  intro N
  induction N with
  | zero =>
    intro l₁ l₂ h
    simp [List.eq_nil_of_length_eq_zero (by omega : l₁.length = 0)]
  | succ N ih =>
    intro l₁ l₂ h
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Nat.succ_eq_add_one, Function.iterate_succ_apply]
    have hlen : (pairSndD l₁).length ≤ N := by
      by_cases h1 : l₁ = []
      · subst h1; simp [pairSndD, pairDecode]
      · have := length_pairSndD_lt h1; omega
    rw [ih (pairSndD l₁) (pairSndD l₂) hlen]
    by_cases h1 : l₁ = []
    · subst h1; simp [show pairSndD ([] : List Bool) = [] from rfl]
    by_cases h2 : l₂ = []
    · subst h2; simp [show pairSndD ([] : List Bool) = [] from rfl]
    rw [if_neg (by tauto), decWords_of_ne h1, decWords_of_ne h2]
    simp

/-- **The zip loop zips**: on `⟨q, ⟨l₁, l₂⟩⟩` it outputs the encoded list of `g ⟨q, ⟨x, y⟩⟩`
over the paired entries read from `l₁` and `l₂` (truncated to the shorter list). -/
theorem zipWithW_pairEncode (g : List Bool → List Bool) (q l₁ l₂ : List Bool) :
    zipWithW g (pairEncode q (pairEncode l₁ l₂)) =
      encWords (List.zipWith (fun x y => g (pairEncode q (pairEncode x y)))
        (decWords l₁) (decWords l₂)) := by
  unfold zipWithW
  simp only [iterate_zipStep, zipChunk, pairSndD_pairEncode, pairFstD_pairEncode]
  rw [flatMap_zipLoop (fun x y => pairEncode (g (pairEncode q (pairEncode x y))) []) _ l₁ l₂
    (by simp [length_pairEncode]; omega)]
  simp [encWords, List.flatMap_def, List.map_zipWith]

/-- **The zip loop is polynomial-time** for a polynomial-time `g`.

**Proof sketch.** As for `polyTimeComputable_mapW`: the round drops the head entries of both
lists, the chunk is `g` of them, and the iterates keep suffixes of the input
(`iterate_zipStep`), so `Complexity.polyTimeComputable_emitIter` applies. -/
theorem polyTimeComputable_zipWithW {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (zipWithW g) := by
  have hl1 : PolyTimeComputable (fun S => pairFstD (pairSndD S)) := polyTimeComputable_slot2
  have hl2 : PolyTimeComputable (fun S => pairSndD (pairSndD S)) := polyTimeComputable_slot3
  have hs : PolyTimeComputable zipStep :=
    polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairSndD.comp hl1).pairEncode
      (polyTimeComputable_pairSndD.comp hl2))
  have he : PolyTimeComputable (zipChunk g) := by
    unfold zipChunk
    convert polyTimeComputable_ite
      (polyTimeComputable_or (polyTimeComputable_isNil.comp hl1)
        (polyTimeComputable_isNil.comp hl2)) (polyTimeComputable_const [])
      ((hg.comp (polyTimeComputable_pairFstD.pairEncode
        ((polyTimeComputable_pairFstD.comp hl1).pairEncode
          (polyTimeComputable_pairFstD.comp hl2)))).pairEncode (polyTimeComputable_const []))
      using 1
    funext S; simp
  refine polyTimeComputable_emitIter hs he 1 1 5 1 (fun w i => ?_)
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply, show zipStep w = pairEncode (pairFstD w)
      (pairEncode (pairSndD (pairFstD (pairSndD w))) (pairSndD (pairSndD (pairSndD w))))
      from rfl, iterate_zipStep, length_pairEncode, length_pairEncode]
    have h1 := length_iterate_pairSndD_le (pairSndD (pairFstD (pairSndD w))) i
    have h2 := length_iterate_pairSndD_le (pairSndD (pairSndD (pairSndD w))) i
    have h3 := length_pair_components_le w
    have h4 := length_pair_components_le (pairSndD w)
    have h5 := length_pairSndD_le (pairFstD (pairSndD w))
    have h6 := length_pairSndD_le (pairSndD (pairSndD w))
    simp; omega

/-! ### Counting -/

/-- The number of entries of the list read from `w`, in unary. -/
def countW (w : List Bool) : List Bool :=
  (List.range (1 * (w.length + 1) ^ 1 + 1)).flatMap
    (fun i => if pairSndD^[i] w = [] then [] else [true])

/-- `countW w` is `1^k` for the number `k` of entries read from `w`. -/
theorem countW_eq (w : List Bool) : countW w = List.replicate (decWords w).length true := by
  unfold countW
  rw [flatMap_listLoop (fun _ => [true]) _ w (by simp; omega)]
  induction decWords w with
  | nil => rfl
  | cons x L ih => simp [ih, List.replicate_succ]

/-- **Counting the entries is polynomial-time.** -/
theorem polyTimeComputable_countW : PolyTimeComputable countW := by
  have he : PolyTimeComputable (fun w : List Bool => if w = [] then [] else [true]) := by
    convert polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
      (polyTimeComputable_const [true]) using 1
    funext w; simp
  exact polyTimeComputable_emitIter polyTimeComputable_pairSndD he 1 1 1 1 (fun w i => by
    have := length_iterate_pairSndD_le w i; simp; omega)

end BinArith

end Complexity
```

## ===== TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Iterating a polynomial-time step polynomially often

Infrastructure for [AB09 §7.2]; not itself a result of the book. The arithmetic algorithms of
§7.2 (repeated squaring, Euclid, the Jacobi-symbol recursion, long division) all have the
shape "run a polynomial-time step a polynomial number of times on a state of polynomially
bounded length". This file proves that this shape is polynomial-time, and gives the
measure argument used to show that such a loop has reached its fixed point.

## Main definitions

* `Complexity.BinArith.guardNxt`, `Complexity.BinArith.guardLoop` — the guarded round and the
  guarded countdown loop.
* `Complexity.BinArith.SlotsLe` — the slot-length bound keeping its orbits linear.

## Main results

* `Complexity.BinArith.polyTimeComputable_iterate` — if `g` and `init` are polynomial-time
  and the orbit `g^[i] (init z)`, `i ≤ a(|z|+1)^k`, stays inside `B(|z|+1)^b`, then
  `z ↦ g^[a(|z|+1)^k] (init z)` is polynomial-time.
* `Complexity.BinArith.iterate_measure_eq_zero` — a measure that strictly drops on every
  non-fixed state of an invariant reaches `0` within its initial value many steps.

## Implementation notes

The loop is `Complexity.BlockLoop.step` (the shared countdown loop of
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`) on the state
`⟨[1], ⟨1^T, ⟨1^U, s⟩⟩⟩`: the countdown `1^T` counts the rounds, and the unary marker `1^U`
guards each round, which replaces `s` by `g s` only if `|g s| ≤ U`. The guard keeps every
orbit of the loop, from every word, inside a linear envelope (the hypothesis
`Complexity.polyTimeComputable_emitIter` needs), while on the genuine orbit the length
hypothesis makes it inert.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.)
-/

namespace Complexity

namespace BinArith

open Turing

/-! ### Measure arguments for loops -/

/-- An invariant of `g` holds along the whole orbit (the special case of Mathlib's
`Function.Iterate.rec` used throughout this development). -/
theorem iterate_invariant {α : Type} {g : α → α} (I : α → Prop) (hI : ∀ s, I s → I (g s))
    (n : ℕ) {s : α} (hs : I s) : I (g^[n] s) := by
  induction n with
  | zero => exact hs
  | succ n ih => rw [Function.iterate_succ_apply']; exact hI _ ih

/-- **Loops reach their fixed point.** Let `I` be an invariant of `g` and `μ` a measure
that strictly drops on every state of `I` with `μ > 0`, while states with `μ = 0` are fixed.
Then `n ≥ μ s` iterations from a state `s` of `I` end in a state of measure `0`. -/
theorem iterate_measure_eq_zero {α : Type} {g : α → α} (I : α → Prop) (μ : α → ℕ)
    (hI : ∀ s, I s → I (g s)) (hdec : ∀ s, I s → 0 < μ s → μ (g s) < μ s)
    (hfix : ∀ s, I s → μ s = 0 → g s = s) :
    ∀ (n : ℕ) (s : α), I s → μ s ≤ n → μ (g^[n] s) = 0 := by
  intro n
  induction n with
  | zero => intro s _ h; simpa using h
  | succ n ih =>
    intro s hs h
    rw [Function.iterate_succ_apply]
    rcases Nat.eq_zero_or_pos (μ s) with h0 | h0
    · rw [hfix s hs h0]; exact ih s hs (by omega)
    · exact ih (g s) (hI s hs) (by have := hdec s hs h0; omega)

/-! ### The guarded countdown loop -/

/-- One guarded round on the remainder `⟨u, s⟩`: replace `s` by `g s` when `|g s| ≤ |u|`. -/
def guardNxt (g : List Bool → List Bool) (_h r : List Bool) : List Bool :=
  pairEncode (pairFstD r)
    (if (g (pairSndD r)).length ≤ (pairFstD r).length then g (pairSndD r) else pairSndD r)

/-- The guarded loop: the countdown loop with constant head and the round `guardNxt g`. -/
def guardLoop (g : List Bool → List Bool) : List Bool → List Bool :=
  BlockLoop.step (fun h _ => h) (guardNxt g)

/-- The four slots of a loop state (head, countdown, marker, payload) are no longer than `L`. -/
def SlotsLe (L : ℕ) (W : List Bool) : Prop :=
  (pairFstD W).length ≤ L ∧ (pairFstD (pairSndD W)).length ≤ L ∧
    (pairFstD (pairSndD (pairSndD W))).length ≤ L ∧
    (pairSndD (pairSndD (pairSndD W))).length ≤ L

/-- Every slot of a word is no longer than the word. -/
theorem slotsLe_self (W : List Bool) : SlotsLe W.length W := by
  have h1 := length_pairSndD_le W
  have h2 := length_pairSndD_le (pairSndD W)
  refine ⟨length_pairFstD_le W, ?_, ?_, ?_⟩
  · exact (length_pairFstD_le _).trans h1
  · exact (length_pairFstD_le _).trans (h2.trans h1)
  · exact (length_pairSndD_le _).trans (h2.trans h1)

/-- A round of the guarded loop either stops or keeps head and marker, shortens the
countdown and applies the guard to the payload. -/
theorem guardLoop_cases (g : List Bool → List Bool) (W : List Bool) :
    guardLoop g W = blockDone ∨
      guardLoop g W = pairEncode (pairFstD W) (pairEncode ((pairFstD (pairSndD W)).drop 1)
        (guardNxt g (pairFstD W) (pairSndD (pairSndD W)))) := by
  unfold guardLoop BlockLoop.step
  split_ifs
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The guarded round preserves the slot bound. -/
theorem slotsLe_guardLoop (g : List Bool → List Bool) {L : ℕ} {W : List Bool}
    (h : SlotsLe L W) : SlotsLe L (guardLoop g W) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases guardLoop_cases g W with hW | hW <;> rw [hW]
  · simp [SlotsLe, blockDone, pairFstD_nil, show pairSndD [] = [] from rfl]
  · simp only [SlotsLe, guardNxt, pairFstD_pairEncode, pairSndD_pairEncode, List.length_drop]
    refine ⟨h1, by omega, h3, ?_⟩
    split_ifs with hg
    · exact hg.trans h3
    · exact h4

/-- The output of a guarded round has length at most `7L + 6` when its input's slots are
bounded by `L`. -/
theorem length_guardLoop_le (g : List Bool → List Bool) {L : ℕ} {W : List Bool}
    (h : SlotsLe L W) : (guardLoop g W).length ≤ 7 * L + 6 := by
  have h' := slotsLe_guardLoop g h
  rcases guardLoop_cases g W with hW | hW
  · rw [hW]; simp [blockDone, length_pairEncode]
  · obtain ⟨h1, h2, h3, h4⟩ := h'
    rw [hW] at h1 h2 h3 h4 ⊢
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, guardNxt] at h1 h2 h3 h4
    simp only [guardNxt, length_pairEncode]
    omega

/-- Every orbit of the guarded loop stays inside the linear envelope `7(|w| + 1)`. -/
theorem length_iterate_guardLoop_le (g : List Bool → List Bool) (w : List Bool) (i : ℕ) :
    ((guardLoop g)^[i] w).length ≤ 7 * (w.length + 1) ^ 1 := by
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply']
    have := length_guardLoop_le g
      (iterate_invariant (g := guardLoop g) (SlotsLe w.length) (fun _ h => slotsLe_guardLoop g h) i
        (slotsLe_self w))
    rw [pow_one]; omega

/-- The guarded round is polynomial-time when `g` is. -/
theorem polyTimeComputable_guardLoop {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (guardLoop g) := by
  have hr : PolyTimeComputable (fun W => pairSndD (pairSndD W)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hu : PolyTimeComputable (fun W => pairFstD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairFstD.comp hr
  have hs : PolyTimeComputable (fun W => pairSndD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairSndD.comp hr
  have hgs : PolyTimeComputable (fun W => g (pairSndD (pairSndD (pairSndD W)))) := hg.comp hs
  have htest : PolyTimeComputable (fun W => [decide
      ((g (pairSndD (pairSndD (pairSndD W)))).length ≤
        (pairFstD (pairSndD (pairSndD W))).length)]) := by
    have := polyTimeComputable_lenLe.comp (hu.pairEncode hgs)
    simpa [Function.comp_def] using this
  refine BlockLoop.polyTimeComputable_step rfl polyTimeComputable_pairFstD ?_
  have := hu.pairEncode (polyTimeComputable_ite htest hgs hs)
  simpa [guardNxt] using this

/-- **Iterating a polynomial-time step polynomially often is polynomial-time**
(infrastructure for [AB09 §7.2]; not itself a result of the book). If `g` and `init` are
polynomial-time and every state `g^[i] (init z)` with `i ≤ a(|z|+1)^k` has length at most
`B(|z|+1)^b`, then `z ↦ g^[a(|z|+1)^k] (init z)` is polynomial-time.

**Proof sketch.** Run the countdown loop `Complexity.BlockLoop.step` from
`⟨[1], ⟨1^T, ⟨1^U, init z⟩⟩⟩` with `T = a(|z|+1)^k`, `U = B(|z|+1)^b`, and the guarded
round `guardNxt g`, which applies `g` only when the result fits in `U`. The guard bounds
every orbit from every word by `7(|w|+1)` (`length_iterate_guardLoop_le`), as
`Complexity.BlockLoop.polyTimeComputable_of_loop` requires; on the genuine orbit the length
hypothesis makes the guard pass, so after `T` rounds the payload is `g^[T] (init z)`, which
the loop's single emission (`Complexity.BlockLoop.loop_output`) outputs. -/
theorem polyTimeComputable_iterate {g init : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hinit : PolyTimeComputable init) (a k B b : ℕ)
    (hbound : ∀ z i, i ≤ a * (z.length + 1) ^ k →
      (g^[i] (init z)).length ≤ B * (z.length + 1) ^ b) :
    PolyTimeComputable (fun z => g^[a * (z.length + 1) ^ k] (init z)) := by
  -- the remainder `⟨1^U, init z⟩` and the loop's initial state
  have hr : PolyTimeComputable
      (fun z => pairEncode (List.replicate (B * (z.length + 1) ^ b) true) (init z)) :=
    (polyTimeComputable_polyUnary B b).pairEncode hinit
  have hstart := BlockLoop.polyTimeComputable_countdownInit [true] polyTimeComputable_id hr a k
  have hout : PolyTimeComputable (fun W => pairSndD (pairSndD (pairSndD W))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  refine BlockLoop.polyTimeComputable_of_loop (polyTimeComputable_guardLoop hg)
    (BlockLoop.polyTimeComputable_emit hout) hstart 1 1 7
    (length_iterate_guardLoop_le g) (fun z => ?_)
  -- the loop's output is the payload after `T` guarded rounds
  set T := a * (z.length + 1) ^ k
  set U := List.replicate (B * (z.length + 1) ^ b) true
  have hK : T < 1 * ((pairEncode [true] (pairEncode (List.replicate (a * ((id z).length + 1) ^ k)
      true) (pairEncode U (init z)))).length + 1) ^ 1 + 1 := by
    simp only [id, length_pairEncode, List.length_replicate, pow_one, one_mul]
    omega
  have hstep : guardLoop g = BlockLoop.step (fun h _ => h) (guardNxt g) := rfl
  rw [BlockLoop.loop_output hstep (fun _ => [true]) (fun i => pairEncode U (g^[i] (init z)))
    (by simp [T]) (fun _ _ => List.cons_ne_nil _ _) (fun _ _ => rfl) (fun i hi => ?_) hK]
  · simp
  · have hb := hbound z (i + 1) (by omega)
    rw [Function.iterate_succ_apply'] at hb
    simp only [guardNxt, pairFstD_pairEncode, pairSndD_pairEncode, U, List.length_replicate,
      Function.iterate_succ_apply', if_pos hb]

end BinArith

end Complexity
```

## ===== campaign/items/ladner/fill-routes-request/delivery/ladner-fill-routes.md =====

# Fill routes for the six Ladner targets

Route draft for Shilun-Allan-Li/tcslib, Arora–Barak chapters 3–4. No library source is changed, no theorem is filled, and no PR is opened. All new interfaces below are proposals unless explicitly identified as the already approved, pending SAT reader. These routes preserve all six audited target statements, all four definitions, and all six published Ladner readings.

## 1. Pins, evidence, and how to read this draft

| Input | Pin / result |
|---|---|
| Lean source | `5ab222167eb12664d97d255766c5def15b6d5d50` |
| Records | `624196fbcb402019e3762565b2964d0027ec8c51` |
| Dispatched exchange | `ccd0a51374631a8414ff233673ec71fc9c466058` |
| Bundle | `arora-barak-ch3-4/outbox/fills/ladner-fill-routes/ladner-fill-routes-bundle.md` |
| Bundle SHA-256 | `a9b368ac95570ce7137934445d30ab90d27c1ab5576effcb858a455802d7367b` — verified |
| Sections | 23 — verified |
| Source binding | The bundle at the exchange pin is byte-identical. All 23 payloads match their stated Lean/records pins after removing bundle framing; the Ladner source section also has an enclosing code fence. |

The campaign branch was fetched. Sources were read with `git show` and an unmodified `git archive` extraction of the Lean pin; a newer branch head was never substituted. Repository reports and scripts were inspected as data. The first section of the bundle supplies this task's standards; maintainer-only workflow actions were not treated as instructions to this worker.

Citation throughout: [AB09, Theorem 3.3 and its proof], S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009. This is the approved fallback. The bundled source check distinguishes the January 2007 draft's Theorem 3.4 from the 2009 numbering. Direct web fetches of the [author-linked draft](https://theory.cs.princeton.edu/complexity/book.pdf) and [Barak's assignment](https://www.cs.princeton.edu/courses/archive/spring09/cos522/hw6.pdf) returned 403 on this run. I rely on the supplied source-check record for that edition mapping and do not claim to have verified Exercise 3.6(a)/(b).

The first section's LD9 approval supersedes the older proposal README's “UNAPPROVED” label. `Complexity.SAT_exists_linear_verifier` may be assumed for a route, but is absent at the Lean pin and must land separately before an unconditional consumer fill.

The code blocks below are exact proposed definitions and intermediate theorem types, with intentionally admitted bodies. They also appear in the standalone `Route-*.lean.txt` probes. Probe namespaces isolate candidate helper names; in production all consumer helpers belong **private inside namespace `Complexity` in the existing `TCSlib/Complexity/Diagonalization/Ladner.lean`**, with one shared parser/finite-table implementation. Standalone probes repeat that small parser specification so each can be checked without importing another scratch file; this is not a proposal to duplicate it in the library. No new file is proposed. Every public declaration listed in §3, including arithmetic leaves, requires the indicated separate scope decision. No probe admission is evidence that its mathematical statement has been proved.

Presentation order is 3, 4, 1, 2, 5, 6: the two qualitative selector arguments are independent of the memo implementation; NP membership waits for the memo result; the general padding theorem is independent of the special function; the final conjunction waits for all five.

## 2. Existing API checked at the Lean pin

`Route-API.lean.txt` checks the full names of the existing declarations used here and prints their axiom dependencies. The following table gives their homes. A declaration appearing in another table as **proposed** is deliberately not counted as existing API. Public structure fields may be applied as contracts without unfolding the structure-valued constant containing them.

| Home under `TCSlib/Complexity/` | Existing declarations used |
|---|---|
| `Diagonalization/Ladner.lean` | `Complexity.mem_padSAT_iff`, `padSAT_congr`, `ladnerMachine_eq`, `ladnerH_eq`, `ladnerH_le`, `SAT_H_eq`; the six target names are checked, not assumed proved. |
| `ClassP/P.lean` | `Complexity.mem_P_iff`. |
| `ClassP/ModelInvariance.lean` | `Complexity.mem_P_iff_one_work_tape`. |
| `ClassNP/NP.lean` | `Complexity.mem_NP_iff_exists_length_le`. This avoids unfolding `NP`. |
| `ClassNP/SAT.lean`; `CookLevin/Hardness.lean` | `Complexity.SAT_mem_NP`; `Complexity.SAT_NPHard`. No private SAT verifier is read by a consumer. |
| `ClassNP/Reductions.lean` | `Complexity.mem_P_of_polyTimeReducible`, `Complexity.P_eq_NP_of_NPHard_mem_P`. |
| `ClassNP/PolyTime.lean` | `Complexity.PolyTimeComputable.output_length_le`, `Complexity.PolyTimeComputable.comp`. |
| `ClassNP/PolyTimePairing.lean` | `Complexity.PolyTimeComputable.pairEncode`, `.append`; `polyTimeComputable_of_linear`, `polyTimeComputable_id`, `_const`, `_unary`, `_polyUnary`, `_pairFstD`, `_pairSndD`, `_ite`, `_and`; `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairFstD_le`. Each shortened entry here has the `Complexity.` prefix and the displayed common stem. |
| `ClassNP/PolyTimeBlockLoop.lean` | `Complexity.polyTimeComputable_or`, `_not`, `_tail`, `_headD`, `Complexity.length_pairSndD_le`. |
| `ClassNP/PolyTimePrefix.lean` | `Complexity.polyTimeComputable_takePrefixByLength`, `polyTimeComputable_dropPrefixByLength`. |
| `ClassNP/PClosure.lean` | `Complexity.mem_P_of_test`, `test_of_mem_P`, `mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `inter_mem_P`. |
| `ClassNP/Transducer.lean` | `Complexity.transduce_nil`, `transduce_cons`, `polyTimeComputable_transduce`. |
| `ClassNP/EXP.lean` | `Complexity.exists_proj_decider`. Its private word-enumeration lemmas are not consumer API. |
| `Diagonalization/EXPCOM.lean` | `Complexity.expCode`; `Turing.UniformMachineCode.simulator_accepts`, `.simulator_rejects`. The proof uses their contracts and does not unfold `expCode` or read its choice witness. |
| `TuringMachine/Encoding.lean` | `Turing.MachineCode.decode_encode_pad` (structure field), `Turing.FinTM.toCodeTM_computesInTime_iff`, `Turing.length_pairEncode`, `Turing.pairEncode_injective`. |
| `TuringMachine/Finite.lean` | `Turing.FinTM.not_computesInTime_zero`, `ComputesInTime.mono`, `ComputesInTime.output_unique`, `computesFunInTime_iff`, `computesInTime_iff`. |
| `TuringMachine/Composition.lean` | `Turing.FinTM.exists_comp_on_image`. Its clock is exactly `2*T₁ n + T₂ n + 2`. |
| `TuringMachine/Build/Primitives.lean`; `Build/WordTests.lean` | `Turing.FinTM.computesFunInTime_lengthBits`, `computesFunInTime_polyBits`; `Turing.FinTM.computesFunInTime_decideEq`. |
| `TuringMachine/NatBits.lean` | `Turing.length_bits_le_self`. |
| `ClassP/BinaryArith/Iterate.lean` | `Complexity.BinArith.polyTimeComputable_iterate`, `iterate_invariant`, `iterate_measure_eq_zero`. These are the proposed memo, finite scan, saturated-power, and shrinking-loop hosts. |
| `ClassP/BinaryArith/Basic.lean` | `Complexity.BinArith.polyTimeComputable_normBits`, `polyTimeComputable_cons`, `bitsVal_eq_headD`, `bitsVal_drop_one`. |
| `ClassP/BinaryArith/AddSub.lean` | `Complexity.BinArith.polyTimeComputable_add`, `_sub`, `_lt`, `_le`, `_beq`; `add_pairEncode`, `sub_pairEncode`, `lt_pairEncode`, `le_pairEncode`, `beq_pairEncode`. |
| `ClassP/BinaryArith/Mul.lean` | `Complexity.BinArith.polyTimeComputable_reverse`, `polyTimeComputable_mul`, `mul_pairEncode`. |
| `ClassP/BinaryArith/Words.lean` | `Complexity.BinArith.encWords_nil`, `encWords_cons`, `encWords_append_singleton`, `length_encWords_le`, `length_decWords_le`, `decWords_encWords`, `polyTimeComputable_countW`, `countW_eq`, `polyTimeComputable_mapW`, `mapW_pairEncode`. |
| `ClassP/BinaryArith/Loops.lean` | `Complexity.BinArith.polyTimeComputable_forLoop`, `forLoop_pairEncode`, `polyTimeComputable_getW`, `getW_pairEncode_bits`, `polyTimeComputable_uRest`, `polyTimeComputable_hasFalse`, `uRest_nil`, `uRest_true_cons`, `uRest_false_cons`, `hasFalse_nil`, `hasFalse_cons`, `polyTimeComputable_eqW`, `eqW_pairEncode`, `polyTimeComputable_mulU`, `length_mulU`. |
| `SpaceComplexity/Machines/Bin.lean` | `Complexity.LogProg.bitsVal_bits`, `bits_injective`, `bitsVal_lt_two_pow`. |

Arithmetic on canonical numbers uses the existing `*_pairEncode` equations. There is no need to unfold `BinArith.add`, `mul`, `lt`, `le`, or `beq` or commission duplicate equations for those canonical inputs. Normalization already has a public FP theorem with an explicit lambda result. `bitsVal_eq_headD` and `bitsVal_drop_one` read arbitrary exponent words, so a missing `bitsVal` equation is not a blocker here.

The API probe also checks the Mathlib/core names explicitly used in the carried selector/numerical arguments: `Nat.find_spec`, `Nat.find_min'`, `Nat.log_lt_self`, `Nat.log_le_self`, `Nat.le_log_of_pow_le`, `Nat.pow_log_le_self`, `Nat.pow_le_of_le_log`, `Nat.lt_pow_succ_log_self`, `Nat.bits_append_bit`, `Nat.bit_val`, `Nat.one_bits`, `Nat.pow_le_pow_left`, `Nat.pow_le_pow_right`, `Function.iterate_succ_apply`, `Function.iterate_succ_apply'`, `Finset.le_sup`, and `Finset.mem_range`. Ordinary list length/append/map/getD equations are core/Mathlib equations; no core or Mathlib definition is proposed as an explicit `simp`, `rw`, or `unfold` argument.

## 3. Reader and import preparation

These are all foreign-definition reader gaps used by this route. Each statement is in `Route-Readers.lean.txt`. The homes are existing files. All proposed names below need Seyoon's public-API ruling; the SAT reader is already approved but pending. No definitions or target headers need to change.

| ID | Exact name(s) | Existing home | Consumers / reason |
|---|---|---|---|
| R0 | `Complexity.SAT_exists_linear_verifier` | `ClassNP/SAT.lean`, after `SAT_mem_NP` | Already approved LD9. Needed by short SAT search and the simple linear-certificate padded verifier. The owner may use its private SAT facts; consumers may not. |
| R1 | `Complexity.polyTimeComputable_iff` | `ClassNP/PolyTime.lean` | Extract/assemble an FP machine and its clock for simulator preparation. Existing closure results do not expose this existential by a published equation. |
| R2 | `Complexity.polyTimeReducible_iff` | `ClassNP/Reductions.lean` | Extract the reduction in target 5; assemble the bounded-padding reduction in target 6. |
| R3 | `Complexity.NPHard_iff` | `ClassNP/Reductions.lean` | Specialize hardness to `SAT_mem_NP` without applying the body of `NPHard`. |
| R4 | `Complexity.NPComplete_iff` | `ClassNP/Reductions.lean` | Extract hardness in the final contradiction. `NPComplete.mem_P_iff` alone does not supply it. |
| R5 | `Turing.FinTM.decidesInTime_iff` | `ClassP/DTIME.lean`, beside `DecidesInTime` | Relate a language decider to its indicator-valued function computation; use `computesFunInTime_iff` afterward. |
| R6a,b | `Turing.MultiTapeTM.indicator_of_mem`, `indicator_of_not_mem` | `TuringMachine/Deterministic.lean`, beside `indicator` | Interpret the decider's two outputs in targets 3 and 1. Similar `LogProg`/other-namespace indicator facts are not equations for this definition. |

These owner readings are definitional or immediate consequences of the owner definition, the two indicator cases, and published computation contracts. R5 reads the owner's own `DecidesInTime` and rewrites `Turing.FinTM.computesFunInTime_iff`; do not close it by definitional reduction of the foreign `ComputesFunInTime`. The readings introduce no machine, computational assumption, or new `simp` attribute.

```lean
namespace Complexity
-- Approved pending reader. It is absent at the import pin.
theorem SAT_exists_linear_verifier :
    ∃ V : Language Bool, V ∈ P ∧
      ∀ x : List Bool, x ∈ SAT ↔
        ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V := by sorry

-- Proposed owner readers, not existing API at the import pin.
theorem polyTimeComputable_iff (f : List Bool → List Bool) :
    PolyTimeComputable f ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.ComputesFunInTime f (fun n => C * (n + 1) ^ d) := by sorry

theorem polyTimeReducible_iff (L L' : Language Bool) :
    PolyTimeReducible L L' ↔ ∃ f : List Bool → List Bool,
      PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L' := by sorry

theorem NPHard_iff (L : Language Bool) :
    NPHard L ↔ ∀ L' : Language Bool, L' ∈ NP → PolyTimeReducible L' L := by sorry

theorem NPComplete_iff (L : Language Bool) :
    NPComplete L ↔ L ∈ NP ∧ NPHard L := by sorry
end Complexity

namespace Turing.FinTM
theorem decidesInTime_iff (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    M.DecidesInTime L T ↔ M.ComputesFunInTime
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T := by sorry
end Turing.FinTM

namespace Turing.MultiTapeTM
theorem indicator_of_mem {α : Type} {L : Set α} {x : α} (hx : x ∈ L) :
    indicator L x = true := by sorry
theorem indicator_of_not_mem {α : Type} {L : Set α} {x : α} (hx : x ∉ L) :
    indicator L x = false := by sorry
end Turing.MultiTapeTM
```

**Imports and host coverage.** The frozen Ladner imports are unchanged in this delivery. The implementation route proposes an explicit import of `ClassP.BinaryArith.Loops` (which already imports `Iterate`, `Words`, `AddSub`, `Mul`, and `Div`) and, if not retained transitively, `ClassP.ModelInvariance`. These are proof-route import decisions, not already authorized changes to the pinned source. All statement probes show their extended import context explicitly.

The existing `BinArith.polyTimeComputable_iterate` is the actual driver: it accepts an FP step/init and a polynomial orbit-length bound. `BinArith.polyTimeComputable_forLoop` is its existing counted variant; table access uses the existing `getW` host; exact SAT search uses the existing `exists_proj_decider`; uniform acceptance uses the existing simulator fields and `exists_comp_on_image`. No handwritten memo-table, search, recursion, or universal-machine host is proposed. The pin's §14 registry does not give `BinArith.polyTimeComputable_iterate` a named row or a gate receipt. The maintainer must bind these existing hosts to registry/statement-gate coverage before dispatch; publication of the theorem alone is not evidence of that process requirement. If that check requires a new contract, it is a separate decision/statement gate, not work hidden in a private Ladner helper.

**Common leaves.** The parser and finite table below are private consumer glue in `Ladner.lean`. `parse` is a mathematical specification. Its FP implementation is reverse the word, consume its initial true block and false delimiter with the existing `uRest`, reverse the remaining prefix, and obtain the suffix length by subtraction. `hasFalse` distinguishes all-true words from an empty recovered prefix. Thus `[false]` is distinguishable from “no separator.” Use the public reverse/transducer/pair/binary equations; do not copy a transition table.

The only proposed new shared computational API is the saturated binary power leaf: source names `Complexity.BinArith.powCap`, `powCap_eq`, `powCap_pairEncode`, and `polyTimeComputable_powCap` in the existing `ClassP/BinaryArith/Mul.lean`. The scratch names `powCap_pair` and `powCap_FP` below correspond to the last two production names. `powCap_eq` covers every input, including malformed pairs; the canonical equation alone would not cover the whole public definition. This is an arithmetic leaf, not a new loop host. It still needs a public-name/statement decision. All other helper labels in this section stay private in Ladner.

Compute `min(m^e,c+1)` by binary repeated squaring, consuming one exponent bit per round and saturating every multiplication at `c+1`. Handle `m=0`, `e=0`, and `0^0=1` explicitly. The exponent loop takes at most the input word length plus one iterations; register words have at most the combined input length plus a fixed constant, and a temporary product at most twice that many bits. Obtain the FP result by `BinArith.polyTimeComputable_iterate`, `polyTimeComputable_mul`, comparisons, and the published bit-tail readings. A full bit-size/iterate invariant is still proof work; this statement probe supplies no implementation proof. `syntax_FP` compares the saturated result with the available unary suffix length, so a huge binary exponent cannot force huge output allocation.

`finite_lookup_FP` is a static finite disjunction of fixed-word equality tests (`computesFunInTime_decideEq`, `polyTimeComputable_or`), not a runtime SAT search. `small_SAT_table` intersects the finite set of words shorter than a fixed bound with SAT by classical choice. Its code size may depend arbitrarily on that fixed bound; its runtime degree may not depend on the input.

```lean
namespace LadnerRouteShared

-- Mathematical parser specification; implement through reverse/uRest/hasFalse,
-- not by compiling a new private parser host.
def parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

def padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

def parseWord (y : List Bool) : List Bool :=
  match parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

theorem parse_some (y p : List Bool) (t : ℕ) :
    parse y = some (p, t) ↔ y = p ++ false :: List.replicate t true := by sorry

theorem parse_none (y : List Bool) :
    parse y = none ↔ ∀ b ∈ y, b = true := by sorry

theorem parsed_length {y p : List Bool} {t : ℕ} (hp : parse y = some (p, t)) :
    y.length = p.length + 1 + t ∧ p.length < y.length := by sorry

theorem parse_FP : PolyTimeComputable parseWord := by sorry

theorem syntax_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) :
    PolyTimeComputable (fun y => [padSyntax h y]) := by sorry

theorem pad_membership {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔ ∃ p t, parse y = some (p, t) ∧
      t = p.length ^ h p.length ∧ p ∈ SAT := by sorry

theorem finite_lookup_FP (S : Finset (List Bool)) :
    PolyTimeComputable (fun x : List Bool => [decide (x ∈ S)]) := by sorry

theorem small_SAT_table (B : ℕ) :
    ∃ S : Finset (List Bool), ∀ x : List Bool,
      x ∈ S ↔ x.length < B ∧ x ∈ SAT := by sorry

-- Proposed shared arithmetic leaf in BinaryArith/Mul.lean (public decision).
def powCap (z : List Bool) : List Bool :=
  Nat.bits (min
    ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
    (LogProg.bitsVal (pairSndD (pairSndD z)) + 1))

theorem powCap_eq (z : List Bool) :
    powCap z = Nat.bits (min
      ((LogProg.bitsVal (pairFstD z)) ^ (LogProg.bitsVal (pairFstD (pairSndD z))))
      (LogProg.bitsVal (pairSndD (pairSndD z)) + 1)) := by sorry

theorem powCap_pair (m e c : ℕ) :
    powCap (pairEncode (Nat.bits m) (pairEncode (Nat.bits e) (Nat.bits c))) =
      Nat.bits (min (m ^ e) (c + 1)) := by sorry

theorem powCap_FP : PolyTimeComputable powCap := by sorry

end LadnerRouteShared
```

Common dependency ledger: `parse_some`/`parse_none` use the parser's own recursion equations and list equations; `parsed_length` uses `parse_some`; `parse_FP` uses the reverse/uRest/hasFalse and length/subtraction APIs; `powCap_FP` uses the existing iteration and arithmetic APIs; `syntax_FP` uses `parse_FP`, `powCap_FP`, the supplied `hp`, and canonical arithmetic equations; `pad_membership` uses `mem_padSAT_iff` and `parse_some`; `finite_lookup_FP` uses fixed equality and Boolean closure; `small_SAT_table` uses finite bounded-word enumeration, with no SAT decoder reading. `pad_membership`, `syntax_FP`, and `parse_some` are reused in all three computational consumers, not re-proved there.

Open common premises are R0's landing, R1–R6's reader decisions/proofs, the public saturated-power leaf, the proof-route import decision and host-coverage check, and all admitted common leaves above. Neither successful typing nor the historical conditional probes closes these premises. New source docstrings must cite mathematical sources, state their formulas in prose, and carry proof sketches for nontrivial proofs; scratch/campaign names and paths stay out of Lean docstrings.

## 4. Target 3 — `Complexity.ladnerH_bounded_of_mem_P`

### Mathematical route

Follow [AB09, Theorem 3.3 and its proof], with the approved timed-enumeration adaptation. From a P decider, use `mem_P_iff_one_work_tape`, then `FinTM.toCodeTM_computesInTime_iff`, to obtain a code-normal-form decider with a bound `a(m+1)^d`. Append sufficiently many true bits to `expCode.encode M`. The decode-padding field preserves the machine, while the resulting canonical binary index can exceed any chosen bound. Choose `i` above both `d` and `a*2^d`.

For nonempty inputs, `a(m+1)^d ≤ (a*2^d)*m^d ≤ i*m^i`. A rejecting computation cannot coexist with a completed true output at another time, by `ComputesInTime.output_unique`. At the empty word every indexed deadline is zero; `not_computesInTime_zero` and the separator's positive length make both acceptance and padded membership false. Thus this single `i` passes every word, not only an eventual tail of stages.

Apply `ladnerH_eq`: if the cap is at most `i`, it already supplies the bound; otherwise `i` is a valid candidate and `Nat.find_min'` bounds the minimum. This strengthens the existing sketch's finite-prefix bookkeeping without changing the statement or conventions. No change to that sketch is necessary for this route-drafting delivery.

### Exact intermediate statements, homes, and dependencies

All five helpers below are private in existing `Ladner.lean`. `pad_nil` uses `mem_padSAT_iff` and list lengths; `padded_index` ports the bundled scratch proof using `ladnerMachine_eq`, `MachineCode.decode_encode_pad`, `Nat.bits_append_bit`, and `Nat.bit_val`; `indexed_deadline` ports its numeric companion. `correct_index` uses those three helpers, `mem_P_iff_one_work_tape`, `FinTM.toCodeTM_computesInTime_iff`, R5/R6, and output uniqueness. `selector_bound` ports the bundled selector argument using only `ladnerH_eq`, `Nat.find_spec`, and `Nat.find_min'`. The target obtains `⟨i, selector_bound i good⟩` from `correct_index`.

```lean
namespace LadnerRouteBounded
theorem pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by sorry

theorem padded_index (M : CodeTM) (B : ℕ) :
    ∃ i, B < i ∧ ladnerMachine i = M.toFinTM := by sorry

theorem indexed_deadline (a d i m : ℕ)
    (hd : d ≤ i) (ha : a * 2 ^ d ≤ i) (hm : 1 ≤ m) :
    a * (m + 1) ^ d ≤ i * m ^ i := by sorry

theorem correct_index (hP : SAT_H ∈ P) :
    ∃ i, ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH := by sorry

theorem selector_bound (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) :
    ∀ n, ladnerH n ≤ i := by sorry
end LadnerRouteBounded
```

**Readers needed:** R5 and R6a,b. No unfolding of `PolyTimeComputable`, `NP`, `SAT`, the uniform-code choice, or `CodeTM.toFinTM` is needed. No assumption about whether `[] ∈ SAT` is needed.

**Open premises:** the five private helper proofs and the owner readers; no other Ladner target. The bundled index and selector proofs are prior scratch evidence, not installed API. The checked existing support dependencies are separately inventoried in `probe-validation.log`.

**Size/order:** about 150–300 new Lean lines, approximately 0.5–2 focused agent-days after reader/normalization preflight. It can be prepared independently of targets 1, 2, 4, and 5. Actual merges into the same owner file are serial.

**Risks:** encode indices canonically (an all-false suffix is insufficient); absorb the coefficient as well as degree; do not demand total Boolean output at a zero deadline; use the one-work-tape theorem before code conversion.

## 5. Target 4 — `Complexity.ladnerH_unbounded_of_not_mem_P`

### Mathematical route

The finite-counterexample argument is [AB09, Theorem 3.3 and its proof]. First show that each fixed indexed bounded-acceptance predicate is in P. Prepare the exact simulator layout `pairEncode (pairEncode (bits deadline) code) input`, use `expCode.simulator_accepts`/`simulator_rejects`, and compose only on that preparation function's image. An indexed machine may diverge on a rejected input: the bounded-acceptance simulator still returns a total negative answer. Do not infer a decider directly from the indexed machine.

If index `i` agreed with the padded language on every word, this total polynomial test would put `SAT_H` in P via `mem_P_of_test` and `SAT_H_eq`. Contraposition gives a finite failing word for every `i`. For a requested lower bound `C`, let `B` be the maximum length of the chosen witnesses for `i<C`, put `M=max B (2^C)`, and take `N=2^M`. At every `n≥N`, the query window contains those witnesses and the cap is at least `C`. None of those indices can be selected; the fallback is large enough too. No monotonicity of `ladnerH` is asserted.

### Exact intermediate statements, homes, and dependencies

All six helpers below are private in `Ladner.lean`. `fixed_clock_preparation` uses length bits, fixed-degree multiplication and pairing. Its FP proof must yield an actual preparation machine and polynomial clock through R1. `fixed_clock_budget` is the numeric majorant for the simulator's deadline-value clock, uniform in the input. `fixed_clock_FP` uses these two and `exists_comp_on_image`, not generic composition with a falsely polynomial-in-bit-length simulator. `all_tests_imply_P` uses `fixed_clock_FP` with `code=Nat.bits i`, `a=d=i`, `ladnerMachine_eq`, `mem_P_of_test`, and `SAT_H_eq`. `failing_words` is its classical contrapositive. `selector_threshold` is the bundled finite-sup argument with `ladnerH_eq` and `Nat.le_log_of_pow_le`. The target is `selector_threshold (failing_words hP)`.

```lean
namespace LadnerRouteUnbounded
theorem fixed_clock_preparation (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x) := by sorry

theorem fixed_clock_budget (D u a d n : ℕ) :
    D * (u + n + a * n ^ d + 1) ^ D ≤
      (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by sorry

theorem fixed_clock_FP (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      [decide ((expCode.decode code).toFinTM.ComputesInTime
        x [true] (a * x.length ^ d))]) := by sorry

theorem all_tests_imply_P (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) : SAT_H ∈ P := by sorry

theorem failing_words (hP : SAT_H ∉ P) :
    ∀ i : ℕ, ∃ x : List Bool,
      ¬ ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) := by sorry

theorem selector_threshold
    (bad : ∀ i : ℕ, ∃ x : List Bool,
      ¬ ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)) :
    ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by sorry
end LadnerRouteUnbounded
```

**Readers needed:** R1; R5/R6 only when reading/assembling decider contracts in a lower-level implementation. The `mem_P_of_test` assembly itself avoids unfolding `P` or its indicator. Uniform-code fields and `ladnerMachine_eq` already cover the code boundary.

**Open premises:** preparation and its setup clock, the total fixed-clock FP theorem, and the finite-selector glue. No target 1 or 3 premise. There is no assumption of halting of `ladnerMachine i` on negative inputs.

**Size/order:** 200–400 lines, roughly 1–3 agent-days. Independent mathematical work can run alongside target 3 and the common arithmetic work; owner-file writes remain serial.

**Risks:** the simulator time is polynomial in the *numeric* deadline; binary encoding alone proves nothing about it. Fixed `a,d,code` allow the displayed polynomial envelope. Preserve the conclusion's `∀ n≥N`, not just “arbitrarily large values.”

## 6. Target 1 — `Complexity.ladnerH_polyTime`

### Mathematical route

Use the bottom-up evaluation behind [AB09, Theorem 3.3 and its proof], rather than recursively recomputing all smaller calls. The state is exactly `pairEncode J T`, where `J=1^|z|` is immutable and `T=encWords [bits H(0), …, bits H(j-1)]`. One outer step appends `bits (stage(values T))`. The driver runs `|z|+1` steps from the empty table; readout is the existing `getW` at unary index `J`. Thus there are no serialized simulator configurations or unbounded memo subcalls to hide in a state invariant.

At table length `j`, a padded query prefix has length strictly below its queried word, which has length at most `log₂ j`; for `j>0` this is below `j`. `padSAT_congr` therefore identifies lookup of the table's earlier values with global `ladnerH` on every queried word. At `j=0` the index cap is zero, so no query is needed. `ladnerH_eq` now proves that the finite minimum returned by `stage` is exactly `ladnerH j`.

The inner candidate test enumerates all words of length at most `a=log₂ j` as `(bits(r+1)).dropLast`, for `r<2^(a+1)-1`. This includes the empty word and every bit pattern with trailing zeros. There are at most `2(j+1)` queries per candidate and at most `j` candidates. Build each finite scan as an application of `BinArith.polyTimeComputable_iterate` (or its existing `forLoop` specialization) on a fixed context plus rank/candidate/success flag; use an absorbing completion flag. No private enumeration machine or generic memo host is added. The rank counter, selected index, and masks need only polynomially many bits/positions. The scans have at most `2(j+1)^2` test rounds plus polynomial initialization/finalization overhead, while the outer driver has exactly `|z|+1` **macro** steps. The inner costs are charged inside the FP proof of that macro step.

For candidate `i<log₂ log₂ j`, a short deadline satisfies `i*m^i≤j^3`. The uniform simulator cost is at most `(D*4^D)(j+1)^(3D)`, with `D=expCode.simDegree`. The supplied clock-envelope scratch proof already establishes the numerical leaf. It does not build the simulator input. The explicit guarded `queryPrep` below does so; a bad query maps to zero deadline, empty code and empty input. Test the guard before interpreting an enormous index as a loop count. On a good query compute the deadline with saturation at `j^3+1`, where the bound shows saturation is inert.

For SAT of a short prefix, use the approved R0 and `exists_proj_decider 1 1`. Its clock is `b*2^(m+1)*(a*(2m+2)^d+(2m+2)^2)`, bounded by `2b(a*2^d+4)(j+1)^(d+3)`. A generic NP certificate polynomial is insufficient here. The short SAT predicate is composed only on a guarded short-input image, with an explicit input-preparation clock. Invalid inputs may use an empty default SAT query and must have their final Boolean verdict masked; no assumption about SAT of the empty word is made.

The completed table has at most `|z|+1` entries, each with bit length at most `|z|`, by `ladnerH_le`, `Nat.log_le_self`, and `length_bits_le_self`. `length_encWords_le` and `length_pairEncode` give the explicit orbit bound `4(|z|+1)^2`. Apply the existing iterator with `(a,k,B,b)=(1,1,4,2)` and compose its output with `polyTimeComputable_getW`.

### Exact intermediate statements, homes, and dependencies

Every declaration below is private consumer material in existing `Ladner.lean`; no new public memo state/API is proposed. `values`, `shortWords`, `stage`, `candidate`, `memoInit`, `memoStep`, and the guarded query functions are semantic specifications, not claims that classical quantification executes. Their FP theorems are the construction obligations. The generic iterator, not evaluation of a classical `Nat.find`, implements the scans.

```lean
namespace LadnerRoutePoly
def values (T : List Bool) : List ℕ := (BinArith.decWords T).map LogProg.bitsVal

def shortWords (a : ℕ) : List (List Bool) :=
  (List.range (2 ^ (a + 1) - 1)).map (fun r => (Nat.bits (r + 1)).dropLast)

def stage (vs : List ℕ) : ℕ :=
  let n := vs.length
  if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
      ∀ x : List Bool, x.length ≤ Nat.log 2 n →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0)) then Nat.find hex
  else Nat.log 2 (Nat.log 2 n)

def candidate (S : List Bool) : Bool :=
  let n := (pairFstD S).length
  let i := LogProg.bitsVal (pairFstD (pairSndD S))
  let vs := values (pairSndD (pairSndD S))
  decide (n = vs.length ∧ i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT (fun m => vs.getD m 0)))

def memoInit (z : List Bool) : List Bool :=
  pairEncode (List.replicate z.length true) []

def memoStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairSndD S ++ pairEncode (Nat.bits (stage (values (pairSndD S)))) [])

theorem shortWords_complete (a : ℕ) (x : List Bool) :
    x ∈ shortWords a ↔ x.length ≤ a := by sorry

theorem shortWords_count (n : ℕ) :
    (shortWords (Nat.log 2 n)).length ≤ 2 * (n + 1) := by sorry

theorem short_deadline (n i m : ℕ)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hm : m ≤ Nat.log 2 n) :
    i * m ^ i ≤ n ^ 3 := by sorry

theorem numeric_envelope (D n i : ℕ) (x : List Bool)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hx : x.length ≤ Nat.log 2 n) :
    D * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ D ≤
      (D * 4 ^ D) * (n + 1) ^ (3 * D) := by sorry

theorem short_SAT_machine
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
      (fun m => b * 2 ^ (m + 1) *
        (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2)) := by sorry

theorem short_SAT_envelope (a b d n m : ℕ) (hm : m ≤ Nat.log 2 n) :
    b * 2 ^ (m + 1) * (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2) ≤
      (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by sorry

-- Explicit preparation and envelope transfer: no preparation premise is implicit.
theorem simulation_on_image (code input : List Bool → List Bool)
    (deadline : List Bool → ℕ)
    (hprep : PolyTimeComputable (fun z =>
      pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)))
    (hbudget : ∃ A e, ∀ z, expCode.simDegree *
      ((code z).length + (input z).length + deadline z + 1) ^ expCode.simDegree ≤
        A * (z.length + 1) ^ e) :
    PolyTimeComputable (fun z => [decide
      ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))]) := by sorry

def validQuery (S : List Bool) : Prop :=
  LogProg.bitsVal (pairFstD (pairSndD S)) <
      Nat.log 2 (Nat.log 2 (pairFstD S).length) ∧
    (pairSndD (pairSndD S)).length ≤ Nat.log 2 (pairFstD S).length

def queryCode (S : List Bool) : List Bool :=
  if validQuery S then Nat.bits (LogProg.bitsVal (pairFstD (pairSndD S))) else []
def queryInput (S : List Bool) : List Bool :=
  if validQuery S then pairSndD (pairSndD S) else []
def queryDeadline (S : List Bool) : ℕ :=
  if validQuery S then
    LogProg.bitsVal (pairFstD (pairSndD S)) *
      (pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))
  else 0

def queryPrep (S : List Bool) : List Bool :=
  pairEncode (pairEncode (Nat.bits (queryDeadline S)) (queryCode S)) (queryInput S)

theorem query_preparation :
    ∃ (M : FinTM Bool) (C q : ℕ),
      M.ComputesFunInTime queryPrep (fun n => C * (n + 1) ^ q) := by sorry

theorem query_budget (S : List Bool) :
    expCode.simDegree *
      ((queryCode S).length + (queryInput S).length + queryDeadline S + 1) ^
        expCode.simDegree ≤
      (expCode.simDegree * 4 ^ expCode.simDegree) *
        (S.length + 1) ^ (3 * expCode.simDegree) := by sorry

theorem composition_clock (C q A e n : ℕ) :
    2 * (C * (n + 1) ^ q) + A * (n + 1) ^ e + 2 ≤
      (2 * C + A + 2) * (n + 1) ^ max q e := by sorry

theorem short_SAT_on_image (f : List Bool → List Bool)
    (hf : PolyTimeComputable f)
    (hshort : ∀ z, (f z).length ≤ Nat.log 2 z.length)
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun z => [decide (f z ∈ SAT)]) := by sorry

theorem short_pad_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool => [decide
      ((pairFstD S).length ≤ Nat.log 2 (values (pairSndD S)).length ∧
        pairFstD S ∈ padSAT (fun m => (values (pairSndD S)).getD m 0))]) := by sorry

-- Concrete finite-scan states: no classical quantifier is executed by a host.
def ctxGuard (C : List Bool) : Prop :=
  (pairFstD C).length = (values (pairSndD (pairSndD C))).length ∧
    LogProg.bitsVal (pairFstD (pairSndD C)) <
      Nat.log 2 (Nat.log 2 (pairFstD C).length)

def wordVerdict (C : List Bool) (r : ℕ) : Bool :=
  let x := (Nat.bits (r + 1)).dropLast
  let i := LogProg.bitsVal (pairFstD (pairSndD C))
  decide (ctxGuard C ∧ x.length ≤ Nat.log 2 (pairFstD C).length ∧
    ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
      x ∈ padSAT (fun m => (values (pairSndD (pairSndD C))).getD m 0)))

def queryCount (C : List Bool) : ℕ := 2 ^ (Nat.log 2 (pairFstD C).length + 1) - 1

def testInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (List.replicate (queryCount C) true) (pairEncode [] [true]))

def testStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let rank := pairFstD (pairSndD (pairSndD S))
  let flag := pairSndD (pairSndD (pairSndD S))
  if rem = [] then S else
    pairEncode C (pairEncode (rem.drop 1)
      (pairEncode (rank ++ [true]) [flag.headD false && wordVerdict C rank.length]))

def testOut (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD S))

theorem log_eq_bits_length (n : ℕ) :
    Nat.log 2 n = (Nat.bits n).length - 1 := by sorry

theorem binary_log_FP : PolyTimeComputable
    (fun w : List Bool => Nat.bits (Nat.log 2 (LogProg.bitsVal w))) := by sorry

theorem wordVerdict_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool =>
      [wordVerdict (pairFstD S) (pairSndD S).length]) := by sorry

theorem testInit_FP : PolyTimeComputable testInit := by sorry

theorem testStep_FP
    (hw : PolyTimeComputable (fun S : List Bool =>
      [wordVerdict (pairFstD S) (pairSndD S).length])) :
    PolyTimeComputable testStep := by sorry

theorem test_orbit (C : List Bool) (j : ℕ) :
    testStep^[j] (testInit C) =
      pairEncode C (pairEncode (List.replicate (queryCount C - j) true)
        (pairEncode (List.replicate (min j (queryCount C)) true)
          [decide (∀ r < min j (queryCount C), wordVerdict C r = true)])) := by sorry

theorem test_size (C : List Bool) (j : ℕ) :
    (testStep^[j] (testInit C)).length ≤ 12 * (C.length + 1) ^ 1 := by sorry

theorem candidate_readout (C : List Bool) :
    [candidate C] = if ctxGuard C then
      testOut (testStep^[2 * (C.length + 1) ^ 1] (testInit C)) else [false] := by sorry

def selectCtx (T : List Bool) (i : ℕ) : List Bool :=
  pairEncode (List.replicate (values T).length true) (pairEncode (Nat.bits i) T)

def selectInit (T : List Bool) : List Bool := pairEncode T (pairEncode [] (pairEncode [] []))

def selectStep (S : List Bool) : List Bool :=
  let T := pairFstD S
  let rank := pairFstD (pairSndD S)
  let flag := pairFstD (pairSndD (pairSndD S))
  let cap := Nat.log 2 (Nat.log 2 (values T).length)
  if flag ≠ [] then S else
    if rank.length < cap then
      if candidate (selectCtx T rank.length) then
        pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits rank.length)))
      else pairEncode T (pairEncode (rank ++ [true]) (pairEncode [] []))
    else pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits cap)))

def selectOut (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD S))

def SelectInv (T S : List Bool) : Prop :=
  (∃ i, i ≤ Nat.log 2 (Nat.log 2 (values T).length) ∧
    S = pairEncode T (pairEncode (List.replicate i true) (pairEncode [] [])) ∧
    ∀ j < i, candidate (selectCtx T j) = false) ∨
  (∃ i, i ≤ Nat.log 2 (Nat.log 2 (values T).length) ∧
    S = pairEncode T (pairEncode (List.replicate i true)
      (pairEncode [true] (Nat.bits (stage (values T))))))

def selectMeasure (S : List Bool) : ℕ :=
  if pairFstD (pairSndD (pairSndD S)) = [] then
    Nat.log 2 (Nat.log 2 (values (pairFstD S)).length) - (pairFstD (pairSndD S)).length + 1
  else 0

theorem selectInit_FP : PolyTimeComputable selectInit := by sorry

theorem selectStep_FP (hc : PolyTimeComputable (fun C => [candidate C])) :
    PolyTimeComputable selectStep := by sorry

theorem select_progress (T S : List Bool) (hI : SelectInv T S) :
    SelectInv T (selectStep S) ∧
      (0 < selectMeasure S → selectMeasure (selectStep S) < selectMeasure S) ∧
      (selectMeasure S = 0 → selectStep S = S) := by sorry

theorem select_size (T : List Bool) (j : ℕ) :
    (selectStep^[j] (selectInit T)).length ≤ 12 * (T.length + 1) ^ 1 := by sorry

theorem select_readout (T : List Bool) :
    selectOut (selectStep^[1 * (T.length + 1) ^ 1] (selectInit T)) =
      Nat.bits (stage (values T)) := by sorry

theorem candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [candidate S]) := by sorry

theorem stage_FP
    (hcheck : PolyTimeComputable (fun S => [candidate S])) :
    PolyTimeComputable (fun T => Nat.bits (stage (values T))) := by sorry

theorem stage_correct (vs : List ℕ)
    (hvs : ∀ m < vs.length, vs.getD m 0 = ladnerH m) :
    stage vs = ladnerH vs.length := by sorry

theorem memoStep_FP
    (hstage : PolyTimeComputable (fun T => Nat.bits (stage (values T)))) :
    PolyTimeComputable memoStep := by sorry

theorem memoInit_FP : PolyTimeComputable memoInit := by sorry

theorem memo_orbit (z : List Bool) (j : ℕ) :
    memoStep^[j] (memoInit z) =
      pairEncode (List.replicate z.length true)
        (BinArith.encWords ((List.range j).map (fun m => Nat.bits (ladnerH m)))) := by sorry

theorem memo_size (z : List Bool) (j : ℕ) (hj : j ≤ z.length + 1) :
    (memoStep^[j] (memoInit z)).length ≤ 4 * (z.length + 1) ^ 2 := by sorry

theorem memo_readout (z : List Bool) :
    BinArith.getW (memoStep^[1 * (z.length + 1) ^ 1] (memoInit z)) =
      Nat.bits (ladnerH z.length) := by sorry

-- This is an assembly schema, not an admission of the library target.
theorem memo_transfer
    (hstep : PolyTimeComputable memoStep) (hinit : PolyTimeComputable memoInit)
    (hsize : ∀ z j, j ≤ 1 * (z.length + 1) ^ 1 →
      (memoStep^[j] (memoInit z)).length ≤ 4 * (z.length + 1) ^ 2)
    (hread : ∀ z, BinArith.getW (memoStep^[1 * (z.length + 1) ^ 1] (memoInit z)) =
      Nat.bits (ladnerH z.length)) :
    PolyTimeComputable (fun z => Nat.bits (ladnerH z.length)) := by sorry
end LadnerRoutePoly
```

| Intermediate cluster | Lemmas it uses / required proof content |
|---|---|
| `shortWords_complete`, `shortWords_count` | Canonical `Nat.bits`/bit arithmetic and list equations. Prove the sentinel-rank representation rather than relying on private `EXP.enumWord_*` lemmas. |
| `short_deadline`, `numeric_envelope`, `short_SAT_envelope` | Port the bundled standard-axiom scratch numerical arguments; handle zero and degree zero explicitly. These are private facts, not invented existing library names. |
| `short_SAT_machine` | R0 as its explicit `linear` hypothesis, `mem_P_iff`, `exists_proj_decider 1 1`; identify the language by set extensionality. |
| `simulation_on_image` | R1 to expose the preparation witness; simulator accept/reject fields, `ComputesInTime.mono`, `exists_comp_on_image`, `computesFunInTime_iff`, and `composition_clock`. This discharges the conditional simulator transfer only after **both** displayed premises are proved. |
| `query_preparation` | Guard/canonical arithmetic/length-bits/pair APIs and saturated power; the statement demands a concrete machine and its `C(n+1)^q` setup bound. |
| `query_budget` | `numeric_envelope` on good queries, empty/default case on bad queries, and the public projection-length bounds. |
| `composition_clock` | Pointwise polynomial majorization, including `q=0` and `e=0`; supplies the exact overhead from the image-composition theorem. |
| `short_SAT_on_image` | `short_SAT_machine`, its envelope, R1, R5/R6, and `exists_comp_on_image`; preserves the input preparation cost. |
| `short_pad_FP` | The common parser/syntax equations, saturated power, `getW_pairEncode_bits`, `polyTimeComputable_getW`, `countW_eq`, normalization/mapW, and guarded short-SAT image transfer. Exponents read from malformed tables may be huge; never expand them. |
| `candidate_FP` | Guarded simulation transfer above, `short_pad_FP`, `shortWords_complete/count`, and the existing iterator for the word sweep, with a Boolean conjunction flag. Prove a polynomial length invariant on **all** states reached by each initialized scan; bound scan scratch in serialized length. |
| `stage_FP` | `candidate_FP`, the existing iterator for candidates, and the first-success flag. Normalize returned table words; count table entries with `countW`, not byte length. A never-successful scan returns the exact cap. |
| `stage_correct` | Table hypothesis, `padSAT_congr`, `ladnerH_eq`, and logarithmic decrease; no computational premise. |
| `memoStep_FP`, `memoInit_FP` | `stage_FP`, projections, append and pair closure; `polyTimeComputable_unary` and a constant empty word. |
| `memo_orbit` | Induction using `stage_correct`, `encWords_append_singleton`, `decWords_encWords`, and canonical value readings. |
| `memo_size` | `memo_orbit`, `ladnerH_le`, `length_bits_le_self`, `length_encWords_le`, and pairing lengths. |
| `memo_readout` | `memo_orbit`, `getW_pairEncode_bits`, and the in-range list lookup at index `|z|`. |
| `memo_transfer` | Exactly `BinArith.polyTimeComputable_iterate hstep hinit 1 1 4 2 hsize`, then `polyTimeComputable_getW.comp`, then function extensionality with `hread`. |

The two finite scans also have concrete serialized transitions above. `testInit`/`testStep` keep an immutable context plus remaining-query unary counter, completed-rank unary counter and conjunction bit. `test_orbit` specifies the conjunction after every round; `test_size` supplies `12(|C|+1)` on the whole orbit. `candidate_readout` uses `2(|C|+1)` iterations and masks an invalid context. `wordVerdict_FP` is the guarded single-query leaf using the already displayed short-simulation and short-padding transfers. `log_eq_bits_length` and `binary_log_FP` supply floor-log arithmetic without opening a foreign definition. `testInit_FP` must construct the unary query budget within its proven linear value bound, using counted iteration and capped arithmetic rather than allocating an arbitrary binary value.

`selectInit`/`selectStep` keep the table, unary candidate rank, terminal flag and selected bits. `SelectInv` states that every earlier candidate failed, or that the terminal value is the exact stage minimum/fallback. `select_progress` gives invariant preservation, strict positive-measure decrease and a fixed terminal state. `select_size` gives `12(|T|+1)` uniformly; `select_readout` finishes after `|T|+1` rounds. `stage_FP` is precisely the existing iterator applied to these selection functions, followed by the projection readout. Both scan groups are private applications of the existing public iterator, not new private hosts. Their FP, semantic and size proofs remain fill obligations.

The `memo_orbit` equation specifies every entry at every stage, and `memo_size` is uniform over the required orbit. None of these admitted contracts has been pre-shipped as a proved implementation.

**Readers needed:** R0, R1, R5, R6a,b. All reads of `padSAT`/`ladnerH` are in their owner or through the six approved readings; table and arithmetic reads use §2. No public reader for SAT's private verifier representation or total CNF decoder is needed.

**Open premises:** all displayed helper proofs; especially the saturated-power implementation, input preparation/setup clock, both scan FP proofs with their actual orbit bounds, and exact memo semantics. The historically proved numerical envelopes retire only arithmetic leaves. They do not retire these constructions. Targets 3 and 4 are not prerequisites. The pending approved reader is an allowed route assumption, not a proved theorem at this pin.

**Size/order:** approximately 1,200–2,500 lines excluding shared owner APIs, 5–12 focused agent-days, likely multiple continuation briefs. First retire arithmetic/preparation, then candidate scan, then selection/memo/readout. Split by dispatch stages in the same owner file rather than creating new files solely for line count. Independent scratch proof development can overlap with targets 3/4/5; owner-file fills are serial.

**Risks:** a polynomial deadline value bound is essential; nested scans must be charged in the macro-step FP proof; table entry count differs from its encoded length; a malformed state cannot induce exponential iteration; a size bound on final states alone is insufficient; proving a classical equation is not proving an FP implementation. Preserve least success and fallback exactly. Never assume monotonicity of the selected function.

## 7. Target 2 — `Complexity.SAT_H_mem_NP`

### Mathematical route

Following [AB09, Theorem 3.3 and its proof], parse the final false separator and verify the prescribed unary suffix, then verify SAT of the recovered prefix with a certificate. The certificate contains only the SAT witness; the deterministic parser supplies the prefix, so guessing a split is unnecessary. For R0's verifier `V`, define the paired verifier below. Its certificate has length `|prefix|+1≤|input|+1`, since a parsed prefix is strictly shorter than the padded word.

`verifier_P` is the intersection of syntax/length tests and the polynomial preimage of `V` under the reconstruction `prefix ++ certificate`. `hp` is applied to the prefix word, not the padded word. Use capped exponentiation to compare the required power with the actual suffix length. Apply `mem_NP_iff_exists_length_le` with coefficient and degree both one, then specialize `h=ladnerH` using target 1 and rewrite `SAT_H_eq`. The public exact linear SAT reader makes this especially simple, although ordinary NP membership would also suffice for this target if one accepted a larger certificate polynomial.

### Exact intermediate statements, homes, and dependencies

`verifier`, `verifier_P`, `verifier_equiv`, and `padded_NP` are private in existing `Ladner.lean`. The standalone probe's `parse`, `syntax`, and `parseWord` repeat §3's specification only for independent typing; production reuses the single common implementation. `verifier_P` uses `parse_FP`, `syntax_FP`, FP reconstruction/length comparisons, `preimage_mem_P`, and `inter_mem_P`. `verifier_equiv` uses common parser membership, its strict-prefix length fact and the supplied certificate equivalence. `padded_NP` uses those two and `mem_NP_iff_exists_length_le`. No new public general padding theorem is proposed.

```lean
namespace LadnerRouteNP

-- Mathematical parser specification; implement through reverse/uRest/hasFalse,
-- not by compiling a new private parser host.
def parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

def padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

def parseWord (y : List Bool) : List Bool :=
  match parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

def verifier (h : ℕ → ℕ) (V : Language Bool) : Language Bool :=
  {S | match parse (pairFstD S) with
    | none => False
    | some (p, t) => t = p.length ^ h p.length ∧
      (pairSndD S).length = p.length + 1 ∧ p ++ pairSndD S ∈ V}

theorem verifier_P {h : ℕ → ℕ} {V : Language Bool}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hV : V ∈ P) : verifier h V ∈ P := by sorry

theorem verifier_equiv {h : ℕ → ℕ} {V : Language Bool}
    (hcert : ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) (y : List Bool) :
    y ∈ padSAT h ↔ ∃ u : List Bool,
      u.length ≤ y.length + 1 ∧ pairEncode y u ∈ verifier h V := by sorry

theorem padded_NP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    padSAT h ∈ NP := by sorry
end LadnerRouteNP
```

**Readers needed:** R0; R1 is needed only in a machine-level realization of the common leaves, not to destruct `NP`. R5/R6 are needed if decider contracts are read directly; the closure route avoids that. The available paired-certificate characterization already supplies the NP boundary.

**Open premises:** target 1, R0's landing, common parser/saturated syntax and these three helper proofs. The target does not assume SAT is hard or P differs from NP.

**Size/order:** approximately 200–450 lines after common leaves, 1–3 agent-days. Wait for target 1 (or cite its frozen target only under a separately authorized proved-modulo fill regime). Can be developed in scratch alongside the general shrinking proof; cannot write Ladner simultaneously with another fill.

**Risks:** the SAT reader uses actual concatenation `prefix ++ u`, whereas the outer NP reader uses `pairEncode y u`; preserve both layouts. Check the last false, all-true rejection, empty prefix, exponent zero, and `0^0`. A polynomial bound on the exponent's **bit length** does not justify allocating the full power.

## 8. Target 5 — `Complexity.SAT_mem_P_of_padSAT_NPHard`

### Mathematical route

This is the shrinking part of [AB09, Theorem 3.3 and its proof], with the approved stronger `NPHard` premise. R3/R2 and `SAT_mem_NP` give a single polynomial reduction `f` from SAT; `PolyTimeComputable.output_length_le` gives `|f x|≤A(|x|+1)^d`. Choose `B` such that `h(m)≥2(d+1)` for every `m≥B`. This uses eventual divergence exactly; downward jumps before that threshold are harmless.

For a syntactically valid output with prefix length `m≥B`, `m^h(m)≤|f x|`. When `|x|≥A*2^d+2`, this implies `m²≤|x|`: otherwise `m^(2d+2)=(m²)^(d+1)>|x|^(d+1)>A(|x|+1)^d`, a contradiction. Taking `K=A*2^d+2` ensures `K≥2`, so `m²≤|x|` also gives `m<|x|`. This estimate applies to **every syntactically valid output**, including outputs on no-instances; it is not restricted to members of the padded language. Invalid padding is rejected using `hp` and the common capped syntax test.

The state is `pairEncode [] current` while live and `pairEncode [answer] []` when terminal. Terminal states are fixed. If `|current|<K`, answer with the finite SAT table for that threshold. Otherwise compute `f current`, reject bad syntax, answer from the finite table when its parsed prefix has length `<B`, and otherwise replace current by that prefix. The reduction equivalence and parser uniqueness preserve the SAT answer in the live case. Thus the measure `|current|+1` strictly decreases on live states and is zero on terminal states.

Run the existing generic iterator `|x|+1` times from `pairEncode [] x`, rather than compiling an unbounded recursive call. All live words are at most the original input length; state size is at most `4(|x|+1)`. `iterate_measure_eq_zero` proves termination within the allotted rounds, and the invariant identifies the terminal bit with SAT. Each step is FP, including the two finite tables; its reduction output and parser scratch costs are inside that step's polynomial time, not in the persistent state bound. The final result uses `mem_P_of_test`. No SAT self-reduction, sparse-language theorem, NP membership of `padSAT h`, or monotonicity of `h` is assumed.

### Exact intermediate statements, homes, and dependencies

All declarations below are private in existing `Ladner.lean`; use the common parser instead of a second production implementation. `step` is the pure transition of an application of the existing iterator, not a new recursion host. The FP theorem must implement its classical small SAT bits by the fixed finite tables, never by invoking a general SAT solver during a large-input round.

```lean
namespace LadnerRouteShrink

-- Mathematical parser specification; implement through reverse/uRest/hasFalse,
-- not by compiling a new private parser host.
def parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

def padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

def parseWord (y : List Bool) : List Bool :=
  match parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

def smallSAT (B : ℕ) (x : List Bool) : Bool := decide (x.length < B ∧ x ∈ SAT)

def step (h : ℕ → ℕ) (f : List Bool → List Bool) (B K : ℕ)
    (S : List Bool) : List Bool :=
  let x := pairSndD S
  if pairFstD S ≠ [] then S
  else if x.length < K then pairEncode [smallSAT K x] []
  else match parse (f x) with
    | none => pairEncode [false] []
    | some (p, t) =>
      if t ≠ p.length ^ h p.length then pairEncode [false] []
      else if p.length < B then pairEncode [smallSAT B p] []
      else pairEncode [] p

def Inv (x S : List Bool) : Prop :=
  (∃ y, S = pairEncode [] y ∧ y.length ≤ x.length ∧ (y ∈ SAT ↔ x ∈ SAT)) ∨
  (∃ b : Bool, S = pairEncode [b] [] ∧ (b = true ↔ x ∈ SAT))

def measure (S : List Bool) : ℕ :=
  if pairFstD S = [] then (pairSndD S).length + 1 else 0

theorem reduction_from_hardness {h : ℕ → ℕ} (hH : NPHard (padSAT h)) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ x, x ∈ SAT ↔ f x ∈ padSAT h := by sorry

theorem prefix_square_bound {h : ℕ → ℕ} (A d B n m : ℕ)
    (hh : ∀ r ≥ B, 2 * (d + 1) ≤ h r)
    (hn : A * 2 ^ d + 2 ≤ n) (hm : B ≤ m)
    (hsize : m ^ h m ≤ A * (n + 1) ^ d) : m ^ 2 ≤ n := by sorry

theorem reduction_shrinks {h : ℕ → ℕ} {f : List Bool → List Bool}
    (hf : PolyTimeComputable f)
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) :
    ∃ B K, 2 ≤ K ∧ ∀ x p t,
      K ≤ x.length → parse (f x) = some (p, t) →
      t = p.length ^ h p.length → B ≤ p.length →
        p.length ^ 2 ≤ x.length ∧ p.length < x.length := by sorry

theorem smallSAT_FP (B : ℕ) :
    PolyTimeComputable (fun x => [smallSAT B x]) := by sorry

theorem step_FP {h : ℕ → ℕ} {f : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hf : PolyTimeComputable f) (B K : ℕ) :
    PolyTimeComputable (step h f B K) := by sorry

theorem progress {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hK : 2 ≤ K)
    (hred : ∀ x, x ∈ SAT ↔ f x ∈ padSAT h)
    (hshrink : ∀ x p t, K ≤ x.length → parse (f x) = some (p, t) →
      t = p.length ^ h p.length → B ≤ p.length → p.length < x.length)
    (x S : List Bool) (hI : Inv x S) :
    Inv x (step h f B K S) ∧
      (0 < measure S → measure (step h f B K S) < measure S) ∧
      (measure S = 0 → step h f B K S = S) := by sorry

theorem orbit_size {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hinv : ∀ x S, Inv x S → Inv x (step h f B K S)) (x : List Bool) (j : ℕ) :
    ((step h f B K)^[j] (pairEncode [] x)).length ≤ 4 * (x.length + 1) ^ 1 := by sorry

theorem final_readout {h : ℕ → ℕ} {f : List Bool → List Bool} {B K : ℕ}
    (hprogress : ∀ x S, Inv x S →
      Inv x (step h f B K S) ∧
        (0 < measure S → measure (step h f B K S) < measure S) ∧
        (measure S = 0 → step h f B K S = S)) (x : List Bool) :
    pairFstD ((step h f B K)^[1 * (x.length + 1) ^ 1] (pairEncode [] x)) =
      [decide (x ∈ SAT)] := by sorry

theorem shrinking_transfer {h : ℕ → ℕ} {f : List Bool → List Bool} (B K : ℕ)
    (hstep : PolyTimeComputable (step h f B K))
    (hsize : ∀ x j, j ≤ 1 * (x.length + 1) ^ 1 →
      ((step h f B K)^[j] (pairEncode [] x)).length ≤ 4 * (x.length + 1) ^ 1)
    (hout : ∀ x, pairFstD ((step h f B K)^[1 * (x.length + 1) ^ 1]
      (pairEncode [] x)) = [decide (x ∈ SAT)]) : SAT ∈ P := by sorry
end LadnerRouteShrink
```

| Intermediate | Lemmas it uses |
|---|---|
| `reduction_from_hardness` | R3, R2, and `SAT_mem_NP`. |
| `prefix_square_bound` | Pointwise natural-power inequalities, with the explicit threshold `A*2^d+2`; no P/NP premise. |
| `reduction_shrinks` | `hf.output_length_le`, `hu` at `2(d+1)`, `prefix_square_bound`, `parse_some`/`parsed_length`. |
| `smallSAT_FP` | `small_SAT_table` and `finite_lookup_FP` from the single common implementation. |
| `step_FP` | `hp`, `hf`, parser FP and saturated syntax, the two finite tables, FP Boolean/conditional/pair/projection closure. It does not need hardness or divergence to be an FP function. |
| `progress` | `pad_membership`, parser uniqueness, `hred`, `hshrink`, exact branch equations of the owner's private step, and the finite-table specification. Covers live and both terminal bits. |
| `orbit_size` | Initial invariant and `BinArith.iterate_invariant` using `hinv`, pairing length equations. |
| `final_readout` | `progress`, `BinArith.iterate_measure_eq_zero`, the initialized measure `|x|+1`, and the terminal clause of `Inv`. |
| `shrinking_transfer` | `BinArith.polyTimeComputable_iterate` with `(1,1,4,1)`, FP init/projection, `hout`, then `mem_P_of_test` and set extensionality. |

**Readers needed:** R2/R3 for hardness and reduction extraction; R1 as needed by common arithmetic implementation. No NPComplete reader, no sharp SAT verifier, and no SAT decoder reader is required by this general theorem. The route uses the same registered iteration and finite-word access infrastructure as target 1, not a newly designed shrinking host.

**Open premises:** common parser/saturated power/finite table, the shrinking inequality and all displayed helper proofs, import/host coverage, and R2/R3. Target 1, target 2, and target 4 are not mathematical premises: `hp` and `hu` are already parameters of this target. R0 is also not a premise of this target.

**Size/order:** approximately 600–1,200 lines after common leaves, 3–7 agent-days, with numerical/semantic scratch work parallel to target 1. Dispatch the actual owner-file fill only once the shared leaves and reader contracts are available.

**Risks:** validity of padding is decidable independently of prefix SAT; check syntax before recursing. Prefix `<B` and input `<K` are distinct exceptional sets and both need finite tables. A terminal false flag is a **nonempty word** `[false]`, distinct from the live empty flag `[]`. `hp` has no numeric growth restriction on `h`; all powers must stay capped. One shrinking call per round is essential; do not accidentally branch recursively over possible separators. Never unfold `NPHard` or a reduction existential in a consumer.

## 9. Target 6 — `Complexity.SAT_H_intermediate`

### Mathematical route

As in [AB09, Theorem 3.3 and its proof], combine the two contradictions with NP membership. First suppose `SAT_H ∈ P`. Target 3 bounds `ladnerH` by some `C`; target 1 makes its bits FP. The literal padding map has length at most `2(n+1)^(C+1)` and is FP. It reduces SAT to `padSAT ladnerH`, because the final false separator gives a unique prefix. `mem_P_of_polyTimeReducible` and `P_eq_NP_of_NPHard_mem_P SAT_NPHard` contradict `P≠NP`.

For bounded padding one may select among the fixed finitely many exponent cases `0,…,C`; each unary power is built by finitely many applications of `polyTimeComputable_unary` and `polyTimeComputable_mulU`. Alternatively use saturated power and a proven unary output budget. A bit-length bound alone is not an emitter. The displayed `bounded_pad_FP` is the precise construction obligation; no public seventh target is introduced.

Now outside P, target 4 gives eventual divergence. If `SAT_H` were NP-complete, R4 would give hardness; rewrite `SAT_H_eq` and apply target 5 with target 1's computability. Again `SAT_NPHard` collapses P and NP. Combine with target 2. The existing `ladner` packaging theorem needs no proof change.

### Exact intermediate statements, homes, and dependencies

All six helpers below are private in existing `Ladner.lean`. `bounded_pad_length` uses the padding map's own equation and `hb`. `bounded_pad_FP` uses `hp`, finite selection by the canonical equality tests, unary multiplication, append/pair closure, and the length bound (or the shared saturated implementation). `padWord_membership` uses the common parser's unique final-false decomposition and `mem_padSAT_iff`. `bounded_pad_reduction` uses those two semantic/computational lemmas and R2. `outside_P` uses target 3 and the SAT collapse argument above; `not_complete` uses R4, target 4, target 5 and the same collapse. Their target premises are explicit in the probe. The library target itself assembles their results and target 2, under its unchanged hypothesis.

```lean
namespace LadnerRouteFinal
def padWord (h : ℕ → ℕ) (x : List Bool) : List Bool :=
  x ++ false :: List.replicate (x.length ^ h x.length) true

theorem bounded_pad_length {h : ℕ → ℕ} {C : ℕ} (hb : ∀ n, h n ≤ C)
    (x : List Bool) : (padWord h x).length ≤ 2 * (x.length + 1) ^ (C + 1) := by sorry

theorem bounded_pad_FP {h : ℕ → ℕ} {C : ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hb : ∀ n, h n ≤ C) : PolyTimeComputable (padWord h) := by sorry

theorem padWord_membership (h : ℕ → ℕ) (x : List Bool) :
    padWord h x ∈ padSAT h ↔ x ∈ SAT := by sorry

-- Private obligation, not a seventh public Ladner target.
theorem bounded_pad_reduction {h : ℕ → ℕ} {C : ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)))
    (hb : ∀ n, h n ≤ C) : PolyTimeReducible SAT (padSAT h) := by sorry

theorem outside_P (hne : P ≠ NP)
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (ladnerH x.length)))
    (hbounded : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C) : SAT_H ∉ P := by sorry

theorem not_complete (hne : P ≠ NP)
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (ladnerH x.length)))
    (hout : SAT_H ∉ P)
    (hdiv : SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n)
    (hpadding : ∀ h : ℕ → ℕ,
      PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length)) →
      (∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) → NPHard (padSAT h) → SAT ∈ P) :
    ¬ NPComplete SAT_H := by sorry
end LadnerRouteFinal
```

**Readers needed:** R2 and R4; R1 only if a concrete machine is extracted in the bounded-padding implementation. `SAT_H_eq`, `mem_padSAT_iff`, and the existing P/reduction theorems cover the other boundaries. The helper is private: do not publish a new `SAT_reducible_padSAT_of_bounded` without a separate ruling.

**Open premises:** targets 1–5, the bounded-padding FP/semantic lemmas, common final-separator uniqueness, and R2/R4. The target is a small assembly only once these are proved; otherwise its short conjunction hides a substantial reduction-construction premise.

**Size/order:** 150–350 lines including bounded-padding construction, 1–3 agent-days; final logical assembly alone about 20–50 lines. Last owner-file fill. The bounded-padding scratch proof can be developed earlier, independently of the memo proof, using `hp` as a hypothesis.

**Risks:** boundedness is of the exponent's **value**, not its encoded length. Empty-prefix padding uses `0^0=1`. Recovering a prefix by an arbitrary first false instead of the final false would break the reduction. NPComplete's conjunction cannot be projected through a foreign definition without R4.

## 10. Dependency, scope, and risk assessment

```mermaid
graph TD
  R[Owner readers and pending SAT reader] --> C[Common parser and capped arithmetic]
  R --> B[3. Bounded selector]
  R --> U[4. Divergence selector]
  C --> H[1. Memo computation]
  C --> N[2. Padded NP verifier]
  H --> N
  C --> S[5. General shrinking decider]
  B --> F[6. Intermediate language]
  U --> F
  H --> F
  N --> F
  S --> F
```

The graph groups preparation for readability: target 5 needs R2/R3, **not** R0; target 3 needs R5/R6, **not** the parser/power construction; target 4 needs fixed-clock preparation, **not** the general memo implementation. The normalizing imports and host-coverage decision precede the affected machine fills.

| Work | Approximate new Lean lines | Focused agent-days | May develop independently of |
|---|---:|---:|---|
| Owner readers, common parser/finite tables and saturated arithmetic | 350–800 | 2–5 | Qualitative selector mathematics |
| Target 3 | 150–300 | 0.5–2 | Targets 1,2,4,5 |
| Target 4 | 200–400 | 1–3 | Targets 1,2,3,5 |
| Target 1 | 1,200–2,500 | 5–12 | Targets 3,4,5 |
| Target 2 | 200–450 | 1–3 | Target 5, once common leaves and target 1 are available |
| Target 5 | 600–1,200 | 3–7 | Special Ladner function targets |
| Target 6 | 150–350 | 1–3 | Bounded-padding subproof may be drafted early; final assembly waits |

These are engineering estimates, not budgets or guarantees. Serialization/guard proofs and Rule 10 seals can dominate the line count. All six targets share one owner file, so **none of their actual source-writing fills may overlap**. Independent scratch development, SAT-owner work, reader-owner work, and arithmetic-owner work have disjoint possible ownership. Work in `PolyTime.lean`, `Reductions.lean`, `DTIME.lean`, and `Deterministic.lean` also needs serial integration and downstream validation as appropriate; do not merge snapshots of separately replayed trees.

Before a brief is dispatched, the maintainer must replace the relevant `sorry` sketches here by a concrete contracted route preflight: identify each step/init/readout, discharge the iterator's actual size premise, check the row/word layout, obtain any public API/import decision, bind host registry coverage, seal foreign definitions with paired controls, and replay on the merged tree. No blanket fill-readiness claim follows from this draft. No change to LD1–LD7 or to the audited source statements was found necessary.

Carry the following adversarial cases into that preflight: `n=0,1,2,3` (zero cap), thresholds 4/16, `i=0`, empty input and empty prefix, exponent zero, `0^0`, all-true/no-separator strings, embedded false bits and final-false uniqueness, malformed SAT encodings (they retain their total-decoder semantics), fallback without any successful candidate, nonmonotone but eventually diverging `h`, overlarge binary exponents in malformed tables, and both Boolean terminal flags. No new well-formed-SAT restriction is introduced.

## 11. Execution evidence

Final statement checks (all exit 0; the counts are intentional **new probe admissions**, not imported target proofs):

| Probe | Exit | Errors | `sorry` warnings / bodies |
|---|---:|---:|---:|
| `Route-API.lean.txt` | 0 | 0 | 0 / 0 |
| `Route-Readers.lean.txt` | 0 | 0 | 8 / 8 |
| `Route-SAT_H_intermediate.lean.txt` | 0 | 0 | 6 / 6 |
| `Route-SAT_H_mem_NP.lean.txt` | 0 | 0 | 3 / 3 |
| `Route-SAT_mem_P_of_padSAT_NPHard.lean.txt` | 0 | 0 | 9 / 9 |
| `Route-Shared.lean.txt` | 0 | 0 | 11 / 11 |
| `Route-ladnerH_bounded_of_mem_P.lean.txt` | 0 | 0 | 5 / 5 |
| `Route-ladnerH_polyTime.lean.txt` | 0 | 0 | 34 / 34 |
| `Route-ladnerH_unbounded_of_not_mem_P.lean.txt` | 0 | 0 | 6 / 6 |

Total: 82 intentional admissions; 144 existing full-name checks. The API/axiom probe has no new admission.

See `probe-validation.log` for the exact toolchain, bootstrap/probe exit codes, error counts, intentional sorry counts, existing API checks, axiom inventory, and source hashes. The environment is macOS/APFS: the Linux `/proc`/cgroup fields in addendum v2.6 are not applicable, and native CPU/memory/filesystem readings are recorded instead. Dependencies are the main campaign checkout's `.lake/packages` symlink, permitted by the addendum, with every present package checked against this pin's manifest. No cache was fetched and no package tree was copied. No other session's TCSlib object/scratch tree was used: the import closure was bootstrapped afresh from the archived source pin into this task's own scratch olean tree, serially through the inspected throttled `leanelab-o.sh`. No `lake build` was run.

The macOS sandbox denies `nice`'s priority adjustment; the underlying Lean still runs with `-j4` and only one process started by this task at a time. An initial `/usr/bin/time -l` wrapper could not read `kern.clockrate` and returned 1 after producing a Configuration object. That resource-wrapper attempt was discarded and the serial bootstrap was restarted from the first module without that wrapper; subsequent child exit statuses are the actual script/Lean statuses. Cumulative child maximum RSS is reported as an upper bound, not falsely as each module's peak. These are disclosed environment deviations, not mathematical findings and not reasons to abandon the item. The process-executable shim was not needed.

All route theorem bodies intentionally use `sorry`. These checks establish import/name/type compatibility, not proof correctness, target completion, foreign-boundary seal success, or a merged-tree replay. The bootstrap's inherited warnings and the pin's six Ladner admissions are distinct from the probe admissions. The existing API axiom inventory in the log identifies any inherited `sorryAx` separately. This is a route-drafting delivery, not a zero-sorry certificate.

## 12. Summary — fill briefs to issue

1. **Reader preparation.** Land the already approved `SAT_exists_linear_verifier` in `ClassNP/SAT.lean`; obtain decisions for and prove R1–R6 in their existing owner files. Authorize the precise proof-route imports and bind existing iterator/search/simulator hosts to registry and gate coverage. No Ladner target is filled in this brief.
2. **Arithmetic and parser leaves.** After the public-API ruling, add `BinArith.powCap`, its full and canonical equations, and its FP theorem in `ClassP/BinaryArith/Mul.lean`; add only the private parser, padding-syntax, and finite-table helpers in `Diagonalization/Ladner.lean`. Keep separate file ownership for arithmetic and Ladner work.
3. **Bounded selector.** In `Ladner.lean`, prove only `ladnerH_bounded_of_mem_P` and the five private helpers in §4. This does not wait for the memo computation or parser.
4. **Divergence selector.** In `Ladner.lean`, prove only `ladnerH_unbounded_of_not_mem_P`, its fixed-clock preparation/FP helpers, and the finite-witness threshold in §5. This does not wait for `ladnerH_polyTime`.
5. **Memo computation, staged.** In `Ladner.lean`, first prove the short SAT/simulation preparation contracts, then the two bounded scans, then the table orbit/size/readout lemmas, and finally `ladnerH_polyTime`. Use the existing iterator; add no public memo host. Expect continuation briefs.
6. **Padded NP membership.** In `Ladner.lean`, prove the private paired verifier lemmas and `SAT_H_mem_NP`, after brief 5 and common leaves.
7. **General shrinking decider.** In `Ladner.lean`, prove the square-root bound, two finite exception tables, private iterator transition/invariant/readout, and `SAT_mem_P_of_padSAT_NPHard`. Its mathematical work can precede brief 5; its source fill is scheduled serially.
8. **Final assembly.** In `Ladner.lean`, prove the private bounded-padding reduction and `SAT_H_intermediate` after targets 1–5. Leave the four definitions, six readings, six target signatures, and existing `ladner` packaging unchanged. No public seventh target, new file, or new private host is in scope.

## ===== campaign/items/ladner/fill-routes-request/delivery/Route-ladnerH_polyTime.lean.txt =====

/- Scratch statement-elaboration probe, not a library fill.
Source/import pin: 5ab222167eb12664d97d255766c5def15b6d5d50.
Every theorem body below is intentionally admitted. No target body is replaced.
Additional imports and proposed public interfaces need the decisions in the route report.
-/
import TCSlib.Complexity.Diagonalization.Ladner
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.ModelInvariance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Turing Complexity
open scoped Classical
noncomputable section

namespace LadnerRoutePoly
def values (T : List Bool) : List ℕ := (BinArith.decWords T).map LogProg.bitsVal

def shortWords (a : ℕ) : List (List Bool) :=
  (List.range (2 ^ (a + 1) - 1)).map (fun r => (Nat.bits (r + 1)).dropLast)

def stage (vs : List ℕ) : ℕ :=
  let n := vs.length
  if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
      ∀ x : List Bool, x.length ≤ Nat.log 2 n →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0)) then Nat.find hex
  else Nat.log 2 (Nat.log 2 n)

def candidate (S : List Bool) : Bool :=
  let n := (pairFstD S).length
  let i := LogProg.bitsVal (pairFstD (pairSndD S))
  let vs := values (pairSndD (pairSndD S))
  decide (n = vs.length ∧ i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT (fun m => vs.getD m 0)))

def memoInit (z : List Bool) : List Bool :=
  pairEncode (List.replicate z.length true) []

def memoStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairSndD S ++ pairEncode (Nat.bits (stage (values (pairSndD S)))) [])

theorem shortWords_complete (a : ℕ) (x : List Bool) :
    x ∈ shortWords a ↔ x.length ≤ a := by sorry

theorem shortWords_count (n : ℕ) :
    (shortWords (Nat.log 2 n)).length ≤ 2 * (n + 1) := by sorry

theorem short_deadline (n i m : ℕ)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hm : m ≤ Nat.log 2 n) :
    i * m ^ i ≤ n ^ 3 := by sorry

theorem numeric_envelope (D n i : ℕ) (x : List Bool)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hx : x.length ≤ Nat.log 2 n) :
    D * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ D ≤
      (D * 4 ^ D) * (n + 1) ^ (3 * D) := by sorry

theorem short_SAT_machine
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
      (fun m => b * 2 ^ (m + 1) *
        (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2)) := by sorry

theorem short_SAT_envelope (a b d n m : ℕ) (hm : m ≤ Nat.log 2 n) :
    b * 2 ^ (m + 1) * (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2) ≤
      (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by sorry

-- Explicit preparation and envelope transfer: no preparation premise is implicit.
theorem simulation_on_image (code input : List Bool → List Bool)
    (deadline : List Bool → ℕ)
    (hprep : PolyTimeComputable (fun z =>
      pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)))
    (hbudget : ∃ A e, ∀ z, expCode.simDegree *
      ((code z).length + (input z).length + deadline z + 1) ^ expCode.simDegree ≤
        A * (z.length + 1) ^ e) :
    PolyTimeComputable (fun z => [decide
      ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))]) := by sorry

def validQuery (S : List Bool) : Prop :=
  LogProg.bitsVal (pairFstD (pairSndD S)) <
      Nat.log 2 (Nat.log 2 (pairFstD S).length) ∧
    (pairSndD (pairSndD S)).length ≤ Nat.log 2 (pairFstD S).length

def queryCode (S : List Bool) : List Bool :=
  if validQuery S then Nat.bits (LogProg.bitsVal (pairFstD (pairSndD S))) else []
def queryInput (S : List Bool) : List Bool :=
  if validQuery S then pairSndD (pairSndD S) else []
def queryDeadline (S : List Bool) : ℕ :=
  if validQuery S then
    LogProg.bitsVal (pairFstD (pairSndD S)) *
      (pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))
  else 0

def queryPrep (S : List Bool) : List Bool :=
  pairEncode (pairEncode (Nat.bits (queryDeadline S)) (queryCode S)) (queryInput S)

theorem query_preparation :
    ∃ (M : FinTM Bool) (C q : ℕ),
      M.ComputesFunInTime queryPrep (fun n => C * (n + 1) ^ q) := by sorry

theorem query_budget (S : List Bool) :
    expCode.simDegree *
      ((queryCode S).length + (queryInput S).length + queryDeadline S + 1) ^
        expCode.simDegree ≤
      (expCode.simDegree * 4 ^ expCode.simDegree) *
        (S.length + 1) ^ (3 * expCode.simDegree) := by sorry

theorem composition_clock (C q A e n : ℕ) :
    2 * (C * (n + 1) ^ q) + A * (n + 1) ^ e + 2 ≤
      (2 * C + A + 2) * (n + 1) ^ max q e := by sorry

theorem short_SAT_on_image (f : List Bool → List Bool)
    (hf : PolyTimeComputable f)
    (hshort : ∀ z, (f z).length ≤ Nat.log 2 z.length)
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun z => [decide (f z ∈ SAT)]) := by sorry

theorem short_pad_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool => [decide
      ((pairFstD S).length ≤ Nat.log 2 (values (pairSndD S)).length ∧
        pairFstD S ∈ padSAT (fun m => (values (pairSndD S)).getD m 0))]) := by sorry

-- Concrete finite-scan states: no classical quantifier is executed by a host.
def ctxGuard (C : List Bool) : Prop :=
  (pairFstD C).length = (values (pairSndD (pairSndD C))).length ∧
    LogProg.bitsVal (pairFstD (pairSndD C)) <
      Nat.log 2 (Nat.log 2 (pairFstD C).length)

def wordVerdict (C : List Bool) (r : ℕ) : Bool :=
  let x := (Nat.bits (r + 1)).dropLast
  let i := LogProg.bitsVal (pairFstD (pairSndD C))
  decide (ctxGuard C ∧ x.length ≤ Nat.log 2 (pairFstD C).length ∧
    ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
      x ∈ padSAT (fun m => (values (pairSndD (pairSndD C))).getD m 0)))

def queryCount (C : List Bool) : ℕ := 2 ^ (Nat.log 2 (pairFstD C).length + 1) - 1

def testInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (List.replicate (queryCount C) true) (pairEncode [] [true]))

def testStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let rank := pairFstD (pairSndD (pairSndD S))
  let flag := pairSndD (pairSndD (pairSndD S))
  if rem = [] then S else
    pairEncode C (pairEncode (rem.drop 1)
      (pairEncode (rank ++ [true]) [flag.headD false && wordVerdict C rank.length]))

def testOut (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD S))

theorem log_eq_bits_length (n : ℕ) :
    Nat.log 2 n = (Nat.bits n).length - 1 := by sorry

theorem binary_log_FP : PolyTimeComputable
    (fun w : List Bool => Nat.bits (Nat.log 2 (LogProg.bitsVal w))) := by sorry

theorem wordVerdict_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool =>
      [wordVerdict (pairFstD S) (pairSndD S).length]) := by sorry

theorem testInit_FP : PolyTimeComputable testInit := by sorry

theorem testStep_FP
    (hw : PolyTimeComputable (fun S : List Bool =>
      [wordVerdict (pairFstD S) (pairSndD S).length])) :
    PolyTimeComputable testStep := by sorry

theorem test_orbit (C : List Bool) (j : ℕ) :
    testStep^[j] (testInit C) =
      pairEncode C (pairEncode (List.replicate (queryCount C - j) true)
        (pairEncode (List.replicate (min j (queryCount C)) true)
          [decide (∀ r < min j (queryCount C), wordVerdict C r = true)])) := by sorry

theorem test_size (C : List Bool) (j : ℕ) :
    (testStep^[j] (testInit C)).length ≤ 12 * (C.length + 1) ^ 1 := by sorry

theorem candidate_readout (C : List Bool) :
    [candidate C] = if ctxGuard C then
      testOut (testStep^[2 * (C.length + 1) ^ 1] (testInit C)) else [false] := by sorry

def selectCtx (T : List Bool) (i : ℕ) : List Bool :=
  pairEncode (List.replicate (values T).length true) (pairEncode (Nat.bits i) T)

def selectInit (T : List Bool) : List Bool := pairEncode T (pairEncode [] (pairEncode [] []))

def selectStep (S : List Bool) : List Bool :=
  let T := pairFstD S
  let rank := pairFstD (pairSndD S)
  let flag := pairFstD (pairSndD (pairSndD S))
  let cap := Nat.log 2 (Nat.log 2 (values T).length)
  if flag ≠ [] then S else
    if rank.length < cap then
      if candidate (selectCtx T rank.length) then
        pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits rank.length)))
      else pairEncode T (pairEncode (rank ++ [true]) (pairEncode [] []))
    else pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits cap)))

def selectOut (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD S))

def SelectInv (T S : List Bool) : Prop :=
  (∃ i, i ≤ Nat.log 2 (Nat.log 2 (values T).length) ∧
    S = pairEncode T (pairEncode (List.replicate i true) (pairEncode [] [])) ∧
    ∀ j < i, candidate (selectCtx T j) = false) ∨
  (∃ i, i ≤ Nat.log 2 (Nat.log 2 (values T).length) ∧
    S = pairEncode T (pairEncode (List.replicate i true)
      (pairEncode [true] (Nat.bits (stage (values T))))))

def selectMeasure (S : List Bool) : ℕ :=
  if pairFstD (pairSndD (pairSndD S)) = [] then
    Nat.log 2 (Nat.log 2 (values (pairFstD S)).length) - (pairFstD (pairSndD S)).length + 1
  else 0

theorem selectInit_FP : PolyTimeComputable selectInit := by sorry

theorem selectStep_FP (hc : PolyTimeComputable (fun C => [candidate C])) :
    PolyTimeComputable selectStep := by sorry

theorem select_progress (T S : List Bool) (hI : SelectInv T S) :
    SelectInv T (selectStep S) ∧
      (0 < selectMeasure S → selectMeasure (selectStep S) < selectMeasure S) ∧
      (selectMeasure S = 0 → selectStep S = S) := by sorry

theorem select_size (T : List Bool) (j : ℕ) :
    (selectStep^[j] (selectInit T)).length ≤ 12 * (T.length + 1) ^ 1 := by sorry

theorem select_readout (T : List Bool) :
    selectOut (selectStep^[1 * (T.length + 1) ^ 1] (selectInit T)) =
      Nat.bits (stage (values T)) := by sorry

theorem candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [candidate S]) := by sorry

theorem stage_FP
    (hcheck : PolyTimeComputable (fun S => [candidate S])) :
    PolyTimeComputable (fun T => Nat.bits (stage (values T))) := by sorry

theorem stage_correct (vs : List ℕ)
    (hvs : ∀ m < vs.length, vs.getD m 0 = ladnerH m) :
    stage vs = ladnerH vs.length := by sorry

theorem memoStep_FP
    (hstage : PolyTimeComputable (fun T => Nat.bits (stage (values T)))) :
    PolyTimeComputable memoStep := by sorry

theorem memoInit_FP : PolyTimeComputable memoInit := by sorry

theorem memo_orbit (z : List Bool) (j : ℕ) :
    memoStep^[j] (memoInit z) =
      pairEncode (List.replicate z.length true)
        (BinArith.encWords ((List.range j).map (fun m => Nat.bits (ladnerH m)))) := by sorry

theorem memo_size (z : List Bool) (j : ℕ) (hj : j ≤ z.length + 1) :
    (memoStep^[j] (memoInit z)).length ≤ 4 * (z.length + 1) ^ 2 := by sorry

theorem memo_readout (z : List Bool) :
    BinArith.getW (memoStep^[1 * (z.length + 1) ^ 1] (memoInit z)) =
      Nat.bits (ladnerH z.length) := by sorry

-- This is an assembly schema, not an admission of the library target.
theorem memo_transfer
    (hstep : PolyTimeComputable memoStep) (hinit : PolyTimeComputable memoInit)
    (hsize : ∀ z j, j ≤ 1 * (z.length + 1) ^ 1 →
      (memoStep^[j] (memoInit z)).length ≤ 4 * (z.length + 1) ^ 2)
    (hread : ∀ z, BinArith.getW (memoStep^[1 * (z.length + 1) ^ 1] (memoInit z)) =
      Nat.bits (ladnerH z.length)) :
    PolyTimeComputable (fun z => Nat.bits (ladnerH z.length)) := by sorry
end LadnerRoutePoly

## ===== campaign/fills/ladner-poly-memo/preship/Ladner-move.patch.txt =====

diff --git a/TCSlib/Complexity/Diagonalization/Ladner.lean b/TCSlib/Complexity/Diagonalization/Ladner.lean
index b54e069..6187252 100644
--- a/TCSlib/Complexity/Diagonalization/Ladner.lean
+++ b/TCSlib/Complexity/Diagonalization/Ladner.lean
@@ -187,24 +187,6 @@ noncomputable def SAT_H : Language Bool := padSAT ladnerH
 theorem SAT_H_eq : SAT_H = padSAT ladnerH :=
   rfl
 
-/-- The binary digits of the delayed index at an input's length are polynomial-time
-computable. [AB09, Theorem 3.3 and its proof]
-
-**Proof sketch.** Maintain previously computed index values, simulate only the short
-inputs through the uniformly timed acceptance simulator, and test SAT on short words.
-Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
-poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
-theorem ladnerH_polyTime :
-    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) :=
-  sorry
-
-/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]
-
-**Proof sketch.** Guess the satisfiable prefix and its SAT certificate. Compute the
-index at that prefix length and check the separator and exactly prescribed unary suffix. -/
-theorem SAT_H_mem_NP : SAT_H ∈ NP :=
-  sorry
-
 /-- The empty word is outside every padded language because a separator contributes
 one symbol. [AB09, Theorem 3.3 and its proof] -/
 private theorem ladner_pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by
@@ -515,32 +497,6 @@ theorem ladnerH_unbounded_of_not_mem_P :
   by_contra! hgood
   exact hP (ladner_all_tests_imply_P i hgood)
 
-/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
-to P. The hypothesis uses NP-hardness, rather than NP-completeness.
-[AB09, Theorem 3.3 and its proof]
-
-**Proof sketch.** A polynomial reduction into the padded language eventually maps an
-instance to a satisfiable-prefix candidate at most the square root of its length.
-Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
-theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
-    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
-    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P :=
-  sorry
-
-/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
-not NP-complete. [AB09, Theorem 3.3]
-
-**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
-polynomial reduction from SAT. NP-hardness would instead combine divergence of the
-index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
-theorem SAT_H_intermediate (h : P ≠ NP) :
-    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H :=
-  sorry
-
-/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
-theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
-  ⟨SAT_H, SAT_H_intermediate h⟩
-
 /-! ### Padding syntax and fixed finite tables -/
 
 /-- Parse the final false separator and its true suffix.
@@ -1818,4 +1774,50 @@ private theorem ladner_candidate_FP
   funext C
   simpa only [Function.comp_apply, ladner_testOut, decide_eq_true_eq] using ladner_candidate_readout C
 
+/-! ### The theorem and its remaining targets -/
+
+/-- The binary digits of the delayed index at an input's length are polynomial-time
+computable. [AB09, Theorem 3.3 and its proof]
+
+**Proof sketch.** Maintain previously computed index values, simulate only the short
+inputs through the uniformly timed acceptance simulator, and test SAT on short words.
+Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
+poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
+theorem ladnerH_polyTime :
+    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) :=
+  sorry
+
+/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]
+
+**Proof sketch.** Guess the satisfiable prefix and its SAT certificate. Compute the
+index at that prefix length and check the separator and exactly prescribed unary suffix. -/
+theorem SAT_H_mem_NP : SAT_H ∈ NP :=
+  sorry
+
+/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
+to P. The hypothesis uses NP-hardness, rather than NP-completeness.
+[AB09, Theorem 3.3 and its proof]
+
+**Proof sketch.** A polynomial reduction into the padded language eventually maps an
+instance to a satisfiable-prefix candidate at most the square root of its length.
+Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
+theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
+    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
+    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P :=
+  sorry
+
+/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
+not NP-complete. [AB09, Theorem 3.3]
+
+**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
+polynomial reduction from SAT. NP-hardness would instead combine divergence of the
+index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
+theorem SAT_H_intermediate (h : P ≠ NP) :
+    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H :=
+  sorry
+
+/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
+theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
+  ⟨SAT_H, SAT_H_intermediate h⟩
+
 end Complexity

## ===== campaign/fills/ladner-poly-memo/preship/Fill4PartB.lean.txt =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.CookLevin.Hardness
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.ClassP.ModelInvariance
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Delayed diagonalization and intermediate languages

## Main definitions

* `Complexity.padSAT` is SAT padded by a variable exponent after a final separator.
* `Complexity.ladnerMachine` is the uniformly timed enumeration used in the delayed diagonal.
* `Complexity.ladnerH` is the least currently successful index, capped by a double logarithm.
* `Complexity.SAT_H` is the language padded by that index function.

## Main results

* `Complexity.ladnerH_polyTime` states that the delayed index is polynomial-time computable.
* `Complexity.SAT_H_intermediate` gives an intermediate language when P differs from NP.
* `Complexity.ladner` states the existence of an NP-intermediate language.

## Conventions

The bounded test uses acceptance equivalence at the indexed deadline, rather than
requiring a Boolean output within that deadline. At the empty input the deadline
is zero, so acceptance and padded-language membership are both false. The enumeration
uses the existing uniform binary code scheme. The inherited SAT decoder is total and
maps malformed words to a satisfiable formula. The general padding theorem below uses
the weaker NP-hardness premise, strengthening the NP-complete version.

## References

* [AB09] S. Arora, B. Barak, Computational Complexity: A Modern Approach,
  Cambridge University Press, 2009. Theorem 3.3 and its proof.
-/

namespace Complexity

open Turing
open scoped Classical

/-- `padSAT h` consists of a satisfiable word followed by a false separator and
`|ψ| ^ h |ψ|` true bits. [AB09, Theorem 3.3 and its proof] -/
def padSAT (h : ℕ → ℕ) : Language Bool :=
  {y | ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true}

/-- A word belongs to `padSAT h` exactly when it has the indicated satisfiable prefix
and the prescribed separator and unary suffix. -/
theorem mem_padSAT_iff {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔
      ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true :=
  Iff.rfl

/-- Padding-language membership at a word depends only on exponent values at shorter
prefix lengths.

**Proof sketch.** A padding witness is shorter than the whole word because the separator
contributes one position. Substitute equality of the exponent functions at that length. -/
theorem padSAT_congr {h g : ℕ → ℕ} {y : List Bool}
    (hfg : ∀ m < y.length, h m = g m) :
    y ∈ padSAT h ↔ y ∈ padSAT g := by
  constructor
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [← hfg ψ.length hshort]
    exact he
  · intro hy
    obtain ⟨ψ, hψ, he⟩ := mem_padSAT_iff.mp hy
    have hshort : ψ.length < y.length := by
      rw [he, List.length_append, List.length_cons, List.length_replicate]
      omega
    apply mem_padSAT_iff.mpr
    refine ⟨ψ, hψ, ?_⟩
    rw [hfg ψ.length hshort]
    exact he

/-- The index `i` denotes the machine obtained by decoding its binary digits in the
uniformly timed code scheme. [AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerMachine (i : ℕ) : FinTM Bool :=
  (expCode.decode (Nat.bits i)).toFinTM

/-- The enumeration uses `expCode` on the binary digits of its index. -/
theorem ladnerMachine_eq (i : ℕ) :
    ladnerMachine i = (expCode.decode (Nat.bits i)).toFinTM :=
  rfl

/-- The delayed index at `n` is the least index below the double logarithm that correctly
recognizes the padded language on words of length at most the logarithm, within its indexed
polynomial deadline. If no such index exists, it is the double logarithm. Values used in a
short padded word depend only on smaller arguments, so strong recursion defines the index.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def ladnerH (n : ℕ) : ℕ :=
  Nat.strongRecOn (motive := fun _ => ℕ) n fun n prev =>
    let h : ℕ → ℕ := fun m => if hm : m < n then prev m hm else 0
    let good : ℕ → Prop := fun i => ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔ x ∈ padSAT h)
    if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧ good i then Nat.find hex
    else Nat.log 2 (Nat.log 2 n)

/-- The delayed index satisfies its minimum-index equation, with the global padded
language in the bounded acceptance test.

**Proof sketch.** Read the strong-recursion equation and use `padSAT_congr` to identify
local and global exponents on every queried word. Handle zero before using logarithmic decrease. -/
theorem ladnerH_eq (n : ℕ) :
    ladnerH n =
      if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
          ∀ x : List Bool, x.length ≤ Nat.log 2 n →
            ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
              x ∈ padSAT ladnerH) then
        Nat.find hex
      else Nat.log 2 (Nat.log 2 n) := by
  conv_lhs => rw [ladnerH]
  change (Nat.lt_wfRel.wf.fix (C := fun _ : ℕ => ℕ) _ n) = _
  rw [WellFounded.fix_eq]
  dsimp only
  let previous : ℕ → ℕ := fun m => if hm : m < n then ladnerH m else 0
  let localTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT previous)
  let globalTest : ℕ → Prop := fun i => i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)
  have hpad (hn : n ≠ 0) (x : List Bool) (hx : x.length ≤ Nat.log 2 n) :
      x ∈ padSAT previous ↔ x ∈ padSAT ladnerH := by
    apply padSAT_congr
    intro m hm
    have hmn : m < n := (hm.trans_le hx).trans (Nat.log_lt_self 2 hn)
    exact dif_pos hmn
  have hnonzero (i : ℕ) (hi : i < Nat.log 2 (Nat.log 2 n)) : n ≠ 0 := by
    intro hz
    subst n
    simp at hi
  have htests : localTest = globalTest := by
    funext i
    apply propext
    constructor
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx)
    · rintro ⟨hi, hgood⟩
      refine ⟨hi, fun x hx => ?_⟩
      exact (hgood x hx).trans (hpad (hnonzero i hi) x hx).symm
  have hexists : (∃ i, localTest i) ↔ ∃ i, globalTest i :=
    exists_congr fun i => Iff.of_eq (congrFun htests i)
  split_ifs with hlocal hglobal
  · exact Nat.find_congr' fun {i} => Iff.of_eq (congrFun htests i)
  · exact False.elim (hglobal (hexists.mp hlocal))
  · rename_i hglobal
    exact False.elim (hlocal (hexists.mpr hglobal))
  · rfl

/-- The delayed index never exceeds its double-logarithmic cap.

**Proof sketch.** In the successful case, read the strict index bound of the least witness;
in the fallback case, the index equals the cap. -/
theorem ladnerH_le (n : ℕ) : ladnerH n ≤ Nat.log 2 (Nat.log 2 n) := by
  rw [ladnerH_eq]
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- `SAT_H` is the language obtained by padding SAT with the delayed index function.
[AB09, Theorem 3.3 and its proof] -/
noncomputable def SAT_H : Language Bool := padSAT ladnerH

/-- The witness language is `padSAT ladnerH`. -/
theorem SAT_H_eq : SAT_H = padSAT ladnerH :=
  rfl

/-- The empty word is outside every padded language because a separator contributes
one symbol. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_nil (h : ℕ → ℕ) : ([] : List Bool) ∉ padSAT h := by
  intro hx
  obtain ⟨ψ, _, he⟩ := mem_padSAT_iff.mp hx
  have hlen := congrArg List.length he
  simp only [List.length_nil, List.length_append, List.length_cons,
    List.length_replicate] at hlen
  omega

/-- Prepending a word to the binary word of a positive number gives the binary word of a
number at least as large. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_bits_prepend (u : List Bool) (j : ℕ) (hj : 0 < j) :
    ∃ i, j ≤ i ∧ i.bits = u ++ j.bits := by
  induction u with
  | nil => exact ⟨j, le_rfl, rfl⟩
  | cons b u ih =>
    obtain ⟨i, hi, hbits⟩ := ih
    refine ⟨Nat.bit b i, ?_, ?_⟩
    · rw [Nat.bit_val]
      omega
    · rw [Nat.bits_append_bit i b (fun hz => by omega), hbits, List.cons_append]

/-- Every coded machine occurs at arbitrarily large canonical binary indices.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Construct a positive all-true binary suffix whose value exceeds
the requested bound. Prepending each bit of the machine's encoding preserves
canonicality and cannot decrease the value. The decoding padding law then
identifies the indexed machine. -/
private theorem ladner_padded_index (M : CodeTM) (B : ℕ) :
    ∃ i, B < i ∧ ladnerMachine i = M.toFinTM := by
  have ones : ∀ b : ℕ, ∃ j, b + 1 ≤ j ∧ j.bits = List.replicate (b + 1) true := by
    intro b
    induction b with
    | zero => exact ⟨1, le_rfl, Nat.one_bits⟩
    | succ b ih =>
      obtain ⟨j, hj, hbits⟩ := ih
      refine ⟨Nat.bit true j, ?_, ?_⟩
      · rw [Nat.bit_val]
        omega
      · rw [Nat.bits_append_bit j true (fun _ => rfl), hbits,
          List.replicate_succ (n := b + 1)]
  obtain ⟨j, hj, hbits⟩ := ones B
  obtain ⟨i, hi, hi_bits⟩ := ladner_bits_prepend (expCode.encode M) j (by omega)
  refine ⟨i, by omega, ?_⟩
  rw [ladnerMachine_eq, hi_bits, hbits, expCode.toMachineCode.decode_encode_pad]

/-- An indexed deadline dominates a polynomial on nonempty inputs when its index
bounds both the degree and the scaled coefficient. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_indexed_deadline (a d i m : ℕ)
    (hd : d ≤ i) (ha : a * 2 ^ d ≤ i) (hm : 1 ≤ m) :
    a * (m + 1) ^ d ≤ i * m ^ i := calc
  a * (m + 1) ^ d ≤ a * (2 * m) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  _ = (a * 2 ^ d) * m ^ d := by rw [mul_pow, mul_assoc]
  _ ≤ i * m ^ i := Nat.mul_le_mul ha (Nat.pow_le_pow_right hm hd)

/-- A polynomial decider supplies one index that passes every bounded-acceptance
test. The empty word is handled by the zero-deadline convention.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Replace the decider by a one-work-tape machine and then its coded
normal form. Choose a padded index above the degree and scaled coefficient.
On a positive input length, the indexed clock contains the decider's clock.
Acceptance gives membership by uniqueness of completed outputs; membership gives
acceptance by monotonicity. At the empty input both sides are false. -/
private theorem ladner_correct_index (hP : SAT_H ∈ P) :
    ∃ i, ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH := by
  classical
  obtain ⟨M, a, d, hk, hM⟩ := mem_P_iff_one_work_tape.mp hP
  have hdec := (FinTM.computesFunInTime_iff M _ _).mp
    ((FinTM.decidesInTime_iff M SAT_H _).mp hM)
  obtain ⟨i, hi, hcode⟩ := ladner_padded_index (M.toCodeTM hk) (max d (a * 2 ^ d))
  have hd : d ≤ i := (le_max_left d (a * 2 ^ d)).trans hi.le
  have ha : a * 2 ^ d ≤ i := (le_max_right d (a * 2 ^ d)).trans hi.le
  refine ⟨i, fun x => ?_⟩
  by_cases hx : x = []
  · subst x
    have hzero : i * ([] : List Bool).length ^ i = 0 := by
      have hipos : i ≠ 0 := by omega
      simp only [List.length_nil, zero_pow hipos, Nat.mul_zero]
    rw [hzero]
    exact iff_of_false (FinTM.not_computesInTime_zero _ _ _) (ladner_pad_nil ladnerH)
  · have hlen : 1 ≤ x.length := by
      cases x with
      | nil => exact False.elim (hx rfl)
      | cons b xs => exact Nat.succ_le_succ (Nat.zero_le _)
    have hclock := ladner_indexed_deadline a d i x.length hd ha hlen
    have hrun : (ladnerMachine i).ComputesInTime x
        [MultiTapeTM.indicator (SAT_H : Set (List Bool)) x] (a * (x.length + 1) ^ d) := by
      rw [hcode, FinTM.toCodeTM_computesInTime_iff]
      exact hdec x
    constructor
    · intro hacc
      by_contra hnot
      have hnot' : x ∉ SAT_H := by rw [SAT_H_eq]; exact hnot
      have hfalse := hrun
      rw [MultiTapeTM.indicator_of_not_mem hnot'] at hfalse
      have he := hacc.output_unique hfalse
      simp only [List.cons.injEq, Bool.true_eq_false, false_and] at he
    · intro hmem
      have hmem' : x ∈ SAT_H := by rw [SAT_H_eq]; exact hmem
      rw [MultiTapeTM.indicator_of_mem hmem'] at hrun
      exact hrun.mono hclock

/-- A globally correct index bounds the delayed selector at every stage.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_selector_bound (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) :
    ∀ n, ladnerH n ≤ i := by
  classical
  intro n
  rw [ladnerH_eq]
  split_ifs with h
  · by_cases hcap : i < Nat.log 2 (Nat.log 2 n)
    · exact Nat.find_min' h ⟨hcap, fun x _ => good x⟩
    · exact (Nat.find_spec h).1.le.trans (Nat.le_of_not_gt hcap)
  · apply Nat.le_of_not_gt
    intro hcap
    exact h ⟨i, hcap, fun x _ => good x⟩

/-- A polynomial-time decider for the padded language forces its delayed index to be
bounded. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a padded code of the decider whose enumeration index dominates
its polynomial time degree. That index eventually passes every short acceptance test;
absorb the finitely many earlier index values into one bound. -/
theorem ladnerH_bounded_of_mem_P :
    SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C := by
  intro hP
  obtain ⟨i, hi⟩ := ladner_correct_index hP
  exact ⟨i, ladner_selector_bound i hi⟩

/-- A fixed polynomial clock can be prepared in the uniform simulator's paired
input format in polynomial time. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** On a nonempty word, evaluating the successor-length polynomial
on its tail gives the required polynomial of the original length. Handle the
empty word by a fixed equality test and constant output, then pair the clock
with the fixed machine code and the original word. -/
private theorem ladner_fixed_clock_preparation (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x) := by
  classical
  obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyBits a d
  have hpoly : PolyTimeComputable (fun x : List Bool => Nat.bits (a * (x.length + 1) ^ d)) :=
    (polyTimeComputable_iff _).mpr ⟨M, c, d + 1, hM⟩
  have htail : PolyTimeComputable
      (fun x : List Bool => Nat.bits (a * ((x.drop 1).length + 1) ^ d)) :=
    hpoly.comp polyTimeComputable_tail
  have hnil : PolyTimeComputable (fun x : List Bool => [decide (x = [])]) :=
    polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq [])
  have hbranch := polyTimeComputable_ite hnil
    (polyTimeComputable_const (Nat.bits (a * 0 ^ d))) htail
  have heq : (fun x : List Bool => if decide (x = []) then
      Nat.bits (a * 0 ^ d) else Nat.bits (a * ((x.drop 1).length + 1) ^ d)) =
      (fun x : List Bool => Nat.bits (a * x.length ^ d)) := by
    funext x
    cases x with
    | nil => simp only [decide_true, if_true, List.length_nil]
    | cons b xs =>
      simp only [List.cons_ne_nil, decide_false, Bool.false_eq_true, if_false,
        List.drop_succ_cons, List.drop_zero, List.length_cons]
  rw [heq] at hbranch
  exact (hbranch.pairEncode (polyTimeComputable_const code)).pairEncode polyTimeComputable_id

/-- The simulator's polynomial in the numerical deadline has a polynomial envelope
when the simulated code and clock are fixed. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each input-length term is bounded by a coefficient times the
successor length raised to the larger of one and the clock degree. Add these
bounds, raise to the simulator degree, and collect the constant factors. -/
private theorem ladner_fixed_clock_budget (D u a d n : ℕ) :
    D * (u + n + a * n ^ d + 1) ^ D ≤
      (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
  let q := (n + 1) ^ max 1 d
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : n ≤ q := calc
    n ≤ n + 1 := Nat.le_succ _
    _ = (n + 1) ^ 1 := (pow_one _).symm
    _ ≤ q := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left 1 d)
  have hnd : n ^ d ≤ q :=
    (Nat.pow_le_pow_left (Nat.le_succ n) d).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right 1 d))
  have hu : u ≤ u * q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left u hq
  have ha := Nat.mul_le_mul_left a hnd
  have hbase : u + n + a * n ^ d + 1 ≤ (u + a + 2) * q := calc
    _ ≤ u * q + q + a * q + q := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu hn) ha) hq
    _ = _ := by ring
  calc
    D * (u + n + a * n ^ d + 1) ^ D ≤ D * ((u + a + 2) * q) ^ D :=
      Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase D)
    _ = (D * (u + a + 2) ^ D) * (n + 1) ^ (max 1 d * D) := by
      rw [mul_pow, mul_assoc, ← pow_mul]

/-- The bounded-acceptance test for a fixed code and polynomial clock is a total
polynomial-time Boolean function. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Prepare the exact simulator input with a polynomial-time machine.
The uniform simulator returns the bounded-acceptance bit on this image, including
when the simulated machine diverges. Bound its numerical clock by a fixed
polynomial, compose on the preparation machine's image, and absorb setup and
composition costs into one successor-length polynomial. -/
private theorem ladner_fixed_clock_FP (code : List Bool) (a d : ℕ) :
    PolyTimeComputable (fun x : List Bool =>
      [decide ((expCode.decode code).toFinTM.ComputesInTime
        x [true] (a * x.length ^ d))]) := by
  classical
  obtain ⟨M, C, e, hM⟩ := (polyTimeComputable_iff _).mp
    (ladner_fixed_clock_preparation code a d)
  let A := expCode.simDegree * (code.length + a + 2) ^ expCode.simDegree
  let k := max 1 d * expCode.simDegree
  have hU (x : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (a * x.length ^ d)) code) x)
      [decide ((expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d))]
      (A * (x.length + 1) ^ k) := by
    have hb := ladner_fixed_clock_budget expCode.simDegree code.length a d x.length
    by_cases hacc : (expCode.decode code).toFinTM.ComputesInTime x [true] (a * x.length ^ d)
    · simpa only [hacc, decide_true] using
        (expCode.simulator_accepts code x (a * x.length ^ d) hacc).mono hb
    · simpa only [hacc, decide_false] using
        (expCode.simulator_rejects code x (a * x.length ^ d) hacc).mono hb
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ e) (fun n => A * (n + 1) ^ k) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max e k, (FinTM.computesFunInTime_iff N _ _).mpr ?_⟩
  intro x
  apply (((FinTM.computesFunInTime_iff N _ _).mp hN) x).mono
  have he := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_left e k)
  have hk := Nat.pow_le_pow_right (Nat.succ_pos x.length) (le_max_right e k)
  have hone := Nat.one_le_pow (max e k) (x.length + 1) (Nat.succ_pos _)
  calc
    2 * (C * (x.length + 1) ^ e) + A * (x.length + 1) ^ k + 2 ≤
        2 * (C * (x.length + 1) ^ max e k) + A * (x.length + 1) ^ max e k +
          2 * (x.length + 1) ^ max e k :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C he))
        (Nat.mul_le_mul_left A hk)) (by omega)
    _ = (2 * C + A + 2) * (x.length + 1) ^ max e k := by ring

/-- If one indexed test agrees everywhere with the padded language, its total
bounded simulator decides that language in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_all_tests_imply_P (i : ℕ)
    (good : ∀ x : List Bool,
      (ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH) : SAT_H ∈ P := by
  classical
  have htest := mem_P_of_test (ladner_fixed_clock_FP (Nat.bits i) i i)
  have heq : {x : List Bool | decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true} = SAT_H := by
    ext x
    change (decide ((expCode.decode (Nat.bits i)).toFinTM.ComputesInTime
      x [true] (i * x.length ^ i)) = true) ↔ x ∈ SAT_H
    rw [decide_eq_true_eq, ← ladnerMachine_eq, SAT_H_eq]
    exact good x
  rw [heq] at htest
  exact htest

/-- Finitely many failing words are all visible at every sufficiently large stage,
so the delayed selector eventually exceeds any prescribed bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Choose a failing word for every index. For a given bound, take
the maximum length of witnesses below it. Choose an exponential stage whose query
window contains that maximum and whose double-log cap exceeds the bound. The
least successful index cannot be below the bound; neither can the fallback. -/
private theorem ladner_selector_threshold
    (bad : ∀ i : ℕ, ∃ x : List Bool,
      ¬ ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT ladnerH)) :
    ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  choose witness counterexample using bad
  intro C
  let B := (Finset.range C).sup fun i => (witness i).length
  let M := max B (2 ^ C)
  refine ⟨2 ^ M, ?_⟩
  intro n hn
  have hlog : M ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hcap : C ≤ Nat.log 2 (Nat.log 2 n) :=
    Nat.le_log_of_pow_le (by decide) ((le_max_right B (2 ^ C)).trans hlog)
  rw [ladnerH_eq]
  split_ifs with h
  · by_contra! hi
    have hlen : (witness (Nat.find h)).length ≤ B :=
      Finset.le_sup (f := fun i => (witness i).length) (Finset.mem_range.mpr hi)
    exact counterexample (Nat.find h)
      ((Nat.find_spec h).2 _ (hlen.trans ((le_max_left B (2 ^ C)).trans hlog)))
  · exact hcap

/-- If the padded language is outside P, the delayed index eventually exceeds every
constant. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Each fixed machine has a failing finite test, since a machine that passed
all its indexed polynomial tests would decide the language in polynomial time. Once all
failing tests below a fixed cap are visible, none of those indices is selected. -/
theorem ladnerH_unbounded_of_not_mem_P :
    SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n := by
  classical
  intro hP
  apply ladner_selector_threshold
  intro i
  by_contra! hgood
  exact hP (ladner_all_tests_imply_P i hgood)

/-! ### Padding syntax and fixed finite tables -/

/-- Parse the final false separator and its true suffix.
This is the mathematical padding parser of [AB09, Theorem 3.3 and its proof]. -/
private def ladner_parse : List Bool → Option (List Bool × ℕ)
  | [] => none
  | b :: bs => match ladner_parse bs with
    | some (p, t) => some (b :: p, t)
    | none => if b then none else some ([], bs.length)

/-- Padding syntax requires the suffix length to be the prescribed power.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_padSyntax (h : ℕ → ℕ) (y : List Bool) : Bool :=
  match ladner_parse y with
  | none => false
  | some (p, t) => decide (t = p.length ^ h p.length)

/-- Serialize a successful parse with a nonempty marker; failure is the empty word.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_parseWord (y : List Bool) : List Bool :=
  match ladner_parse y with
  | none => []
  | some (p, t) => pairEncode [true] (pairEncode p (Nat.bits t))

/-- The parser fails exactly on words with no false separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_none (y : List Bool) :
    ladner_parse y = none ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [ladner_parse, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih =>
    rw [List.forall_mem_cons, ← ih]
    cases hs : ladner_parse bs with
    | none => cases b <;> simp only [ladner_parse, hs, Bool.false_eq_true,
        if_false, if_true, Option.some_ne_none, and_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      simp only [ladner_parse, hs, Option.some_ne_none, and_false]

/-- A successful parse reconstructs the input around the final separator.

**Proof sketch.** Induct on the input. A successful recursive parse extends the prefix.
When the recursive parse fails, the tail is all true and the current false bit is the
final separator. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_sound {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : y = p ++ false :: List.replicate t true := by
  induction y generalizing p t with
  | nil => cases hp
  | cons b bs ih =>
    cases hs : ladner_parse bs with
    | none =>
      cases b with
      | false =>
        simp only [ladner_parse, hs, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have he : bs = List.replicate bs.length true :=
          List.eq_replicate_iff.mpr ⟨rfl, (ladner_parse_none bs).mp hs⟩
        simpa only [List.nil_append] using congrArg (List.cons false) he
      | true =>
        simp only [ladner_parse, hs, if_true] at hp
        cases hp
    | some pt =>
      obtain ⟨q, u⟩ := pt
      simp only [ladner_parse, hs, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simpa only [List.cons_append] using congrArg (List.cons b) (ih hs)

/-- The parser reads any prefix followed by a false separator and a true suffix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_pad (p : List Bool) (t : ℕ) :
    ladner_parse (p ++ false :: List.replicate t true) = some (p, t) := by
  have hn : ladner_parse (List.replicate t true) = none :=
    (ladner_parse_none _).mpr (by simp only [List.mem_replicate]; aesop)
  induction p with
  | nil => simp only [List.nil_append, ladner_parse, hn, Bool.false_eq_true,
      if_false, List.length_replicate]
  | cons b p ih => simp only [List.cons_append, ladner_parse, ih]

/-- Parsing succeeds exactly on the indicated padded word.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_some (y p : List Bool) (t : ℕ) :
    ladner_parse y = some (p, t) ↔ y = p ++ false :: List.replicate t true :=
  ⟨ladner_parse_sound, fun he => he ▸ ladner_parse_pad p t⟩

/-- A parsed prefix is shorter than the input, whose length includes the separator.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parsed_length {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) :
    y.length = p.length + 1 + t ∧ p.length < y.length := by
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

/-- The public false-bit test is false exactly on all-true words. -/
private theorem ladner_hasFalse_false (y : List Bool) :
    BinArith.hasFalse y = false ↔ ∀ b ∈ y, b = true := by
  induction y with
  | nil => simp only [BinArith.hasFalse_nil, List.not_mem_nil, false_implies, implies_true]
  | cons b bs ih => cases b <;> simp only [BinArith.hasFalse_cons, Bool.not_false,
      Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_eq_false,
      List.forall_mem_cons, Bool.false_eq_true, false_and, true_and, ih]

/-- The public false-bit test distributes over append. -/
private theorem ladner_hasFalse_append (u v : List Bool) :
    BinArith.hasFalse (u ++ v) = (BinArith.hasFalse u || BinArith.hasFalse v) := by
  induction u with
  | nil => simp only [List.nil_append, BinArith.hasFalse_nil, Bool.false_or]
  | cons b u ih => simp only [List.cons_append, BinArith.hasFalse_cons, ih, Bool.or_assoc]

/-- Reverse and the public unary-rest reader recover a successful parse's prefix.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_prefix {y p : List Bool} {t : ℕ}
    (hp : ladner_parse y = some (p, t)) : (BinArith.uRest y.reverse).reverse = p := by
  have hr (n : ℕ) (w : List Bool) :
      BinArith.uRest (List.replicate n true ++ false :: w) = w := by
    have h := BinArith.uRest_encodeNat n w
    rwa [BoolCircuit.encodeNat_eq, List.append_assoc, List.singleton_append] at h
  rw [(ladner_parse_some y p t).mp hp]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append, hr, List.reverse_reverse]

/-- The binary length of a word is polynomial-time (`FinTM.computesFunInTime_lengthBits`).
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_lengthBits_FP : PolyTimeComputable (fun y : List Bool => Nat.bits y.length) :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits

/-- The mathematical padding parser has a polynomial-time serialization.

**Proof sketch.** Reverse the input, skip its true suffix and separator with the existing
unary-rest reader, and reverse the remainder. Subtract the prefix length and one from
the input length to get the suffix length. The public false-bit test distinguishes a
missing separator from an empty prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_parse_FP : PolyTimeComputable ladner_parseWord := by
  have hl := ladner_lengthBits_FP
  have hpre := BinArith.polyTimeComputable_reverse.comp
    (BinArith.polyTimeComputable_uRest.comp BinArith.polyTimeComputable_reverse)
  have ht := BinArith.polyTimeComputable_sub.comp
    ((BinArith.polyTimeComputable_sub.comp (hl.pairEncode (hl.comp hpre))).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  have hout := polyTimeComputable_ite BinArith.polyTimeComputable_hasFalse
    ((polyTimeComputable_const [true]).pairEncode (hpre.pairEncode ht))
    (polyTimeComputable_const [])
  convert hout using 1
  funext y
  cases hp : ladner_parse y with
  | none =>
    have hf := (ladner_hasFalse_false y).mpr ((ladner_parse_none y).mp hp)
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, Bool.false_eq_true, if_false]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hpre' := ladner_parse_prefix hp
    have hlen := (ladner_parsed_length hp).1
    have hf : BinArith.hasFalse y = true := by
      rw [(ladner_parse_some y p t).mp hp, ladner_hasFalse_append,
        BinArith.hasFalse_cons]
      simp only [Bool.not_false, Bool.true_or, Bool.or_true]
    have ht' : y.length - p.length - 1 = t := by omega
    simp only [ladner_parseWord, hp, Function.comp_apply, hf, if_true, hpre',
      BinArith.sub_pairEncode, ht']

/-- The padding syntax test, for an exponent function that may depend on the input word, is
polynomial-time when the exponent at the parsed prefix length is.

**Proof sketch.** Parse the word and compute the prefix length and exponent in binary.
Use the saturated power with cap parameter equal to the suffix length. Its result equals
the suffix length exactly when the full power does; this avoids allocating an enormous
power. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_padSyntax_FP {g : List Bool → List Bool} {h : List Bool → ℕ → ℕ}
    (hg : PolyTimeComputable g)
    (hh : PolyTimeComputable (fun z : List Bool =>
      Nat.bits (h (pairSndD z) (pairFstD z).length))) :
    PolyTimeComputable (fun S => [ladner_padSyntax (h S) (g S)]) := by
  have hl := ladner_lengthBits_FP
  have hp := ladner_parse_FP.comp hg
  have hpre := BinArith.polyTimeComputable_slot2.comp hp
  have ht := BinArith.polyTimeComputable_slot3.comp hp
  have he := hh.comp (hpre.pairEncode polyTimeComputable_id)
  have hpow := BinArith.polyTimeComputable_powCap.comp
    ((hl.comp hpre).pairEncode (he.pairEncode ht))
  have heq := BinArith.polyTimeComputable_beq.comp (ht.pairEncode hpow)
  have hout := polyTimeComputable_ite (polyTimeComputable_isNil.comp hp)
    (polyTimeComputable_const [false]) heq
  convert hout using 1
  funext S
  cases hy : ladner_parse (g S) with
  | none => simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply,
      decide_true, if_true]
  | some pt =>
    obtain ⟨p, t⟩ := pt
    have hne : pairEncode [true] (pairEncode p (Nat.bits t)) ≠ [] := by
      intro he
      have he' := congrArg List.length he
      rw [length_pairEncode] at he'
      simp only [List.length_cons, List.length_nil] at he'
      omega
    simp only [ladner_padSyntax, ladner_parseWord, hy, Function.comp_apply, id_eq,
      hne, decide_false, Bool.false_eq_true, if_false, pairFstD_pairEncode,
      pairSndD_pairEncode, BinArith.powCap_pairEncode, BinArith.beq_pairEncode]
    have heq' : (t = min (p.length ^ h S p.length) (t + 1)) ↔
        t = p.length ^ h S p.length := by omega
    simp only [heq']

/-- The padding syntax test is polynomial-time when its exponent function is: the
instance of `ladner_padSyntax_FP` with a fixed exponent function.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_syntax_FP {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x : List Bool => Nat.bits (h x.length))) :
    PolyTimeComputable (fun y => [ladner_padSyntax h y]) :=
  ladner_padSyntax_FP (h := fun _ => h) polyTimeComputable_id
    (hp.comp polyTimeComputable_pairFstD)

/-- Padding membership is successful parsing, the prescribed suffix length, and SAT
membership of the prefix. [AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_membership {h : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT h ↔ ∃ p t, ladner_parse y = some (p, t) ∧
      t = p.length ^ h p.length ∧ p ∈ SAT := by
  rw [mem_padSAT_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, p.length ^ h p.length, (ladner_parse_some _ _ _).mpr he, rfl, hp⟩
  · rintro ⟨p, t, hparse, rfl, hp⟩
    exact ⟨p, hp, (ladner_parse_some _ _ _).mp hparse⟩

/-- Every fixed finite table of words has a polynomial-time membership test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_finite_lookup_FP (S : Finset (List Bool)) :
    PolyTimeComputable (fun x : List Bool => [decide (x ∈ S)]) := by
  induction S using Finset.induction_on with
  | empty => exact polyTimeComputable_const [false]
  | @insert w S hw ih =>
    have heq := polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq w)
    convert polyTimeComputable_or heq ih using 1
    funext x
    simp only [Finset.mem_insert, Bool.decide_or]

/-- SAT on words shorter than a fixed bound is represented by a finite table.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Enumerate Boolean functions on each `Fin n` for `n < B`, turn them
into lists, and filter this finite universe by SAT. No SAT computation is performed at
runtime; the table is fixed once the bound is chosen. -/
private theorem ladner_small_SAT_table (B : ℕ) :
    ∃ S : Finset (List Bool), ∀ x : List Bool,
      x ∈ S ↔ x.length < B ∧ x ∈ SAT := by
  classical
  let U : Finset (List Bool) := (Finset.range B).biUnion (fun n =>
    (Finset.univ : Finset (Fin n → Bool)).image List.ofFn)
  have hu (x : List Bool) : x ∈ U ↔ x.length < B := by
    simp only [U, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨n, hn, f, rfl⟩
      simpa only [List.length_ofFn] using hn
    · intro hx
      exact ⟨x.length, hx, x.get, List.ofFn_get x⟩
  exact ⟨U.filter (fun x => x ∈ SAT), fun x => by rw [Finset.mem_filter, hu]⟩


/-! ### Polynomial-time preparation for the bounded candidate test -/

/-- Read the numeric memo entries through `BinArith.decWords`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_values (T : List Bool) : List ℕ :=
  (BinArith.decWords T).map LogProg.bitsVal

/-- Enumerate every short word by deleting the high sentinel bit of a positive rank.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_shortWords (a : ℕ) : List (List Bool) :=
  (List.range (2 ^ (a + 1) - 1)).map (fun r => (Nat.bits (r + 1)).dropLast)

/-- Select the least successful index against the supplied memo values, or the cap.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_stage (vs : List ℕ) : ℕ :=
  let n := vs.length
  if hex : ∃ i, i < Nat.log 2 (Nat.log 2 n) ∧
      ∀ x : List Bool, x.length ≤ Nat.log 2 n →
        ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
          x ∈ padSAT (fun m => vs.getD m 0)) then Nat.find hex
  else Nat.log 2 (Nat.log 2 n)

/-- The candidate predicate checks context consistency and every short input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_candidate (S : List Bool) : Bool :=
  let n := (pairFstD S).length
  let i := LogProg.bitsVal (pairFstD (pairSndD S))
  let vs := ladner_values (pairSndD (pairSndD S))
  decide (n = vs.length ∧ i < Nat.log 2 (Nat.log 2 n) ∧
    ∀ x : List Bool, x.length ≤ Nat.log 2 n →
      ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
        x ∈ padSAT (fun m => vs.getD m 0)))

/-- A simulator query contains an index below the double logarithm and a short input.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_validQuery (S : List Bool) : Prop :=
  LogProg.bitsVal (pairFstD (pairSndD S)) <
      Nat.log 2 (Nat.log 2 (pairFstD S).length) ∧
    (pairSndD (pairSndD S)).length ≤ Nat.log 2 (pairFstD S).length

/-- Invalid queries use the empty code; valid ones use the canonical index bits.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryCode (S : List Bool) : List Bool :=
  if ladner_validQuery S then Nat.bits (LogProg.bitsVal (pairFstD (pairSndD S))) else []

/-- Invalid queries use the empty simulator input.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryInput (S : List Bool) : List Bool :=
  if ladner_validQuery S then pairSndD (pairSndD S) else []

/-- Invalid queries use deadline zero; valid ones use the indexed deadline.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryDeadline (S : List Bool) : ℕ :=
  if ladner_validQuery S then
    LogProg.bitsVal (pairFstD (pairSndD S)) *
      (pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))
  else 0

/-- Serialize the guarded query in the uniform simulator's input format.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_queryPrep (S : List Bool) : List Bool :=
  pairEncode (pairEncode (Nat.bits (ladner_queryDeadline S)) (ladner_queryCode S))
    (ladner_queryInput S)

/-- Check the candidate context before using its numeric index.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_ctxGuard (C : List Bool) : Prop :=
  (pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
    LogProg.bitsVal (pairFstD (pairSndD C)) <
      Nat.log 2 (Nat.log 2 (pairFstD C).length)

/-- A single rank's verdict includes every guard and the acceptance equivalence.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_wordVerdict (C : List Bool) (r : ℕ) : Bool :=
  let x := (Nat.bits (r + 1)).dropLast
  let i := LogProg.bitsVal (pairFstD (pairSndD C))
  decide (ladner_ctxGuard C ∧ x.length ≤ Nat.log 2 (pairFstD C).length ∧
    ((ladnerMachine i).ComputesInTime x [true] (i * x.length ^ i) ↔
      x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0)))

/-- The number of words in the bounded short-input scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryCount (C : List Bool) : ℕ :=
  2 ^ (Nat.log 2 (pairFstD C).length + 1) - 1

/-- Initialize the remaining count, completed rank, and conjunction flag.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (List.replicate (ladner_queryCount C) true) (pairEncode [] [true]))

/-- One transition of the candidate scan, intended for `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private noncomputable def ladner_testStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let rank := pairFstD (pairSndD (pairSndD S))
  let flag := pairSndD (pairSndD (pairSndD S))
  if rem = [] then S else
    pairEncode C (pairEncode (rem.drop 1)
      (pairEncode (rank ++ [true]) [flag.headD false && ladner_wordVerdict C rank.length]))

/-- Read the conjunction flag of the candidate scan.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_testOut (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD S))

/-- The sentinel enumeration contains exactly the words of length at most its bound.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The upper rank bound limits the binary word to `a + 1` bits.
Conversely prepend the bits of any word to the positive sentinel `1`; the resulting
canonical number has that word as its binary expansion with its last bit removed. -/
private theorem ladner_shortWords_complete (a : ℕ) (x : List Bool) :
    x ∈ ladner_shortWords a ↔ x.length ≤ a := by
  constructor
  · intro hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have hr' := List.mem_range.mp hr
    have hl := LogProg.length_bits_le (show r + 1 < 2 ^ (a + 1) by omega)
    rw [List.length_dropLast]
    omega
  · intro hx
    obtain ⟨n, hn, he⟩ := ladner_bits_prepend x 1 Nat.one_pos
    rw [Nat.one_bits] at he
    have hlt := LogProg.lt_two_pow_bits n
    rw [he, List.length_append, List.length_cons, List.length_nil] at hlt
    have hna : n < 2 ^ (a + 1) := hlt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
    apply List.mem_map.mpr
    refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hn, he, List.dropLast_concat]

/-- The short-input scan has at most twice the stage length plus two queries.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_shortWords_count (n : ℕ) :
    (ladner_shortWords (Nat.log 2 n)).length ≤ 2 * (n + 1) := by
  rw [ladner_shortWords, List.length_map, List.length_range, pow_succ']
  have h := Nat.pow_log_le_add_one 2 n
  omega

/-- A uniform elementary bound used to charge the double logarithm.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_square_le_power (k : ℕ) : k ^ 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k < 3
    · have hk0 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk0 with rfl | rfl | rfl <;> norm_num
    · have hk' : 3 ≤ k := by omega
      calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
           _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left _ ih
           _ = 2 ^ (k + 1 + 1) := by simp only [pow_succ']

/-- Short indexed simulations have a deadline bounded by the cube of the stage length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Put `L = log₂ n` and `k = log₂ L`. The index is below `k`,
so `(k + 1)i ≤ k² ≤ 2^(k+1) ≤ 2L`. Thus `m^i ≤ 2^(2L) ≤ n²`,
while `i ≤ n`. No monotonicity of the delayed index is used. -/
private theorem ladner_short_deadline (n i m : ℕ)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hm : m ≤ Nat.log 2 n) :
    i * m ^ i ≤ n ^ 3 := by
  have hL : Nat.log 2 n ≠ 0 := by
    intro h
    rw [h, Nat.log_zero_right] at hi
    omega
  have hn : n ≠ 0 := by
    intro h
    subst n
    rw [Nat.log_zero_right] at hL
    exact hL rfl
  have hi' : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤
      (Nat.log 2 (Nat.log 2 n)) ^ 2 := by
    have h := Nat.mul_le_mul_left (Nat.log 2 (Nat.log 2 n) + 1)
      (Nat.succ_le_of_lt hi)
    nlinarith
  have hexp : (Nat.log 2 (Nat.log 2 n) + 1) * i ≤ 2 * Nat.log 2 n := calc
    _ ≤ (Nat.log 2 (Nat.log 2 n)) ^ 2 := hi'
    _ ≤ 2 ^ (Nat.log 2 (Nat.log 2 n) + 1) := ladner_square_le_power _
    _ = 2 * 2 ^ Nat.log 2 (Nat.log 2 n) := by rw [pow_succ']
    _ ≤ 2 * Nat.log 2 n := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hL)
  have hpow : m ^ i ≤ n ^ 2 := calc
    _ ≤ (2 ^ (Nat.log 2 (Nat.log 2 n) + 1)) ^ i := Nat.pow_le_pow_left
      (hm.trans (Nat.lt_pow_succ_log_self (by decide) (Nat.log 2 n)).le) _
    _ = 2 ^ ((Nat.log 2 (Nat.log 2 n) + 1) * i) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 * Nat.log 2 n) := Nat.pow_le_pow_right (by decide) hexp
    _ = (2 ^ Nat.log 2 n) ^ 2 := by rw [Nat.mul_comm 2, pow_mul]
    _ ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) _
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  calc i * m ^ i ≤ n * n ^ 2 := Nat.mul_le_mul hin hpow
       _ = n ^ 3 := by ring

/-- The uniform simulator's numeric deadline cost has a polynomial stage envelope.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Bound each of the code length, short-input length, deadline, and
constant by `(n + 1)^3`, then raise the sum bound to the simulator degree. -/
private theorem ladner_numeric_envelope (D n i : ℕ) (x : List Bool)
    (hi : i < Nat.log 2 (Nat.log 2 n)) (hx : x.length ≤ Nat.log 2 n) :
    D * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ D ≤
      (D * 4 ^ D) * (n + 1) ^ (3 * D) := by
  have hin : i ≤ n := hi.le.trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))
  have hb := (length_bits_le_self i).trans hin
  have hx' := hx.trans (Nat.log_le_self 2 n)
  have ht := ladner_short_deadline n i x.length hi hx
  have hcube : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hlin : n + 1 ≤ (n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (by decide : 1 ≤ 3)
  calc _ ≤ D * (4 * (n + 1) ^ 3) ^ D :=
         Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
       _ = (D * 4 ^ D) * (n + 1) ^ (3 * D) := by rw [mul_pow, ← pow_mul]; ring

/-- Polynomial preparation and an image budget absorb the exact composition overhead.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_composition_clock (C q A e n : ℕ) :
    2 * (C * (n + 1) ^ q) + A * (n + 1) ^ e + 2 ≤
      (2 * C + A + 2) * (n + 1) ^ max q e := by
  have hq := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_left q e)
  have he := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (le_max_right q e)
  have hp : 1 ≤ (n + 1) ^ max q e := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The floor binary logarithm is the canonical binary length minus one.
`Complexity.LogProg.length_bits_eq_log` supplies the nonzero case. -/
private theorem ladner_log_eq_bits_length (n : ℕ) :
    Nat.log 2 n = (Nat.bits n).length - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.log_zero_right, Nat.zero_bits, List.length_nil, Nat.zero_sub]
  · rw [LogProg.length_bits_eq_log (by omega)]
    omega

/-- The binary floor logarithm is polynomial-time, including noncanonical inputs.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_binary_log_FP : PolyTimeComputable
    (fun w : List Bool => Nat.bits (Nat.log 2 (LogProg.bitsVal w))) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_sub.comp
    ((hl.comp BinArith.polyTimeComputable_normBits).pairEncode
      (polyTimeComputable_const (Nat.bits 1)))
  convert h using 1
  funext w
  simp only [Function.comp_apply, BinArith.sub_pairEncode, ladner_log_eq_bits_length]

/-- A linear SAT verifier yields the exact exponential short-SAT search clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Apply `Complexity.exists_proj_decider` at certificate width `m + 1`.
The verifier sees `2m + 1` symbols, and its clock therefore has base `2m + 2`.
Identify the projected language using the supplied verifier equivalence. -/
private theorem ladner_short_SAT_machine
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    ∃ (a d b : ℕ) (E : FinTM Bool), E.DecidesInTime SAT
      (fun m => b * 2 ^ (m + 1) *
        (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2)) := by
  obtain ⟨V, hV, hv⟩ := linear
  obtain ⟨a, d, M, hM⟩ := mem_P_iff.mp hV
  obtain ⟨b, E, hE⟩ := exists_proj_decider 1 1 V (fun n => a * (n + 1) ^ d) M hM
  have hlang : {x : List Bool | ∃ u, u.length = 1 * (x.length + 1) ^ 1 ∧ x ++ u ∈ V} =
      SAT := by
    ext x
    simpa only [Set.mem_setOf_eq, one_mul, pow_one] using (hv x).symm
  rw [hlang] at hE
  refine ⟨a, d, b, E, ?_⟩
  convert hE using 1
  funext m
  congr 2 <;> simp only [one_mul, pow_one] <;> ring

/-- The short-SAT search clock is polynomial when the queried word is logarithmic.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** `2^m ≤ n + 1` and `2m + 2 ≤ 2(n + 1)`. Raise the latter
bound to each degree, enlarge both degrees to `d + 2`, and charge the outer
factor `2(n + 1)` to obtain degree `d + 3`. -/
private theorem ladner_short_SAT_envelope (a b d n m : ℕ) (hm : m ≤ Nat.log 2 n) :
    b * 2 ^ (m + 1) * (a * (2 * m + 2) ^ d + (2 * m + 2) ^ 2) ≤
      (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
  have hm' := hm.trans (Nat.log_le_self 2 n)
  have hexp : 2 ^ (m + 1) ≤ 2 * (n + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) hm).trans
      (Nat.pow_log_le_add_one 2 n))
  have hd : (2 * m + 2) ^ d ≤ 2 ^ d * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ d * (n + 1) ^ d := mul_pow _ _ _
    _ ≤ 2 ^ d * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  have htwo : (2 * m + 2) ^ 2 ≤ 4 * (n + 1) ^ (d + 2) := calc
    _ ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    _ = 4 * (n + 1) ^ 2 := by ring
    _ ≤ 4 * (n + 1) ^ (d + 2) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc _ ≤ b * (2 * (n + 1)) *
          ((a * 2 ^ d + 4) * (n + 1) ^ (d + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hexp) (by nlinarith)
       _ = (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3) := by
        rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
        ring

/-- Polynomial query preparation and a polynomial numeric budget suffice for simulation.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Extract the preparation machine through `polyTimeComputable_iff`.
The simulator's accepting and rejecting contracts compute the indicated bit on its image.
Use `FinTM.exists_comp_on_image`, then absorb its exact setup overhead with
`ladner_composition_clock`. The simulator clock is charged in the numeric deadline. -/
private theorem ladner_simulation_on_image (code input : List Bool → List Bool)
    (deadline : List Bool → ℕ)
    (hprep : PolyTimeComputable (fun z =>
      pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)))
    (hbudget : ∃ A e, ∀ z, expCode.simDegree *
      ((code z).length + (input z).length + deadline z + 1) ^ expCode.simDegree ≤
        A * (z.length + 1) ^ e) :
    PolyTimeComputable (fun z => [decide
      ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hprep
  obtain ⟨A, e, hA⟩ := hbudget
  have hU (z : List Bool) : expCode.simulator.ComputesInTime
      (pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z))
      [decide ((expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z))] (A * (z.length + 1) ^ e) := by
    by_cases h : (expCode.decode (code z)).toFinTM.ComputesInTime
        (input z) [true] (deadline z)
    · simpa only [h, decide_true] using
        (expCode.simulator_accepts (code z) (input z) (deadline z) h).mono (hA z)
    · simpa only [h, decide_false] using
        (expCode.simulator_rejects (code z) (input z) (deadline z) h).mono (hA z)
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M expCode.simulator _ _
    (fun n => C * (n + 1) ^ q) (fun n => A * (n + 1) ^ e) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + A + 2, max q e, ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q A e z.length)

/-- Short SAT evaluation on an FP-prepared image has polynomial total cost.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the linear verifier's exponential projection decider only on the
logarithmically short image. `ladner_short_SAT_envelope` bounds that phase in the
original input length; image composition explicitly includes the FP preparation clock. -/
private theorem ladner_short_SAT_on_image (f : List Bool → List Bool)
    (hf : PolyTimeComputable f)
    (hshort : ∀ z, (f z).length ≤ Nat.log 2 z.length)
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun z => [decide (f z ∈ SAT)]) := by
  obtain ⟨M, C, q, hM⟩ := (polyTimeComputable_iff _).mp hf
  obtain ⟨a, d, b, E, hE⟩ := ladner_short_SAT_machine linear
  have he := (FinTM.computesFunInTime_iff _ _ _).mp
    ((FinTM.decidesInTime_iff _ _ _).mp hE)
  have hU (z : List Bool) : E.ComputesInTime (f z) [decide (f z ∈ SAT)]
      ((2 * b * (a * 2 ^ d + 4)) * (z.length + 1) ^ (d + 3)) := by
    have h := (he (f z)).mono (ladner_short_SAT_envelope a b d z.length (f z).length (hshort z))
    by_cases hz : f z ∈ SAT
    · simpa only [MultiTapeTM.indicator_of_mem hz, hz, decide_true] using h
    · simpa only [MultiTapeTM.indicator_of_not_mem hz, hz, decide_false] using h
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E f _
    (fun n => C * (n + 1) ^ q)
    (fun n => (2 * b * (a * 2 ^ d + 4)) * (n + 1) ^ (d + 3)) hM hU
  apply (polyTimeComputable_iff _).mpr
  refine ⟨N, 2 * C + (2 * b * (a * 2 ^ d + 4)) + 2, max q (d + 3), ?_⟩
  apply (FinTM.computesFunInTime_iff _ _ _).mpr
  intro z
  exact ((FinTM.computesFunInTime_iff _ _ _).mp hN z).mono
    (ladner_composition_clock C q _ (d + 3) z.length)

/-- A canonical index below the double logarithm of a word's length is an FP test.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_index_lt_loglog_FP {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun S => [decide
      (LogProg.bitsVal (f S) < Nat.log 2 (Nat.log 2 (g S).length))]) := by
  have hl := ladner_lengthBits_FP
  have hi := BinArith.polyTimeComputable_normBits.comp hf
  have hcap := ladner_binary_log_FP.comp (ladner_binary_log_FP.comp (hl.comp hg))
  convert BinArith.polyTimeComputable_lt.comp (hi.pairEncode hcap) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.lt_pairEncode]

/-- The query guard is an FP test of canonical binary lengths and indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_validQuery_FP :
    PolyTimeComputable (fun S => [decide (ladner_validQuery S)]) := by
  have hl := ladner_lengthBits_FP
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hlog := ladner_binary_log_FP.comp (hl.comp polyTimeComputable_pairFstD)
  convert polyTimeComputable_and
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD)
    (BinArith.polyTimeComputable_le.comp (hx.pairEncode hlog)) using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode,
    Bool.decide_and, ladner_validQuery]

/-- The guarded simulator query has a polynomial preparation machine and clock.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Normalize the index, compute the input and context lengths, and test
`ladner_validQuery` in binary. Compute the power with `BinArith.powCap` capped at
`n³ + 1`; the short deadline bound makes saturation inert on valid queries. All
operations remain FP on malformed inputs. Mask all three fields on invalid queries,
then pair them and expose the preparation witness through `polyTimeComputable_iff`. -/
private theorem ladner_query_preparation :
    ∃ (M : FinTM Bool) (C q : ℕ),
      M.ComputesFunInTime ladner_queryPrep (fun n => C * (n + 1) ^ q) := by
  have hl := ladner_lengthBits_FP
  have hn := hl.comp polyTimeComputable_pairFstD
  have hi := BinArith.polyTimeComputable_normBits.comp BinArith.polyTimeComputable_slot2
  have hx := hl.comp BinArith.polyTimeComputable_slot3
  have hc : PolyTimeComputable (fun S : List Bool => Nat.bits ((pairFstD S).length ^ 3)) := by
    convert BinArith.polyTimeComputable_mul.comp
      ((BinArith.polyTimeComputable_mul.comp (hn.pairEncode hn)).pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, BinArith.mul_pairEncode]
    congr 1
    ring
  have hpower := BinArith.polyTimeComputable_powCap.comp (hx.pairEncode (hi.pairEncode hc))
  have hraw := BinArith.polyTimeComputable_mul.comp (hi.pairEncode hpower)
  have hd : PolyTimeComputable (fun S => Nat.bits (ladner_queryDeadline S)) := by
    convert polyTimeComputable_ite ladner_validQuery_FP hraw (polyTimeComputable_const []) using 1
    funext S
    by_cases hv : ladner_validQuery S
    · have ht := ladner_short_deadline (pairFstD S).length
        (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)).length hv.1 hv.2
      have hcap : (pairSndD (pairSndD S)).length ^
          LogProg.bitsVal (pairFstD (pairSndD S)) ≤ (pairFstD S).length ^ 3 + 1 := by
        by_cases hi0 : LogProg.bitsVal (pairFstD (pairSndD S)) = 0
        · simp only [hi0, pow_zero]
          omega
        · have hi1 : 1 ≤ LogProg.bitsVal (pairFstD (pairSndD S)) := by omega
          have hm := Nat.mul_le_mul_right
            ((pairSndD (pairSndD S)).length ^ LogProg.bitsVal (pairFstD (pairSndD S))) hi1
          rw [one_mul] at hm
          omega
      simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_true, if_true,
        BinArith.powCap_pairEncode, BinArith.mul_pairEncode, min_eq_left hcap]
    · simp only [Function.comp_apply, ladner_queryDeadline, hv, decide_false, Bool.false_eq_true, if_false,
        Nat.zero_bits]
  have hcode : PolyTimeComputable ladner_queryCode := by
    convert polyTimeComputable_ite ladner_validQuery_FP hi (polyTimeComputable_const []) using 1
    funext S
    simp only [Function.comp_apply, ladner_queryCode, decide_eq_true_eq]
  have hin : PolyTimeComputable ladner_queryInput := by
    convert polyTimeComputable_ite ladner_validQuery_FP BinArith.polyTimeComputable_slot3
      (polyTimeComputable_const []) using 1
    funext S
    simp only [ladner_queryInput, decide_eq_true_eq]
  exact (polyTimeComputable_iff _).mp ((hd.pairEncode hcode).pairEncode hin)

/-- The simulator's guarded numeric clock is polynomial in the serialized query length.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** For valid queries use `ladner_numeric_envelope` and the public
projection length bound. Invalid queries have empty code and input and deadline zero,
so their simulator budget reduces to its degree. -/
private theorem ladner_query_budget (S : List Bool) :
    expCode.simDegree *
      ((ladner_queryCode S).length + (ladner_queryInput S).length + ladner_queryDeadline S + 1) ^
        expCode.simDegree ≤
      (expCode.simDegree * 4 ^ expCode.simDegree) *
        (S.length + 1) ^ (3 * expCode.simDegree) := by
  by_cases hv : ladner_validQuery S
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_true]
    exact (ladner_numeric_envelope expCode.simDegree (pairFstD S).length
      (LogProg.bitsVal (pairFstD (pairSndD S))) (pairSndD (pairSndD S)) hv.1 hv.2).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (length_pairFstD_le S) 1) _))
  · simp only [ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hv, if_false,
      List.length_nil, Nat.zero_add, one_pow, mul_one]
    calc expCode.simDegree ≤ expCode.simDegree * 4 ^ expCode.simDegree :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
         _ ≤ _ * (S.length + 1) ^ (3 * expCode.simDegree) :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- Canonicalize all memo entries using the public encoded-list map.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_table_FP : PolyTimeComputable
    (fun T => BinArith.encWords ((ladner_values T).map Nat.bits)) := by
  have hg := BinArith.polyTimeComputable_normBits.comp polyTimeComputable_pairSndD
  have h := (BinArith.polyTimeComputable_mapW hg).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext T
  simp only [Function.comp_apply, BinArith.mapW_pairEncode, pairSndD_pairEncode,
    ladner_values, List.map_map, id_eq]
  rfl

/-- The number of numeric memo entries is available in binary in polynomial time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_values_length_FP :
    PolyTimeComputable (fun T => Nat.bits (ladner_values T).length) := by
  have hl := ladner_lengthBits_FP
  convert hl.comp BinArith.polyTimeComputable_countW using 1
  funext T
  simp only [Function.comp_apply, BinArith.countW_eq, List.length_replicate,
    ladner_values, List.length_map]

/-- Numeric memo entries are no more numerous than their serialized input bits.
`Complexity.BinArith.length_decWords_le` supplies the bound. -/
private theorem ladner_values_length_le (T : List Bool) : (ladner_values T).length ≤ T.length := by
  simpa only [ladner_values, List.length_map] using BinArith.length_decWords_le T

/-- Lookup of a memo exponent is FP after canonicalizing the table through `mapW`.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_get_value_FP : PolyTimeComputable (fun S : List Bool =>
    Nat.bits ((ladner_values (pairSndD S)).getD (pairFstD S).length 0)) := by
  have h := BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairFstD.pairEncode
    (ladner_table_FP.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext S
  simp only [Function.comp_apply, BinArith.getW_pairEncode_bits]

/-- Check the padding syntax against an exponent read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_tableSyntax (S : List Bool) : Bool :=
  match ladner_parse (pairFstD S) with
  | none => false
  | some (p, t) => decide (t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0)

/-- Table-dependent padding syntax is FP, even for enormous malformed exponents: the
instance of `ladner_padSyntax_FP` whose exponent is read from the supplied table.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_tableSyntax_FP : PolyTimeComputable (fun S => [ladner_tableSyntax S]) := by
  have hh : PolyTimeComputable (fun z : List Bool => Nat.bits
      ((ladner_values (pairSndD (pairSndD z))).getD (pairFstD z).length 0)) := by
    convert ladner_get_value_FP.comp
      (polyTimeComputable_pairFstD.pairEncode BinArith.polyTimeComputable_slot3) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact ladner_padSyntax_FP (h := fun S m => (ladner_values (pairSndD S)).getD m 0)
    polyTimeComputable_pairFstD hh

/-- The short-word guard relative to the memo entry count is an FP predicate.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_pad_guard_FP : PolyTimeComputable (fun S : List Bool =>
    [decide ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length)]) := by
  have hl := ladner_lengthBits_FP
  have h := BinArith.polyTimeComputable_le.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode
    (ladner_binary_log_FP.comp (ladner_values_length_FP.comp polyTimeComputable_pairSndD)))
  convert h using 1
  funext S
  simp only [Function.comp_apply, LogProg.bitsVal_bits, BinArith.le_pairEncode]

/-- Table-dependent padding membership of short words is polynomial-time.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Test the short-word guard and table-dependent syntax with the public
parser, list map, lookup, and saturated-power routines. Feed the parsed prefix to the
short-SAT machine only on guarded inputs, using the empty word as a default. The final
bit is masked by both syntax and guard, so no SAT fact about the default is assumed. -/
private theorem ladner_short_pad_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool => [decide
      ((pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length ∧
        pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0))]) := by
  let f : List Bool → List Bool := fun S =>
    if (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length then
      pairFstD (pairSndD (ladner_parseWord (pairFstD S))) else []
  have hf : PolyTimeComputable f := by
    convert polyTimeComputable_ite ladner_pad_guard_FP
      (BinArith.polyTimeComputable_slot2.comp (ladner_parse_FP.comp polyTimeComputable_pairFstD))
      (polyTimeComputable_const []) using 1
    funext S
    simp only [f, Function.comp_apply, decide_eq_true_eq]
  have hfst0 : pairFstD [] = [] := pairFstD_nil
  have hsnd0 : pairSndD [] = [] := by
    simpa only [Function.iterate_one] using BinArith.iterate_pairSndD_nil 1
  have hshort (S : List Bool) : (f S).length ≤ Nat.log 2 S.length := by
    by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
    · dsimp only [f]
      rw [if_pos hg]
      cases hp : ladner_parse (pairFstD S) with
      | none => simp only [ladner_parseWord, hp, hsnd0, hfst0, List.length_nil, Nat.zero_le]
      | some pt =>
        obtain ⟨p, t⟩ := pt
        simp only [ladner_parseWord, hp, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ((ladner_parsed_length hp).2.le.trans hg).trans
          (Nat.log_mono_right ((ladner_values_length_le _).trans (length_pairSndD_le S)))
    · simp only [f, hg, if_false, List.length_nil, Nat.zero_le]
  have hsat := ladner_short_SAT_on_image f hf hshort linear
  have hout := polyTimeComputable_and ladner_pad_guard_FP
    (polyTimeComputable_and ladner_tableSyntax_FP hsat)
  convert hout using 1
  funext S
  by_cases hg : (pairFstD S).length ≤ Nat.log 2 (ladner_values (pairSndD S)).length
  · cases hp : ladner_parse (pairFstD S) with
    | none =>
      have hn : pairFstD S ∉ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0) := by
        rintro h
        obtain ⟨p, t, ht, -, -⟩ := ladner_pad_membership.mp h
        rw [hp] at ht
        cases ht
      simp only [hg, hn, and_false, decide_false, ladner_tableSyntax, hp, Bool.false_and,
        Bool.true_and, decide_true]
    | some pt =>
      obtain ⟨p, t⟩ := pt
      have hm : (pairFstD S ∈ padSAT (fun m => (ladner_values (pairSndD S)).getD m 0)) ↔
          t = p.length ^ (ladner_values (pairSndD S)).getD p.length 0 ∧ p ∈ SAT := by
        rw [ladner_pad_membership]
        constructor
        · rintro ⟨p', t', hp', ht, hsat⟩
          rw [hp, Option.some.injEq, Prod.mk.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          exact ⟨ht, hsat⟩
        · rintro ⟨ht, hsat⟩
          exact ⟨p, t, hp, ht, hsat⟩
      simp only [hg, true_and, decide_true, Bool.true_and, hm, Bool.decide_and,
        ladner_tableSyntax, hp, f, if_true, ladner_parseWord, pairFstD_pairEncode,
        pairSndD_pairEncode]
  · simp only [hg, false_and, decide_false, Bool.false_and]

/-- The candidate context guard is an FP test of lengths and canonical indices.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_ctxGuard_FP : PolyTimeComputable (fun C => [decide (ladner_ctxGuard C)]) := by
  have hl := ladner_lengthBits_FP
  have hcount := ladner_values_length_FP.comp BinArith.polyTimeComputable_slot3
  convert polyTimeComputable_and
    (BinArith.polyTimeComputable_beq.comp ((hl.comp polyTimeComputable_pairFstD).pairEncode hcount))
    (ladner_index_lt_loglog_FP BinArith.polyTimeComputable_slot2 polyTimeComputable_pairFstD) using 1
  funext C
  simp only [Function.comp_apply, BinArith.beq_pairEncode, ladner_ctxGuard, Bool.decide_and]

/-- Deleting the high sentinel bit is FP through reversal and the public tail routine.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_dropLast_FP : PolyTimeComputable (fun w : List Bool => w.dropLast) := by
  convert BinArith.polyTimeComputable_reverse.comp
    (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse) using 1
  funext w
  simp only [Function.comp_apply, List.drop_one, List.tail_reverse, List.reverse_reverse]

/-- The guarded single-word acceptance equivalence has a polynomial-time test.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Decode the unary rank with a high sentinel, test the context and
short-input guards, and build a guarded uniform-simulator query. Compare its verdict
with short padded-SAT membership. The outer guards mask every invalid state; the
SAT and simulator implementations retain their explicit preparation clocks. -/
private theorem ladner_wordVerdict_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length]) := by
  have hl := ladner_lengthBits_FP
  let x : List Bool → List Bool := fun S => (Nat.bits ((pairSndD S).length + 1)).dropLast
  have hx : PolyTimeComputable x := by
    convert ladner_dropLast_FP.comp (BinArith.polyTimeComputable_add.comp
      ((hl.comp polyTimeComputable_pairSndD).pairEncode
        (polyTimeComputable_const (Nat.bits 1)))) using 1
    funext S
    simp only [x, Function.comp_apply, BinArith.add_pairEncode]
  let Q : List Bool → List Bool := fun S =>
    pairEncode (pairFstD (pairFstD S)) (pairEncode (pairFstD (pairSndD (pairFstD S))) (x S))
  have hQ : PolyTimeComputable Q :=
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      ((BinArith.polyTimeComputable_slot2.comp polyTimeComputable_pairFstD).pairEncode hx)
  have hprep : PolyTimeComputable ladner_queryPrep :=
    (polyTimeComputable_iff _).mpr ladner_query_preparation
  have hsim := (ladner_simulation_on_image ladner_queryCode ladner_queryInput
    ladner_queryDeadline hprep ⟨_, _, ladner_query_budget⟩).comp hQ
  have hpad := (ladner_short_pad_FP linear).comp
    (hx.pairEncode (BinArith.polyTimeComputable_slot3.comp polyTimeComputable_pairFstD))
  have hshort := BinArith.polyTimeComputable_le.comp ((hl.comp hx).pairEncode
    (ladner_binary_log_FP.comp (hl.comp (polyTimeComputable_pairFstD.comp
      polyTimeComputable_pairFstD))))
  have hout := polyTimeComputable_and (ladner_ctxGuard_FP.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_and hshort
      (polyTimeComputable_not (BinArith.polyTimeComputable_xor hsim hpad)))
  convert hout using 1
  funext S
  have hxS : (Nat.bits ((pairSndD S).length + 1)).dropLast = x S := rfl
  by_cases hc : ladner_ctxGuard (pairFstD S)
  · by_cases hs : (x S).length ≤ Nat.log 2 (pairFstD (pairFstD S)).length
    · have hvalid : ladner_validQuery (Q S) := by
        simp only [ladner_validQuery, Q, pairFstD_pairEncode, pairSndD_pairEncode]
        exact ⟨hc.2, hs⟩
      have htable : (x S).length ≤
          Nat.log 2 (ladner_values (pairSndD (pairSndD (pairFstD S)))).length := by
        rw [← hc.1]
        exact hs
      by_cases hrun : (ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))))).ComputesInTime (x S) [true]
          (LogProg.bitsVal (pairFstD (pairSndD (pairFstD S))) *
            (x S).length ^ LogProg.bitsVal (pairFstD (pairSndD (pairFstD S)))) <;>
        by_cases hsat : x S ∈ padSAT
          (fun m => (ladner_values (pairSndD (pairSndD (pairFstD S)))).getD m 0) <;>
        simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
          decide_true, Bool.true_and, BinArith.le_pairEncode, LogProg.bitsVal_bits,
          ladner_queryCode, ladner_queryInput, ladner_queryDeadline, hvalid, if_true,
          Q, pairFstD_pairEncode, pairSndD_pairEncode, ← ladnerMachine_eq,
          htable, hrun, hsat, iff_self, iff_true, iff_false, not_true_eq_false,
          decide_false, Bool.false_xor, Bool.true_xor,
          Bool.not_false, Bool.not_true]
    · simp only [Function.comp_apply, ladner_wordVerdict, hxS, hc, hs, true_and,
        false_and, decide_false, decide_true, BinArith.le_pairEncode, LogProg.bitsVal_bits,
        Bool.false_and, Bool.and_false]
  · simp only [Function.comp_apply, ladner_wordVerdict, hc, false_and, decide_false,
      Bool.false_and]

/-- A candidate-scan transition is FP once its single-word verdict is FP.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_testStep_FP
    (hw : PolyTimeComputable (fun S : List Bool =>
      [ladner_wordVerdict (pairFstD S) (pairSndD S).length])) :
    PolyTimeComputable ladner_testStep := by
  have hr := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hf := polyTimeComputable_headD.comp BinArith.polyTimeComputable_slot4
  have hword := hw.comp (polyTimeComputable_pairFstD.pairEncode hr)
  have hstep := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      ((hr.append (polyTimeComputable_const [true])).pairEncode
        (polyTimeComputable_and hf hword)))
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hstep using 1
  funext S
  simp only [Function.comp_apply, ladner_testStep, decide_eq_true_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

/-- The short-word count needs one doubling per bit of the positive stage length.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_queryFuel (C : List Bool) : List Bool :=
  if pairFstD C = [] then [true] else Nat.bits (pairFstD C).length

/-- The count-generation counter has exactly `log₂ n + 1` symbols, including at zero.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_length (C : List Bool) :
    (ladner_queryFuel C).length = Nat.log 2 (pairFstD C).length + 1 := by
  by_cases hn : pairFstD C = []
  · simp only [ladner_queryFuel, hn, if_true, List.length_cons, List.length_nil,
      Nat.log_zero_right]
  · have hlen : (pairFstD C).length ≠ 0 := by
      intro h
      exact hn (List.eq_nil_of_length_eq_zero h)
    simp only [ladner_queryFuel, hn, if_false, LogProg.length_bits_eq_log hlen]

/-- The doubling loop's final unary count is linearly bounded by the context length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryFuel_power_le (C : List Bool) :
    2 ^ (ladner_queryFuel C).length ≤ 2 * (C.length + 1) := by
  rw [ladner_queryFuel_length, pow_succ']
  exact Nat.mul_le_mul_left _ ((Nat.pow_log_le_add_one 2 _).trans
    (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Initialize the bounded query-count generation through the existing iterator.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countInit (C : List Bool) : List Bool :=
  pairEncode C (pairEncode (ladner_queryFuel C) [])

/-- A bounded doubling transition for query-count initialization; malformed states
cannot grow beyond the explicit guard. It is consumed by `BinArith.polyTimeComputable_iterate`.
[AB09, Theorem 3.3 and its proof] -/
private def ladner_countStep (S : List Bool) : List Bool :=
  let C := pairFstD S
  let rem := pairFstD (pairSndD S)
  let acc := pairSndD (pairSndD S)
  let next := acc ++ acc ++ [true]
  if rem = [] then S else pairEncode C (pairEncode (rem.drop 1)
    (if next.length ≤ 2 * (C.length + 1) then next else acc))

/-- Query-count initialization is an FP serialization.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countInit_FP : PolyTimeComputable ladner_countInit := by
  have hl := ladner_lengthBits_FP
  have hf : PolyTimeComputable ladner_queryFuel := by
    convert polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_const [true]) (hl.comp polyTimeComputable_pairFstD) using 1
    funext C
    simp only [Function.comp_apply, ladner_queryFuel, decide_eq_true_eq]
  exact polyTimeComputable_id.pairEncode (hf.pairEncode (polyTimeComputable_const []))

/-- One guarded query-count doubling transition is polynomial-time.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_countStep_FP : PolyTimeComputable ladner_countStep := by
  have ha := BinArith.polyTimeComputable_slot3
  have hn := (ha.append ha).append (polyTimeComputable_const [true])
  have hb := (polyTimeComputable_polyUnary 2 1).comp polyTimeComputable_pairFstD
  have hg : PolyTimeComputable (fun S : List Bool =>
      [decide ((pairSndD (pairSndD S) ++ pairSndD (pairSndD S) ++ [true]).length ≤
        2 * ((pairFstD S).length + 1))]) := by
    convert polyTimeComputable_lenLe.comp (hb.pairEncode hn) using 1
    funext S
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, pow_one]
  have hs := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp BinArith.polyTimeComputable_slot2).pairEncode
      (polyTimeComputable_ite hg hn ha))
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp BinArith.polyTimeComputable_slot2)
    polyTimeComputable_id hs using 1
  funext S
  simp only [Function.comp_apply, ladner_countStep, decide_eq_true_eq, id_eq]

/-- Every round of bounded query-count generation has the exact doubling value.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Before fuel exhaustion, `2^j - 1` becomes `2^(j+1) - 1` by
doubling and appending one. The full-fuel power bound makes the cap guard inert.
After exhaustion the transition is fixed, and the `min` in the exponent records this. -/
private theorem ladner_count_orbit (C : List Bool) (j : ℕ) :
    ladner_countStep^[j] (ladner_countInit C) =
      pairEncode C (pairEncode ((ladner_queryFuel C).drop j)
        (List.replicate (2 ^ min j (ladner_queryFuel C).length - 1) true)) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_countInit, List.drop_zero,
      Nat.zero_min, pow_zero, Nat.sub_self, List.replicate_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < (ladner_queryFuel C).length
    · have hm : min j (ladner_queryFuel C).length = j := min_eq_left hj.le
      have hm' : min (j + 1) (ladner_queryFuel C).length = j + 1 := min_eq_left (by omega)
      have hp : 0 < 2 ^ j := Nat.pow_pos (by decide)
      have he : 2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1 := by
        rw [pow_succ']
        omega
      have hn : List.replicate (2 ^ j - 1) true ++ List.replicate (2 ^ j - 1) true ++ [true] =
          List.replicate (2 ^ (j + 1) - 1) true := by
        rw [← List.replicate_add, ← List.replicate_succ']
        congr 1
        omega
      have hg : (List.replicate (2 ^ j - 1) true ++
          List.replicate (2 ^ j - 1) true ++ [true]).length ≤ 2 * (C.length + 1) := by
        rw [hn, List.length_replicate]
        have hp' := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
          (by omega : j + 1 ≤ (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
        omega
      have hne : (ladner_queryFuel C).drop j ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_drop, List.length_nil] at hlen
        omega
      have hg' : (List.replicate (2 ^ (j + 1) - 1) true).length ≤ 2 * (C.length + 1) := by
        rw [← hn]
        exact hg
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode, hm,
        hm', hne, if_false, hn, hg', if_true, List.drop_drop]
    · have hm : min j (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      have hm' : min (j + 1) (ladner_queryFuel C).length = (ladner_queryFuel C).length :=
        min_eq_right (by omega)
      simp only [ladner_countStep, pairFstD_pairEncode, pairSndD_pairEncode,
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j),
        List.drop_eq_nil_of_le (by omega : (ladner_queryFuel C).length ≤ j + 1),
        hm, hm', if_true]

/-- All initialized query-count generation states have a linear serialized envelope.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_count_size (C : List Bool) (j : ℕ) :
    (ladner_countStep^[j] (ladner_countInit C)).length ≤ 8 * (C.length + 1) ^ 1 := by
  rw [ladner_count_orbit]
  simp only [length_pairEncode, List.length_drop, List.length_replicate, pow_one]
  have hfuel : (ladner_queryFuel C).length ≤ C.length + 1 := by
    rw [ladner_queryFuel_length]
    exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
  have hpow := (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (min_le_right j (ladner_queryFuel C).length)).trans (ladner_queryFuel_power_le C)
  omega

/-- The candidate scan's unary budget is constructed in polynomial time with a capped
application of the public iterator.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Generate `2^(log₂ n+1)-1` true bits by bounded doubling for one
round per binary length bit. Every intermediate state has the linear envelope
`ladner_count_size`; the guard protects malformed states. Compose the resulting
budget with the fixed initial rank and conjunction flag. -/
private theorem ladner_testInit_FP : PolyTimeComputable ladner_testInit := by
  have hloop := BinArith.polyTimeComputable_iterate ladner_countStep_FP ladner_countInit_FP
    1 1 8 1 (fun C j _ => ladner_count_size C j)
  have hu : PolyTimeComputable (fun C => List.replicate (ladner_queryCount C) true) := by
    convert BinArith.polyTimeComputable_slot3.comp hloop using 1
    funext C
    have hfuel : (ladner_queryFuel C).length ≤ 1 * (C.length + 1) ^ 1 := by
      rw [ladner_queryFuel_length, pow_one, one_mul]
      exact Nat.add_le_add_right ((Nat.log_le_self 2 _).trans (length_pairFstD_le C)) 1
    simp only [Function.comp_apply, ladner_count_orbit, pairSndD_pairEncode, min_eq_right hfuel]
    rw [ladner_queryFuel_length]
    rfl
  exact polyTimeComputable_id.pairEncode
    (hu.pairEncode ((polyTimeComputable_const []).pairEncode (polyTimeComputable_const [true])))

/-- Every initialized scan state has the exact remaining count, completed rank, and flag.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Induct on the iteration count. Before exhaustion the unary counter
loses one symbol and the conjunction gains exactly the next verdict. After exhaustion
the transition fixes the state, so both counters and the flag remain constant. -/
private theorem ladner_test_orbit (C : List Bool) (j : ℕ) :
    ladner_testStep^[j] (ladner_testInit C) =
      pairEncode C (pairEncode (List.replicate (ladner_queryCount C - j) true)
        (pairEncode (List.replicate (min j (ladner_queryCount C)) true)
          [decide (∀ r < min j (ladner_queryCount C), ladner_wordVerdict C r = true)])) := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, ladner_testInit, Nat.sub_zero,
      Nat.zero_min, List.replicate_zero, Nat.not_lt_zero, false_implies, implies_true,
      decide_true]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hj : j < ladner_queryCount C
    · have hmin : min j (ladner_queryCount C) = j := min_eq_left hj.le
      have hmin' : min (j + 1) (ladner_queryCount C) = j + 1 := min_eq_left (by omega)
      have hne : List.replicate (ladner_queryCount C - j) true ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_replicate, List.length_nil] at hlen
        omega
      have hrem : ladner_queryCount C - j - 1 = ladner_queryCount C - (j + 1) := by omega
      have hrank : List.replicate j true ++ [true] = List.replicate (j + 1) true :=
        List.replicate_succ'.symm
      have hflag : (decide (∀ r < j, ladner_wordVerdict C r = true) && ladner_wordVerdict C j) =
          decide (∀ r < j + 1, ladner_wordVerdict C r = true) := by
        cases hv : ladner_wordVerdict C j <;>
          simp only [Nat.forall_lt_succ_right, Bool.decide_and, hv, Bool.false_eq_true,
            decide_false, decide_true, Bool.and_false, Bool.and_true]
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hne,
        if_false, hmin, hmin', List.drop_replicate, List.length_replicate,
        List.headD_cons, hrem, hrank, hflag]
    · have hmin : min j (ladner_queryCount C) = ladner_queryCount C := min_eq_right (by omega)
      have hmin' : min (j + 1) (ladner_queryCount C) = ladner_queryCount C :=
        min_eq_right (by omega)
      have hsub : ladner_queryCount C - j = 0 := by omega
      have hsub' : ladner_queryCount C - (j + 1) = 0 := by omega
      simp only [ladner_testStep, pairFstD_pairEncode, pairSndD_pairEncode, hmin,
        hmin', hsub, hsub', List.replicate_zero, if_true]

/-- The number of scan queries is bounded by twice the serialized context length plus two.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_queryCount_le (C : List Bool) :
    ladner_queryCount C ≤ 2 * (C.length + 1) := by
  have h := ladner_shortWords_count (pairFstD C).length
  simp only [ladner_shortWords, List.length_map, List.length_range] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (length_pairFstD_le C) 1))

/-- Every state reached by an initialized candidate scan has linear serialized length.
[AB09, Theorem 3.3 and its proof] -/
private theorem ladner_test_size (C : List Bool) (j : ℕ) :
    (ladner_testStep^[j] (ladner_testInit C)).length ≤ 12 * (C.length + 1) ^ 1 := by
  rw [ladner_test_orbit]
  simp only [length_pairEncode, List.length_replicate, List.length_cons, List.length_nil,
    pow_one]
  have h := ladner_queryCount_le C
  have hsum : ladner_queryCount C - j + min j (ladner_queryCount C) = ladner_queryCount C :=
    by omega
  omega

/-- After the bounded word scan, its masked flag is exactly the candidate predicate.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** The query-count bound ensures the scan is exhausted. Sentinel
completeness changes the conjunction over ranks into the universal short-word test.
The context guard supplies the table-length and index conditions, and masks all
inconsistent inputs. -/
private theorem ladner_candidate_readout (C : List Bool) :
    [ladner_candidate C] = if ladner_ctxGuard C then
      ladner_testOut (ladner_testStep^[2 * (C.length + 1) ^ 1] (ladner_testInit C))
      else [false] := by
  have hq : ladner_queryCount C ≤ 2 * (C.length + 1) ^ 1 := by
    simpa only [pow_one] using ladner_queryCount_le C
  by_cases hc : ladner_ctxGuard C
  · rw [if_pos hc, ladner_test_orbit]
    simp only [ladner_testOut, pairSndD_pairEncode, min_eq_right hq]
    have hequiv :
        (∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) ↔
        ∀ r < ladner_queryCount C, ladner_wordVerdict C r = true := by
      constructor
      · intro h r hr
        have hx : (Nat.bits (r + 1)).dropLast ∈
            ladner_shortWords (Nat.log 2 (pairFstD C).length) :=
          List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
        have hlen := (ladner_shortWords_complete _ _).mp hx
        simp only [ladner_wordVerdict, hc, hlen, true_and, decide_eq_true_eq]
        exact h _ hlen
      · intro h x hx
        obtain ⟨r, hr, he⟩ := List.mem_map.mp ((ladner_shortWords_complete _ _).mpr hx)
        have htest := h r (List.mem_range.mp hr)
        simp only [ladner_wordVerdict, decide_eq_true_eq] at htest
        simpa only [he] using htest.2.2
    have hlen : decide ((pairFstD C).length =
        (ladner_values (pairSndD (pairSndD C))).length) = true := decide_eq_true hc.1
    have hindex : decide (LogProg.bitsVal (pairFstD (pairSndD C)) <
        Nat.log 2 (Nat.log 2 (pairFstD C).length)) = true := decide_eq_true hc.2
    simp only [ladner_candidate, Bool.decide_and, hlen, hindex, Bool.true_and, hequiv]
  · rw [if_neg hc]
    have hn : ¬ ((pairFstD C).length = (ladner_values (pairSndD (pairSndD C))).length ∧
        LogProg.bitsVal (pairFstD (pairSndD C)) < Nat.log 2 (Nat.log 2 (pairFstD C).length) ∧
        ∀ x : List Bool, x.length ≤ Nat.log 2 (pairFstD C).length →
          ((ladnerMachine (LogProg.bitsVal (pairFstD (pairSndD C)))).ComputesInTime x [true]
            (LogProg.bitsVal (pairFstD (pairSndD C)) *
              x.length ^ LogProg.bitsVal (pairFstD (pairSndD C))) ↔
            x ∈ padSAT (fun m => (ladner_values (pairSndD (pairSndD C))).getD m 0))) := by
      rintro ⟨hn, hi, -⟩
      exact hc ⟨hn, hi⟩
    simp only [ladner_candidate, hn, decide_false]

/-- The polynomial-time candidate test is the guarded readout of the existing bounded
iterator; no Ladner target is used or proved here.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** Use the single-word FP verdict in the scan transition, the FP unary
initialization, and the linear bound on every scan state. Run `2(|C|+1)` rounds through
`BinArith.polyTimeComputable_iterate`, then read and mask its flag by the context guard. -/
private theorem ladner_candidate_FP
    (linear : ∃ V : Language Bool, V ∈ P ∧ ∀ x : List Bool, x ∈ SAT ↔
      ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V) :
    PolyTimeComputable (fun S => [ladner_candidate S]) := by
  have hstep := ladner_testStep_FP (ladner_wordVerdict_FP linear)
  have hloop := BinArith.polyTimeComputable_iterate hstep ladner_testInit_FP 2 1 12 1
    (fun C j _ => ladner_test_size C j)
  have hflag := BinArith.polyTimeComputable_slot4.comp hloop
  convert polyTimeComputable_ite ladner_ctxGuard_FP hflag (polyTimeComputable_const [false]) using 1
  funext C
  simpa only [Function.comp_apply, ladner_testOut, decide_eq_true_eq] using ladner_candidate_readout C

/-! ### Pre-ship: part B route statements (admitted; not proof evidence) -/

private def ladner_selectCtx (T : List Bool) (i : ℕ) : List Bool :=
  pairEncode (List.replicate (ladner_values T).length true) (pairEncode (Nat.bits i) T)

private def ladner_selectInit (T : List Bool) : List Bool :=
  pairEncode T (pairEncode [] (pairEncode [] []))

private noncomputable def ladner_selectStep (S : List Bool) : List Bool :=
  let T := pairFstD S
  let rank := pairFstD (pairSndD S)
  let flag := pairFstD (pairSndD (pairSndD S))
  let cap := Nat.log 2 (Nat.log 2 (ladner_values T).length)
  if flag ≠ [] then S else
    if rank.length < cap then
      if ladner_candidate (ladner_selectCtx T rank.length) then
        pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits rank.length)))
      else pairEncode T (pairEncode (rank ++ [true]) (pairEncode [] []))
    else pairEncode T (pairEncode rank (pairEncode [true] (Nat.bits cap)))

private def ladner_selectOut (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD S))

private noncomputable def ladner_memoInit (z : List Bool) : List Bool :=
  pairEncode (List.replicate z.length true) []

private noncomputable def ladner_memoStep (S : List Bool) : List Bool :=
  pairEncode (pairFstD S)
    (pairSndD S ++ pairEncode (Nat.bits (ladner_stage (ladner_values (pairSndD S)))) [])

private theorem ladner_selectInit_FP : PolyTimeComputable ladner_selectInit := by sorry

private theorem ladner_selectStep_FP (hc : PolyTimeComputable (fun C => [ladner_candidate C])) :
    PolyTimeComputable ladner_selectStep := by sorry

private theorem ladner_select_size (T : List Bool) (j : ℕ) :
    (ladner_selectStep^[j] (ladner_selectInit T)).length ≤ 12 * (T.length + 1) ^ 1 := by sorry

private theorem ladner_select_readout (T : List Bool) :
    ladner_selectOut (ladner_selectStep^[1 * (T.length + 1) ^ 1] (ladner_selectInit T)) =
      Nat.bits (ladner_stage (ladner_values T)) := by sorry

private theorem ladner_stage_FP
    (hcheck : PolyTimeComputable (fun S => [ladner_candidate S])) :
    PolyTimeComputable (fun T => Nat.bits (ladner_stage (ladner_values T))) := by
  have hloop := BinArith.polyTimeComputable_iterate (ladner_selectStep_FP hcheck)
    ladner_selectInit_FP 1 1 12 1 (fun T j _ => ladner_select_size T j)
  convert BinArith.polyTimeComputable_slot4.comp hloop using 1
  funext T
  exact (ladner_select_readout T).symm

private theorem ladner_stage_correct (vs : List ℕ)
    (hvs : ∀ m < vs.length, vs.getD m 0 = ladnerH m) :
    ladner_stage vs = ladnerH vs.length := by sorry

private theorem ladner_memoStep_FP
    (hstage : PolyTimeComputable (fun T => Nat.bits (ladner_stage (ladner_values T)))) :
    PolyTimeComputable ladner_memoStep := by sorry

private theorem ladner_memoInit_FP : PolyTimeComputable ladner_memoInit := by sorry

private theorem ladner_memo_orbit (z : List Bool) (j : ℕ) :
    ladner_memoStep^[j] (ladner_memoInit z) =
      pairEncode (List.replicate z.length true)
        (BinArith.encWords ((List.range j).map (fun m => Nat.bits (ladnerH m)))) := by sorry

private theorem ladner_memo_size (z : List Bool) (j : ℕ) (hj : j ≤ z.length + 1) :
    (ladner_memoStep^[j] (ladner_memoInit z)).length ≤ 4 * (z.length + 1) ^ 2 := by sorry

private theorem ladner_memo_readout (z : List Bool) :
    BinArith.getW (ladner_memoStep^[1 * (z.length + 1) ^ 1] (ladner_memoInit z)) =
      Nat.bits (ladnerH z.length) := by sorry

/-! ### The theorem and its remaining targets -/

/-- The binary digits of the delayed index at an input's length are polynomial-time
computable. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Maintain previously computed index values, simulate only the short
inputs through the uniformly timed acceptance simulator, and test SAT on short words.
Polynomially bounded iteration supplies the memo-table driver; the short-SAT search,
poly-bounded simulator invocation and state-size ledger are separate route obligations. -/
theorem ladnerH_polyTime :
    PolyTimeComputable (fun x => Nat.bits (ladnerH x.length)) := by
  have hloop := BinArith.polyTimeComputable_iterate
    (ladner_memoStep_FP (ladner_stage_FP (ladner_candidate_FP SAT_exists_linear_verifier)))
    ladner_memoInit_FP 1 1 4 2 (fun z j hj => ladner_memo_size z j (by simpa using hj))
  convert BinArith.polyTimeComputable_getW.comp hloop using 1
  funext z
  exact (ladner_memo_readout z).symm

/-- The padded SAT witness is in NP. [AB09, Theorem 3.3 and its proof]

**Proof sketch.** Guess the satisfiable prefix and its SAT certificate. Compute the
index at that prefix length and check the separator and exactly prescribed unary suffix. -/
theorem SAT_H_mem_NP : SAT_H ∈ NP :=
  sorry

/-- Polynomial-time computable, diverging padding cannot be NP-hard unless SAT belongs
to P. The hypothesis uses NP-hardness, rather than NP-completeness.
[AB09, Theorem 3.3 and its proof]

**Proof sketch.** A polynomial reduction into the padded language eventually maps an
instance to a satisfiable-prefix candidate at most the square root of its length.
Repeatedly shrink, with the finite small cases tabulated, to obtain a polynomial SAT decider. -/
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P :=
  sorry

/-- If P differs from NP, the explicit padded SAT language is in NP, outside P and
not NP-complete. [AB09, Theorem 3.3]

**Proof sketch.** A P decider would bound the delayed index and make bounded padding a
polynomial reduction from SAT. NP-hardness would instead combine divergence of the
index with the shrinking reduction. Each case would put SAT in P and collapse P and NP. -/
theorem SAT_H_intermediate (h : P ≠ NP) :
    SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H :=
  sorry

/-- If P differs from NP, an NP-intermediate language exists. [AB09, Theorem 3.3] -/
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L :=
  ⟨SAT_H, SAT_H_intermediate h⟩

end Complexity

## ===== campaign/fills/ladner-poly-memo/preship/RESULT.json =====

{
 "base": "1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb (campaign after #320)",
 "objects": "oleans-c1320 (gate 138 replay output, adopted)",
 "move": {
  "patch": "Ladner-move.patch.txt",
  "patch_sha256": "e16134f47a83ad3e95a5c71e30867b800a42e46affcd679ada2164b88f7461b1",
  "base_ladner_sha256": "29e0b907c0aba0929f3b5a66b6a706b0e0a0bda81efcebf2b07ecf0bdb5754c3",
  "moved_ladner_sha256": "4c9a04c3b28ae8a43cfded8ebdca4bf57b638214e82dabdccce7cd966ff0d914",
  "content": "the five admitted declarations ladnerH_polyTime, SAT_H_mem_NP, SAT_mem_P_of_padSAT_NPHard, SAT_H_intermediate, ladner (with docstrings) moved byte-identical, in order, to the end, under one new section header; sorted-line diff vs base: the header and one blank line",
  "elaboration": "Ladner exit 0, 0 errors, 4 sorry warnings (the admitted targets); Diagonalization facade exit 0, 0 errors"
 },
 "probe": "Fill4PartB.lean.txt",
 "exit": 0,
 "errors": 0,
 "sorry_warnings": 13,
 "admitted": "10 part B route helpers and the 3 targets other than ladnerH_polyTime",
 "proved_from_admitted": ["ladner_stage_FP (iterator assembly)", "ladnerH_polyTime (iterator + getW assembly, using ladner_candidate_FP and SAT_exists_linear_verifier)"],
 "note": "Route statements elaborate at the moved base with admitted bodies; not proof evidence."
}

## ===== campaign/items/ladner/LADNER-design.md =====

# Ladner statement phase: decisions and host obligations

**Post-#249 update:** the scratch [numeric clock probe](clock-envelope-probe/README.md)
proves the deadline bound and the numerical simulator polynomial envelope.
The setup, memo and other quantitative premises below remain open.


This records the already approved statement phase. It introduces no new mathematical proof, public host, theorem header, name, import or route decision. Mathematical holes remain for separately dispatched fills. The intended new home is `TCSlib/Complexity/Diagonalization/Ladner.lean`, namespace `Complexity`, with the planned `Diagonalization.lean` import/Contents wiring. PLAN Track3(c) requires this design note before the source file.

## Approved formal surface

PLAN§(f) records Seyoon's LD1–7 rulings. The planned chapter home/layout and necessary own-definition readings are included in that approved architecture, as recorded in the revised authorization correction; a separate LD10 permission is not required for that existing plan.

| Item | Recorded choice |
|---|---|
| LD1 | `ladnerMachine i := (expCode.decode (Nat.bits i)).toFinTM`, using the existing uniformly timed enumeration. Infinite padded indices remain a fill obligation. |
| LD2 | Test bounded acceptance: `M_i.ComputesInTime x [true] (i * x.length ^ i) ↔ x ∈ padSAT h`, over `x.length ≤ Nat.log 2 n`. Do not replace this with a total Boolean-output deadline at zero length. |
| LD3 | Literal pad: satisfiable `ψ`, then a false separator, then `ψ.length ^ h ψ.length` true bits. The split is at the final false separator. |
| LD4 | Floor logarithms `Nat.log 2 n` and `Nat.log 2 (Nat.log 2 n)`. |
| LD5 | Classical strong recursion, least qualifying index below the double-log cap, fallback to the cap. Skeleton-time readings are proved. |
| LD6 | The general diverging-`h` theorem has the approved `NPHard (padSAT h)` premise. NPHard is a weaker premise than NPComplete, so this is a stronger theorem; disclose the strengthening. |
| LD7 | Both the explicit `SAT_H_intermediate` witness and the existential `ladner` packaging theorem. |

The prototype uses the planned imports `ClassNP.Reductions`, `ClassNP.PClosure`, `CookLevin.Hardness`, `Diagonalization.EXPCOM` and `Mathlib.Data.Nat.Log`. No additional memo-driver import is part of the statement proposal.

The exact revised prototype is `campaign/items/dedup/overnight-2026-11-08/review/ladner-v2/Ladner-v2.lean.txt`, SHA256 `56c999de7f9a86a9d67cf4de3e567381fc448d2f798435602a99d79783bb3a6a`, on BASE/MAC8 `9b5dcf46408db681bcbc721930ef2203fa6bc47d`. It has 17 declarations: four definitions, six own-definition readings, six mathematical targets and the existential packaging theorem. The three substantive routine readings `padSAT_congr`, `ladnerH_eq`, `ladnerH_le` are proved; `mem_padSAT_iff`, `ladnerMachine_eq` and `SAT_H_eq` are definitional readings.

The six direct mathematical holes are exactly:

1. `ladnerH_polyTime`;
2. `SAT_H_mem_NP`;
3. `ladnerH_bounded_of_mem_P`;
4. `ladnerH_unbounded_of_not_mem_P`;
5. `SAT_mem_P_of_padSAT_NPHard`;
6. `SAT_H_intermediate`.

`ladner` only packages `SAT_H_intermediate`; its dependence on sorryAx does not constitute an independent proof of Ladner's theorem. The final proposal check exited0 with six declaration-sorry warnings. The selected17 AX inventory has sorryAx only in those six targets and the dependent packaging theorem; the owner readings use only standard axioms. Existing four-head/eight-pair seals are bounded proposal evidence, not a complete future gate.

## Source fidelity and declared deviations

Use `campaign/items/ladner/2026-11-08-source-check.md`. The accessible author-linked book is a January2007 draft, where the theorem is numbered3.4, and the older Duke chapter has different numbering. The2009 contents/assignment support the campaign's Theorem3.3 location, but exact2009 Exercise3.6 part(a)/(b) wording remains unverified. Follow the approved citation fallback: [AB09, Theorem3.3 and its proof]; do not claim the exercise parts were independently checked.

The natural-language deviations must state the approved acceptance equivalence/zero-deadline convention, uniform enumeration, and stronger NPHard premise. Also preserve the existing SAT convention: its total CNF decoder falls back to the empty satisfiable formula, so malformed words are in SAT. That convention is not altered here. It does not make the empty word belong to padSAT: the separator contributes a symbol, regardless of whether the SAT prefix itself is empty.

## LD9 remains a quantitative fill-route obligation

The current source has no dependency on the separately pending `SAT_exists_linear_verifier` proposal. That missing reader blocks a concrete short-SAT fill route, not the approved statement headers or their preparation. A statement-only PR can therefore proceed with the six admitted targets and explicit host limits. This note does not declare a full gate or fill ready.

The existing successful conditional probes, under the same MAC8 source, are:

| Probe | Actual result | What is still a premise |
|---|---|---|
| `Conditional-bounded-simulator.lean.txt`, attempt07 | exit0, errors0, sorries0 | A preparation machine for `pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)`, its setup clock, a polynomial bound on the simulator's numeric deadline cost, and a final polynomial envelope. |
| `Conditional-linear-SAT-search.lean.txt`, attempt08 | exit0, errors0, sorries0 | A P verifier language `V` and the exact `x.length+1` certificate equivalence for SAT. |
| `Conditional-memo-driver.lean.txt`, attempt10 | exit0, errors0, six unchanged main holes | Concrete FP step/init/readout functions, a polynomial iteration count, a uniform polynomial state-length invariant and exact final readout correctness. This scratch probe imports existing `BinaryArith.Iterate`; that extra import is not applied to the statement prototype. |

For fixed simulator degree `d`, the needed Ladner-specific numerical leaf includes

```text
∃ A e, ∀ n i (x : List Bool),
  i < Nat.log 2 (Nat.log 2 n) → x.length ≤ Nat.log 2 n →
  d * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ d
    ≤ A * (n + 1) ^ e.
```

The simulator's bound is polynomial in the value of the deadline, not in its bit length. Binary clock encoding alone does not discharge this leaf or the preparation-machine contract.

The conditional short-SAT probe assumes exactly

```text
∃ V : Language Bool, V ∈ P ∧
  ∀ x : List Bool, x ∈ SAT ↔
    ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V.
```

It derives an explicit search clock of the form

```text
b * 2^(m+1) * (a * (m+(m+1)+1)^d + (m+(m+1)+1)^2).
```

Public `SAT_mem_NP` loses the fixed certificate constants; a generic bound `2^(C*(log n+1)^c)` with `c>1` does not establish polynomial time in `n`. Existing private SAT verifier facts supply the intended sharp shape in the owner file, but they are not a public consumer interface. The proposed reader remains a separate pending decision; do not implement it, unfold private/foreign definitions, or infer approval from this note. An alternative sharp route is not claimed complete.

For memo iteration, the successful transfer is conditional on

```text
∀ z i, i ≤ a*(z.length+1)^k →
  (step^[i] (init z)).length ≤ B*(z.length+1)^b
```

and on the output equaling `Nat.bits (ladnerH z.length)` after the specified iterations. No concrete serialization, step algorithm, iteration count, orbit correctness or size bound has been supplied. These can be stated as local quantified fill obligations inside the already approved target; this note chooses no new public host or generic API. Any genuinely new host/header/name/import route must receive its own ruling.

## Preparation boundary

Proceed with the approved source skeleton, planned facade wiring and statement-gate preparation after recording this note. Keep the six mathematical holes. Do not silently add `SAT_reducible_padSAT_of_bounded` as a new public seventh obligation, the SAT verifier reader, a memo-machine API, or the iterator import. The bounded-padding reduction and code-index facts can remain named obligations in the approved sketches/local fill plan without changing the public surface.

Before declaring a gate ready, bind actual source/facade bytes, source fidelity/deviations, full relevant imported-definition boundaries and controls, AX/admission scope, names/screens/lints and the proper replay under maintainer rules. The host survey above is a conditional decomposition with unresolved premises, not a completed quantitative route. Before a fill brief, identify and preflight a concrete complete route or obtain the genuinely necessary new interface/import decision.

Carry forward the semantic checks at `n=0,1`, caps near4/16, `i=0`, empty inputs, exponent0 and `0^0`, malformed SAT words, final-false parsing, least-index fallback, and eventual divergence rather than mere unboundedness. Nonvacuity examples using `mem_padSAT_iff` may carry an explicit SAT witness; do not present that conditional fact as an unconditional SAT_H-nonempty proof. No new mathematical proof or interface was chosen by this record.
