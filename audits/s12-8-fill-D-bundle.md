## ===== audits/s12-8-fill-D-pack.md =====

# External audit pack — §12.8 stream D: R8.0b (the rich-body counter loop, generalized in place) and R8.6, fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). Design:
`machine-library-design.md` §12.8a §1 "R8.0b" and §8 "R8.0b target signatures", under the
user's decision **O2**.

§12.7's `counterLoopTM` runs only `Bool` bodies. Every rich-alphabet consumer of §12.8
needs a counter loop with a **rich body**: S1b's round, Savitch's frame step, and the record
rows' find and next. One batch (brief `briefs/s128-fill-D.md`, report attached verbatim)
built it **in place**, in `TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`:

1. it generalized `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` to any
   symbol type, types only;
2. it added `lastEmb`, `counterLoopTMVia` and the two generic contracts, proved by **the
   existing round induction, generalized**;
3. it re-derived the landed `Bool` contracts, with byte-identical statements, from the
   generic ones at `Function.Embedding.refl Bool` through Z5, `runFrom_eq_of_agreeOn`;
4. it filled R8.6, `expandTM_run_ofCfg`, **proved modulo** Scan's `writeAdvTM_run_ofCfg`.

**Why a separate gate.** This batch changes **audited public signatures**: the three
type-only generalizations. Under the §13d process rule, the user merges the PR (#38) only
after this gate closes. Fill gates close on zero blockers and zero majors (`workflow.md` §4).
The duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

The fill is the attached single-commit patch, `audits/evidence/s12-8/r80b-fill/s128-fill-D.patch`.
- It is Codex-authored (agent commit `b2b7ac5d` on base `37ab6091`), integrated by
  `git am -3` as `be1b7691` at the campaign tip `aed5b4ff`.
- `CounterLoop.lean` is byte-identical between `5afed90b`, the brief's base, and `aed5b4ff`.
- Since then the campaign tip has advanced. Stream B's `writeAdvTM_run_ofCfg` is now proved,
  in PR #41, so on merge R8.6 is admission-free.

**Every proof is kernel-checked**; the replay evidence is below. The audit object is the
**surface and its fidelity**:
- the signature generalizations;
- the four new declarations;
- the routes the brief binds;
- the privates;
- the duplication rule, including escalation **E1**.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Type-only generalization, body verbatim** (the gate's main object) | `counterLoopCfg`, `counterLoopOrbit`, `counterLoop_time_le`: exactly `{S : Type}` ↦ `{Symbol S : Type}`, `x : List Bool` ↦ `x : List Symbol`, and `Bool` ↦ `Symbol` where it denotes the tape alphabet. The counter word `w : List Bool` stays |
| **New public, the brief's exact text** | `lastEmb`, `counterLoopTMVia`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` |
| **Frozen statement, authorized body swap** | `counter_cfg_eq`, now an instance of the private `counter_layout`; `counterLoopTM_run_done`/`_escape`, now Z5 re-derivations; `expandTM_run_ofCfg`, from `sorry` to proof |
| **Frozen, statement and body byte-identical** | the other 20 publics, including `counterLoopTM` and `expandTM` |
| **Privates, 24 → 23** | added `counter_layout`, `counter_refl_agree`; removed (inlined, single-use) `counter_last_unselected`, `counter_patch_initial`, `counter_orbit_succ`; nine rewritten over a generic alphabet (ledger in the report); `counter_buffer_complement` by disposition (i), a body swap to `FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p` |
| **Imports** | exactly one added: `TuringMachine.SymbolLift` |
| **Docstrings** | the flagged re-derivation appendices, new-declaration prose and sketches, and the module bullets and status |

## Brief for the auditor

1. **The signature changes are sound and harmless.**
   - Confirm that each of the three generalized statements is its base statement with exactly
     the substitutions above.
   - Confirm that every existing call site elaborates unchanged, and that the base statements
     still hold as instances. The instance file `R80bInstances.lean.txt` restates each base
     statement verbatim and proves it by the in-tree theorem, and the maintainer re-ran it:
     0 errors, 0 warnings.
   - Rule on whether any consumer could be broken or weakened by the generalization, for
     example through elaboration of an implicit `Symbol`.
2. **One host induction** (§12.7 fill gate F4).
   - Confirm that `counter_rounds` is still the **only** round induction, with its
     unrestricted final state.
   - Confirm that both generic contracts are derived from it.
   - Confirm that both `Bool` contracts are short Z5 re-derivations at `refl` with no
     induction: one `counter_refl_agree`, then `simp only [z5]` and the generic contract.
   - Check that no second host, decrement trace or overlay re-proof exists. That is rule 4: no
     `counterLoopCfgVia`, and nothing private restating `SymbolLift`'s overlay layer.
3. **Route fidelity** (the brief's routes 1–4).
   - **The generic decrement phase:** guarded transport with `emb := counterLoopDecExit a`;
     the R1 configuration at `lastEmb k`; the overlay transport
     `Cfg.liftOver_decodeSymbols` / `MultiTapeTM.liftSymbols_runFrom_over`, **cited, not
     re-proved**; the landed `decrementTM_run_*_ofCfg` on the shadow; and read-back by
     `decodeBool_eq_some` and `FinTM.bufferTape_map`.
   - **`counter_refl_agree`:** it computes R1's action at `lastEmb k` from Embed's **public**
     surface and names no private Embed declaration.
   - **R8.6:**
     - `counterLoopTM_run_done` with `τ := fun _ => pat.length + 1`;
     - the orbit's closed form by induction over the **writer's** orbit, never over host
       rounds;
     - liveness from `runFrom_state_ne_none_of_le`;
     - the gate's checks `d = 0`, `w = []`, and `pat = []` with `d > 0`.
4. **Guards and range** (F5, F6).
   - The injectivity and guard discipline, including anchor priority when `exit = some a`,
     must be preserved by the generalized `counter_debit`/`counter_body`.
   - Every physical cost must stay within `r ≤ value + 1`, which is `counterOverhead`'s
     range.
5. **Freeze.** Re-establish from the attached patch:
   - every public in its class;
   - base lines 106–541 (symbol transport, C1 decrement, counter arithmetic)
     **byte-identical**, except `counter_buffer_complement`'s one-line body. The maintainer
     confirms this: the only changed line in that block is base line 213;
   - only `CounterLoop.lean` changed.

   Two independent checks agree, the agent's mechanical surface diff and the maintainer's,
   and both are attached.
6. **Duplication (failure mode 5) and escalation E1.** The screen (CounterLoop, Catalog,
   Embed, Seam, Simulation, SymbolLift) goes from 414 to 418 pairs. All four new pairs are
   in-file, with no cross-file pair and none removed.
   - **E1.** `counterLoopTMVia` reproduces the frozen `counterLoopTM` at 91%, and 84% in the
     other direction. Both texts are mandated: one is the new definition's exact text, the
     other a frozen definition. So the pair cannot be factored without breaking a mandate.
     The agent escalated correctly. **Maintainer's proposed disposition:** authorize this
     one definition pair, and open a 12.2c follow-up to redefine `counterLoopTM` as the
     identity-embedding instance of `counterLoopTMVia`. Rule on that, or propose another
     disposition.
   - `counterLoopTM_run_escape` ↔ `_run_done`, 83% / 72%: the two required Z5
     re-derivations, which share transport setup. Rule on whether this is idiom or a copy
     to factor.
   - Check the brief's hazards: `counter_layout` against `counter_cfg_eq`, where the body
     must have moved and not been duplicated; and the expand orbit induction against
     `counter_rounds`.
7. **Docstrings.**
   - Check the re-derivation appendices and the new declarations' sketches against the
     proofs as delivered.
   - Check the module status line: it names `writeAdvTM_run_ofCfg` as R8.6's only admitted
     dependency. Say whether that is now stale, since B is proved at the tip, and if so,
     whether to fix it by a doc-only refresh after this gate.
8. **Size.** `CounterLoop.lean` grows from 1,279 to 1,697 lines. The justification is
   recorded: the brief makes the generalization in place and forbids new files, file size
   alone is not a driver (user, 2026-10-11), and 12.2c owns the per-theme split. Say whether
   you disagree.
9. Report anything else the fill misstates, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** `SHA256SUMS` are all OK. The zip's C file (`lean-readlink.c`, an
  environment shim) was not compiled or run, and nothing references it. The agent's Python
  helpers were not run, and are not attached.
* **Freeze** (`audits/logs/s12-8-fill-D-freeze.log`), the maintainer's declaration-level
  check. It is consistent with the agent's `declaration-freeze.md`:
  - publics 27 → 31, the four additions;
  - three type-only lines with byte-identical bodies;
  - exactly the four authorized swaps;
  - privates 24 → 23;
  - one import.
* **Replay** (`audits/logs/s12-8-fill-D-replay.log`). The downstream closure of
  `CounterLoop`, 6 modules (`CounterLoop`, `InputCall`, `CfgRecord`, `TQBF`, and the
  `ClassPSPACE` and `TuringMachine` facades), run at `be1b7691`. **0 errors.** 11 sorry
  warnings, all out of scope at that tree; `CounterLoop` has 0. The user ran it from the
  maintainer's command. The agent's own 74-module sweep agrees: 37 → 36, exactly
  `expandTM_run_ofCfg` removed.
* **Axioms** (`audits/logs/s12-8-fill-D-axioms.log`).
  - All 31 publics are printed. Each is within the standard triple, except
    `expandTM_run_ofCfg`, which has `sorryAx`.
  - The prints match the agent's after-log line for line. The agent's base/after comparison
    shows the 28 existing lines unchanged.
  - The **admission walk** (`…-admissions.log`) shows that `expandTM_run_ofCfg`'s only
    `sorryAx` source is `writeAdvTM_run_ofCfg`. That row is proved at the current tip.
* **Instances** (`audits/logs/s12-8-fill-D-instances.log`): the maintainer re-ran
  `R80bInstances.lean.txt` read-only, with 0 errors and 0 warnings. A control copy with an
  appended false `decide` example fails as expected.
* **Lint** (`audits/logs/s12-8-fill-D-stylelint.log`): 0 FAIL over `TuringMachine` and over
  `TuringMachine/Build`. The warnings are all file-size ones.
* **Screen** (`audits/evidence/s12-8/r80b-fill/screen-{base,after}.txt` and
  `screen-delta.md`; the maintainer's run is `audits/logs/s12-8-fill-D-screen-after.txt`):
  identical.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-fill-D-findings.md`. When this gate closes, the user merges #38. With stream B
already merged, R8.0b and R8.6 are then fully proved.

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

## ===== briefs/s128-fill-D.md =====

# §12.8 fill, stream D — R8.0b: generalize `counterLoopTM`'s machinery in place (`counterLoopTMVia`), and R8.6


## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` succeeds.
  That commit contains the §12.8 statement layer and its closed gate (PR #28,
  `audits/s12-8-statements-{findings,r2-findings,resolutions}.md`), the Catalog
  trace promotion (PR #32), the shared pre-issue layer (`5afed90b`: the overlay transport
  in `SymbolLift`, `counter_cfg_eq` made public) and this brief's order list. If the check
  fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-D`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-D.zip`, containing
  `REPORT.md`, the full modified `Build/CounterLoop.lean`, a `git format-patch` series
  against your base, a git bundle, the final sweep log, the axiom logs (base and after), the
  evidence files listed under "Evidence for the R8.0b gate", and `SHA256SUMS`.
- Integration note, no action for you: this batch changes audited public signatures, so,
  under the §13d process rule, the maintainer integrates on a side branch, opens a PR, and
  runs a **separate R8.0b audit gate** before the user merges.

## What this is

Design `machine-library-design.md` §12.8a §1 "R8.0b" and §8 "R8.0b target signatures",
under the user's decision **O2**. `counterLoopTM` (§12.7) runs only `Bool` bodies, and
every rich-alphabet consumer of §12.8 (S1b's round, Savitch's frame step, the record rows)
needs a counter loop with a **rich body**. You build it **in place**:

1. generalize `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` to any symbol
   type (types only; bodies verbatim; every call site unchanged);
2. add `lastEmb`, `counterLoopTMVia` and its two contracts
   `counterLoopTMVia_run_done`/`_escape`, proved by **the existing round induction,
   generalized in place**;
3. re-derive the landed `counterLoopTM_run_done`/`_escape` (statements byte-identical) from
   the generic contracts at `e := Function.Embedding.refl Bool` through Z5,
   `MultiTapeTM.runFrom_eq_of_agreeOn`. There is **one** round induction. There is no second
   host with its own induction;
4. fill R8.6, `expandTM_run_ofCfg` (§12.8 gate: round-1 note 25, round-2 note 26),
   proved modulo Scan's sorried `writeAdvTM_run_ofCfg`.

**No new trace.** The decrement is the landed `decrementTM`, run through R1 and the
symbol lift; its framed contracts are cited, never re-traced.

**Pre-ship check (maintainer, executed):** `audits/evidence/s12-8/R80bPreShip.lean.txt`
(output `.out`). Against the round-2 olean tree it gave **0 errors and exactly 2 `sorry`
warnings**, both on the two generic contracts. Its pre-issue-2 variant cites the landed
overlay layer and adds the generic layout (Part 3(h)). Against the pre-issue-2 tree it
gives the same result: 0 errors and the same two warnings. It contains:

- **Part 1:** the three generalized declarations as probe-local copies, with `rfl` and
  instance checks against the landed `Bool` ones, including the landed `expandTM_run_ofCfg`
  statement restated over the generalized configuration;
- **Part 2:** the exact text of the four new declarations;
- **Part 3:** your route, proved piece by piece: (a) the decrement table is
  input-oblivious and writes no blank; (b) its lift at `refl` is the same table; (c) R1's
  action at `lastEmb k` from Embed's public surface; (d) the dec-table agreement and the
  whole-host `AgreeOn … Set.univ`; (e) **both landed `Bool` contracts, statements copied
  verbatim, re-derived from the generic ones by Z5**; (f) the frame-respecting lift: its
  step, run, shadow and decoding lemmas (landed in `SymbolLift` at `5afed90b`; the variant
  applies them to `decrementTM 1 0` from an arbitrary rich start); (g) the dec-phase
  configuration as an R1 configuration at `lastEmb k`; (h) the generic host layout, with the
  public `Bool` `counter_cfg_eq`, statement verbatim, as its instance;
- **Part 4:** `decide` runs of `counterLoopTMVia` over `Fin 3`, with foreign symbols in
  the input, on the body tape and in the counter tape's frame: the returning case at value 2
  with a leading-zero counter (exact time 16), escape (time 5), `k = 0`, `w = [false]` and
  `w = []`.

## Owned file and the freeze (modify this file and nothing else)

`TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean` (1279 lines at `5afed90b`).

| Class | Declarations (base line) |
|---|---|
| **Frozen: statement and body byte-identical** | `Action.mapWorkSymbols` 114, `Cfg.mapWorkSymbols` 123, `MultiTapeTM.mapWorkSymbols` 130, `MultiTapeTM.mapWorkSymbols_runFrom` 173, `decFixed` 189, `decrementTM` 225, `decrementTM_run_succ_ofCfg` 252, `decrementTM_run_underflow_ofCfg` 308, `counterWord` 355, `counterOverhead` 366, `counterWord_length` 419, `counterWord_value` 439, `counterOverhead_le_of_le` 501, `counterOverhead_le` 531, `CounterLoopState` 546 (with its `deriving`), `counterLoopStateFintype` 557, `counterLoopRedirect` 563, `counterLoopDecExit` 570, `counterLoopTM` 583, `expandTM` 1221 |
| **Frozen statement, sanctioned body swap** | `counter_cfg_eq` 626: public since `5afed90b`, it stays `Bool`-typed over the generalized `counterLoopCfg`. **Authorized body swap of a frozen public** (maintainer-confirmed): its statement stays byte-identical and its body becomes the instance `counter_layout q c ct cp` (route 2); `counterLoopTM_run_done` 1048, `counterLoopTM_run_escape` 1141 (the Z5 re-derivation, route 3); `expandTM_run_ofCfg` 1242 (`sorry` to proof, route 4) |
| **Type-only generalization, body verbatim** | `counterLoopCfg` 600, `counterLoopOrbit` 609, `counterLoop_time_le` 1197 |
| **New public** | `lastEmb`, `counterLoopTMVia` (directly after `counterLoopTM`, since the generalized privates use them); `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` (directly before `counterLoopTM_run_done`, after `counter_rounds`). The ordered declaration sequence is otherwise unchanged |

### Exact statements (binding; probe Part 1–2 with the landed names)

```lean
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=
  (fun c => M.runFrom c (τ c))^[r] c

theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2

def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j)

theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j)
```

The three generalized declarations keep their bodies (for `counterLoop_time_le`, its
proof) verbatim. Each generic contract is its `Bool` counterpart with exactly these
substitutions: `M, τ, c, ct` over `Γ`; `counterLoopTM M a …` becomes `counterLoopTMVia e M
a …`; `hw` has `w.map e`; the done finish is `some (e true)`; the escape finish is
`(counterWord w (r₀ + 1)).map e`; and the escape exit state is `ex`, since `e` is the
embedding. The done contract's first no-exit clause is re-wrapped to stay under 100
columns. All four clauses are kept in both.

## Proof routes (binding)

1. **The generic decrement phase**: `counter_debit`, rewritten. Its statement is the landed
   one over `Γ`, with host `counterLoopTMVia e M a exit`, `hw` over `w.map e`, and
   conclusion `counterPatch ct cp (v.map e)`. Steps:
   - Guarded transport, as now (`MultiTapeTM.runFrom_mapState_of_agreeOn`, `emb :=
     counterLoopDecExit a`, agreement by `rfl` on the pre-verdict controls). Its source is
     `embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)`.
   - The state-renamed start is the R1 configuration `embedEmitCfg (lastEmb k)
     (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d₁`, with `d₁ :=
     ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩` (probe 3(g): public
     selected-tape and frame lemmas only). Then `embedEmitTM_runFrom`.
   - The **overlay transport** landed in `SymbolLift` (cite it; never re-prove it).
     `Cfg.liftOver_decodeSymbols e d₁` rewrites `d₁` as the overlay of its decoded shadow
     `Cfg.decodeSymbols e d₁`. Then `MultiTapeTM.liftSymbols_runFrom_over` makes the lifted
     decrement's run the overlay of the `Bool` run from the shadow. Its two hypotheses for
     `decrementTM 1 0` are input-obliviousness (`fun _ _ _ _ => rfl`) and no blank write
     (case analysis, probe 3(a)).
   - On the shadow, apply the **landed** `decrementTM_run_succ_ofCfg` and
     `decrementTM_run_underflow_ofCfg` at `k := 1`, `i := 0`. The shadow's `hw` is `hw`
     rewritten by `FinTM.bufferTape_map_decode`.
   - Read back: on `[cp, cp + |w|)` the overlay is `bufferTape (v.map e)`, by
     `decodeBool_eq_some` and `FinTM.bufferTape_map`; off it, the cell is `ct`'s. State,
     heads and the verdict cut transfer unchanged. The trajectory gives `counterSpan`'s
     three parts as now.

   The plain `MultiTapeTM.liftSymbols_runFrom` **does not apply here**. It needs a
   configuration that is a lift everywhere, input included (`Cfg.liftSymbols` has input
   `x.map e`), while the host input `x : List Γ` and `ct` off the word are arbitrary. That
   is why the overlay layer was landed.
2. **The host layout and the round induction.** `counter_cfg_eq` is public and frozen at
   `Bool`, but the generic privates need the layout at `Γ`. Add one private
   `counter_layout`: `counter_cfg_eq`'s statement and body with `Bool` ↦ `Symbol` (binders
   `{k : ℕ} {Symbol S : Type} {x : List Symbol}`), and `counter_last_unselected` inlined
   (probe 3(h)). Every present use of `counter_cfg_eq` (base lines 773–967) cites
   `counter_layout`, and `counter_cfg_eq`'s body becomes `counter_layout q c ct cp`. This is
   G1's "specialization proved by instantiation", not a parallel copy.

   Then `counter_rounds`, generalized in place. It is the landed
   proof with the host `counterLoopTMVia e M a exit`, the counter words mapped by `e` in
   every `counterPatch` and frame hypothesis (lengths by `List.length_map`,
   `counterWord_length`), and `counter_body` generalized the same way (types plus host
   substitution only). It stays **the only host induction**, with its unrestricted final
   state (§12.7 fill F4). The generic contracts' bodies are the landed `Bool` bodies under
   the same substitutions; the done case's fill uses `List.map_replicate`.
3. **The `Bool` contracts by Z5** (probe 3(c)–(e)). One private `counter_refl_agree :
   (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn (counterLoopTM M a
   exit) Set.univ`. Body controls, `done` and `escape` agree by `rfl`. For `dec f`, compute
   R1's action at `lastEmb k` from the **public** surface: `conv_lhs => whnf`, `split` on
   the slot search, and `show` its defining term `(List.finRange 1).find? fun i => decide
   ((lastEmb k) i = j)`. Name **no** private Embed declaration. The lift at `refl` is the
   identity table (`decodeBool refl` is `some`; `Option.map refl` is `id`), and the
   remaining comparison is `incrementTM`'s table by cases. Then each `Bool` contract is
   `simp only [z5]` followed by the generic contract at `refl`, with `hw` converted by
   `Function.Embedding.coe_refl` and `List.map_id`. These are about 15 lines each and contain
   no induction.
4. **R8.6, `expandTM_run_ofCfg`.** `counterLoopTM_run_done` with `τ := fun _ => pat.length
   + 1`.
   - The orbit's closed form (`r` copies of `pat` from `pos`, head at `pos + r·|pat|`,
     state `some 0`) by induction on `r` **over the writer's orbit**, from
     `writeAdvTM_run_ofCfg`, never over host rounds. Keep it a `have`.
   - Intermediate liveness from the writer's finish by
     `MultiTapeTM.runFrom_state_ne_none_of_le`, since the writer contract has no liveness
     clause.
   - The sum is `Finset.sum_const` with `Finset.card_range`. The head clauses come from the
     loop's body-head clause and the writer's interval.
   - Checks named by the gate: `d = 0`, `w = []`, and `pat = []` with `d > 0`.
   - `writeAdvTM_run_ofCfg` is sorried at base in `Build/Scan.lean`, which is not yours:
     cite it. **Deliver R8.6 proved modulo it** (D5). The axiom print keeps `sorryAx` until
     Scan's fill lands; state that in `REPORT.md`.

## Ground rules (binding)

1. **Statement shape.** The type-only generalizations are their base statements with
   exactly `{S : Type}` ↦ `{Symbol S : Type}`, `x : List Bool` ↦ `x : List Symbol`, and
   `Bool` ↦ `Symbol` where it denotes the tape alphabet (`Cfg`, `MultiTapeTM`, `ct`). The
   counter word `w : List Bool` is **not** the tape alphabet and stays. The new declarations
   are the text above, character for character. Nothing else may change: no new
   hypotheses, no reordering, no renaming, no `Type*`.
2. **Docstrings.** Frozen declarations keep theirs. One flagged sentence in the module
   docstring may note alphabet genericity. The two `Bool` contracts and `counter_cfg_eq`
   get one flagged **Re-derivation appendix** paragraph each (their sketches describe the
   generic proof; policy §3 synchronization). New declarations get statement prose, the tag "(design
   §12.8a, R8.0b)" and a **Proof sketch**. Module docstring: add the four new names to
   `## Main definitions`/`## Main results`, a Design bullet for R8.0b, and update the
   status line (flagged; it names `writeAdvTM_run_ofCfg` while that is still sorried).
3. **Instance attestation (evidence, mandatory)**: `evidence/R80bInstances.lean.txt`,
   checked as a module against your tree. It must contain:
   - an `example` whose type is the **base** `counterLoop_time_le` statement, copied
     verbatim, proved by the generalized one;
   - the base statements of `counter_cfg_eq`, `counterLoopTM_run_done`,
     `counterLoopTM_run_escape` and `expandTM_run_ofCfg`, copied verbatim, each proved by
     the in-tree theorem (so each still elaborates over the generalized `counterLoopCfg`);
   - the probe's Part 4 instances run against the real `counterLoopTMVia` by `decide`.

   For the two generalized definitions, the mechanical diff of rule 6 is the evidence.
4. **No consumer edits; no parallel copies.** No file other than CounterLoop changes. If a
   call site fails because nothing fixes the alphabet, restore that one declaration's
   `Bool` form, record an escalation with the error, and continue. Never keep a `Bool` and
   a generic copy of the same declaration (no `counterLoopCfgVia`). The only `Bool`
   specialization kept beside a generic private is `counter_cfg_eq`, proved by
   instantiating `counter_layout`. There is no second host, round induction or decrement
   trace. Nothing private restates the landed `SymbolLift` overlay layer.
5. **Imports and privates.** Exactly one new import, `TCSlib.Complexity.TuringMachine.
   SymbolLift`. It is the fill's only new import edge. It is checked on `5afed90b`: no
   cycle (SymbolLift's closure is `Configuration`, `Deterministic`, `Finite`,
   `Simulation`), and it adds SymbolLift only to the closures of CounterLoop and InputCall.
   - Sanctioned new privates: `counter_refl_agree` (route 3) and `counter_layout`
     (route 2).
   - The single-use privates may be inlined: `counter_last_unselected` (into
     `counter_layout`), `counter_orbit_succ`, `counter_dec_injective`,
     `counter_redirect_injective`, `counter_patch_initial`.
   - **Net private count in CounterLoop: strictly below the base's 24** (D3; it was 25
     before `counter_cfg_eq` went public). List every added, removed and rewritten private,
     with its role.
   - `counter_buffer_complement` (line 211) is a special case of the public
     `FinTM.bufferTape_map`: its statement is `FinTM.bufferTape_map
     Equiv.boolNot.toEmbedding w p` by definition (checked read-only at the issue tree). Do
     **not** keep the duplicate proof. Take one of the two authorized dispositions, and keep
     every frozen public statement byte-identical:
     - **(i) Preferred: a private body swap.** Its statement is unchanged and its body
       becomes `FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p`. The four call sites are
       untouched. It counts as a rewritten private.
     - **(ii) Deletion.** Delete it and re-point its four call sites (lines 280, 292, 333
       and 340, in the bodies of `decrementTM_run_succ_ofCfg` and
       `decrementTM_run_underflow_ofCfg`) to `FinTM.bufferTape_map Equiv.boolNot.toEmbedding`.
       These are authorized body changes of those two frozen publics; their statements stay
       byte-identical. It counts −1. `simp`/`rw` see `⇑Equiv.boolNot.toEmbedding`, not
       `not`, so a re-pointed site needs the instance with its `not`-form type ascribed. If
       that would add a local copy at each site, take (i).

     Either way it counts toward the target of **at most 23**.
6. **Mechanical surface diff (evidence):** a declaration-level, comment-stripped
   comparison of CounterLoop against the base. Every public declaration is listed in its
   freeze class above: unchanged, type-only (show the exact token diff), body-swapped, or
   new. Every body change is listed. Lines 106–541 of the base (symbol transport, C1
   decrement, counter arithmetic) are **byte-identical**, bodies included. The one exception
   is rule 5's authorized `counter_buffer_complement` disposition: its body (lines 211–213),
   or, under (ii), its deletion and the four re-pointed call sites.
7. **Escalation** on anything unprovable as stated: stop on that item, record the
   obstruction, continue.
8. **Size: report only** (D7). Report the final line count. No new file may be created;
   12.2c owns the per-theme split.

## Gate guidance carried forward (binding)

- §12.7 fill gate (`audits/s12-counter-fill-findings.md`): **F4**, one round induction
  with an unrestricted final state; **F5**, the injectivity and guard discipline (anchor
  priority when `exit = some a`); **F6**, every physical cost within `r ≤ value + 1`
  (`counterOverhead`'s docstring).
- §12.8 gate: round-1 note 25 and round-2 note 26 (R8.6 is the stated counter-loop
  instance: "retain the single existing loop induction"). Round-2 notes 31 and 32 (consumers
  keep the dedicated-digit-tape discipline and O6 validation). The generic contract's
  arbitrary `ct` frame is strictly more general; do not restate it.

## Cited infrastructure (public and proved at the issue commit)

R1 (`Build/Embed`): `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom`,
`embedEmitTM_frame`, `embedEmitCfg_selected_tape`/`_pos`,
`MultiTapeTM.runFrom_mapState_of_agreeOn`. Z5 (`Simulation`): `MultiTapeTM.AgreeOn`,
`MultiTapeTM.runFrom_eq_of_agreeOn`, `FinTM.bufferTape` and its lemmas. Transport
(`SymbolLift`): `decodeBool`, `decodeBool_apply`, `MultiTapeTM.liftSymbols`,
`Cfg.liftSymbols`, and the overlay layer landed at `5afed90b`: `Cfg.liftOver`,
`MultiTapeTM.liftSymbols_step_over`, `MultiTapeTM.liftSymbols_runFrom_over`,
`Cfg.decodeSymbols`, `Cfg.liftOver_decodeSymbols`, `decodeBool_eq_some`,
`FinTM.bufferTape_map`, `FinTM.bufferTape_map_decode`. `Finite`:
`MultiTapeTM.runFrom_state_ne_none_of_le`.
Catalog: `incrementTM`, `FlagPhase`. Scan: `writeAdvTM`, and `writeAdvTM_run_ofCfg`
(sorried; cite only). Mathlib: `Function.Embedding.coe_refl`,
`Function.Semiconj.iterate_right`.

## Duplication governance (binding)

Run the text-level screen **before and after** (base: `audits/logs/s12-8-fill-D-screen-base.txt`,
539 declarations, 414 pairs at `5afed90b`):

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Simulation.lean \
  TCSlib/Complexity/TuringMachine/SymbolLift.lean
```

- **No new cross-file pair** with a CounterLoop declaration on one side.
- **Known hazards:**
  - the generic contracts against the `Bool` ones they replace: the `Bool` bodies shrink to
    Z5 re-derivations, so no pair should survive;
  - `counter_refl_agree` against Embed's core;
  - `counter_layout` against `counter_cfg_eq`: the body moves, so it must not be left in
    both;
  - the generic `counter_debit` against the overlay lemmas: cite them, never unfold them;
  - the expand orbit induction against `counter_rounds`.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-D.txt` (74 modules: the upstream closure
  of CounterLoop with the new `SymbolLift` edge, plus everything downstream and its
  closure; `TCSlib` and `TCSlib/ComputationalModels` excluded). Since `5afed90b`,
  `CfgRecord` imports `InputCall`, so `CfgRecord`, TQBF and the `ClassPSPACE` facade are
  downstream of CounterLoop:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-D.txt )
  ```

  **Base sorry-warning set, 37.** Yours: `CounterLoop` 1 (`expandTM_run_ofCfg`).
  Elsewhere: `Seam` 1, `Catalog` 12, `Scan` 4, `InputCall` 2, `CfgRecord` 5, TQBF 4,
  `NDCodes` 1, `Constructible` 2, `ConfigGraph` 3, `Inclusions` 2. Record the base list
  by name first.
- **Full downstream replay**: `Build/CounterLoop`, `Build/InputCall`, `Build/CfgRecord`,
  `ClassPSPACE/TQBF`, the `ClassPSPACE` facade and the `TuringMachine` facade, all with
  **zero errors**. Sorry warnings must be exactly the base's minus `expandTM_run_ofCfg`
  (36), by name.
- **Axiom prints, base and after,** for every public declaration of CounterLoop (base:
  `audits/logs/s12-8-fill-D-axioms-base.log`, 28 names). Every frozen and type-only name
  must be byte-identical with its base print, except that `expandTM_run_ofCfg` loses
  `sorryAx` only once `writeAdvTM_run_ofCfg` is proved (D5). The four new names must be
  within `[propext, Classical.choice, Quot.sound]`.
- Lint: `python3 scripts/campaign_style_lint.py` on `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/TuringMachine/Build`, 0 FAIL each.

## Evidence for the R8.0b gate (the zip must contain all of it)

1. The full downstream replay log, and the bootstrap log with the base sorry list.
2. The mechanical surface diff (rule 6), with the freeze class of every public declaration.
3. `evidence/R80bInstances.lean.txt` and its check output (rule 3).
4. The axiom logs, base and after, name by name.
5. The two copy-text screen outputs and their delta.
6. The private ledger (rule 5) and the file size.
7. The lint lines.

## Out-of-scope sorries you will see (leave every one untouched)

Catalog's twelve (`fieldsTape_field`, `compareTM_run_ofCfg`, the four seeks,
`scanTM_run_ofCfg`, the five `scanResult_*` identities); Scan's four (cite
`writeAdvTM_run_ofCfg`, never prove it); Seam's `seamCompTM₂_run_ofCfg`; CfgRecord's five;
InputCall's `exists_inputCallTM`, `exists_inputSeekTM`; NDCodes'
`exists_effectiveNDMachineCode`. Downstream, TQBF's four (`exists_adjacency_codec_cnf`,
`TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`). Upstream of TQBF:
`spaceConstructible_logSpace`, `spaceConstructible_linear`, `NSPACE_subset_exp_dtime`,
`NL_subset_P`, `polyTimeReducible_of_mem_NL`, `NP_subset_PSPACE`, `SAT3_mem_PSPACE`.
Other streams and batches own them. If a proof seems to *need*
one of them beyond the cited `writeAdvTM_run_ofCfg`, that is an escalation.

## REPORT.md checklist

- [ ] The base hash and the ancestor check.
- [ ] Every declaration per freeze class; every body change; the private ledger and delta
      (at most 23); the `counter_buffer_complement` disposition, (i) or (ii).
- [ ] R8.6 stated as proved modulo `writeAdvTM_run_ofCfg`, with its axiom print.
- [ ] Escalations (rule 4, rule 7), or "none".
- [ ] The instance attestation file and its result; the mechanical surface diff.
- [ ] Both screens, in-file pairs justified, "new copies: none".
- [ ] The replay (modules, zero errors, sorry set by name), the axiom comparison, the lint
      lines, the file size. The diff touches only CounterLoop.

## Known pitfalls at this pin (hard-won)

- **Embed's R1 core is private.** `(embedEmitTM ι N).tr` unfolds to `embedActionCore✝`,
  and `decide (Fin.last k = Fin.last k)` does not reduce for a variable `k`. Use probe 3(c)'s
  `conv_lhs => whnf`, `split` and `show` pattern; `Action` has no `@[ext]`, so compare
  fields with a local `have`.
- **`x.map (Function.Embedding.refl Bool)` is not `x` definitionally.** Re-derive at the
  level of runs (Z5), never by casting configurations. `simp` needs
  `Function.Embedding.coe_refl` (it is not `@[simp]`) and `List.map_id`.
- **Close the re-derivations with `exact`.** After `simp only [z5]`, `exact` the generic
  contract at `refl` (probe 3(e)); `Function.Embedding.refl Bool true` and `true` unify by
  definition. Rewrite the escape finish's `.map refl` away first.
- **The overlay layer's hypotheses** are table-level. For `decrementTM 1 0`,
  input-obliviousness is `fun _ _ _ _ => rfl`; the no-blank-write proof is probe 3(a). The
  shadow's input is `x.map fun _ => false`; pass the length proof as `by simp`.
- **The writer has no liveness clause.** Use `MultiTapeTM.runFrom_state_ne_none_of_le`.
- **`Inference needs context`** (G1): a `def`/`let` naming `counterLoopCfg` with no typed
  argument cannot infer `Symbol`. All landed call sites pass a typed `c` (probe Part 1).

## ===== audits/s12-8-fill-agent-reports/D-REPORT.md =====

# §12.8 stream D — R8.0b and R8.6

Code delivery is complete. The required signatures and frozen surface are preserved. One specification conflict remains for the separate audit gate: the exact new host definition triggers the brief's 90% duplication threshold, but both host definitions are frozen. See escalation E1 below.

## Base and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch checked out: `complexity/arora-barak-ch3-4`; working branch: `fill/s128-D`.
- Base: `37ab609199b2fad253b136375243db20faf88b16`.
- `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD`: exit 0 before editing.
- Delivery commit: `b2b7ac5d066086c9241be5007ba7d4b7eff95fc0`.
- No rebase, push or PR. Only `TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean` changes in the patch.
- Source size: 1,279 lines / 65,151 bytes at base; 1,697 lines / 87,771 bytes after. No new repository source files. The per-theme split remains outside this stream.

## Proofs and reuse

The configuration, orbit and uniform time bound are generalized in place with their bodies verbatim. The generic decrement uses the existing one-tape decrement, its two framed contracts, `Cfg.decodeSymbols`, `Cfg.liftOver_decodeSymbols`, `MultiTapeTM.liftSymbols_runFrom_over`, `FinTM.bufferTape_map_decode`, `FinTM.bufferTape_map` and `decodeBool_eq_some`. R1 embeds it on `lastEmb k`; guarded injective state transport supplies the verdict and both head trajectories. There is no new decrement trace or overlay theorem.

`counter_rounds` remains the one host-round induction, with unrestricted final body state. Both generic contracts instantiate it. Both Bool contracts are short re-derivations at `Function.Embedding.refl Bool` through `MultiTapeTM.runFrom_eq_of_agreeOn`; neither contains an induction. The agreement proof uses only Embed's public surface, including the prescribed slot-search calculation.

`expandTM_run_ofCfg` is **proved modulo `writeAdvTM_run_ofCfg`** (D5). Its only new induction is a local `have` for the advancing writer's orbit. Intermediate liveness comes from `MultiTapeTM.runFrom_state_ne_none_of_le`. The loop supplies the exact total time and trajectories. Scan is unchanged and remains sorried, so the expansion's axiom print still contains `sorryAx`.

## Declaration freeze

`evidence/declaration-freeze.md` lists every public declaration and every private change; its accompanying Python script, base source and brief permit replay. It reports zero failures, preserves the ordered sequence of surviving declarations, and checks the new declarations against the brief's exact text.

| Class | Declarations |
|---|---|
| Statement and body unchanged | `Action.mapWorkSymbols`, `Cfg.mapWorkSymbols`, `MultiTapeTM.mapWorkSymbols`, `MultiTapeTM.mapWorkSymbols_runFrom`, `decFixed`, `decrementTM`, both `decrementTM_run_*_ofCfg`, `counterWord`, `counterOverhead`, `counterWord_length`, `counterWord_value`, `counterOverhead_le_of_le`, `counterOverhead_le`, `CounterLoopState` and its deriving clause, `counterLoopStateFintype`, `counterLoopRedirect`, `counterLoopDecExit`, `counterLoopTM`, `expandTM` |
| Type-only, body verbatim | `counterLoopCfg`, `counterLoopOrbit`, `counterLoop_time_le` |
| Frozen statement, authorized body swap | `counter_cfg_eq`, `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `expandTM_run_ofCfg` |
| New, exact brief text | `lastEmb`, `counterLoopTMVia`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` |

The symbol-transport, decrement and counter-arithmetic block is byte-identical except for the authorized private `counter_buffer_complement` proof-body swap. Disposition **(i)** is used: it now directly cites `FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p`; all four callers remain untouched. Frozen docstrings are preserved, with only the authorized re-derivation appendices. Module status and the four new names are documented.

The only new import is `TCSlib.Complexity.TuringMachine.SymbolLift`.

## Private ledger

**24 → 23:** two additions, three removals. Every change is listed below; all other privates are unchanged.

| Private | Disposition and role |
|---|---|
| `counter_layout` | Added: the existing layout proof moved to its generic form; `counter_cfg_eq` instantiates it. |
| `counter_refl_agree` | Added: table agreement of the prescribed hosts at the identity embedding. |
| `counter_last_unselected` | Removed: its one-use proof is inlined into `counter_layout`. |
| `counter_patch_initial` | Removed: its one-use proof is inlined into the round-zero case. |
| `counter_orbit_succ` | Removed: its one-use invocation is replaced by `Function.iterate_succ_apply'`. |
| `counter_buffer_complement` | Rewritten: direct public buffer-map instance, disposition (i). |
| `counterSpan` | Rewritten: alphabet-generic trajectory predicate; body unchanged. |
| `counter_span_append` | Rewritten: alphabet-generic segment composition; proof unchanged. |
| `counterPatch` | Rewritten: alphabet-generic counter interval overwrite. |
| `counter_patch_twice` | Rewritten: alphabet-generic equal-width overwrite identity. |
| `counter_patch_frame` | Rewritten: alphabet-generic delimiter preservation. |
| `counter_debit` | Rewritten: one-tape decrement through overlay, R1 and guarded state transport. |
| `counter_body` | Rewritten: generic types/host/layout substitutions; same guarded R1 route. |
| `counter_rounds` | Rewritten: the existing single induction, with embedded counter words. |

## Verification

- **Final full replay:** all 74 modules from `briefs/orders/s128-fill-D.txt`, exit 0, zero errors, with fresh oleans. This includes `Build/CounterLoop`, `Build/InputCall`, `Build/CfgRecord`, `ClassPSPACE/TQBF`, the `ClassPSPACE` facade and the `TuringMachine` facade. See `final-sweep.log` and `evidence/downstream-replay.log`.
- **Sorry-warning inventory:** 37 at base → 36 after, by name. Exactly `expandTM_run_ofCfg` disappears; no warning is added. Full inventories are `evidence/sorries-base.txt` and `evidence/sorries-after.txt`.
- **Axiom prints:** all 28 existing lines, including the expansion's inherited `sorryAx`, are byte-identical to base. The four new names use only permitted axioms. See `axioms-base.log`, `axioms-after.log` and `evidence/axiom-comparison.txt`.
- **Instances:** `evidence/R80bInstances.lean.txt` checks with exit 0, zero errors and zero sorry warnings. It includes the five base statements verbatim, proved by their in-tree theorems, all probe Part 4 `decide` instances against the real host, and direct R8.6 checks for a zero counter, an empty counter and an empty pattern with positive counter.
- **Lint:** `style_lint: 0 FAIL, 14 WARN over 52 files`; `style_lint: 0 FAIL, 6 WARN over 16 files`. File-size warnings are report-only under D7. Full logs are included.
- **Diff:** `git diff --check` passes; the commit changes only the owned file. The git bundle verifies against the base.

The base bootstrap was resumed after environment failures (the initial compiler bus error and an empty `Mathlib` output directory shadowing the package cache); `evidence/bootstrap-base.log` concatenates the successful check for each of the 74 modules in the prescribed order. Raw attempt logs are retained. Initially Lean could not find its own executable in this runtime; the included C shim redirects only `/proc/<current-pid>/exe` to `/proc/self/exe`, without changing Lean or proof-checking code. A shared-cache refresh then caused a bus error. Dependencies were isolated in this checkout, and two unavailable cache modules were compiled from the pinned mathlib sources through `scripts/lean_check_tree.sh`. The final sweep uses an independent fresh output tree. `evidence/environment.txt` records the pin and shim hash. No `lake build` was run.

## Duplication and escalation E1

Before:

```text
declarations screened: 539; copy pairs (target reproduces >= half of source): 414; reproduced text: 121,876 chars
```

After:

```text
declarations screened: 543; copy pairs (target reproduces >= half of source): 418; reproduced text: 123,184 chars
```

`evidence/screen-delta.md` records all four added directed pairs and zero removed pairs. Both complete outputs are quoted in the appendices and shipped separately.

The screen is unmodified. All new pairs involving CounterLoop are in-file. No new cross-file pair involving CounterLoop appears. The low-level layout proof was moved, not copied beside its Bool specialization. Overlay lemmas are cited, not restated.

**E1 — incompatible instructions for the exact host definitions.** The mandatory new `counterLoopTMVia` definition reproduces 261 of the frozen `counterLoopTM` definition's 287 screened characters (91%). In the other direction the same overlap is 84%. The brief requires both exact definitions, yet also requires factoring every pair at 90% or above. Factoring would violate its explicit freeze and exact-text requirements. The definitions are therefore preserved and this item is escalated for the separate R8.0b gate. A narrow authorization for this prescribed pair, or a revised definition freeze, is needed to close that textual rule. There is no additional host induction.

The two Bool re-derivations also form one bidirectional in-file screen pair (83% / 72%). They are the separately required done and escape contracts, each applying Z5 and its corresponding generic theorem. They share transport setup but neither reproduces a proof of the loop. No pair of these proof bodies reaches 90%.

**New proof copies: none.** The unqualified requested phrase “new copies: none” is not attested, because the raw screen does classify the mandatory definition pair above as a new copy. No truth, inference, statement-shape or consumer-edit escalation was needed.

## Archive

The archive contains this report, the full modified source, the format-patch series against the recorded base, a git bundle with the base as prerequisite, final and base verification evidence, base/after axiom logs, the full screen outputs and delta, instance source/output, freeze checker/input/output, the private ledger, lint results and `SHA256SUMS`.

## Appendix — Base screen (complete output)

```text
declarations screened: 539; copy pairs (target reproduces >= half of source): 414; reproduced text: 121,876 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```

## Appendix — After screen (complete output)

```text
declarations screened: 543; copy pairs (target reproduces >= half of source): 418; reproduced text: 123,184 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
```

## ===== audits/s12-8-fill-D-integration.md =====

# §12.8 fill, stream D (R8.0b and R8.6): integration record

Brief: `briefs/s128-fill-D.md` (ancestor `182e6f44`). Delivery: `infra_local/fill-s128-D.zip`,
agent commit `b2b7ac5d` on base `37ab6091`. The agent's report is
`audits/s12-8-fill-agent-reports/D-REPORT.md`.

**This PR is held for the separate R8.0b audit gate.** The batch changes audited public
signatures, so under the brief's integration note (the §13d process rule) the user merges it
only after that gate closes. The gate's evidence set is in `audits/evidence/s12-8/r80b-fill/`.

## Result

**Complete.** The four tasks of the brief are done, with no admitted helper.

| Task | Declarations | Status |
|---|---|---|
| 1. Generalize in place (types only) | `counterLoopCfg`, `counterLoopOrbit`, `counterLoop_time_le` | bodies byte-identical; every call site unchanged |
| 2. The rich-body host | `lastEmb`, `counterLoopTMVia`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` | new, the brief's exact text; proved by the one round induction `counter_rounds` |
| 3. Re-derive the `Bool` contracts | `counterLoopTM_run_done`, `counterLoopTM_run_escape` | statements byte-identical; short re-derivations at `Function.Embedding.refl Bool` through Z5 `MultiTapeTM.runFrom_eq_of_agreeOn`, no induction |
| 4. R8.6 | `expandTM_run_ofCfg` | proved **modulo `writeAdvTM_run_ofCfg`** (stream B), as the brief allows |

`counter_cfg_eq`'s body now instantiates the generic private `counter_layout`, and the private
`counter_buffer_complement` takes disposition (i), a direct instance of
`FinTM.bufferTape_map`.

## Verification (maintainer)

- **Integrity.** All 44 `SHA256SUMS` entries are OK. The zip's C file
  (`evidence/lean-readlink.c`, an `LD_PRELOAD` shim for the agent's environment) is excluded:
  it was never compiled or run, and neither the patch nor any source references it. The
  agent's Python helpers (`declaration-freeze.py`, `screen-delta.py`, the copied
  `copy-text-screen.py`) were not run either, and are not committed.
- **Integration.** `git am -3` applied the one-patch series cleanly at the campaign tip
  `aed5b4ff` as `be1b7691`, keeping the agent's authorship. `CounterLoop.lean` is unchanged
  between the agent's base and the tip, and matches the delivered snapshot byte for byte.
- **Freeze** (`audits/logs/s12-8-fill-D-freeze.log`, the maintainer's own check).
  - Publics 27 → 31: the four additions of task 2, each checked against the brief's text.
  - The three `STATEMENT CHANGED` lines are task 1's type-only generalizations. Their bodies
    are byte-identical (comment-aware body comparison), as are `counterLoopTM`'s and
    `expandTM`'s.
  - Body changes exactly at the brief's four swaps: `counter_cfg_eq`,
    `counterLoopTM_run_done`, `counterLoopTM_run_escape`, `expandTM_run_ofCfg`.
  - Privates 24 → 23: `counter_layout` and `counter_refl_agree` added; `counter_last_unselected`,
    `counter_patch_initial` and `counter_orbit_succ` removed (one-use, inlined); nine rewritten
    over a generic alphabet, matching the report's ledger.
  - One import added, `TCSlib.Complexity.TuringMachine.SymbolLift`, which the brief prescribes.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in
    the added lines.
- **Duplication** (`audits/logs/s12-8-fill-D-screen-after.txt`, base
  `audits/logs/s12-8-fill-D-screen-base.txt`). 539 → 543 declarations and 414 → 418 pairs.
  The four new pairs are all in-file, with no cross-file pair and none removed:
  - `counterLoopTMVia` ↔ `counterLoopTM`, 91% / 84%: **E1**, below.
  - `counterLoopTM_run_escape` ↔ `counterLoopTM_run_done`, 83% / 72%: the two required
    `Bool` re-derivations. Each applies Z5 to its own generic contract; they share transport
    setup, and neither reproduces a proof of the loop.
  - **New proof copies: none.**
- **Lint** (`audits/logs/s12-8-fill-D-stylelint.log`): 0 FAIL over `TuringMachine` (14 WARN)
  and over `TuringMachine/Build` (6 WARN), all size warnings.
- **Size.** `CounterLoop.lean` grows from 1,279 to 1,697 lines. Justification: the brief makes
  the generalization in place and forbids new files, and file size alone is not a driver (user,
  2026-10-11). The file stays whole until 12.2c's per-theme reorganization of `Build/`.
- **Replay** (`audits/logs/s12-8-fill-D-replay.log`). 6 modules, the downstream closure of
  `CounterLoop`, at `be1b7691` into a snapshot of a tip-consistent olean tree; the user ran it
  from the maintainer's command. **0 errors.** 11 sorry warnings: `CounterLoop` 0,
  `InputCall` 2, `CfgRecord` 5, `TQBF` 4, both facades 0.
- **Axioms** (`audits/logs/s12-8-fill-D-axioms.log`; probe
  `audits/evidence/s12-8/S128FillDAxioms.lean.txt`, every public declaration). Read-only
  against the replay's tree.
  - All 31 prints are within `[propext, Classical.choice, Quot.sound]`, except
    `expandTM_run_ofCfg`'s `sorryAx`.
  - They match the agent's after-log line for line, and the agent's base/after comparison
    shows the 28 existing lines unchanged.
- **Admission walk** (`audits/logs/s12-8-fill-D-admissions.log`). The only constant in
  `expandTM_run_ofCfg`'s dependency closure that mentions `sorryAx` is
  `writeAdvTM_run_ofCfg`. So R8.6 is proved modulo exactly the cited row, as reported.
  Stream B proves that row (PR for B+C), so R8.6 becomes admission-free once both are merged.
- **Instances** (`audits/logs/s12-8-fill-D-instances.log`). The agent's
  `R80bInstances.lean.txt` was re-run read-only by the maintainer: 0 errors, 0 warnings. It
  covers the five base statements verbatim, the brief's executed rich-alphabet instances, and
  R8.6 at a zero counter, an empty counter and an empty pattern. A control copy confirms the
  file is genuinely checked.

## Escalation E1 (for the R8.0b gate)

The brief requires both definitions verbatim:
- `counterLoopTMVia` is mandated new text;
- `counterLoopTM` is frozen.

Their screen pair is 91%, over the 90% copy line. Factoring the pair would break one of the
two text mandates, so the agent kept both and escalated, correctly. This is a definition pair
the brief itself prescribed, not copied proof: there is one round induction, and the `Bool`
contracts are derived from the generic ones.

**Proposed disposition:**
1. Authorize this one pair at the R8.0b gate.
2. Open a 12.2c follow-up: redefine `counterLoopTM` as the identity-embedding instance of
   `counterLoopTMVia`. That would remove the pair; the brief's freeze ruled it out here.

## Disposition

- The R8.0b gate pack follows. The user merges this PR after that gate closes.
- With stream B merged, R8.6 is admission-free; the post-merge sweep confirms it.

## ===== audits/evidence/s12-8/r80b-fill/s128-fill-D.patch =====

From be1b7691b2f23de6b252d4d467d9c3cf2cfabdb9 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Sun, 11 Oct 2026 14:02:11 -0600
Subject: [PATCH] Generalize counter loop machinery and prove expansion
 contract

---
 .../TuringMachine/Build/CounterLoop.lean      | 844 +++++++++++++-----
 1 file changed, 631 insertions(+), 213 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean b/TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
index 5fdb5fad..48df3714 100644
--- a/TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean
@@ -7,6 +7,7 @@ import Mathlib.Data.Nat.Digits.Defs
 import Mathlib.Logic.Equiv.Bool
 import TCSlib.Complexity.TuringMachine.Build.Catalog
 import TCSlib.Complexity.TuringMachine.Build.Scan
+import TCSlib.Complexity.TuringMachine.SymbolLift
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -25,10 +26,10 @@ are the two-tape uniform machine-code scheme (`Codes2Tape`), the EXPCOM
 simulation, the nondeterministic time hierarchy (a fused countdown at
 linear overhead) and the space hierarchy's configuration-count clock.
 
-**Status: proved, except the §12.8 row.** All definitions are real and every
-§12.7 contract is proved (§12.7 fill, `2e99bda1`; fill gate closed
-2026-10-10). The §12.8 expansion row `Turing.expandTM_run_ofCfg` (R8.6) is a
-statement, sorried with a proof sketch, pending the §12.8 fill.
+**Status update (§12.8 fill, R8.0b/R8.6).** All contracts in this file are proved.
+The expansion proof is modulo `Turing.writeAdvTM_run_ofCfg`, still sorried in `Build/Scan`.
+**Alphabet update (R8.0b).** The shared loop machinery now admits any tape alphabet,
+with binary digits embedded into its dedicated counter tape.
 
 ## Design (decisions 12.7.1–12.7.6, user 2026-10-10)
 
@@ -48,6 +49,9 @@ statement, sorried with a proof sketch, pending the §12.8 fill.
   designated body exit leaves through the live anchor `escape` (12.7.2).
   A consumer branches on the two exits with `Turing.seamCompTM`; with no
   exit (`none`), `escape` is unreachable.
+* **R8.0b, rich alphabets.** `Turing.counterLoopTMVia` transports the one-tape
+  decrement through the symbol overlay and R1. Both generic contracts use the
+  single round induction; the Bool contracts follow by identity-table agreement.
 * **Round cost** (12.7.3). Each round from body configuration `c` lasts
   the **exact** time `τ c`. A round-indexed cost is the special case of
   `τ` along the orbit, and a uniform bound is the corollary
@@ -70,6 +74,8 @@ statement, sorried with a proof sketch, pending the §12.8 fill.
 * `Turing.CounterLoopState`, `Turing.counterLoopTM`,
   `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
   configurations, and the body's round-start configurations.
+* `Turing.lastEmb`, `Turing.counterLoopTMVia` — the last-tape embedding and
+  the rich-alphabet counter host.
 * `Turing.expandTM` — the expansion (§12.8, R8.6): the counter loop whose
   round is the advancing writer `Turing.writeAdvTM`.
 
@@ -85,9 +91,11 @@ statement, sorried with a proof sketch, pending the §12.8 fill.
 * `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
   host's exact whole-run contracts, with no earlier exit, the counter
   head's range, and the body heads' trajectory.
+* `Turing.counterLoopTMVia_run_done`, `Turing.counterLoopTMVia_run_escape` —
+  the rich-alphabet whole-run contracts, preserving the arbitrary rich frame.
 * `Turing.counterLoop_time_le` — the uniform per-round bound.
 * `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per
-  counter unit, contiguously, at exact time (statement, §12.8).
+  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).
 
 ## References
 
@@ -210,7 +218,7 @@ private lemma counter_complement_twice {k : ℕ} {S : Type} {x : List Bool}
 /-- Complementation of a buffered word preserves its blank delimiters. -/
 private lemma counter_buffer_complement (w : List Bool) (p : ℤ) :
     FinTM.bufferTape (w.map not) p = (FinTM.bufferTape w p).map not := by
-  by_cases hp : 0 ≤ p <;> simp [FinTM.bufferTape, hp]
+  exact FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p
 
 /-- **R3, decrement** (design §12.7, C1). In-place little-endian fixed-width
 binary decrement on tape `i`. The borrow pass flips `false` cells to `true`
@@ -592,47 +600,61 @@ def counterLoopTM {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S
     | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
     | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩
 
+/-- Select the last host tape as a one-tape bank (design §12.8a, R8.0b).
+**Proof sketch.** The singleton domain makes the constant last-tape map injective. -/
+def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
+  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
+
+/-- Run a rich-alphabet body with an embedded binary counter on the last tape
+(design §12.8a, R8.0b).
+**Proof sketch.** R1 forwards the body and the symbol-lifted one-tape decrement;
+the existing redirections connect the phases without dispatch steps. -/
+def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
+    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
+    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
+  q₀ := .dec .run
+  tr := fun q inp work =>
+    match q with
+    | .body s =>
+      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
+    | .dec f =>
+      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
+        (counterLoopDecExit a)
+    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
+    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩
+
 /-- A host configuration with host state `q`: the body configuration `c` on
 the first `k` tapes (its own state field is ignored), the counter tape `ct`
 with its head at `cp` as the last tape, and the body's output as the host's
 output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
 with the counter as the ambient frame. -/
-def counterLoopCfg {k : ℕ} {S : Type} {x : List Bool}
-    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
-    (ct : ℤ → Option Bool) (cp : ℤ) : Cfg (k + 1) Bool (CounterLoopState S) x :=
+def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
+    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
   { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
       CounterLoopState.body with state := q }
 
 /-- The body configurations at the starts of successive rounds: round `r`
 starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
 steps. -/
-def counterLoopOrbit {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
-    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) : Cfg k Bool S x :=
+def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
+    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=
   (fun c => M.runFrom c (τ c))^[r] c
 
 /-! ### Shared phase and prefix invariants -/
 
-/-- The last tape is outside the forwarding embedding's selected bank. -/
-private lemma counter_last_unselected (k : ℕ) :
-    Fin.last k ∉ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) := by
-  rintro ⟨i, hi⟩
-  exact Fin.castSucc_ne_last i hi
-
-/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
-host configuration is the body bank followed by its counter tape.
-
-**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
-`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`). -/
-theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
-    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
-    (ct : ℤ → Option Bool) (cp : ℤ) :
+/-- The host layout over any tape alphabet.
+**Proof sketch.** R1 identifies the selected body bank and the last-tape frame. -/
+private lemma counter_layout {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
+    (ct : ℤ → Option Symbol) (cp : ℤ) :
     counterLoopCfg q c ct cp =
       ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
         Fin.lastCases cp c.workTapePos, c.output⟩ := by
   have hf := (embedEmitTM_frame Fin.castSuccEmb
-    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Bool Unit)
+    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Symbol Unit)
     (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
-    (Fin.last k) (counter_last_unselected k)
+    (Fin.last k) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
   apply Cfg.ext <;> try rfl
   · funext j
     refine Fin.lastCases ?_ (fun i => ?_) j
@@ -647,6 +669,21 @@ theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
     · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
         embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
 
+/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
+host configuration is the body bank followed by its counter tape.
+
+**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
+`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`).
+
+**Re-derivation appendix (R8.0b).** Instantiate the generic private layout at the Bool alphabet. -/
+theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
+    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
+    (ct : ℤ → Option Bool) (cp : ℤ) :
+    counterLoopCfg q c ct cp =
+      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
+        Fin.lastCases cp c.workTapePos, c.output⟩ :=
+  counter_layout q c ct cp
+
 /-- Injective successor redirection for the decrement's five controls. -/
 private lemma counter_dec_injective {S : Type} (a : S) :
     Function.Injective (counterLoopDecExit a) := by
@@ -671,9 +708,9 @@ private lemma counter_redirect_injective {S : Type} [DecidableEq S]
 
 /-- Common trajectory data for a finite host segment, with a chosen set of
 permitted body-head vectors. -/
-private def counterSpan {k : ℕ} {S : Type} {x : List Bool}
-    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
-    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
+private def counterSpan {k : ℕ} {Γ S : Type} {x : List Γ}
+    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
+    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
     (R : (Fin k → ℤ) → Prop) : Prop :=
   (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
     (H.runFrom z u).state ≠ some .escape) ∧
@@ -685,9 +722,9 @@ private def counterSpan {k : ℕ} {S : Type} {x : List Bool}
 **Proof sketch.** Split a queried time at the first segment's length and
 use run addition on the suffix. The two head-vector relations imply the
 requested relation separately. -/
-private lemma counter_span_append {k : ℕ} {S : Type} {x : List Bool}
-    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
-    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
+private lemma counter_span_append {k : ℕ} {Γ S : Type} {x : List Γ}
+    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
+    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
     (R₁ R₂ R : (Fin k → ℤ) → Prop)
     (h₁ : counterSpan H z s cp width R₁)
     (h₂ : counterSpan H (H.runFrom z s) t cp width R₂)
@@ -711,22 +748,12 @@ private lemma counter_span_append {k : ℕ} {S : Type} {x : List Bool}
     · rw [suffix u (by omega)]; exact hr₂ _ (h₂.2.2 (u - s) (by omega))
 
 /-- A width-preserving overwrite of just the counter word interval. -/
-private def counterPatch (ct : ℤ → Option Bool) (cp : ℤ) (w : List Bool) : ℤ → Option Bool :=
+private def counterPatch {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (w : List Γ) : ℤ → Option Γ :=
   fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
     then FinTM.bufferTape w (q - cp) else ct q
 
-/-- Patching the word that is already present changes no cell. -/
-private lemma counter_patch_initial (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
-    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
-      ct (cp + p) = FinTM.bufferTape w p) : counterPatch ct cp w = ct := by
-  funext q
-  apply ite_eq_right_iff.mpr
-  intro h
-  have hf := hw (q - cp) (by omega) (by omega)
-  simpa using hf.symm
-
 /-- Equal-width patches overwrite the same interval, preserving the original frame. -/
-private lemma counter_patch_twice (ct : ℤ → Option Bool) (cp : ℤ) (u v : List Bool)
+private lemma counter_patch_twice {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
     (hv : v.length = u.length) :
     counterPatch (counterPatch ct cp u) cp v = counterPatch ct cp v := by
   funext q
@@ -734,7 +761,7 @@ private lemma counter_patch_twice (ct : ℤ → Option Bool) (cp : ℤ) (u v : L
   split_ifs <;> rfl
 
 /-- Replacing a framed word by an equal-width word keeps both blank delimiters. -/
-private lemma counter_patch_frame (w v : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
+private lemma counter_patch_frame {Γ : Type} (w v : List Γ) (ct : ℤ → Option Γ) (cp : ℤ)
     (hv : v.length = w.length)
     (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
       ct (cp + p) = FinTM.bufferTape w p) :
@@ -749,39 +776,65 @@ private lemma counter_patch_frame (w v : List Bool) (ct : ℤ → Option Bool) (
     · simp [counterPatch, hv, hw w.length (by omega) le_rfl, FinTM.bufferTape_nat]
 
 /-- A decrement phase uses the proved framed contract and guarded state transport.
-**Proof sketch.** Select success or underflow from the word function. The
-host agrees with the decrement on every pre-verdict control, so the single
-injective transport carries its endpoint, first-verdict cut, and head bounds. -/
-private lemma counter_debit {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
-    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
-    (c : Cfg k Bool S x) (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
+**Proof sketch.** Decode the rich one-tape start, apply the landed success or
+underflow contract, and read back through the public symbol overlay. Its input
+obliviousness and absence of blank writes preserve arbitrary rich frame cells.
+R1 puts this run on the last tape; injective guarded state transport supplies
+the host's verdict cut and the two head trajectories. -/
+private lemma counter_debit {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
+    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
+    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
     (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
-      ct (cp + p) = FinTM.bufferTape w p) :
+      ct (cp + p) = FinTM.bufferTape (w.map e) p) :
     let cost := 2 * (w.takeWhile not).length + 2
     let v := (decFixed w).getD (List.replicate w.length true)
     let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
-    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
-      counterLoopCfg (some q) c (counterPatch ct cp v) cp ∧
-    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
+    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
+      counterLoopCfg (some q) c (counterPatch ct cp (v.map e)) cp ∧
+    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
       cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
-  let z : Cfg (k + 1) Bool FlagPhase x :=
-    (counterLoopCfg (some (.dec .run)) c ct cp).mapState (fun _ => FlagPhase.run)
+  let D : Cfg 1 Γ FlagPhase x :=
+    ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩
+  let z := Cfg.decodeSymbols e D
   let v := (decFixed w).getD (List.replicate w.length true)
   let cost := 2 * (w.takeWhile not).length + 2
+  let N := (decrementTM 1 0).liftSymbols e
+  let E := embedEmitTM (lastEmb k) N
+  let bank (d : Cfg 1 Γ FlagPhase x) := embedEmitCfg (lastEmb k)
+    (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d
+  have layout (d : Cfg 1 Γ FlagPhase x) : bank d =
+      ⟨d.state, d.inputPos, Fin.lastCases (d.workTapes 0) c.workTapes,
+        Fin.lastCases (d.workTapePos 0) c.workTapePos, d.output⟩ := by
+    have frame (i : Fin k) := (embedEmitTM_frame (lastEmb k) N
+      (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d 0).1
+      i.castSucc (by rintro ⟨j, hj⟩; exact Fin.castSucc_ne_last i hj.symm)
+    apply Cfg.ext <;> try rfl
+    · funext j
+      refine Fin.lastCases ?_ (fun i => ?_) j
+      · simpa only [bank, Fin.lastCases_last] using
+          embedEmitCfg_selected_tape (lastEmb k) (Fin.lastCases ct c.workTapes)
+            (Fin.lastCases cp c.workTapePos) [] d 0
+      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).1
+    · funext j
+      refine Fin.lastCases ?_ (fun i => ?_) j
+      · simpa only [bank, Fin.lastCases_last] using
+          embedEmitCfg_selected_pos (lastEmb k) (Fin.lastCases ct c.workTapes)
+            (Fin.lastCases cp c.workTapePos) [] d 0
+      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).2
   have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
-      z.workTapes (Fin.last k) (z.workTapePos (Fin.last k) + p) = FinTM.bufferTape w p := by
-    simpa [z, Cfg.mapState, counter_cfg_eq] using hw
+      z.workTapes 0 (z.workTapePos 0 + p) = FinTM.bufferTape w p := by
+    intro p hl hr
+    change (ct (cp + p)).bind (decodeBool e) = _
+    rw [hw p hl hr, FinTM.bufferTape_map_decode]
+  -- The only decrement facts are the landed framed contracts, on the decoded shadow.
   have spec :
-      (decrementTM (k + 1) (Fin.last k)).runFrom z cost =
+      (decrementTM 1 0).runFrom z cost =
         {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
-          if j = Fin.last k ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
+          if j = 0 ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
           then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
-      (∀ t < cost, ∀ b, ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state ≠
-        some (.done b)) ∧
-      (∀ j t, t ≤ cost → if j = Fin.last k then
-        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j ∈
-          Finset.Icc (z.workTapePos j - 1) (z.workTapePos j + (w.length : ℤ))
-        else ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j = z.workTapePos j) := by
+      (∀ t < cost, ∀ b, ((decrementTM 1 0).runFrom z t).state ≠ some (.done b)) ∧
+      (∀ t ≤ cost, ((decrementTM 1 0).runFrom z t).workTapePos 0 ∈
+        Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
     cases hd : decFixed w with
     | none =>
       have hs := counter_dec_spec w
@@ -789,100 +842,144 @@ private lemma counter_debit {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
       have hp : (w.takeWhile not).length = w.length := by
         conv_lhs => rw [hs]
         simp
-      simpa [cost, v, hd, hp] using decrementTM_run_underflow_ofCfg (Fin.last k) w hd z rfl hz
+      obtain ⟨he, hc, hh⟩ := decrementTM_run_underflow_ofCfg 0 w hd z rfl hz
+      refine ⟨by simpa [cost, v, hd, hp] using he,
+        by simpa [cost, hp] using hc, ?_⟩
+      intro t ht
+      simpa [z, D, Cfg.decodeSymbols] using hh 0 t (by simpa [cost, hp] using ht)
     | some u =>
-      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg (Fin.last k) w u hd z rfl hz
+      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg 0 w u hd z rfl hz
       refine ⟨by simpa [v, hd] using he, hc, ?_⟩
-      intro j t ht
-      have h := hh j t ht
-      split_ifs at h ⊢ with hj
-      · simp only [Finset.mem_Icc] at h ⊢
-        have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
-        exact ⟨h.1, by omega⟩
-      · exact h
+      intro t ht
+      have h := hh 0 t ht
+      simp only [ite_true, Finset.mem_Icc] at h ⊢
+      have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
+      exact ⟨h.1, by
+        have upper : ((decrementTM 1 0).runFrom z t).workTapePos 0 ≤
+            cp + ((w.takeWhile not).length : ℤ) := h.2
+        omega⟩
+  have rich (t : ℕ) : N.runFrom D t =
+      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t) := by
+    conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
+    apply MultiTapeTM.liftSymbols_runFrom_over e _ (fun _ _ _ _ => rfl)
+    intro f inp work j
+    rcases f with _ | b | b <;>
+    rcases h : work 0 with _ | b' <;> (try cases b') <;>
+    simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
+    split_ifs <;> simp
   let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
+  have start : (bank D).mapState emb = counterLoopCfg (some (.dec .run)) c ct cp := by
+    rw [layout, counter_layout]
+    rfl
   have run (t : ℕ) (ht : t ≤ cost) :
-      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
-        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).mapState emb := by
-    refine MultiTapeTM.runFrom_mapState_of_agreeOn
-      (decrementTM (k + 1) (Fin.last k)) (counterLoopTM M a exit) emb
-      (fun f => ∀ b, f ≠ .done b) ?_ z t ?_
-    · intro f hf inp work
-      cases f with
-      | run => rfl
-      | rewind b => rfl
-      | done b => exact False.elim (hf b rfl)
-    · intro u hu f hf b he
-      exact spec.2.1 u (by omega) b (hf.trans (congrArg some he))
+      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
+        (bank (Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t))).mapState emb := by
+    rw [← start]
+    have h := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
+      (fun f => ∀ b, f ≠ .done b) (by
+        intro f hf inp work
+        cases f with
+        | run => rfl
+        | rewind b => rfl
+        | done b => exact False.elim (hf b rfl)) (bank D) t (by
+          intro u hu f hf b he
+          rw [show E.runFrom (bank D) u = bank (N.runFrom D u) from
+            embedEmitTM_runFrom (lastEmb k) N _ _ [] D u, rich] at hf
+          exact spec.2.1 u (by omega) b (hf.trans (congrArg some he)))
+    rw [h, show E.runFrom (bank D) t = bank (N.runFrom D t) from
+      embedEmitTM_runFrom (lastEmb k) N _ _ [] D t, rich]
   have vl : v.length = w.length := by
     have hs := counter_dec_spec w
     cases hd : decFixed w <;> simp [v, hd] at *
     exact hs.1
   refine ⟨?_, ?_, ?_, ?_⟩
-  · rw [run cost le_rfl, spec.1]
-    apply Cfg.ext <;> try rfl
-    · cases hd : decFixed w <;> simp [Cfg.mapState, emb, counterLoopDecExit, counterLoopCfg]
+  · rw [run cost le_rfl, spec.1, layout, counter_layout]
+    apply Cfg.ext
+    · cases hd : decFixed w <;> simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols,
+        emb, counterLoopDecExit]
+    · apply Fin.ext; rfl
     · funext j p
       refine Fin.lastCases ?_ (fun i => ?_) j
-      · simp only [z, Cfg.mapState, counter_cfg_eq, Fin.lastCases_last,
-          true_and, counterPatch]
-        change _ = if cp ≤ p ∧ p < cp + (v.length : ℤ) then FinTM.bufferTape v (p - cp) else ct p
-        rw [vl]
-      · simp [z, Cfg.mapState, counter_cfg_eq, Fin.castSucc_ne_last]
+      · simp only [Cfg.mapState, Fin.lastCases_last]
+        change (if (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
+            then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)) =
+              (ct p).bind (decodeBool e) then ct p
+            else (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
+              then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)).map e) =
+          counterPatch ct cp (v.map e) p
+        simp only [true_and, counterPatch, List.length_map, vl, FinTM.bufferTape_map]
+        by_cases hp : cp ≤ p ∧ p < cp + (w.length : ℤ)
+        · simp only [if_pos hp]
+          split_ifs with he
+          · have hn : (p - cp).toNat < v.length := by omega
+            have hb : FinTM.bufferTape v (p - cp) = some v[(p - cp).toNat] := by
+              simp [FinTM.bufferTape, hp.1, hn]
+            cases hct : ct p with
+            | none => simp [hct, hb] at he
+            | some γ =>
+              have decoded : decodeBool e γ = some v[(p - cp).toNat] := by
+                simpa only [hct, hb, Option.bind_some] using he.symm
+              simp only [hb, Option.map_some, decodeBool_eq_some e γ _ decoded]
+          · rfl
+        · simp only [if_neg hp, if_true]
+      · simp only [Cfg.mapState, Fin.lastCases_castSucc]
+    · rfl
+    · simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, z, Cfg.decodeSymbols, D]
   · intro t ht
-    rw [run t (by omega)]
+    rw [run t (by omega), layout]
     have hc := spec.2.1 t ht
-    cases hs : ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state with
-    | none => simp [Cfg.mapState, hs]
+    cases hs : ((decrementTM 1 0).runFrom z t).state with
+    | none => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs]
     | some f =>
       cases f with
-      | run => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
-      | rewind b => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
+      | run => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
+      | rewind b =>
+        simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
       | done b => exact False.elim (hc b hs)
   · intro t ht
-    rw [run t ht]
-    simpa [Cfg.mapState, z, counter_cfg_eq] using spec.2.2 (Fin.last k) t ht
+    rw [run t ht, layout]
+    simpa only [Cfg.mapState, Fin.lastCases_last, Cfg.liftOver, Cfg.liftSymbols] using
+      spec.2.2 t ht
   · intro t ht j
-    rw [run t ht]
-    simpa [Cfg.mapState, z, counter_cfg_eq, Fin.castSucc_ne_last] using
-      spec.2.2 j.castSucc t ht
+    rw [run t ht, layout]
+    simp only [Cfg.mapState, Fin.lastCases_castSucc]
 
 /-- The body phase executes its entry action once, then uses guarded transport.
 **Proof sketch.** The entry action reads the forwarding embedding. After that
 step, all strict intermediate states avoid both redirections, and the RB5
 transport lemma applies. R1 identifies every transported configuration and
 therefore preserves the counter frame and all body-head trajectories. -/
-private lemma counter_body {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
-    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
-    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) (width t : ℕ)
+private lemma counter_body {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
+    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
+    (c : Cfg k Γ S x) (ct : ℤ → Option Γ) (cp : ℤ) (width t : ℕ)
     (hc : c.state = some a) (ht : 0 < t)
     (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
       s ≠ a ∧ exit ≠ some s) :
-    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
+    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
       counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
         (M.runFrom c t) ct cp ∧
-    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.body a)) c ct cp)
+    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.body a)) c ct cp)
       t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
   let E := embedEmitTM Fin.castSuccEmb M
   let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
   let emb : S ↪ CounterLoopState S :=
     ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
-  have first : (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
+  have first : (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
       (E.runFrom ec 1).mapState emb := by
-    change (counterLoopTM M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
+    change (counterLoopTMVia e M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
       (E.step ec).mapState emb
     have hec : ec.state = some a := hc
     simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
     rfl
   have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
-      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
+      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
         counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
           (M.runFrom c u) ct cp := by
     obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
     rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
-    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTM M a exit) emb
+    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
       (fun s => s ≠ a ∧ exit ≠ some s)
-      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTM, E])
+      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTMVia, E])
       (E.runFrom ec 1) n (by
         intro v hv s hs
         have he := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c (1 + v)
@@ -908,22 +1005,105 @@ private lemma counter_body {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
       simp [counterLoopCfg, hs, counterLoopRedirect, ha, hx]
   · intro u hu
     by_cases hz : u = 0
-    · subst u; simp [counter_cfg_eq, Finset.mem_Icc]
+    · subst u; simp [counter_layout, Finset.mem_Icc]
     · rw [run u (by omega) hu]
-      simp [counter_cfg_eq, Finset.mem_Icc]
+      simp [counter_layout, Finset.mem_Icc]
   · intro u hu
     refine ⟨u, hu, ?_⟩
     by_cases hz : u = 0
-    · subst u; simp [counter_cfg_eq]
+    · subst u; simp [counter_layout]
     · rw [run u (by omega) hu]
-      simp [counter_cfg_eq]
-
-/-- An orbit successor is the completed current body round. -/
-private lemma counter_orbit_succ {k : ℕ} {S : Type} {x : List Bool}
-    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) :
-    counterLoopOrbit M τ c (r + 1) =
-      M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) :=
-  Function.iterate_succ_apply' _ _ _
+      simp [counter_layout]
+
+/-- At the identity embedding the generic and Bool hosts have the same table.
+**Proof sketch.** Compute R1 on its public last-tape embedding, cancel the
+identity symbol lift, and compare the decrement tables field by field. -/
+private lemma counter_refl_agree {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
+    (a : S) (exit : Option S) :
+    (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn
+      (counterLoopTM M a exit) Set.univ := by
+  have action_eq {k : ℕ} {Sy Q : Type} {A B : Action k Sy Q}
+      (h1 : A.inputTape = B.inputTape) (h2 : A.workTapes = B.workTapes)
+      (h3 : A.output = B.output) (h4 : A.state = B.state) : A = B := by
+    cases A; cases B; simp_all
+  have lift_refl (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) :
+      ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool)).tr f inp work =
+        (decrementTM 1 0).tr f inp work := by
+    have hd : ∀ o : Option Bool, o.bind (decodeBool (Function.Embedding.refl Bool)) = o := by
+      intro o; cases o with
+      | none => rfl
+      | some b => cases b <;> rfl
+    simp only [MultiTapeTM.liftSymbols, hd]
+    cases ((decrementTM 1 0).tr f inp work) with
+    | mk i w o s =>
+      simp only [Action.liftSymbols]
+      congr 1
+      · funext j
+        cases w j with
+        | mk a m => cases a with
+          | none => rfl
+          | some b => cases b <;> rfl
+      · cases o <;> rfl
+  have embed_last {k : ℕ} {Sy Q : Type} (N : MultiTapeTM 1 Sy Q) (q : Q)
+      (inp : Option Sy) (work : Fin (k + 1) → Option Sy) :
+      (embedEmitTM (lastEmb k) N).tr q inp work =
+        ⟨(N.tr q inp fun _ => work (Fin.last k)).inputTape,
+          fun j => if j = Fin.last k then (N.tr q inp fun _ => work (Fin.last k)).workTapes 0
+            else (none, 0),
+          (N.tr q inp fun _ => work (Fin.last k)).output,
+          (N.tr q inp fun _ => work (Fin.last k)).state⟩ := by
+    apply action_eq
+    · rfl
+    · funext j
+      refine Fin.lastCases ?_ (fun i => ?_) j
+      · simp only [if_true]
+        conv_lhs => whnf
+        split
+        · rename_i i h
+          rw [Subsingleton.elim i 0]
+          rfl
+        · rename_i h
+          revert h
+          show ((List.finRange 1).find? fun i => decide ((lastEmb k) i = Fin.last k)) = none → _
+          simp [lastEmb]
+      · simp only [Fin.castSucc_ne_last, if_false]
+        conv_lhs => whnf
+        split
+        · rename_i i' h
+          revert h
+          show ((List.finRange 1).find? fun i' => decide ((lastEmb k) i' = Fin.castSucc i)) =
+            some i' → _
+          simp only [lastEmb, Function.Embedding.coeFn_mk, (Fin.castSucc_ne_last i).symm,
+            decide_false]
+          intro h
+          rw [List.find?_eq_none.mpr (fun _ _ => by simp)] at h
+          cases h
+        · rfl
+    · rfl
+    · rfl
+  have dec_refl (k : ℕ) (f : FlagPhase) (inp : Option Bool)
+      (work : Fin (k + 1) → Option Bool) :
+      (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool))).tr
+          f inp work =
+        (decrementTM (k + 1) (Fin.last k)).tr f inp work := by
+    rw [embed_last, lift_refl]
+    apply action_eq
+    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
+        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
+    · funext j
+      rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
+        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
+        split_ifs <;> simp_all
+    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
+        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
+    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
+        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
+  intro q _ inp work
+  cases q with
+  | body s => rfl
+  | dec f => exact congrArg (Action.mapState (counterLoopDecExit a)) (dec_refl k f inp work)
+  | done => rfl
+  | escape => rfl
 
 /-- The shared round invariant, with the final body state left unrestricted.
 Returning prefixes are exactly the configurations before the next decrement.
@@ -932,11 +1112,11 @@ positive value, so the framed decrement succeeds. Append its transported
 segment and the forwarding body segment. Equal-width overwrites keep the
 original counter frame, and the two cost recurrences give the exact elapsed
 time. Earlier starts at the anchor supply all returns needed by the induction. -/
-private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
-    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
-    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
-    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
-    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
+private lemma counter_rounds {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
+    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
+    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
+    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
+    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
     (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
     (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
       0 < τ (counterLoopOrbit M τ c r) ∧
@@ -944,11 +1124,11 @@ private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool
         ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
           s ≠ a ∧ exit ≠ some s)) :
     let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
-    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
+    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
       counterLoopCfg (if n = 0 then some (.dec .run) else
         (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
-        (counterLoopOrbit M τ c n) (counterPatch ct cp (counterWord w n)) cp ∧
-    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
+        (counterLoopOrbit M τ c n) (counterPatch ct cp ((counterWord w n).map e)) cp ∧
+    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
       elapsed cp w.length (fun p => ∃ r u,
         ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
         ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
@@ -956,15 +1136,22 @@ private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool
   | zero =>
     simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
       Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
-    have hpatch : counterPatch ct cp (counterWord w 0) = ct := counter_patch_initial w ct cp hw
+    have hpatch : counterPatch ct cp ((counterWord w 0).map e) = ct := by
+      change counterPatch ct cp (w.map e) = ct
+      funext q
+      apply ite_eq_right_iff.mpr
+      intro h
+      simp only [List.length_map] at h
+      have hf := hw (q - cp) (by omega) (by omega)
+      simpa using hf.symm
     rw [hpatch]
     refine ⟨rfl, ?_, ?_, ?_⟩
     · intro u hu; omega
     · intro u hu; have hz : u = 0 := by omega
-      subst u; simp [counter_cfg_eq, Finset.mem_Icc]
+      subst u; simp [counter_layout, Finset.mem_Icc]
     · intro u hu; have hz : u = 0 := by omega
       subst u
-      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_cfg_eq, counterLoopOrbit]⟩
+      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_layout, counterLoopOrbit]⟩
   | succ n ih =>
     obtain ⟨before, span⟩ := ih (by omega) (fun r hr => hround r (by omega))
     obtain ⟨ha, ht, hg⟩ := hround n (by omega)
@@ -975,27 +1162,30 @@ private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool
     rw [control] at before
     let cn := counterLoopOrbit M τ c n
     let wn := counterWord w n
-    let pn := counterPatch ct cp wn
-    let nextTape := counterPatch ct cp (counterWord w (n + 1))
+    let pn := counterPatch ct cp (wn.map e)
+    let nextTape := counterPatch ct cp ((counterWord w (n + 1)).map e)
     let cost := 2 * (wn.takeWhile not).length + 2
     have hd := counter_word_decrement w n (by omega)
-    have hf := counter_patch_frame w wn ct cp (counterWord_length w n) hw
-    obtain ⟨debit, ds⟩ := counter_debit M a exit cn wn pn cp hf
+    have hf := counter_patch_frame (w.map e) (wn.map e) ct cp
+      (by simp [List.length_map, wn, counterWord_length]) (by simpa using hw)
+    obtain ⟨debit, ds⟩ := counter_debit e M a exit cn wn pn cp (by simpa using hf)
     change decFixed wn = some (counterWord w (n + 1)) at hd
     simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
-    rw [counter_patch_twice ct cp wn (counterWord w (n + 1))
-      (by simp only [wn, counterWord_length])] at debit
-    obtain ⟨body, bs⟩ := counter_body M a exit cn nextTape cp w.length (τ cn) ha ht hg
-    have round : (counterLoopTM M a exit).runFrom
+    rw [counter_patch_twice ct cp (wn.map e) ((counterWord w (n + 1)).map e)
+      (by simp only [List.length_map, wn, counterWord_length])] at debit
+    obtain ⟨body, bs⟩ := counter_body e M a exit cn nextTape cp w.length (τ cn) ha ht hg
+    have round : (counterLoopTMVia e M a exit).runFrom
         (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
         counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
           (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
-      rw [MultiTapeTM.runFrom_add, debit, body, counter_orbit_succ]
-    have rs : counterSpan (counterLoopTM M a exit)
+      rw [MultiTapeTM.runFrom_add, debit, body]
+      rw [show counterLoopOrbit M τ c (n + 1) = M.runFrom cn (τ cn) from
+        Function.iterate_succ_apply' _ _ _]
+    have rs : counterSpan (counterLoopTMVia e M a exit)
         (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
         (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
       apply counter_span_append _ _ cost (τ cn) cp w.length _ _ _
-        (by simpa only [wn, counterWord_length] using ds) (by rw [debit]; exact bs)
+        (by simpa only [List.length_map, wn, counterWord_length] using ds) (by rw [debit]; exact bs)
       · intro p hp; exact ⟨0, Nat.zero_le _, by simpa using hp⟩
       · exact fun _ h => h
     have time : (∑ r ∈ Finset.range (n + 1), τ (counterLoopOrbit M τ c r)) +
@@ -1021,35 +1211,16 @@ private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool
         obtain ⟨u, hu, heads⟩ := hp
         exact ⟨n, u, Or.inl ⟨by omega, hu⟩, heads⟩
 
-/-- **The counter-driven loop, every round returns** (design §12.7, C2).
-Start the host at its decrement phase, with body configuration `c` and the
-delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
-rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
-anchor, the exit and halting in between, and returns to `a`. Then the host
-reaches `done` at exactly `T`: the `d` round times plus the exact decrement
-overhead, including the final underflow sweep. Its body part is the orbit
-after `d` rounds, its counter is all `true`, and its counter head is back at
-`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
-within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
-some point of some round. With `exit = none`, the hypotheses do not mention an
-exit at all.
-
-**Proof sketch.** Induct on the round. Each decrement is
-`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
-idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
-redirection is applied at the exit step. Each round is the R1 run
-`Turing.embedEmitTM_runFrom` with its states renamed by
-`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
-step while the body's next state is neither the anchor nor the exit, which
-the round hypothesis guarantees before the final step; the final step is the
-redirection. The counter word before round
-`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
-costs add to `Turing.counterOverhead w (d + 1)`. -/
-theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
-    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
-    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
-    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
-    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
+/-- The rich-alphabet counter host returns after all rounds
+(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
+**Proof sketch.** Instantiate the single generic round induction and append the
+transported final underflow sweep. -/
+theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
+    {x : List Γ} (e : Bool ↪ Γ)
+    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
+    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
+    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
+    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
     (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
     (hround : ∀ r < d,
       (counterLoopOrbit M τ c r).state = some a ∧
@@ -1061,26 +1232,26 @@ theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bo
     (T : ℕ)
     (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
       counterOverhead w (d + 1)) :
-    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
+    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
         counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
-          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
+          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
       (∀ t < T,
-        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
-          some .done ∧
-        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
-          some .escape) ∧
+        ((counterLoopTMVia e M a exit).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
+        ((counterLoopTMVia e M a exit).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
       (∀ t ≤ T,
-        ((counterLoopTM M a exit).runFrom
+        ((counterLoopTMVia e M a exit).runFrom
             (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
           Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
       (∀ t ≤ T, ∃ r u,
         ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
         ∀ j : Fin k,
-          ((counterLoopTM M a exit).runFrom
+          ((counterLoopTMVia e M a exit).runFrom
               (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
             (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
   subst T
-  obtain ⟨before, span⟩ := counter_rounds M a exit τ c w ct cp hw d (by omega)
+  obtain ⟨before, span⟩ := counter_rounds e M a exit τ c w ct cp hw d (by omega)
     (fun r hr => ⟨(hround r hr).1, (hround r hr).2.1, (hround r hr).2.2.1⟩)
   have control : (if d = 0 then some (.dec .run) else
       (counterLoopOrbit M τ c d).state.map (counterLoopRedirect a exit)) =
@@ -1096,17 +1267,18 @@ theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bo
   have empty : wd = List.replicate w.length false := by
     simpa only [hd] using counter_word_exhausted w
   have under : decFixed wd = none := (counter_dec_zero wd).mpr (by simp [empty])
-  have framed := counter_patch_frame w wd ct cp width hw
-  obtain ⟨debit, ds⟩ := counter_debit M a exit (counterLoopOrbit M τ c d) wd
-    (counterPatch ct cp wd) cp framed
+  have framed := counter_patch_frame (w.map e) (wd.map e) ct cp
+    (by simpa using width) (by simpa using hw)
+  obtain ⟨debit, ds⟩ := counter_debit e M a exit (counterLoopOrbit M τ c d) wd
+    (counterPatch ct cp (wd.map e)) cp (by simpa using framed)
   simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
     width] at debit
-  rw [counter_patch_twice ct cp wd (List.replicate w.length true)
+  rw [counter_patch_twice ct cp (wd.map e) ((List.replicate w.length true).map e)
     (by simp [width])] at debit
-  have fill : counterPatch ct cp (List.replicate w.length true) =
-      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) := by
+  have fill : counterPatch ct cp ((List.replicate w.length true).map e) =
+      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) := by
     funext q
-    simp only [counterPatch, List.length_replicate]
+    simp only [counterPatch, List.length_replicate, List.map_replicate]
     split_ifs with h
     · have hp : 0 ≤ q - cp := by omega
       have hn : (q - cp).toNat < w.length := by omega
@@ -1125,6 +1297,133 @@ theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bo
       (by rw [before]; simpa only [width] using ds) (fun _ h => h)
       (fun p hp => ⟨d, 0, Or.inr ⟨rfl, rfl⟩, by simpa using hp⟩)
 
+/-- The rich-alphabet counter host takes an early body exit
+(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
+**Proof sketch.** Instantiate the single generic round induction; its unrestricted
+last body state redirects to the designated escape. -/
+theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
+    {x : List Γ} (e : Bool ↪ Γ)
+    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
+    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
+    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
+    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
+    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
+    (hround : ∀ r ≤ r₀,
+      (counterLoopOrbit M τ c r).state = some a ∧
+      0 < τ (counterLoopOrbit M τ c r) ∧
+      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
+        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
+    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
+    (T : ℕ)
+    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
+      counterOverhead w (r₀ + 1)) :
+    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
+        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
+          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
+            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
+      (∀ t < T,
+        ((counterLoopTMVia e M a (some ex)).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
+        ((counterLoopTMVia e M a (some ex)).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
+      (∀ t ≤ T,
+        ((counterLoopTMVia e M a (some ex)).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
+          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
+      (∀ t ≤ T, ∃ r u,
+        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
+        ∀ j : Fin k,
+          ((counterLoopTMVia e M a (some ex)).runFrom
+              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
+            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
+  subst T
+  obtain ⟨he, hs⟩ := counter_rounds e M a (some ex) τ c w ct cp hw (r₀ + 1)
+    (by omega) (by
+      intro r hr
+      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
+      refine ⟨ha, ht, ?_⟩
+      intro u hu hut
+      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
+      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
+  refine ⟨?_, hs.1, hs.2.1, ?_⟩
+  · unfold counterPatch at he
+    simp only [List.length_map, counterWord_length] at he
+    simpa [hexit, hea, counterLoopRedirect] using he
+  · simpa only [Nat.lt_succ_iff] using hs.2.2
+
+/-- **The counter-driven loop, every round returns** (design §12.7, C2).
+Start the host at its decrement phase, with body configuration `c` and the
+delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
+rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
+anchor, the exit and halting in between, and returns to `a`. Then the host
+reaches `done` at exactly `T`: the `d` round times plus the exact decrement
+overhead, including the final underflow sweep. Its body part is the orbit
+after `d` rounds, its counter is all `true`, and its counter head is back at
+`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
+within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
+some point of some round. With `exit = none`, the hypotheses do not mention an
+exit at all.
+
+**Proof sketch.** Induct on the round. Each decrement is
+`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
+idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
+redirection is applied at the exit step. Each round is the R1 run
+`Turing.embedEmitTM_runFrom` with its states renamed by
+`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
+step while the body's next state is neither the anchor nor the exit, which
+the round hypothesis guarantees before the final step; the final step is the
+redirection. The counter word before round
+`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
+costs add to `Turing.counterOverhead w (d + 1)`.
+
+**Re-derivation appendix (R8.0b).** Apply the generic returning contract at the identity embedding and transport
+its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
+theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
+    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
+    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
+    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
+    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
+    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
+    (hround : ∀ r < d,
+      (counterLoopOrbit M τ c r).state = some a ∧
+      0 < τ (counterLoopOrbit M τ c r) ∧
+      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
+        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
+          s ≠ a ∧ exit ≠ some s) ∧
+      (counterLoopOrbit M τ c (r + 1)).state = some a)
+    (T : ℕ)
+    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
+      counterOverhead w (d + 1)) :
+    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
+        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
+          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
+      (∀ t < T,
+        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
+          some .done ∧
+        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
+          some .escape) ∧
+      (∀ t ≤ T,
+        ((counterLoopTM M a exit).runFrom
+            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
+          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
+      (∀ t ≤ T, ∃ r u,
+        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
+        ∀ j : Fin k,
+          ((counterLoopTM M a exit).runFrom
+              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
+            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
+  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
+      (counterLoopTM M a exit).runFrom z t =
+        (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).runFrom z t :=
+    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a exit) z t
+      (fun _ _ _ _ => Set.mem_univ _)
+  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
+      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
+    simpa [Function.Embedding.coe_refl] using hw
+  simp only [z5]
+  exact counterLoopTMVia_run_done (Function.Embedding.refl Bool) M a exit τ c w ct cp hw'
+    d hd hround T hT
+
 /-- **The counter-driven loop, early exit** (design §12.7, C2). As
 `Turing.counterLoopTM_run_done`, except that round `r₀`, below the counter's
 value, ends at the designated exit `e ≠ a` while every earlier round returns
@@ -1137,7 +1436,10 @@ the returning case.
 **Proof sketch.** The induction of `Turing.counterLoopTM_run_done`, stopped at
 round `r₀`: every decrement before it succeeds, since `r₀` is below the value
 (`Turing.counterWord_value`), and the redirection sends round `r₀`'s final
-step to `escape`. -/
+step to `escape`.
+
+**Re-derivation appendix (R8.0b).** Apply the generic escape contract at the identity embedding and transport
+its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
 theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
     (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
     (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
@@ -1172,20 +1474,19 @@ theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List
           ((counterLoopTM M a (some e)).runFrom
               (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
             (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
-  subst T
-  obtain ⟨he, hs⟩ := counter_rounds M a (some e) τ c w ct cp hw (r₀ + 1)
-    (by omega) (by
-      intro r hr
-      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
-      refine ⟨ha, ht, ?_⟩
-      intro u hu hut
-      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
-      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
-  refine ⟨?_, hs.1, hs.2.1, ?_⟩
-  · unfold counterPatch at he
-    simp only [counterWord_length] at he
-    simpa [hexit, hea, counterLoopRedirect] using he
-  · simpa only [Nat.lt_succ_iff] using hs.2.2
+  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
+      (counterLoopTM M a (some e)).runFrom z t =
+        (counterLoopTMVia (Function.Embedding.refl Bool) M a (some e)).runFrom z t :=
+    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a (some e)) z t
+      (fun _ _ _ _ => Set.mem_univ _)
+  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
+      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
+    simpa [Function.Embedding.coe_refl] using hw
+  have h := counterLoopTMVia_run_escape (Function.Embedding.refl Bool) M a e hea τ c w ct cp
+    hw' r₀ hr₀ hround hexit T hT
+  simp only [Function.Embedding.coe_refl, List.map_id] at h
+  simp only [z5]
+  exact h
 
 /-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
 the `d` rounds costs at most `B`, the returning run's exact time is at most
@@ -1194,8 +1495,8 @@ the `d` rounds costs at most `B`, the returning run's exact time is at most
 **Proof sketch.** Bound the round sum termwise by `B`
 (`Finset.sum_le_card_nsmul`) and the decrement share by
 `Turing.counterOverhead_le`. -/
-theorem counterLoop_time_le {k : ℕ} {S : Type} {x : List Bool}
-    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
+theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
     (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
     (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
     ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
@@ -1274,6 +1575,123 @@ theorem expandTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Boo
           ((expandTM k i pat).runFrom
               (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
             c.workTapePos j) := by
-  sorry
+  let M := writeAdvTM k i pat
+  let τ : Cfg k Bool (Fin (pat.length + 1)) x → ℕ := fun _ => pat.length + 1
+  let finish (r : ℕ) : Cfg k Bool (Fin (pat.length + 1)) x :=
+    { c with
+      workTapes := fun j q =>
+        if j = i ∧ c.workTapePos j ≤ q ∧
+            q < c.workTapePos j + ((r * pat.length : ℕ) : ℤ)
+          then FinTM.bufferTape (List.replicate r pat).flatten (q - c.workTapePos j)
+        else c.workTapes j q
+      workTapePos := Function.update c.workTapePos i
+        (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) }
+  -- This induction concerns only the advancing writer's orbit, not the loop host.
+  have orbit (r : ℕ) : counterLoopOrbit M τ c r = finish r := by
+    induction r with
+    | zero =>
+      change c = finish 0
+      apply Cfg.ext <;> try rfl
+      · funext j q
+        simp [finish]
+      · funext j
+        by_cases hj : j = i <;> simp [finish, hj]
+    | succ r ih =>
+      have step := (writeAdvTM_run_ofCfg i pat (finish r) hc).1
+      rw [show counterLoopOrbit M τ c (r + 1) =
+        M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) from
+        Function.iterate_succ_apply' _ _ _, ih]
+      change (writeAdvTM k i pat).runFrom (finish r) (pat.length + 1) = finish (r + 1)
+      rw [step]
+      have length : (List.replicate r pat).flatten.length = r * pat.length := by simp
+      have append : (List.replicate (r + 1) pat).flatten =
+          (List.replicate r pat).flatten ++ pat := by
+        rw [List.replicate_succ', List.flatten_append]
+        simp
+      apply Cfg.ext
+      · exact hc.symm
+      · rfl
+      · funext j q
+        by_cases hj : j = i
+        · subst j
+          simp only [finish, Function.update_self, true_and, Nat.add_mul, Nat.one_mul,
+            Nat.cast_add, append]
+          by_cases hnew : c.workTapePos i + ((r * pat.length : ℕ) : ℤ) ≤ q ∧
+              q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)
+          · have hwhole : c.workTapePos i ≤ q ∧
+                q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
+            simp only [hnew, hwhole]
+            have h0 : 0 ≤ q - c.workTapePos i := by omega
+            have h1 : 0 ≤ q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) := by omega
+            have hn : ¬ (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
+              rw [length]; omega
+            simp only [FinTM.bufferTape, h0, h1, if_true, List.getElem?_append, hn, if_false]
+            rw [show (q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ))).toNat =
+              (q - c.workTapePos i).toNat - (List.replicate r pat).flatten.length by
+                rw [length]; omega]
+            simp only [and_self, if_true]
+          · simp only [hnew, if_false]
+            by_cases hold : c.workTapePos i ≤ q ∧
+                q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ)
+            · have hwhole : c.workTapePos i ≤ q ∧
+                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
+              have h0 : 0 ≤ q - c.workTapePos i := by omega
+              have hn : (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
+                rw [length]; omega
+              simp only [hold, hwhole, FinTM.bufferTape, h0, List.getElem?_append, hn, if_true]
+            · have hwhole : ¬ (c.workTapePos i ≤ q ∧
+                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ))) := by omega
+              simp only [hold, hwhole, if_false]
+        · simp [finish, hj]
+      · funext j
+        by_cases hj : j = i
+        · subst j
+          simp [finish, Nat.add_mul, Nat.cast_add, add_assoc]
+        · simp [finish, hj]
+      · rfl
+  have state (r : ℕ) : (counterLoopOrbit M τ c r).state = some 0 := by
+    rw [orbit]; exact hc
+  have rounds : ∀ r < d,
+      (counterLoopOrbit M τ c r).state = some 0 ∧
+      0 < τ (counterLoopOrbit M τ c r) ∧
+      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
+        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
+          s ≠ 0 ∧ (none : Option (Fin (pat.length + 1))) ≠ some s) ∧
+      (counterLoopOrbit M τ c (r + 1)).state = some 0 := by
+    intro r hr
+    have spec := writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)
+    refine ⟨state r, Nat.succ_pos _, ?_, state (r + 1)⟩
+    intro u hu hut
+    change u < pat.length + 1 at hut
+    have live := MultiTapeTM.runFrom_state_ne_none_of_le M (counterLoopOrbit M τ c r)
+      (pat.length + 1) (by rw [spec.1]; simp) u (by omega)
+    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp live
+    refine ⟨s, hs, ?_, Option.noConfusion⟩
+    intro he
+    exact spec.2.1 u hu hut (hs.trans (congrArg some he))
+  obtain ⟨he, hcut, hcounter, hbody⟩ := counterLoopTM_run_done M 0 none τ c w ct cp hw d hd
+    rounds (d * (pat.length + 1) + counterOverhead w (d + 1)) (by simp [τ])
+  refine ⟨?_, hcut, hcounter, ?_⟩
+  · rw [orbit] at he
+    exact he
+  · intro t ht j
+    obtain ⟨r, u, hr, heads⟩ := hbody t ht
+    have spec := (writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)).2.2
+    have hu : u ≤ pat.length + 1 := by
+      rcases hr with h | ⟨rfl, rfl⟩
+      · exact h.2
+      · omega
+    have hh := spec j u hu
+    rw [heads j]
+    by_cases hj : j = i
+    · subst j
+      simp only [ite_true, orbit, finish, Function.update_self, Finset.mem_Icc] at hh ⊢
+      rcases hr with ⟨hr, _⟩ | ⟨rfl, rfl⟩
+      · have hrd : (r + 1) * pat.length ≤ d * pat.length := Nat.mul_le_mul_right _ hr
+        rw [Nat.add_mul, Nat.one_mul] at hrd
+        exact ⟨by omega, by omega⟩
+      · simpa only [MultiTapeTM.runFrom_zero, Function.update_self, le_refl, and_true,
+          le_add_iff_nonneg_right] using (Int.natCast_nonneg (r * pat.length))
+    · simpa [hj, orbit, finish] using hh
 
 end Turing
-- 
2.50.1 (Apple Git-155)


## ===== TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Bool
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: counter-driven loops (§12.7)

The §12.7 increment of the machine-construction library
(`machine-library-design.md` §12.7): a loop whose number of rounds is a
little-endian binary counter **read from a tape**, running a body whose
state lives on **persistent, arbitrarily positioned tapes**. Every public
loop host of `Build/Loop.lean` instead runs a number of rounds fixed by the
input length, between canonical `Turing.Cfg.ofWords` seams. The consumers
are the two-tape uniform machine-code scheme (`Codes2Tape`), the EXPCOM
simulation, the nondeterministic time hierarchy (a fused countdown at
linear overhead) and the space hierarchy's configuration-count clock.

**Status update (§12.8 fill, R8.0b/R8.6).** All contracts in this file are proved.
The expansion proof is modulo `Turing.writeAdvTM_run_ofCfg`, still sorried in `Build/Scan`.
**Alphabet update (R8.0b).** The shared loop machinery now admits any tape alphabet,
with binary digits embedded into its dedicated counter tape.

## Design (decisions 12.7.1–12.7.6, user 2026-10-10)

* **Symbol transport** (`Turing.MultiTapeTM.mapWorkSymbols`). A machine
  conjugated by a permutation of the work-tape alphabet runs as the
  original, cell for cell, from every configuration. This is the generic
  route of decision 12.7.4, so the decrement proof never copies the
  increment proof.
* **C1, decrement** (`Turing.decrementTM`). It is defined as
  `Turing.incrementTM` conjugated by bit complement, and its framed
  contracts are the §12.6 increment contracts transported.
* **C2, the counter-driven host** (`Turing.counterLoopTM`). The body's `k`
  tapes are embedded by R1 along `Fin.castSucc`, and the counter is the
  dedicated last tape (12.7.1). Arriving at the anchor starts a decrement,
  and success re-enters the body at the anchor, with no dispatch steps.
  Underflow leaves through the live anchor `done`; reaching the optional
  designated body exit leaves through the live anchor `escape` (12.7.2).
  A consumer branches on the two exits with `Turing.seamCompTM`; with no
  exit (`none`), `escape` is unreachable.
* **R8.0b, rich alphabets.** `Turing.counterLoopTMVia` transports the one-tape
  decrement through the symbol overlay and R1. Both generic contracts use the
  single round induction; the Bool contracts follow by identity-table agreement.
* **Round cost** (12.7.3). Each round from body configuration `c` lasts
  the **exact** time `τ c`. A round-indexed cost is the special case of
  `τ` along the orbit, and a uniform bound is the corollary
  `Turing.counterLoop_time_le`.
* **Amortized time** (12.7.6). The total is stated exactly over the whole
  run. The decrements' share, `Turing.counterOverhead`, is at most four
  steps per round plus one sweep of the counter.

## Main definitions

* `Turing.MultiTapeTM.mapWorkSymbols` — conjugation by a work-tape symbol
  permutation, with `Turing.Action.mapWorkSymbols` and
  `Turing.Cfg.mapWorkSymbols`.
* `Turing.decFixed`, `Turing.decrementTM` — fixed-width decrement, as a
  word function and as a machine.
* `Turing.counterWord`, `Turing.counterOverhead` — the counter after `r`
  decrements, and the exact cost of the first `r` decrements, valid as a
  physical cost for `r ≤ value + 1` (the counter word freezes at zero,
  while the machine wraps).
* `Turing.CounterLoopState`, `Turing.counterLoopTM`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
  configurations, and the body's round-start configurations.
* `Turing.lastEmb`, `Turing.counterLoopTMVia` — the last-tape embedding and
  the rich-alphabet counter host.
* `Turing.expandTM` — the expansion (§12.8, R8.6): the counter loop whose
  round is the advancing writer `Turing.writeAdvTM`.

## Main results


* `Turing.MultiTapeTM.mapWorkSymbols_runFrom` — symbol transport.
* `Turing.decrementTM_run_succ_ofCfg`, `Turing.decrementTM_run_underflow_ofCfg`
  — the framed decrement contracts, in the §12.6 shape.
* `Turing.counterWord_length`, `Turing.counterWord_value`,
  `Turing.counterOverhead_le_of_le`, `Turing.counterOverhead_le` — counter
  arithmetic, including the amortized bound.
* `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
  host's exact whole-run contracts, with no earlier exit, the counter
  head's range, and the body heads' trajectory.
* `Turing.counterLoopTMVia_run_done`, `Turing.counterLoopTMVia_run_escape` —
  the rich-alphabet whole-run contracts, preserving the arbitrary rich frame.
* `Turing.counterLoop_time_le` — the uniform per-round bound.
* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per
  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1–§3.2 and §4.1: the hierarchy
  arguments run a universal machine for a bounded number of steps under a
  step counter; this file is that counter as a reusable machine.)

**Fill appendix (§12.7).** All ten contracts are proved. Decrement is transported from increment once; `counter_rounds` is the single
round induction used by both host contracts. Its final state is unrestricted,
so it covers returning prefixes and the last escaping round with the same
trajectory invariant. The amortization proofs use the audit's bit-count
potential, as recorded in their fill appendices.
-/

namespace Turing

section SymbolTransport

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the symbols an action writes on its work tapes along an
equivalence. Input movement, output and successor state are unchanged. -/
def Action.mapWorkSymbols (e : Symbol ≃ Symbol) (a : Action k Symbol State) :
    Action k Symbol State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output
  state := a.state

/-- Rename every work-tape cell of a configuration along an equivalence;
blank cells stay blank. -/
def Cfg.mapWorkSymbols {input : List Symbol} (e : Symbol ≃ Symbol)
    (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  { c with workTapes := fun j p => (c.workTapes j p).map e }

/-- Conjugate a machine by a work-tape symbol permutation: read the work
tapes through `e.symm` and write through `e`. The input tape and the output
are not renamed. -/
def MultiTapeTM.mapWorkSymbols (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) : MultiTapeTM k Symbol State where
  q₀ := M.q₀
  tr := fun q inp work => (M.tr q inp fun j => (work j).map e.symm).mapWorkSymbols e

/-- One step commutes with work-symbol conjugation, including writes into the frame.
**Proof sketch.** Inverse decoding cancels the equivalence at each read.
On the written cell the renamed update stores the renamed symbol; off that
cell the original tape is retained. The remaining configuration fields agree. -/
private lemma counter_work_step (M : MultiTapeTM k Symbol State) (e : Symbol ≃ Symbol)
    {input : List Symbol} (d : Cfg k Symbol State input) :
    (M.mapWorkSymbols e).step (d.mapWorkSymbols e) = (M.step d).mapWorkSymbols e := by
  cases hs : d.state with
  | none => simp [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
  | some s =>
    have reads : (fun j => ((d.workTapeSymbols j).map e).map e.symm) =
        d.workTapeSymbols := by
      funext j
      cases d.workTapeSymbols j <;> simp
    simp only [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
    change ((M.tr s d.inputSymbol (fun j =>
        ((d.workTapeSymbols j).map e).map e.symm)).mapWorkSymbols e).apply
        (d.mapWorkSymbols e) = _
    rw [reads]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Action.apply, Action.mapWorkSymbols, Cfg.mapWorkSymbols]
    cases hw : (M.tr s d.inputSymbol d.workTapeSymbols).workTapes j |>.1 with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      by_cases hp : p = d.workTapePos j
      · subst p; simp
      · simp [Function.update_of_ne hp]

/-- **Symbol transport** (design §12.7, decision 12.7.4). From every
configuration and at every time, the conjugated machine runs as the original
with every work-tape cell renamed.

**Proof sketch.** One step: the conjugate reads `e.symm (e s) = s`, so it
chooses the original's action; writing renamed symbols commutes with
`Function.update`; heads, input position, output and state are copied. Then
`Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem MultiTapeTM.mapWorkSymbols_runFrom (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) :
    (M.mapWorkSymbols e).runFrom (c.mapWorkSymbols e) t =
      (M.runFrom c t).mapWorkSymbols e := by
  exact MultiTapeTM.runFrom_comm_of_step (fun d => d.mapWorkSymbols e)
    (counter_work_step M e) c t

end SymbolTransport

/-! ## C1 — decrement -/

/-- Little-endian fixed-width binary decrement with explicit underflow, the
mirror of `Turing.incFixed`: `decFixed w` is the predecessor word of the same
length, or `none` when `w` is all `false`, that is, has value zero. Width zero
underflows immediately. -/
def decFixed : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest => (decFixed rest).map (true :: ·)

/-- Complement exchanges the word-level carry and borrow recursions. -/
private lemma counter_dec_complement (w : List Bool) :
    decFixed w = (incFixed (w.map not)).map (List.map not) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [decFixed, incFixed, ih, List.map_map, Function.comp_def]

/-- Complementing work cells twice restores an arbitrary configuration. -/
private lemma counter_complement_twice {k : ℕ} {S : Type} {x : List Bool}
    (d : Cfg k Bool S x) :
    (d.mapWorkSymbols Equiv.boolNot).mapWorkSymbols Equiv.boolNot = d := by
  apply Cfg.ext <;> try rfl
  funext j p
  simp [Cfg.mapWorkSymbols, Option.map_map, Function.comp_def]

/-- Complementation of a buffered word preserves its blank delimiters. -/
private lemma counter_buffer_complement (w : List Bool) (p : ℤ) :
    FinTM.bufferTape (w.map not) p = (FinTM.bufferTape w p).map not := by
  exact FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p

/-- **R3, decrement** (design §12.7, C1). In-place little-endian fixed-width
binary decrement on tape `i`. The borrow pass flips `false` cells to `true`
moving right. The first `true` flips to `false` and selects the success
verdict. Running off the width (all `false`, value zero) selects the
underflow verdict, leaving the wrapped all-`true` word. The return pass
carries the verdict to the live `done` anchor at the origin.

It is defined as `Turing.incrementTM` conjugated by bit complement, so its
contracts are the increment's, transported by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`. -/
def decrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase :=
  (incrementTM k i).mapWorkSymbols Equiv.boolNot

/-- Every decrement run is one complemented increment run, including its frame. -/
private lemma counter_decrement_run {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool FlagPhase x) (t : ℕ) :
    (decrementTM k i).runFrom d t =
      ((incrementTM k i).runFrom (d.mapWorkSymbols Equiv.boolNot) t).mapWorkSymbols
        Equiv.boolNot := by
  simpa only [decrementTM, counter_complement_twice] using
    (incrementTM k i).mapWorkSymbols_runFrom Equiv.boolNot
      (d.mapWorkSymbols Equiv.boolNot) t

/-- **Decrement, framed success with exact borrow cost** (design §12.7, C1;
the mirror of `Turing.incrementTM_run_succ_ofCfg`). Let the delimited word `w`
on tape `i` have a predecessor at its width, `decFixed w = some v`, and let
`q = (w.takeWhile not).length` be its number of leading `false` cells. Then
the routine reaches the success anchor at exactly `2q + 2` and not earlier,
with the word interval holding `v` and everything else unchanged. Up to the
exit the head stays within `[pos - 1, pos + q]`.

**Proof sketch.** Complement the configuration's work tapes. The result
carries `w.map not`, whose successor is `v.map not` (`decFixed` is `incFixed`
conjugated by `not`) and whose `true` prefix has length `q`. Apply
`Turing.incrementTM_run_succ_ofCfg`, transport back by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`, and use that complementing
twice is the identity and that `FinTM.bufferTape` commutes with `map not`. -/
theorem decrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : decFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * (w.takeWhile not).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile not).length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile not).length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile not).length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = some (v.map not) := by
    have h := congrArg (Option.map (List.map not)) hv
    simpa [counter_dec_complement, Option.map_map, List.map_map, Function.comp_def] using h
  have hf : ∀ p : ℤ, -1 ≤ p → p ≤ ((w.map not).length : ℤ) →
      (d.mapWorkSymbols Equiv.boolNot).workTapes i
        ((d.mapWorkSymbols Equiv.boolNot).workTapePos i + p) =
          FinTM.bufferTape (w.map not) p := by
    intro p hl hr
    simpa [Cfg.mapWorkSymbols, counter_buffer_complement] using
      congrArg (Option.map not) (hw p hl (by simpa using hr))
  have hp : ((w.map not).takeWhile id).length = (w.takeWhile not).length := by
    simp [List.takeWhile_map, Function.comp_def]
  obtain ⟨he, hc, hh⟩ := incrementTM_run_succ_ofCfg i (w.map not) (v.map not)
    hv' (d.mapWorkSymbols Equiv.boolNot) hstate hf
  rw [hp] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Cfg.mapWorkSymbols, List.length_map]
    split_ifs <;> simp [counter_buffer_complement, Option.map_map, Function.comp_def]
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hc
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-- **Decrement, framed underflow** (design §12.7, C1; the mirror of
`Turing.incrementTM_run_overflow_ofCfg`). If the delimited word `w` on tape
`i` has no predecessor at its width (`decFixed w = none`, that is, it is all
`false`), the routine reaches the underflow anchor at exactly `2|w| + 2` and
not earlier. The word interval then holds `|w|` copies of `true`, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`.

**Proof sketch.** As the success case, through
`Turing.incrementTM_run_overflow_ofCfg`: the complemented word is all `true`,
so `incFixed` overflows, and the wrapped all-`false` word complements back to
all `true`. -/
theorem decrementTM_run_underflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : decFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length true) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = none := by
    simpa only [counter_dec_complement, Option.map_eq_none_iff] using hv
  obtain ⟨he, hc, hh⟩ := incrementTM_run_overflow_ofCfg i (w.map not) hv'
    (d.mapWorkSymbols Equiv.boolNot) hstate (by
      intro p hl hr
      change (d.workTapes i (d.workTapePos i + p)).map Equiv.boolNot = _
      rw [hw p hl (by simpa using hr), counter_buffer_complement]
      rfl)
  simp only [List.length_map] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    have hb := counter_buffer_complement (List.replicate w.length false)
      (p - d.workTapePos j)
    simp only [Cfg.mapWorkSymbols]
    split_ifs
    · simpa using hb.symm
    · simp [Option.map_map, Function.comp_def]
  · intro t ht b
    exact (hc t ht b) ∘ (by simp only [counter_decrement_run, Cfg.mapWorkSymbols]; exact id)
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-! ## Counter arithmetic -/

/-- The counter word after `r` decrements. A decrement at value zero leaves
the word unchanged here; the machine's underflow wrap is stated in the host
contract. -/
def counterWord (w : List Bool) (r : ℕ) : List Bool :=
  (fun u => (decFixed u).getD u)^[r] w

/-- The cost sum of the first `r` decrements along the frozen word orbit
`Turing.counterWord`: the decrement of the word `u` costs
`2 * (u.takeWhile not).length + 2`, which is also the underflow cost
`2|u| + 2` when `u` is all `false`. Because `counterWord` freezes at value
zero while the machine wraps on underflow, the sum equals the physical
countdown's cost only through its first underflow, that is for
`r ≤ value + 1`. That range covers every use in this file (§12.7 statement
gate, SC-1). -/
def counterOverhead (w : List Bool) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, (2 * ((counterWord w j).takeWhile not).length + 2)

/-- A borrow either detects an all-false word or preserves width, subtracts one,
and changes the true-bit potential by its false-prefix length.
**Proof sketch.** Induct on the word. A true low bit stops the borrow; a false
low bit propagates it and gains one true bit. -/
private lemma counter_dec_spec (w : List Bool) :
    match decFixed w with
    | none => w = List.replicate w.length false
    | some v => v.length = w.length ∧
        Nat.ofDigits 2 (w.map Bool.toNat) = Nat.ofDigits 2 (v.map Bool.toNat) + 1 ∧
        v.count true + 1 = w.count true + (w.takeWhile not).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true => simp [decFixed, Nat.ofDigits_cons, Nat.add_comm]
    | false =>
      cases hd : decFixed w with
      | none =>
        simp only [hd] at ih
        simpa [decFixed, hd, List.replicate_succ] using congrArg (false :: ·) ih
      | some v =>
        simp only [hd] at ih
        rcases ih with ⟨hl, hv, hc⟩
        simp [decFixed, hd, Nat.ofDigits_cons, hl]
        omega

/-- The next frozen counter word is obtained by one optional decrement. -/
private lemma counter_word_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- Underflow occurs exactly at binary value zero, including padded words. -/
private lemma counter_dec_zero (w : List Bool) :
    decFixed w = none ↔ Nat.ofDigits 2 (w.map Bool.toNat) = 0 := by
  have hs := counter_dec_spec w
  cases hd : decFixed w with
  | none =>
    simp only [hd] at hs
    simp only [true_iff]
    conv_lhs => rw [hs]
    simp
  | some v =>
    simp only [hd] at hs
    simp only [reduceCtorEq, false_iff]
    omega

/-- Decrements preserve the counter's width.

**Proof sketch.** `decFixed` preserves length, by induction on the word, and
`Option.getD` keeps the word otherwise; induct on `r`. -/
theorem counterWord_length (w : List Bool) (r : ℕ) :
    (counterWord w r).length = w.length := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [counter_word_succ]
    have hs := counter_dec_spec (counterWord w r)
    cases hd : decFixed (counterWord w r) with
    | none => simpa [hd] using ih
    | some v =>
      rw [hd] at hs
      simpa [hd] using hs.1.trans ih

/-- Each of the first `value w` decrements lowers the little-endian value by
one.

**Proof sketch.** For a word of positive value, `decFixed` succeeds and its
result has value one less, by induction on the word: a leading `true`
loses weight one, and a leading `false` borrows from the rest with weight
two. Induct on `r`. -/
theorem counterWord_value (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    Nat.ofDigits 2 ((counterWord w r).map Bool.toNat) =
      Nat.ofDigits 2 (w.map Bool.toNat) - r := by
  induction r with
  | zero => simp [counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_succ]
    cases hb : decFixed (counterWord w r) with
    | none =>
      have hz := (counter_dec_zero _).mp hb
      omega
    | some v =>
      simp only [hb] at hs
      simp only [Option.getD_some]
      omega

/-- Before exhaustion, the physical predecessor is the next frozen word. -/
private lemma counter_word_decrement (w : List Bool) (r : ℕ)
    (hr : r < Nat.ofDigits 2 (w.map Bool.toNat)) :
    decFixed (counterWord w r) = some (counterWord w (r + 1)) := by
  have hv := counterWord_value w r (by omega)
  rw [counter_word_succ]
  cases hd : decFixed (counterWord w r) with
  | none => have hz := (counter_dec_zero _).mp hd; omega
  | some v => rfl

/-- Successful borrow costs telescope against twice the number of true bits.
**Proof sketch.** At each step the borrow specification equates the new
potential plus four with the old potential plus the exact decrement cost.
Add this equality to the induction hypothesis. -/
private lemma counter_potential (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r + 2 * w.count true =
      4 * r + 2 * (counterWord w r).count true := by
  induction r with
  | zero => simp [counterOverhead, counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_decrement w r (by omega)] at hs
    simp only [counterOverhead, Finset.sum_range_succ]
    change (counterOverhead w r + (2 * (List.takeWhile not (counterWord w r)).length + 2)) +
      2 * w.count true = 4 * (r + 1) + 2 * (counterWord w (r + 1)).count true
    omega

/-- **Prefix amortization.** The first `r` decrements, for `r` at most the
counter's value, cost at most `4r + 2|w|`.

**Proof sketch.** The `j`th decrement acts on a word of value `n - j`
(`Turing.counterWord_value`), where `n` is the counter's value, and its
`false` prefix is the number of trailing zero bits of that value. Summed over
`r` consecutive values below `2^|w|`, the trailing zeros total
`ν₂(r!) + ν₂(binom) ≤ (r - 1) + (|w| - 1)` by Legendre and Kummer, so the
cost is at most `4r + 2|w| - 4` once `r ≥ 1`.

**Fill proof appendix.** The binding statement-gate route replaces the
number-theoretic sketch above by the exact telescoping identity proved in
`counter_potential`. Twice the count of true bits is the potential; its
terminal value is bounded by twice the preserved word length. -/
theorem counterOverhead_le_of_le (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r ≤ 4 * r + 2 * w.length := by
  have hp := counter_potential w r hr
  have hc : (counterWord w r).count true ≤ w.length :=
    (List.count_le_length).trans_eq (counterWord_length w r)
  omega

/-- At exhaustion the fixed-width word is all false, retaining any padding. -/
private lemma counter_word_exhausted (w : List Bool) :
    counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)) =
      List.replicate w.length false := by
  have hz := counterWord_value w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  simp only [Nat.sub_self] at hz
  have hs := counter_dec_spec (counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)))
  rw [(counter_dec_zero _).mpr hz] at hs
  simpa only [counterWord_length] using hs

/-- **Whole-run amortization** (design §12.7, decision 12.7.6). Counting a
counter of value `n` down to zero and through the final underflow costs at
most `4n + 2|w| + 2`.

**Proof sketch.** The successful decrements act on the values `n, …, 1`,
whose trailing zeros sum to `n - s₂(n) ≤ n` (Legendre), so they cost at most
`4n`. The final word is all `false` (`Turing.counterWord_value`), so the
underflow sweep costs `2|w| + 2` (`Turing.counterWord_length`).

**Fill proof appendix.** Use `counter_potential` at exhaustion, where the
remaining true-bit count is zero, then add the full underflow sweep.
No Legendre or Kummer theorem is used. -/
theorem counterOverhead_le (w : List Bool) :
    counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) ≤
      4 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2 := by
  have hp := counter_potential w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  rw [counter_word_exhausted] at hp
  simp [List.count_replicate] at hp
  have hs : counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) =
      counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat)) + (2 * w.length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, counter_word_exhausted]
  omega

/-! ## C2 — the counter-driven host -/

/-- Control of the counter-driven host (design §12.7, C2): a body state, a
decrement phase, or one of the two live exit anchors. -/
inductive CounterLoopState (S : Type) where
  /-- running the body -/
  | body (s : S)
  /-- running the decrement on the counter tape -/
  | dec (f : FlagPhase)
  /-- the live exit anchor after the counter underflows -/
  | done
  /-- the live exit anchor after the body reaches its designated exit -/
  | escape
deriving DecidableEq

instance counterLoopStateFintype (S : Type) [Fintype S] :
    Fintype (CounterLoopState S) := derive_fintype% _

/-- Where a body transition lands in the host. Arriving at the anchor `a`
starts the next decrement; arriving at the designated exit leaves through
`escape`; every other body state is kept. -/
def counterLoopRedirect {S : Type} [DecidableEq S] (a : S) (exit : Option S)
    (s : S) : CounterLoopState S :=
  if s = a then .dec .run else if exit = some s then .escape else .body s

/-- Where a decrement transition lands in the host. The success anchor
re-enters the body at `a`, the underflow anchor is the host's `done`, and the
working phases are kept. -/
def counterLoopDecExit {S : Type} (a : S) : FlagPhase → CounterLoopState S
  | .done true => .body a
  | .done false => .done
  | f => .dec f

/-- **C2, the counter-driven loop host** (design §12.7). The body `M` runs on
the first `k` tapes, embedded by `Turing.embedEmitTM` along `Fin.castSucc`
with its emissions forwarded, and the counter is the last tape. The host
starts with a decrement. Each successful decrement re-enters the body at the
anchor `a`, and each arrival at `a` starts the next decrement, with no
dispatch steps in between. Underflow leaves through the live anchor `done`;
reaching the optional exit leaves through the live anchor `escape`. Both
anchors are stationary. -/
def counterLoopTM {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) : MultiTapeTM (k + 1) Bool (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((decrementTM (k + 1) (Fin.last k)).tr f inp work).mapState (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- Select the last host tape as a one-tape bank (design §12.8a, R8.0b).
**Proof sketch.** The singleton domain makes the constant last-tape map injective. -/
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

/-- Run a rich-alphabet body with an embedded binary counter on the last tape
(design §12.8a, R8.0b).
**Proof sketch.** R1 forwards the body and the symbol-lifted one-tape decrement;
the existing redirections connect the phases without dispatch steps. -/
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- A host configuration with host state `q`: the body configuration `c` on
the first `k` tapes (its own state field is ignored), the counter tape `ct`
with its head at `cp` as the last tape, and the body's output as the host's
output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
with the counter as the ambient frame. -/
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- The body configurations at the starts of successive rounds: round `r`
starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
steps. -/
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-! ### Shared phase and prefix invariants -/

/-- The host layout over any tape alphabet.
**Proof sketch.** R1 identifies the selected body bank and the last-tape frame. -/
private lemma counter_layout {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Symbol Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
  apply Cfg.ext <;> try rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.1
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.2
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i

/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
host configuration is the body bank followed by its counter tape.

**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`).

**Re-derivation appendix (R8.0b).** Instantiate the generic private layout at the Bool alphabet. -/
theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ :=
  counter_layout q c ct cp

/-- Injective successor redirection for the decrement's five controls. -/
private lemma counter_dec_injective {S : Type} (a : S) :
    Function.Injective (counterLoopDecExit a) := by
  intro f g h
  cases f <;> cases g <;> (try casesm* Bool) <;> simp_all [counterLoopDecExit]

/-- Anchor priority still gives an injective body-state redirection. -/
private lemma counter_redirect_injective {S : Type} [DecidableEq S]
    (a : S) (exit : Option S) : Function.Injective (counterLoopRedirect a exit) := by
  intro s t h
  by_cases hs : s = a
  · subst s
    by_cases ht : t = a
    · exact ht.symm
    · simp only [counterLoopRedirect, ht, if_false] at h
      split_ifs at h
  · by_cases ht : t = a
    · subst t; simp only [counterLoopRedirect, hs, if_false] at h
      split_ifs at h
    · simp only [counterLoopRedirect, hs, ht, if_false] at h
      split_ifs at h <;> simp_all

/-- Common trajectory data for a finite host segment, with a chosen set of
permitted body-head vectors. -/
private def counterSpan {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
    (R : (Fin k → ℤ) → Prop) : Prop :=
  (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
    (H.runFrom z u).state ≠ some .escape) ∧
  (∀ u ≤ t, (H.runFrom z u).workTapePos (Fin.last k) ∈
    Finset.Icc (cp - 1) (cp + (width : ℤ))) ∧
  (∀ u ≤ t, R (fun j => (H.runFrom z u).workTapePos j.castSucc))

/-- Adjacent segments concatenate their cuts and trajectory bounds.
**Proof sketch.** Split a queried time at the first segment's length and
use run addition on the suffix. The two head-vector relations imply the
requested relation separately. -/
private lemma counter_span_append {k : ℕ} {Γ S : Type} {x : List Γ}
    (H : MultiTapeTM (k + 1) Γ (CounterLoopState S))
    (z : Cfg (k + 1) Γ (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
    (R₁ R₂ R : (Fin k → ℤ) → Prop)
    (h₁ : counterSpan H z s cp width R₁)
    (h₂ : counterSpan H (H.runFrom z s) t cp width R₂)
    (hr₁ : ∀ p, R₁ p → R p) (hr₂ : ∀ p, R₂ p → R p) :
    counterSpan H z (s + t) cp width R := by
  have suffix (u : ℕ) (hu : s ≤ u) :
      H.runFrom z u = H.runFrom (H.runFrom z s) (u - s) := by
    rw [← H.runFrom_add, Nat.add_sub_of_le hu]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    by_cases hs : u < s
    · exact h₁.1 u hs
    · rw [suffix u (by omega)]; exact h₂.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact h₁.2.1 u hs
    · rw [suffix u (by omega)]; exact h₂.2.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact hr₁ _ (h₁.2.2 u hs)
    · rw [suffix u (by omega)]; exact hr₂ _ (h₂.2.2 (u - s) (by omega))

/-- A width-preserving overwrite of just the counter word interval. -/
private def counterPatch {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (w : List Γ) : ℤ → Option Γ :=
  fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
    then FinTM.bufferTape w (q - cp) else ct q

/-- Equal-width patches overwrite the same interval, preserving the original frame. -/
private lemma counter_patch_twice {Γ : Type} (ct : ℤ → Option Γ) (cp : ℤ) (u v : List Γ)
    (hv : v.length = u.length) :
    counterPatch (counterPatch ct cp u) cp v = counterPatch ct cp v := by
  funext q
  simp only [counterPatch, hv]
  split_ifs <;> rfl

/-- Replacing a framed word by an equal-width word keeps both blank delimiters. -/
private lemma counter_patch_frame {Γ : Type} (w v : List Γ) (ct : ℤ → Option Γ) (cp : ℤ)
    (hv : v.length = w.length)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      counterPatch ct cp v (cp + p) = FinTM.bufferTape v p := by
  intro p hl hr
  by_cases h : 0 ≤ p ∧ p < (v.length : ℤ)
  · simp [counterPatch, show cp ≤ cp + p ∧ cp + p < cp + (v.length : ℤ) by omega]
  · have hp : p = -1 ∨ p = (v.length : ℤ) := by omega
    rcases hp with rfl | rfl
    · simp [counterPatch, hw (-1) (by omega) (by omega), FinTM.bufferTape_left]
    · simp [counterPatch, hv, hw w.length (by omega) le_rfl, FinTM.bufferTape_nat]

/-- A decrement phase uses the proved framed contract and guarded state transport.
**Proof sketch.** Decode the rich one-tape start, apply the landed success or
underflow contract, and read back through the public symbol overlay. Its input
obliviousness and absence of blank writes preserve arbitrary rich frame cells.
R1 puts this run on the last tape; injective guarded state transport supplies
the host's verdict cut and the two head trajectories. -/
private lemma counter_debit {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map e) p) :
    let cost := 2 * (w.takeWhile not).length + 2
    let v := (decFixed w).getD (List.replicate w.length true)
    let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
      counterLoopCfg (some q) c (counterPatch ct cp (v.map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
  let D : Cfg 1 Γ FlagPhase x :=
    ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩
  let z := Cfg.decodeSymbols e D
  let v := (decFixed w).getD (List.replicate w.length true)
  let cost := 2 * (w.takeWhile not).length + 2
  let N := (decrementTM 1 0).liftSymbols e
  let E := embedEmitTM (lastEmb k) N
  let bank (d : Cfg 1 Γ FlagPhase x) := embedEmitCfg (lastEmb k)
    (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d
  have layout (d : Cfg 1 Γ FlagPhase x) : bank d =
      ⟨d.state, d.inputPos, Fin.lastCases (d.workTapes 0) c.workTapes,
        Fin.lastCases (d.workTapePos 0) c.workTapePos, d.output⟩ := by
    have frame (i : Fin k) := (embedEmitTM_frame (lastEmb k) N
      (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d 0).1
      i.castSucc (by rintro ⟨j, hj⟩; exact Fin.castSucc_ne_last i hj.symm)
    apply Cfg.ext <;> try rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [bank, Fin.lastCases_last] using
          embedEmitCfg_selected_tape (lastEmb k) (Fin.lastCases ct c.workTapes)
            (Fin.lastCases cp c.workTapePos) [] d 0
      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).1
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [bank, Fin.lastCases_last] using
          embedEmitCfg_selected_pos (lastEmb k) (Fin.lastCases ct c.workTapes)
            (Fin.lastCases cp c.workTapePos) [] d 0
      · simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (frame i).2
  have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      z.workTapes 0 (z.workTapePos 0 + p) = FinTM.bufferTape w p := by
    intro p hl hr
    change (ct (cp + p)).bind (decodeBool e) = _
    rw [hw p hl hr, FinTM.bufferTape_map_decode]
  -- The only decrement facts are the landed framed contracts, on the decoded shadow.
  have spec :
      (decrementTM 1 0).runFrom z cost =
        {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
          if j = 0 ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
      (∀ t < cost, ∀ b, ((decrementTM 1 0).runFrom z t).state ≠ some (.done b)) ∧
      (∀ t ≤ cost, ((decrementTM 1 0).runFrom z t).workTapePos 0 ∈
        Finset.Icc (cp - 1) (cp + (w.length : ℤ))) := by
    cases hd : decFixed w with
    | none =>
      have hs := counter_dec_spec w
      rw [hd] at hs
      have hp : (w.takeWhile not).length = w.length := by
        conv_lhs => rw [hs]
        simp
      obtain ⟨he, hc, hh⟩ := decrementTM_run_underflow_ofCfg 0 w hd z rfl hz
      refine ⟨by simpa [cost, v, hd, hp] using he,
        by simpa [cost, hp] using hc, ?_⟩
      intro t ht
      simpa [z, D, Cfg.decodeSymbols] using hh 0 t (by simpa [cost, hp] using ht)
    | some u =>
      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg 0 w u hd z rfl hz
      refine ⟨by simpa [v, hd] using he, hc, ?_⟩
      intro t ht
      have h := hh 0 t ht
      simp only [ite_true, Finset.mem_Icc] at h ⊢
      have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
      exact ⟨h.1, by
        have upper : ((decrementTM 1 0).runFrom z t).workTapePos 0 ≤
            cp + ((w.takeWhile not).length : ℤ) := h.2
        omega⟩
  have rich (t : ℕ) : N.runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t) := by
    conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
    apply MultiTapeTM.liftSymbols_runFrom_over e _ (fun _ _ _ _ => rfl)
    intro f inp work j
    rcases f with _ | b | b <;>
    rcases h : work 0 with _ | b' <;> (try cases b') <;>
    simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
    split_ifs <;> simp
  let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
  have start : (bank D).mapState emb = counterLoopCfg (some (.dec .run)) c ct cp := by
    rw [layout, counter_layout]
    rfl
  have run (t : ℕ) (ht : t ≤ cost) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
        (bank (Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom z t))).mapState emb := by
    rw [← start]
    have h := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun f => ∀ b, f ≠ .done b) (by
        intro f hf inp work
        cases f with
        | run => rfl
        | rewind b => rfl
        | done b => exact False.elim (hf b rfl)) (bank D) t (by
          intro u hu f hf b he
          rw [show E.runFrom (bank D) u = bank (N.runFrom D u) from
            embedEmitTM_runFrom (lastEmb k) N _ _ [] D u, rich] at hf
          exact spec.2.1 u (by omega) b (hf.trans (congrArg some he)))
    rw [h, show E.runFrom (bank D) t = bank (N.runFrom D t) from
      embedEmitTM_runFrom (lastEmb k) N _ _ [] D t, rich]
  have vl : v.length = w.length := by
    have hs := counter_dec_spec w
    cases hd : decFixed w <;> simp [v, hd] at *
    exact hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run cost le_rfl, spec.1, layout, counter_layout]
    apply Cfg.ext
    · cases hd : decFixed w <;> simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols,
        emb, counterLoopDecExit]
    · apply Fin.ext; rfl
    · funext j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Cfg.mapState, Fin.lastCases_last]
        change (if (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
            then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)) =
              (ct p).bind (decodeBool e) then ct p
            else (if (0 : Fin 1) = 0 ∧ cp ≤ p ∧ p < cp + (w.length : ℤ)
              then FinTM.bufferTape v (p - cp) else (ct p).bind (decodeBool e)).map e) =
          counterPatch ct cp (v.map e) p
        simp only [true_and, counterPatch, List.length_map, vl, FinTM.bufferTape_map]
        by_cases hp : cp ≤ p ∧ p < cp + (w.length : ℤ)
        · simp only [if_pos hp]
          split_ifs with he
          · have hn : (p - cp).toNat < v.length := by omega
            have hb : FinTM.bufferTape v (p - cp) = some v[(p - cp).toNat] := by
              simp [FinTM.bufferTape, hp.1, hn]
            cases hct : ct p with
            | none => simp [hct, hb] at he
            | some γ =>
              have decoded : decodeBool e γ = some v[(p - cp).toNat] := by
                simpa only [hct, hb, Option.bind_some] using he.symm
              simp only [hb, Option.map_some, decodeBool_eq_some e γ _ decoded]
          · rfl
        · simp only [if_neg hp, if_true]
      · simp only [Cfg.mapState, Fin.lastCases_castSucc]
    · rfl
    · simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, z, Cfg.decodeSymbols, D]
  · intro t ht
    rw [run t (by omega), layout]
    have hc := spec.2.1 t ht
    cases hs : ((decrementTM 1 0).runFrom z t).state with
    | none => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs]
    | some f =>
      cases f with
      | run => simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
      | rewind b =>
        simp [Cfg.mapState, Cfg.liftOver, Cfg.liftSymbols, hs, emb, counterLoopDecExit]
      | done b => exact False.elim (hc b hs)
  · intro t ht
    rw [run t ht, layout]
    simpa only [Cfg.mapState, Fin.lastCases_last, Cfg.liftOver, Cfg.liftSymbols] using
      spec.2.2 t ht
  · intro t ht j
    rw [run t ht, layout]
    simp only [Cfg.mapState, Fin.lastCases_castSucc]

/-- The body phase executes its entry action once, then uses guarded transport.
**Proof sketch.** The entry action reads the forwarding embedding. After that
step, all strict intermediate states avoid both redirections, and the RB5
transport lemma applies. R1 identifies every transported configuration and
therefore preserves the counter frame and all body-head trajectories. -/
private lemma counter_body {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (c : Cfg k Γ S x) (ct : ℤ → Option Γ) (cp : ℤ) (width t : ℕ)
    (hc : c.state = some a) (ht : 0 < t)
    (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
      s ≠ a ∧ exit ≠ some s) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
      counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
        (M.runFrom c t) ct cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.body a)) c ct cp)
      t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
  let E := embedEmitTM Fin.castSuccEmb M
  let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
  let emb : S ↪ CounterLoopState S :=
    ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
  have first : (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
      (E.runFrom ec 1).mapState emb := by
    change (counterLoopTMVia e M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
      (E.step ec).mapState emb
    have hec : ec.state = some a := hc
    simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
    rfl
  have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
      (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
        counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
          (M.runFrom c u) ct cp := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTMVia e M a exit) emb
      (fun s => s ≠ a ∧ exit ≠ some s)
      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTMVia, E])
      (E.runFrom ec 1) n (by
        intro v hv s hs
        have he := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c (1 + v)
        change E.runFrom ec (1 + v) = _ at he
        rw [MultiTapeTM.runFrom_add] at he
        have hstate := congrArg Cfg.state he
        change (E.runFrom (E.runFrom ec 1) v).state = (M.runFrom c (1 + v)).state at hstate
        obtain ⟨s', hs', ha, hx⟩ := hmid (1 + v) (by omega) (by omega)
        have eqs : s = s' := Option.some.inj (hs.symm.trans (hstate.trans hs'))
        simpa [eqs] using And.intro ha hx)
    rw [tr, ← MultiTapeTM.runFrom_add]
    change (E.runFrom ec (1 + n)).mapState emb = _
    rw [show E.runFrom ec (1 + n) =
      embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] (M.runFrom c (1 + n)) from
      embedEmitTM_runFrom Fin.castSuccEmb M _ _ [] c (1 + n)]
    rfl
  refine ⟨run t ht le_rfl, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counterLoopCfg]
    · rw [run u (by omega) (by omega)]
      obtain ⟨s, hs, ha, hx⟩ := hmid u (by omega) hu
      simp [counterLoopCfg, hs, counterLoopRedirect, ha, hx]
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counter_layout, Finset.mem_Icc]
    · rw [run u (by omega) hu]
      simp [counter_layout, Finset.mem_Icc]
  · intro u hu
    refine ⟨u, hu, ?_⟩
    by_cases hz : u = 0
    · subst u; simp [counter_layout]
    · rw [run u (by omega) hu]
      simp [counter_layout]

/-- At the identity embedding the generic and Bool hosts have the same table.
**Proof sketch.** Compute R1 on its public last-tape embedding, cancel the
identity symbol lift, and compare the decrement tables field by field. -/
private lemma counter_refl_agree {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) :
    (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn
      (counterLoopTM M a exit) Set.univ := by
  have action_eq {k : ℕ} {Sy Q : Type} {A B : Action k Sy Q}
      (h1 : A.inputTape = B.inputTape) (h2 : A.workTapes = B.workTapes)
      (h3 : A.output = B.output) (h4 : A.state = B.state) : A = B := by
    cases A; cases B; simp_all
  have lift_refl (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) :
      ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool)).tr f inp work =
        (decrementTM 1 0).tr f inp work := by
    have hd : ∀ o : Option Bool, o.bind (decodeBool (Function.Embedding.refl Bool)) = o := by
      intro o; cases o with
      | none => rfl
      | some b => cases b <;> rfl
    simp only [MultiTapeTM.liftSymbols, hd]
    cases ((decrementTM 1 0).tr f inp work) with
    | mk i w o s =>
      simp only [Action.liftSymbols]
      congr 1
      · funext j
        cases w j with
        | mk a m => cases a with
          | none => rfl
          | some b => cases b <;> rfl
      · cases o <;> rfl
  have embed_last {k : ℕ} {Sy Q : Type} (N : MultiTapeTM 1 Sy Q) (q : Q)
      (inp : Option Sy) (work : Fin (k + 1) → Option Sy) :
      (embedEmitTM (lastEmb k) N).tr q inp work =
        ⟨(N.tr q inp fun _ => work (Fin.last k)).inputTape,
          fun j => if j = Fin.last k then (N.tr q inp fun _ => work (Fin.last k)).workTapes 0
            else (none, 0),
          (N.tr q inp fun _ => work (Fin.last k)).output,
          (N.tr q inp fun _ => work (Fin.last k)).state⟩ := by
    apply action_eq
    · rfl
    · funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [if_true]
        conv_lhs => whnf
        split
        · rename_i i h
          rw [Subsingleton.elim i 0]
          rfl
        · rename_i h
          revert h
          show ((List.finRange 1).find? fun i => decide ((lastEmb k) i = Fin.last k)) = none → _
          simp [lastEmb]
      · simp only [Fin.castSucc_ne_last, if_false]
        conv_lhs => whnf
        split
        · rename_i i' h
          revert h
          show ((List.finRange 1).find? fun i' => decide ((lastEmb k) i' = Fin.castSucc i)) =
            some i' → _
          simp only [lastEmb, Function.Embedding.coeFn_mk, (Fin.castSucc_ne_last i).symm,
            decide_false]
          intro h
          rw [List.find?_eq_none.mpr (fun _ _ => by simp)] at h
          cases h
        · rfl
    · rfl
    · rfl
  have dec_refl (k : ℕ) (f : FlagPhase) (inp : Option Bool)
      (work : Fin (k + 1) → Option Bool) :
      (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool))).tr
          f inp work =
        (decrementTM (k + 1) (Fin.last k)).tr f inp work := by
    rw [embed_last, lift_refl]
    apply action_eq
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · funext j
      rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
        split_ifs <;> simp_all
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
    · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
        simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
  intro q _ inp work
  cases q with
  | body s => rfl
  | dec f => exact congrArg (Action.mapState (counterLoopDecExit a)) (dec_refl k f inp work)
  | done => rfl
  | escape => rfl

/-- The shared round invariant, with the final body state left unrestricted.
Returning prefixes are exactly the configurations before the next decrement.
**Proof sketch.** Induct once on the number of rounds. The current word has
positive value, so the framed decrement succeeds. Append its transported
segment and the forwarding body segment. Equal-width overwrites keep the
original counter frame, and the two cost recurrences give the exact elapsed
time. Earlier starts at the anchor supply all returns needed by the induction. -/
private lemma counter_rounds {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] {x : List Γ}
    (e : Bool ↪ Γ) (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s)) :
    let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
      counterLoopCfg (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
        (counterLoopOrbit M τ c n) (counterPatch ct cp ((counterWord w n).map e)) cp ∧
    counterSpan (counterLoopTMVia e M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      elapsed cp w.length (fun p => ∃ r u,
        ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
      Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
    have hpatch : counterPatch ct cp ((counterWord w 0).map e) = ct := by
      change counterPatch ct cp (w.map e) = ct
      funext q
      apply ite_eq_right_iff.mpr
      intro h
      simp only [List.length_map] at h
      have hf := hw (q - cp) (by omega) (by omega)
      simpa using hf.symm
    rw [hpatch]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro u hu; omega
    · intro u hu; have hz : u = 0 := by omega
      subst u; simp [counter_layout, Finset.mem_Icc]
    · intro u hu; have hz : u = 0 := by omega
      subst u
      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_layout, counterLoopOrbit]⟩
  | succ n ih =>
    obtain ⟨before, span⟩ := ih (by omega) (fun r hr => hround r (by omega))
    obtain ⟨ha, ht, hg⟩ := hround n (by omega)
    have control : (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit)) =
        some (CounterLoopState.dec FlagPhase.run) := by
      split_ifs <;> simp [ha, counterLoopRedirect]
    rw [control] at before
    let cn := counterLoopOrbit M τ c n
    let wn := counterWord w n
    let pn := counterPatch ct cp (wn.map e)
    let nextTape := counterPatch ct cp ((counterWord w (n + 1)).map e)
    let cost := 2 * (wn.takeWhile not).length + 2
    have hd := counter_word_decrement w n (by omega)
    have hf := counter_patch_frame (w.map e) (wn.map e) ct cp
      (by simp [List.length_map, wn, counterWord_length]) (by simpa using hw)
    obtain ⟨debit, ds⟩ := counter_debit e M a exit cn wn pn cp (by simpa using hf)
    change decFixed wn = some (counterWord w (n + 1)) at hd
    simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
    rw [counter_patch_twice ct cp (wn.map e) ((counterWord w (n + 1)).map e)
      (by simp only [List.length_map, wn, counterWord_length])] at debit
    obtain ⟨body, bs⟩ := counter_body e M a exit cn nextTape cp w.length (τ cn) ha ht hg
    have round : (counterLoopTMVia e M a exit).runFrom
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
        counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
          (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
      rw [MultiTapeTM.runFrom_add, debit, body]
      rw [show counterLoopOrbit M τ c (n + 1) = M.runFrom cn (τ cn) from
        Function.iterate_succ_apply' _ _ _]
    have rs : counterSpan (counterLoopTMVia e M a exit)
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
        (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
      apply counter_span_append _ _ cost (τ cn) cp w.length _ _ _
        (by simpa only [List.length_map, wn, counterWord_length] using ds) (by rw [debit]; exact bs)
      · intro p hp; exact ⟨0, Nat.zero_le _, by simpa using hp⟩
      · exact fun _ h => h
    have time : (∑ r ∈ Finset.range (n + 1), τ (counterLoopOrbit M τ c r)) +
        counterOverhead w (n + 1) =
        ((∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r)) + counterOverhead w n) +
          (cost + τ cn) := by
      simp [counterOverhead, Finset.sum_range_succ, cost, wn, cn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    dsimp only
    rw [time]
    refine ⟨?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, before, round]
      rfl
    · apply counter_span_append _ _ _ (cost + τ cn) cp w.length _ _ _ span
        (by rw [before]; exact rs)
      · intro p hp
        obtain ⟨r, u, hr, heads⟩ := hp
        refine ⟨r, u, Or.inl ?_, heads⟩
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · exact ⟨by omega, hu⟩
        · exact ⟨by omega, Nat.zero_le _⟩
      · intro p hp
        obtain ⟨u, hu, heads⟩ := hp
        exact ⟨n, u, Or.inl ⟨by omega, hu⟩, heads⟩

/-- The rich-alphabet counter host returns after all rounds
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction and append the
transported final underflow sweep. -/
theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨before, span⟩ := counter_rounds e M a exit τ c w ct cp hw d (by omega)
    (fun r hr => ⟨(hround r hr).1, (hround r hr).2.1, (hround r hr).2.2.1⟩)
  have control : (if d = 0 then some (.dec .run) else
      (counterLoopOrbit M τ c d).state.map (counterLoopRedirect a exit)) =
      some (CounterLoopState.dec FlagPhase.run) := by
    by_cases hz : d = 0
    · simp [hz]
    · have ret := (hround (d - 1) (by omega)).2.2.2
      rw [show d - 1 + 1 = d by omega] at ret
      simp [hz, ret, counterLoopRedirect]
  rw [control] at before
  let wd := counterWord w d
  have width : wd.length = w.length := counterWord_length w d
  have empty : wd = List.replicate w.length false := by
    simpa only [hd] using counter_word_exhausted w
  have under : decFixed wd = none := (counter_dec_zero wd).mpr (by simp [empty])
  have framed := counter_patch_frame (w.map e) (wd.map e) ct cp
    (by simpa using width) (by simpa using hw)
  obtain ⟨debit, ds⟩ := counter_debit e M a exit (counterLoopOrbit M τ c d) wd
    (counterPatch ct cp (wd.map e)) cp (by simpa using framed)
  simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
    width] at debit
  rw [counter_patch_twice ct cp (wd.map e) ((List.replicate w.length true).map e)
    (by simp [width])] at debit
  have fill : counterPatch ct cp ((List.replicate w.length true).map e) =
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) := by
    funext q
    simp only [counterPatch, List.length_replicate, List.map_replicate]
    split_ifs with h
    · have hp : 0 ≤ q - cp := by omega
      have hn : (q - cp).toNat < w.length := by omega
      simp [FinTM.bufferTape, h.1, hn]
    · rfl
  rw [fill] at debit
  have time : (∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) +
      counterOverhead w (d + 1) =
      ((∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) + counterOverhead w d) +
        (2 * (wd.takeWhile not).length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, wd, Nat.add_assoc]
  rw [time]
  refine ⟨?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, before, debit]
  · exact counter_span_append _ _ _ _ cp w.length _ _ _ span
      (by rw [before]; simpa only [width] using ds) (fun _ h => h)
      (fun p hp => ⟨d, 0, Or.inr ⟨rfl, rfl⟩, by simpa using hp⟩)

/-- The rich-alphabet counter host takes an early body exit
(design §12.8a, R8.0b), with exact time, first-exit and both head trajectories.
**Proof sketch.** Instantiate the single generic round induction; its unrestricted
last body state redirects to the designated escape. -/
theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨he, hs⟩ := counter_rounds e M a (some ex) τ c w ct cp hw (r₀ + 1)
    (by omega) (by
      intro r hr
      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
      refine ⟨ha, ht, ?_⟩
      intro u hu hut
      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
  refine ⟨?_, hs.1, hs.2.1, ?_⟩
  · unfold counterPatch at he
    simp only [List.length_map, counterWord_length] at he
    simpa [hexit, hea, counterLoopRedirect] using he
  · simpa only [Nat.lt_succ_iff] using hs.2.2

/-- **The counter-driven loop, every round returns** (design §12.7, C2).
Start the host at its decrement phase, with body configuration `c` and the
delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
anchor, the exit and halting in between, and returns to `a`. Then the host
reaches `done` at exactly `T`: the `d` round times plus the exact decrement
overhead, including the final underflow sweep. Its body part is the orbit
after `d` rounds, its counter is all `true`, and its counter head is back at
`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
some point of some round. With `exit = none`, the hypotheses do not mention an
exit at all.

**Proof sketch.** Induct on the round. Each decrement is
`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
redirection is applied at the exit step. Each round is the R1 run
`Turing.embedEmitTM_runFrom` with its states renamed by
`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
step while the body's next state is neither the anchor nor the exit, which
the round hypothesis guarantees before the final step; the final step is the
redirection. The counter word before round
`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
costs add to `Turing.counterOverhead w (d + 1)`.

**Re-derivation appendix (R8.0b).** Apply the generic returning contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a exit).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a exit) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  simp only [z5]
  exact counterLoopTMVia_run_done (Function.Embedding.refl Bool) M a exit τ c w ct cp hw'
    d hd hround T hT

/-- **The counter-driven loop, early exit** (design §12.7, C2). As
`Turing.counterLoopTM_run_done`, except that round `r₀`, below the counter's
value, ends at the designated exit `e ≠ a` while every earlier round returns
to `a`. Then the host reaches `escape` at exactly the `r₀ + 1` round times plus
the cost of the `r₀ + 1` decrements before them. Its body part is the orbit
after round `r₀`, and its counter holds `Turing.counterWord w (r₀ + 1)`.
Earlier, neither exit anchor occurs, and the trajectory clauses hold as in
the returning case.

**Proof sketch.** The induction of `Turing.counterLoopTM_run_done`, stopped at
round `r₀`: every decrement before it succeeds, since `r₀` is below the value
(`Turing.counterWord_value`), and the redirection sends round `r₀`'s final
step to `escape`.

**Re-derivation appendix (R8.0b).** Apply the generic escape contract at the identity embedding and transport
its run by `MultiTapeTM.runFrom_eq_of_agreeOn`; no new induction is used. -/
theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a (some e)).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a (some e)).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (counter_refl_agree M a (some e)) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  have h := counterLoopTMVia_run_escape (Function.Embedding.refl Bool) M a e hea τ c w ct cp
    hw' r₀ hr₀ hround hexit T hT
  simp only [Function.Embedding.coe_refl, List.map_id] at h
  simp only [z5]
  exact h

/-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
the `d` rounds costs at most `B`, the returning run's exact time is at most
`d·B + 4d + 2|w| + 2`.

**Proof sketch.** Bound the round sum termwise by `B`
(`Finset.sum_le_card_nsmul`) and the decrement share by
`Turing.counterOverhead_le`. -/
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range d)
    (fun r => τ (counterLoopOrbit M τ c r)) B
    (fun r hr => hB r (Finset.mem_range.mp hr))
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hc := counterOverhead_le w
  rw [hd] at hc
  calc
    _ ≤ d * B + (4 * d + 2 * w.length + 2) :=
      Nat.add_le_add (by simpa using hsum) hc
    _ = _ := by omega

/-! ## R8.6 — the expansion (§12.8) -/

/-- **R8.6, the expansion** (design §12.8a). The counter loop whose round is
the advancing writer: with a counter of value `d` on the last tape, it writes
the pattern `pat` on tape `i` `d` times, contiguously from the head, and leaves
the head after the last copy. Its uses are lengths given in binary: the
window halves of a record, of length `d·|pat|` for a radius counter `d`. -/
def expandTM (k : ℕ) (i : Fin k) (pat : List Bool) :
    MultiTapeTM (k + 1) Bool (CounterLoopState (Fin (pat.length + 1))) :=
  counterLoopTM (writeAdvTM k i pat) 0 none

/-- **R8.6, the expansion, framed** (design §12.8a). Start the expansion at its
decrement phase with body configuration `c` at the writer's state `0` and the
delimited counter word `w`, of value `d`, at `cp`. It reaches `done` at exactly
`d·(|pat| + 1) + counterOverhead w (d + 1)` and neither exit anchor earlier.
At that point the interval `[pos, pos + d·|pat|)` of tape `i` holds `d` copies
of `pat`, whatever it held before, the head of tape `i` is at `pos + d·|pat|`,
the counter is all `true` with its head back at `cp`, and every other cell,
every other head, the input position and the output are unchanged. Throughout,
the counter head stays within `[cp - 1, cp + |w|]`, the head of tape `i`
within `[pos, pos + d·|pat|]`, and every other body head is fixed.

**Proof sketch.** Apply `Turing.counterLoopTM_run_done` with the constant round
time `τ := |pat| + 1`. The round hypotheses are `Turing.writeAdvTM_run_ofCfg`
at the orbit's `r`-th configuration, which by induction on `r` has `r` copies
of `pat` written from `pos` and its head at `pos + r·|pat|`. The round sum is
`d·(|pat| + 1)`. The head clauses follow from the loop's trajectory clause and
the writer's. -/
theorem expandTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfg (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) := by
  let M := writeAdvTM k i pat
  let τ : Cfg k Bool (Fin (pat.length + 1)) x → ℕ := fun _ => pat.length + 1
  let finish (r : ℕ) : Cfg k Bool (Fin (pat.length + 1)) x :=
    { c with
      workTapes := fun j q =>
        if j = i ∧ c.workTapePos j ≤ q ∧
            q < c.workTapePos j + ((r * pat.length : ℕ) : ℤ)
          then FinTM.bufferTape (List.replicate r pat).flatten (q - c.workTapePos j)
        else c.workTapes j q
      workTapePos := Function.update c.workTapePos i
        (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) }
  -- This induction concerns only the advancing writer's orbit, not the loop host.
  have orbit (r : ℕ) : counterLoopOrbit M τ c r = finish r := by
    induction r with
    | zero =>
      change c = finish 0
      apply Cfg.ext <;> try rfl
      · funext j q
        simp [finish]
      · funext j
        by_cases hj : j = i <;> simp [finish, hj]
    | succ r ih =>
      have step := (writeAdvTM_run_ofCfg i pat (finish r) hc).1
      rw [show counterLoopOrbit M τ c (r + 1) =
        M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) from
        Function.iterate_succ_apply' _ _ _, ih]
      change (writeAdvTM k i pat).runFrom (finish r) (pat.length + 1) = finish (r + 1)
      rw [step]
      have length : (List.replicate r pat).flatten.length = r * pat.length := by simp
      have append : (List.replicate (r + 1) pat).flatten =
          (List.replicate r pat).flatten ++ pat := by
        rw [List.replicate_succ', List.flatten_append]
        simp
      apply Cfg.ext
      · exact hc.symm
      · rfl
      · funext j q
        by_cases hj : j = i
        · subst j
          simp only [finish, Function.update_self, true_and, Nat.add_mul, Nat.one_mul,
            Nat.cast_add, append]
          by_cases hnew : c.workTapePos i + ((r * pat.length : ℕ) : ℤ) ≤ q ∧
              q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)
          · have hwhole : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
            simp only [hnew, hwhole]
            have h0 : 0 ≤ q - c.workTapePos i := by omega
            have h1 : 0 ≤ q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ)) := by omega
            have hn : ¬ (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
              rw [length]; omega
            simp only [FinTM.bufferTape, h0, h1, if_true, List.getElem?_append, hn, if_false]
            rw [show (q - (c.workTapePos i + ((r * pat.length : ℕ) : ℤ))).toNat =
              (q - c.workTapePos i).toNat - (List.replicate r pat).flatten.length by
                rw [length]; omega]
            simp only [and_self, if_true]
          · simp only [hnew, if_false]
            by_cases hold : c.workTapePos i ≤ q ∧
                q < c.workTapePos i + ((r * pat.length : ℕ) : ℤ)
            · have hwhole : c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ)) := by omega
              have h0 : 0 ≤ q - c.workTapePos i := by omega
              have hn : (q - c.workTapePos i).toNat < (List.replicate r pat).flatten.length := by
                rw [length]; omega
              simp only [hold, hwhole, FinTM.bufferTape, h0, List.getElem?_append, hn, if_true]
            · have hwhole : ¬ (c.workTapePos i ≤ q ∧
                  q < c.workTapePos i + (((r * pat.length : ℕ) : ℤ) + (pat.length : ℤ))) := by omega
              simp only [hold, hwhole, if_false]
        · simp [finish, hj]
      · funext j
        by_cases hj : j = i
        · subst j
          simp [finish, Nat.add_mul, Nat.cast_add, add_assoc]
        · simp [finish, hj]
      · rfl
  have state (r : ℕ) : (counterLoopOrbit M τ c r).state = some 0 := by
    rw [orbit]; exact hc
  have rounds : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some 0 ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ 0 ∧ (none : Option (Fin (pat.length + 1))) ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some 0 := by
    intro r hr
    have spec := writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)
    refine ⟨state r, Nat.succ_pos _, ?_, state (r + 1)⟩
    intro u hu hut
    change u < pat.length + 1 at hut
    have live := MultiTapeTM.runFrom_state_ne_none_of_le M (counterLoopOrbit M τ c r)
      (pat.length + 1) (by rw [spec.1]; simp) u (by omega)
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp live
    refine ⟨s, hs, ?_, Option.noConfusion⟩
    intro he
    exact spec.2.1 u hu hut (hs.trans (congrArg some he))
  obtain ⟨he, hcut, hcounter, hbody⟩ := counterLoopTM_run_done M 0 none τ c w ct cp hw d hd
    rounds (d * (pat.length + 1) + counterOverhead w (d + 1)) (by simp [τ])
  refine ⟨?_, hcut, hcounter, ?_⟩
  · rw [orbit] at he
    exact he
  · intro t ht j
    obtain ⟨r, u, hr, heads⟩ := hbody t ht
    have spec := (writeAdvTM_run_ofCfg i pat (counterLoopOrbit M τ c r) (state r)).2.2
    have hu : u ≤ pat.length + 1 := by
      rcases hr with h | ⟨rfl, rfl⟩
      · exact h.2
      · omega
    have hh := spec j u hu
    rw [heads j]
    by_cases hj : j = i
    · subst j
      simp only [ite_true, orbit, finish, Function.update_self, Finset.mem_Icc] at hh ⊢
      rcases hr with ⟨hr, _⟩ | ⟨rfl, rfl⟩
      · have hrd : (r + 1) * pat.length ≤ d * pat.length := Nat.mul_le_mul_right _ hr
        rw [Nat.add_mul, Nat.one_mul] at hrd
        exact ⟨by omega, by omega⟩
      · simpa only [MultiTapeTM.runFrom_zero, Function.update_self, le_refl, and_true,
          le_add_iff_nonneg_right] using (Int.natCast_nonneg (r * pat.length))
    · simpa [hj, orbit, finish] using hh

end Turing
```

## ===== audits/evidence/s12-8/r80b-fill/CounterLoop.base.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Logic.Equiv.Bool
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Scan

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: counter-driven loops (§12.7)

The §12.7 increment of the machine-construction library
(`machine-library-design.md` §12.7): a loop whose number of rounds is a
little-endian binary counter **read from a tape**, running a body whose
state lives on **persistent, arbitrarily positioned tapes**. Every public
loop host of `Build/Loop.lean` instead runs a number of rounds fixed by the
input length, between canonical `Turing.Cfg.ofWords` seams. The consumers
are the two-tape uniform machine-code scheme (`Codes2Tape`), the EXPCOM
simulation, the nondeterministic time hierarchy (a fused countdown at
linear overhead) and the space hierarchy's configuration-count clock.

**Status: proved, except the §12.8 row.** All definitions are real and every
§12.7 contract is proved (§12.7 fill, `2e99bda1`; fill gate closed
2026-10-10). The §12.8 expansion row `Turing.expandTM_run_ofCfg` (R8.6) is a
statement, sorried with a proof sketch, pending the §12.8 fill.

## Design (decisions 12.7.1–12.7.6, user 2026-10-10)

* **Symbol transport** (`Turing.MultiTapeTM.mapWorkSymbols`). A machine
  conjugated by a permutation of the work-tape alphabet runs as the
  original, cell for cell, from every configuration. This is the generic
  route of decision 12.7.4, so the decrement proof never copies the
  increment proof.
* **C1, decrement** (`Turing.decrementTM`). It is defined as
  `Turing.incrementTM` conjugated by bit complement, and its framed
  contracts are the §12.6 increment contracts transported.
* **C2, the counter-driven host** (`Turing.counterLoopTM`). The body's `k`
  tapes are embedded by R1 along `Fin.castSucc`, and the counter is the
  dedicated last tape (12.7.1). Arriving at the anchor starts a decrement,
  and success re-enters the body at the anchor, with no dispatch steps.
  Underflow leaves through the live anchor `done`; reaching the optional
  designated body exit leaves through the live anchor `escape` (12.7.2).
  A consumer branches on the two exits with `Turing.seamCompTM`; with no
  exit (`none`), `escape` is unreachable.
* **Round cost** (12.7.3). Each round from body configuration `c` lasts
  the **exact** time `τ c`. A round-indexed cost is the special case of
  `τ` along the orbit, and a uniform bound is the corollary
  `Turing.counterLoop_time_le`.
* **Amortized time** (12.7.6). The total is stated exactly over the whole
  run. The decrements' share, `Turing.counterOverhead`, is at most four
  steps per round plus one sweep of the counter.

## Main definitions

* `Turing.MultiTapeTM.mapWorkSymbols` — conjugation by a work-tape symbol
  permutation, with `Turing.Action.mapWorkSymbols` and
  `Turing.Cfg.mapWorkSymbols`.
* `Turing.decFixed`, `Turing.decrementTM` — fixed-width decrement, as a
  word function and as a machine.
* `Turing.counterWord`, `Turing.counterOverhead` — the counter after `r`
  decrements, and the exact cost of the first `r` decrements, valid as a
  physical cost for `r ≤ value + 1` (the counter word freezes at zero,
  while the machine wraps).
* `Turing.CounterLoopState`, `Turing.counterLoopTM`,
  `Turing.counterLoopCfg`, `Turing.counterLoopOrbit` — the host, its
  configurations, and the body's round-start configurations.
* `Turing.expandTM` — the expansion (§12.8, R8.6): the counter loop whose
  round is the advancing writer `Turing.writeAdvTM`.

## Main results


* `Turing.MultiTapeTM.mapWorkSymbols_runFrom` — symbol transport.
* `Turing.decrementTM_run_succ_ofCfg`, `Turing.decrementTM_run_underflow_ofCfg`
  — the framed decrement contracts, in the §12.6 shape.
* `Turing.counterWord_length`, `Turing.counterWord_value`,
  `Turing.counterOverhead_le_of_le`, `Turing.counterOverhead_le` — counter
  arithmetic, including the amortized bound.
* `Turing.counterLoopTM_run_done`, `Turing.counterLoopTM_run_escape` — the
  host's exact whole-run contracts, with no earlier exit, the counter
  head's range, and the body heads' trajectory.
* `Turing.counterLoop_time_le` — the uniform per-round bound.
* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per
  counter unit, contiguously, at exact time (statement, §12.8).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1–§3.2 and §4.1: the hierarchy
  arguments run a universal machine for a bounded number of steps under a
  step counter; this file is that counter as a reusable machine.)

**Fill appendix (§12.7).** All ten contracts are proved. Decrement is transported from increment once; `counter_rounds` is the single
round induction used by both host contracts. Its final state is unrestricted,
so it covers returning prefixes and the last escaping round with the same
trajectory invariant. The amortization proofs use the audit's bit-count
potential, as recorded in their fill appendices.
-/

namespace Turing

section SymbolTransport

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the symbols an action writes on its work tapes along an
equivalence. Input movement, output and successor state are unchanged. -/
def Action.mapWorkSymbols (e : Symbol ≃ Symbol) (a : Action k Symbol State) :
    Action k Symbol State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output
  state := a.state

/-- Rename every work-tape cell of a configuration along an equivalence;
blank cells stay blank. -/
def Cfg.mapWorkSymbols {input : List Symbol} (e : Symbol ≃ Symbol)
    (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  { c with workTapes := fun j p => (c.workTapes j p).map e }

/-- Conjugate a machine by a work-tape symbol permutation: read the work
tapes through `e.symm` and write through `e`. The input tape and the output
are not renamed. -/
def MultiTapeTM.mapWorkSymbols (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) : MultiTapeTM k Symbol State where
  q₀ := M.q₀
  tr := fun q inp work => (M.tr q inp fun j => (work j).map e.symm).mapWorkSymbols e

/-- One step commutes with work-symbol conjugation, including writes into the frame.
**Proof sketch.** Inverse decoding cancels the equivalence at each read.
On the written cell the renamed update stores the renamed symbol; off that
cell the original tape is retained. The remaining configuration fields agree. -/
private lemma counter_work_step (M : MultiTapeTM k Symbol State) (e : Symbol ≃ Symbol)
    {input : List Symbol} (d : Cfg k Symbol State input) :
    (M.mapWorkSymbols e).step (d.mapWorkSymbols e) = (M.step d).mapWorkSymbols e := by
  cases hs : d.state with
  | none => simp [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
  | some s =>
    have reads : (fun j => ((d.workTapeSymbols j).map e).map e.symm) =
        d.workTapeSymbols := by
      funext j
      cases d.workTapeSymbols j <;> simp
    simp only [MultiTapeTM.step, Cfg.mapWorkSymbols, hs]
    change ((M.tr s d.inputSymbol (fun j =>
        ((d.workTapeSymbols j).map e).map e.symm)).mapWorkSymbols e).apply
        (d.mapWorkSymbols e) = _
    rw [reads]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Action.apply, Action.mapWorkSymbols, Cfg.mapWorkSymbols]
    cases hw : (M.tr s d.inputSymbol d.workTapeSymbols).workTapes j |>.1 with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      by_cases hp : p = d.workTapePos j
      · subst p; simp
      · simp [Function.update_of_ne hp]

/-- **Symbol transport** (design §12.7, decision 12.7.4). From every
configuration and at every time, the conjugated machine runs as the original
with every work-tape cell renamed.

**Proof sketch.** One step: the conjugate reads `e.symm (e s) = s`, so it
chooses the original's action; writing renamed symbols commutes with
`Function.update`; heads, input position, output and state are copied. Then
`Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem MultiTapeTM.mapWorkSymbols_runFrom (M : MultiTapeTM k Symbol State)
    (e : Symbol ≃ Symbol) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) :
    (M.mapWorkSymbols e).runFrom (c.mapWorkSymbols e) t =
      (M.runFrom c t).mapWorkSymbols e := by
  exact MultiTapeTM.runFrom_comm_of_step (fun d => d.mapWorkSymbols e)
    (counter_work_step M e) c t

end SymbolTransport

/-! ## C1 — decrement -/

/-- Little-endian fixed-width binary decrement with explicit underflow, the
mirror of `Turing.incFixed`: `decFixed w` is the predecessor word of the same
length, or `none` when `w` is all `false`, that is, has value zero. Width zero
underflows immediately. -/
def decFixed : List Bool → Option (List Bool)
  | [] => none
  | true :: rest => some (false :: rest)
  | false :: rest => (decFixed rest).map (true :: ·)

/-- Complement exchanges the word-level carry and borrow recursions. -/
private lemma counter_dec_complement (w : List Bool) :
    decFixed w = (incFixed (w.map not)).map (List.map not) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [decFixed, incFixed, ih, List.map_map, Function.comp_def]

/-- Complementing work cells twice restores an arbitrary configuration. -/
private lemma counter_complement_twice {k : ℕ} {S : Type} {x : List Bool}
    (d : Cfg k Bool S x) :
    (d.mapWorkSymbols Equiv.boolNot).mapWorkSymbols Equiv.boolNot = d := by
  apply Cfg.ext <;> try rfl
  funext j p
  simp [Cfg.mapWorkSymbols, Option.map_map, Function.comp_def]

/-- Complementation of a buffered word preserves its blank delimiters. -/
private lemma counter_buffer_complement (w : List Bool) (p : ℤ) :
    FinTM.bufferTape (w.map not) p = (FinTM.bufferTape w p).map not := by
  by_cases hp : 0 ≤ p <;> simp [FinTM.bufferTape, hp]

/-- **R3, decrement** (design §12.7, C1). In-place little-endian fixed-width
binary decrement on tape `i`. The borrow pass flips `false` cells to `true`
moving right. The first `true` flips to `false` and selects the success
verdict. Running off the width (all `false`, value zero) selects the
underflow verdict, leaving the wrapped all-`true` word. The return pass
carries the verdict to the live `done` anchor at the origin.

It is defined as `Turing.incrementTM` conjugated by bit complement, so its
contracts are the increment's, transported by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`. -/
def decrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase :=
  (incrementTM k i).mapWorkSymbols Equiv.boolNot

/-- Every decrement run is one complemented increment run, including its frame. -/
private lemma counter_decrement_run {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool FlagPhase x) (t : ℕ) :
    (decrementTM k i).runFrom d t =
      ((incrementTM k i).runFrom (d.mapWorkSymbols Equiv.boolNot) t).mapWorkSymbols
        Equiv.boolNot := by
  simpa only [decrementTM, counter_complement_twice] using
    (incrementTM k i).mapWorkSymbols_runFrom Equiv.boolNot
      (d.mapWorkSymbols Equiv.boolNot) t

/-- **Decrement, framed success with exact borrow cost** (design §12.7, C1;
the mirror of `Turing.incrementTM_run_succ_ofCfg`). Let the delimited word `w`
on tape `i` have a predecessor at its width, `decFixed w = some v`, and let
`q = (w.takeWhile not).length` be its number of leading `false` cells. Then
the routine reaches the success anchor at exactly `2q + 2` and not earlier,
with the word interval holding `v` and everything else unchanged. Up to the
exit the head stays within `[pos - 1, pos + q]`.

**Proof sketch.** Complement the configuration's work tapes. The result
carries `w.map not`, whose successor is `v.map not` (`decFixed` is `incFixed`
conjugated by `not`) and whose `true` prefix has length `q`. Apply
`Turing.incrementTM_run_succ_ofCfg`, transport back by
`Turing.MultiTapeTM.mapWorkSymbols_runFrom`, and use that complementing
twice is the identity and that `FinTM.bufferTape` commutes with `map not`. -/
theorem decrementTM_run_succ_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w v : List Bool) (hv : decFixed w = some v) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * (w.takeWhile not).length + 2) =
        { d with
          state := some (FlagPhase.done true)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape v (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * (w.takeWhile not).length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * (w.takeWhile not).length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1)
              (d.workTapePos j + ((w.takeWhile not).length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = some (v.map not) := by
    have h := congrArg (Option.map (List.map not)) hv
    simpa [counter_dec_complement, Option.map_map, List.map_map, Function.comp_def] using h
  have hf : ∀ p : ℤ, -1 ≤ p → p ≤ ((w.map not).length : ℤ) →
      (d.mapWorkSymbols Equiv.boolNot).workTapes i
        ((d.mapWorkSymbols Equiv.boolNot).workTapePos i + p) =
          FinTM.bufferTape (w.map not) p := by
    intro p hl hr
    simpa [Cfg.mapWorkSymbols, counter_buffer_complement] using
      congrArg (Option.map not) (hw p hl (by simpa using hr))
  have hp : ((w.map not).takeWhile id).length = (w.takeWhile not).length := by
    simp [List.takeWhile_map, Function.comp_def]
  obtain ⟨he, hc, hh⟩ := incrementTM_run_succ_ofCfg i (w.map not) (v.map not)
    hv' (d.mapWorkSymbols Equiv.boolNot) hstate hf
  rw [hp] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    simp only [Cfg.mapWorkSymbols, List.length_map]
    split_ifs <;> simp [counter_buffer_complement, Option.map_map, Function.comp_def]
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hc
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-- **Decrement, framed underflow** (design §12.7, C1; the mirror of
`Turing.incrementTM_run_overflow_ofCfg`). If the delimited word `w` on tape
`i` has no predecessor at its width (`decFixed w = none`, that is, it is all
`false`), the routine reaches the underflow anchor at exactly `2|w| + 2` and
not earlier. The word interval then holds `|w|` copies of `true`, and
everything else is unchanged. Up to the exit the head stays within
`[pos - 1, pos + |w|]`.

**Proof sketch.** As the success case, through
`Turing.incrementTM_run_overflow_ofCfg`: the complemented word is all `true`,
so `incFixed` overflows, and the wrapped all-`false` word complements back to
all `true`. -/
theorem decrementTM_run_underflow_ofCfg {k : ℕ} {x : List Bool} (i : Fin k)
    (w : List Bool) (hv : decFixed w = none) (d : Cfg k Bool FlagPhase x)
    (hstate : d.state = some FlagPhase.run)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p) :
    (decrementTM k i).runFrom d (2 * w.length + 2) =
        { d with
          state := some (FlagPhase.done false)
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
              then FinTM.bufferTape (List.replicate w.length true) (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w.length + 2, ∀ b : Bool,
        ((decrementTM k i).runFrom d t).state ≠ some (FlagPhase.done b)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w.length + 2 →
        if j = i then
          ((decrementTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (w.length : ℤ))
        else ((decrementTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  have hv' : incFixed (w.map not) = none := by
    simpa only [counter_dec_complement, Option.map_eq_none_iff] using hv
  obtain ⟨he, hc, hh⟩ := incrementTM_run_overflow_ofCfg i (w.map not) hv'
    (d.mapWorkSymbols Equiv.boolNot) hstate (by
      intro p hl hr
      change (d.workTapes i (d.workTapePos i + p)).map Equiv.boolNot = _
      rw [hw p hl (by simpa using hr), counter_buffer_complement]
      rfl)
  simp only [List.length_map] at he hc hh
  refine ⟨?_, ?_, ?_⟩
  · rw [counter_decrement_run, he]
    apply Cfg.ext <;> try rfl
    funext j p
    have hb := counter_buffer_complement (List.replicate w.length false)
      (p - d.workTapePos j)
    simp only [Cfg.mapWorkSymbols]
    split_ifs
    · simpa using hb.symm
    · simp [Option.map_map, Function.comp_def]
  · intro t ht b
    exact (hc t ht b) ∘ (by simp only [counter_decrement_run, Cfg.mapWorkSymbols]; exact id)
  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh

/-! ## Counter arithmetic -/

/-- The counter word after `r` decrements. A decrement at value zero leaves
the word unchanged here; the machine's underflow wrap is stated in the host
contract. -/
def counterWord (w : List Bool) (r : ℕ) : List Bool :=
  (fun u => (decFixed u).getD u)^[r] w

/-- The cost sum of the first `r` decrements along the frozen word orbit
`Turing.counterWord`: the decrement of the word `u` costs
`2 * (u.takeWhile not).length + 2`, which is also the underflow cost
`2|u| + 2` when `u` is all `false`. Because `counterWord` freezes at value
zero while the machine wraps on underflow, the sum equals the physical
countdown's cost only through its first underflow, that is for
`r ≤ value + 1`. That range covers every use in this file (§12.7 statement
gate, SC-1). -/
def counterOverhead (w : List Bool) (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, (2 * ((counterWord w j).takeWhile not).length + 2)

/-- A borrow either detects an all-false word or preserves width, subtracts one,
and changes the true-bit potential by its false-prefix length.
**Proof sketch.** Induct on the word. A true low bit stops the borrow; a false
low bit propagates it and gains one true bit. -/
private lemma counter_dec_spec (w : List Bool) :
    match decFixed w with
    | none => w = List.replicate w.length false
    | some v => v.length = w.length ∧
        Nat.ofDigits 2 (w.map Bool.toNat) = Nat.ofDigits 2 (v.map Bool.toNat) + 1 ∧
        v.count true + 1 = w.count true + (w.takeWhile not).length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true => simp [decFixed, Nat.ofDigits_cons, Nat.add_comm]
    | false =>
      cases hd : decFixed w with
      | none =>
        simp only [hd] at ih
        simpa [decFixed, hd, List.replicate_succ] using congrArg (false :: ·) ih
      | some v =>
        simp only [hd] at ih
        rcases ih with ⟨hl, hv, hc⟩
        simp [decFixed, hd, Nat.ofDigits_cons, hl]
        omega

/-- The next frozen counter word is obtained by one optional decrement. -/
private lemma counter_word_succ (w : List Bool) (r : ℕ) :
    counterWord w (r + 1) = (decFixed (counterWord w r)).getD (counterWord w r) :=
  Function.iterate_succ_apply' _ _ _

/-- Underflow occurs exactly at binary value zero, including padded words. -/
private lemma counter_dec_zero (w : List Bool) :
    decFixed w = none ↔ Nat.ofDigits 2 (w.map Bool.toNat) = 0 := by
  have hs := counter_dec_spec w
  cases hd : decFixed w with
  | none =>
    simp only [hd] at hs
    simp only [true_iff]
    conv_lhs => rw [hs]
    simp
  | some v =>
    simp only [hd] at hs
    simp only [reduceCtorEq, false_iff]
    omega

/-- Decrements preserve the counter's width.

**Proof sketch.** `decFixed` preserves length, by induction on the word, and
`Option.getD` keeps the word otherwise; induct on `r`. -/
theorem counterWord_length (w : List Bool) (r : ℕ) :
    (counterWord w r).length = w.length := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [counter_word_succ]
    have hs := counter_dec_spec (counterWord w r)
    cases hd : decFixed (counterWord w r) with
    | none => simpa [hd] using ih
    | some v =>
      rw [hd] at hs
      simpa [hd] using hs.1.trans ih

/-- Each of the first `value w` decrements lowers the little-endian value by
one.

**Proof sketch.** For a word of positive value, `decFixed` succeeds and its
result has value one less, by induction on the word: a leading `true`
loses weight one, and a leading `false` borrows from the rest with weight
two. Induct on `r`. -/
theorem counterWord_value (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    Nat.ofDigits 2 ((counterWord w r).map Bool.toNat) =
      Nat.ofDigits 2 (w.map Bool.toNat) - r := by
  induction r with
  | zero => simp [counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_succ]
    cases hb : decFixed (counterWord w r) with
    | none =>
      have hz := (counter_dec_zero _).mp hb
      omega
    | some v =>
      simp only [hb] at hs
      simp only [Option.getD_some]
      omega

/-- Before exhaustion, the physical predecessor is the next frozen word. -/
private lemma counter_word_decrement (w : List Bool) (r : ℕ)
    (hr : r < Nat.ofDigits 2 (w.map Bool.toNat)) :
    decFixed (counterWord w r) = some (counterWord w (r + 1)) := by
  have hv := counterWord_value w r (by omega)
  rw [counter_word_succ]
  cases hd : decFixed (counterWord w r) with
  | none => have hz := (counter_dec_zero _).mp hd; omega
  | some v => rfl

/-- Successful borrow costs telescope against twice the number of true bits.
**Proof sketch.** At each step the borrow specification equates the new
potential plus four with the old potential plus the exact decrement cost.
Add this equality to the induction hypothesis. -/
private lemma counter_potential (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r + 2 * w.count true =
      4 * r + 2 * (counterWord w r).count true := by
  induction r with
  | zero => simp [counterOverhead, counterWord]
  | succ r ih =>
    have hi := ih (by omega)
    have hs := counter_dec_spec (counterWord w r)
    rw [counter_word_decrement w r (by omega)] at hs
    simp only [counterOverhead, Finset.sum_range_succ]
    change (counterOverhead w r + (2 * (List.takeWhile not (counterWord w r)).length + 2)) +
      2 * w.count true = 4 * (r + 1) + 2 * (counterWord w (r + 1)).count true
    omega

/-- **Prefix amortization.** The first `r` decrements, for `r` at most the
counter's value, cost at most `4r + 2|w|`.

**Proof sketch.** The `j`th decrement acts on a word of value `n - j`
(`Turing.counterWord_value`), where `n` is the counter's value, and its
`false` prefix is the number of trailing zero bits of that value. Summed over
`r` consecutive values below `2^|w|`, the trailing zeros total
`ν₂(r!) + ν₂(binom) ≤ (r - 1) + (|w| - 1)` by Legendre and Kummer, so the
cost is at most `4r + 2|w| - 4` once `r ≥ 1`.

**Fill proof appendix.** The binding statement-gate route replaces the
number-theoretic sketch above by the exact telescoping identity proved in
`counter_potential`. Twice the count of true bits is the potential; its
terminal value is bounded by twice the preserved word length. -/
theorem counterOverhead_le_of_le (w : List Bool) (r : ℕ)
    (hr : r ≤ Nat.ofDigits 2 (w.map Bool.toNat)) :
    counterOverhead w r ≤ 4 * r + 2 * w.length := by
  have hp := counter_potential w r hr
  have hc : (counterWord w r).count true ≤ w.length :=
    (List.count_le_length).trans_eq (counterWord_length w r)
  omega

/-- At exhaustion the fixed-width word is all false, retaining any padding. -/
private lemma counter_word_exhausted (w : List Bool) :
    counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)) =
      List.replicate w.length false := by
  have hz := counterWord_value w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  simp only [Nat.sub_self] at hz
  have hs := counter_dec_spec (counterWord w (Nat.ofDigits 2 (w.map Bool.toNat)))
  rw [(counter_dec_zero _).mpr hz] at hs
  simpa only [counterWord_length] using hs

/-- **Whole-run amortization** (design §12.7, decision 12.7.6). Counting a
counter of value `n` down to zero and through the final underflow costs at
most `4n + 2|w| + 2`.

**Proof sketch.** The successful decrements act on the values `n, …, 1`,
whose trailing zeros sum to `n - s₂(n) ≤ n` (Legendre), so they cost at most
`4n`. The final word is all `false` (`Turing.counterWord_value`), so the
underflow sweep costs `2|w| + 2` (`Turing.counterWord_length`).

**Fill proof appendix.** Use `counter_potential` at exhaustion, where the
remaining true-bit count is zero, then add the full underflow sweep.
No Legendre or Kummer theorem is used. -/
theorem counterOverhead_le (w : List Bool) :
    counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) ≤
      4 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2 := by
  have hp := counter_potential w (Nat.ofDigits 2 (w.map Bool.toNat)) le_rfl
  rw [counter_word_exhausted] at hp
  simp [List.count_replicate] at hp
  have hs : counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat) + 1) =
      counterOverhead w (Nat.ofDigits 2 (w.map Bool.toNat)) + (2 * w.length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, counter_word_exhausted]
  omega

/-! ## C2 — the counter-driven host -/

/-- Control of the counter-driven host (design §12.7, C2): a body state, a
decrement phase, or one of the two live exit anchors. -/
inductive CounterLoopState (S : Type) where
  /-- running the body -/
  | body (s : S)
  /-- running the decrement on the counter tape -/
  | dec (f : FlagPhase)
  /-- the live exit anchor after the counter underflows -/
  | done
  /-- the live exit anchor after the body reaches its designated exit -/
  | escape
deriving DecidableEq

instance counterLoopStateFintype (S : Type) [Fintype S] :
    Fintype (CounterLoopState S) := derive_fintype% _

/-- Where a body transition lands in the host. Arriving at the anchor `a`
starts the next decrement; arriving at the designated exit leaves through
`escape`; every other body state is kept. -/
def counterLoopRedirect {S : Type} [DecidableEq S] (a : S) (exit : Option S)
    (s : S) : CounterLoopState S :=
  if s = a then .dec .run else if exit = some s then .escape else .body s

/-- Where a decrement transition lands in the host. The success anchor
re-enters the body at `a`, the underflow anchor is the host's `done`, and the
working phases are kept. -/
def counterLoopDecExit {S : Type} (a : S) : FlagPhase → CounterLoopState S
  | .done true => .body a
  | .done false => .done
  | f => .dec f

/-- **C2, the counter-driven loop host** (design §12.7). The body `M` runs on
the first `k` tapes, embedded by `Turing.embedEmitTM` along `Fin.castSucc`
with its emissions forwarded, and the counter is the last tape. The host
starts with a decrement. Each successful decrement re-enters the body at the
anchor `a`, and each arrival at `a` starts the next decrement, with no
dispatch steps in between. Underflow leaves through the live anchor `done`;
reaching the optional exit leaves through the live anchor `escape`. Both
anchors are stationary. -/
def counterLoopTM {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) : MultiTapeTM (k + 1) Bool (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((decrementTM (k + 1) (Fin.last k)).tr f inp work).mapState (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- A host configuration with host state `q`: the body configuration `c` on
the first `k` tapes (its own state field is ignored), the counter tape `ct`
with its head at `cp` as the last tape, and the body's output as the host's
output. It is the R1 transport `Turing.embedEmitCfg` along `Fin.castSucc`,
with the counter as the ambient frame. -/
def counterLoopCfg {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) : Cfg (k + 1) Bool (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- The body configurations at the starts of successive rounds: round `r`
starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`
steps. -/
def counterLoopOrbit {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) : Cfg k Bool S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-! ### Shared phase and prefix invariants -/

/-- The last tape is outside the forwarding embedding's selected bank. -/
private lemma counter_last_unselected (k : ℕ) :
    Fin.last k ∉ Set.range (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

/-- **The counter-loop host layout** (design §12.7; public since the §12.8 fill): the
host configuration is the body bank followed by its counter tape.

**Proof sketch.** The body tapes are R1's selected tapes (`Turing.embedEmitCfg_selected_tape`,
`_pos`); the counter tape is its frame (`Turing.embedEmitTM_frame` at time `0`). -/
theorem counter_cfg_eq {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Bool Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (counter_last_unselected k)
  apply Cfg.ext <;> try rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.1
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfg, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.2
    · simpa only [counterLoopCfg, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i

/-- Injective successor redirection for the decrement's five controls. -/
private lemma counter_dec_injective {S : Type} (a : S) :
    Function.Injective (counterLoopDecExit a) := by
  intro f g h
  cases f <;> cases g <;> (try casesm* Bool) <;> simp_all [counterLoopDecExit]

/-- Anchor priority still gives an injective body-state redirection. -/
private lemma counter_redirect_injective {S : Type} [DecidableEq S]
    (a : S) (exit : Option S) : Function.Injective (counterLoopRedirect a exit) := by
  intro s t h
  by_cases hs : s = a
  · subst s
    by_cases ht : t = a
    · exact ht.symm
    · simp only [counterLoopRedirect, ht, if_false] at h
      split_ifs at h
  · by_cases ht : t = a
    · subst t; simp only [counterLoopRedirect, hs, if_false] at h
      split_ifs at h
    · simp only [counterLoopRedirect, hs, ht, if_false] at h
      split_ifs at h <;> simp_all

/-- Common trajectory data for a finite host segment, with a chosen set of
permitted body-head vectors. -/
private def counterSpan {k : ℕ} {S : Type} {x : List Bool}
    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) (cp : ℤ) (width : ℕ)
    (R : (Fin k → ℤ) → Prop) : Prop :=
  (∀ u < t, (H.runFrom z u).state ≠ some .done ∧
    (H.runFrom z u).state ≠ some .escape) ∧
  (∀ u ≤ t, (H.runFrom z u).workTapePos (Fin.last k) ∈
    Finset.Icc (cp - 1) (cp + (width : ℤ))) ∧
  (∀ u ≤ t, R (fun j => (H.runFrom z u).workTapePos j.castSucc))

/-- Adjacent segments concatenate their cuts and trajectory bounds.
**Proof sketch.** Split a queried time at the first segment's length and
use run addition on the suffix. The two head-vector relations imply the
requested relation separately. -/
private lemma counter_span_append {k : ℕ} {S : Type} {x : List Bool}
    (H : MultiTapeTM (k + 1) Bool (CounterLoopState S))
    (z : Cfg (k + 1) Bool (CounterLoopState S) x) (s t : ℕ) (cp : ℤ) (width : ℕ)
    (R₁ R₂ R : (Fin k → ℤ) → Prop)
    (h₁ : counterSpan H z s cp width R₁)
    (h₂ : counterSpan H (H.runFrom z s) t cp width R₂)
    (hr₁ : ∀ p, R₁ p → R p) (hr₂ : ∀ p, R₂ p → R p) :
    counterSpan H z (s + t) cp width R := by
  have suffix (u : ℕ) (hu : s ≤ u) :
      H.runFrom z u = H.runFrom (H.runFrom z s) (u - s) := by
    rw [← H.runFrom_add, Nat.add_sub_of_le hu]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    by_cases hs : u < s
    · exact h₁.1 u hs
    · rw [suffix u (by omega)]; exact h₂.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact h₁.2.1 u hs
    · rw [suffix u (by omega)]; exact h₂.2.1 (u - s) (by omega)
  · intro u hu
    by_cases hs : u ≤ s
    · exact hr₁ _ (h₁.2.2 u hs)
    · rw [suffix u (by omega)]; exact hr₂ _ (h₂.2.2 (u - s) (by omega))

/-- A width-preserving overwrite of just the counter word interval. -/
private def counterPatch (ct : ℤ → Option Bool) (cp : ℤ) (w : List Bool) : ℤ → Option Bool :=
  fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
    then FinTM.bufferTape w (q - cp) else ct q

/-- Patching the word that is already present changes no cell. -/
private lemma counter_patch_initial (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) : counterPatch ct cp w = ct := by
  funext q
  apply ite_eq_right_iff.mpr
  intro h
  have hf := hw (q - cp) (by omega) (by omega)
  simpa using hf.symm

/-- Equal-width patches overwrite the same interval, preserving the original frame. -/
private lemma counter_patch_twice (ct : ℤ → Option Bool) (cp : ℤ) (u v : List Bool)
    (hv : v.length = u.length) :
    counterPatch (counterPatch ct cp u) cp v = counterPatch ct cp v := by
  funext q
  simp only [counterPatch, hv]
  split_ifs <;> rfl

/-- Replacing a framed word by an equal-width word keeps both blank delimiters. -/
private lemma counter_patch_frame (w v : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hv : v.length = w.length)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (v.length : ℤ) →
      counterPatch ct cp v (cp + p) = FinTM.bufferTape v p := by
  intro p hl hr
  by_cases h : 0 ≤ p ∧ p < (v.length : ℤ)
  · simp [counterPatch, show cp ≤ cp + p ∧ cp + p < cp + (v.length : ℤ) by omega]
  · have hp : p = -1 ∨ p = (v.length : ℤ) := by omega
    rcases hp with rfl | rfl
    · simp [counterPatch, hw (-1) (by omega) (by omega), FinTM.bufferTape_left]
    · simp [counterPatch, hv, hw w.length (by omega) le_rfl, FinTM.bufferTape_nat]

/-- A decrement phase uses the proved framed contract and guarded state transport.
**Proof sketch.** Select success or underflow from the word function. The
host agrees with the decrement on every pre-verdict control, so the single
injective transport carries its endpoint, first-verdict cut, and head bounds. -/
private lemma counter_debit {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (c : Cfg k Bool S x) (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape w p) :
    let cost := 2 * (w.takeWhile not).length + 2
    let v := (decFixed w).getD (List.replicate w.length true)
    let q : CounterLoopState S := if (decFixed w).isSome then .body a else .done
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) cost =
      counterLoopCfg (some q) c (counterPatch ct cp v) cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      cost cp w.length (fun p => ∀ j, p j = c.workTapePos j) := by
  let z : Cfg (k + 1) Bool FlagPhase x :=
    (counterLoopCfg (some (.dec .run)) c ct cp).mapState (fun _ => FlagPhase.run)
  let v := (decFixed w).getD (List.replicate w.length true)
  let cost := 2 * (w.takeWhile not).length + 2
  have hz : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      z.workTapes (Fin.last k) (z.workTapePos (Fin.last k) + p) = FinTM.bufferTape w p := by
    simpa [z, Cfg.mapState, counter_cfg_eq] using hw
  have spec :
      (decrementTM (k + 1) (Fin.last k)).runFrom z cost =
        {z with state := some (.done (decFixed w).isSome), workTapes := fun j p =>
          if j = Fin.last k ∧ z.workTapePos j ≤ p ∧ p < z.workTapePos j + (w.length : ℤ)
          then FinTM.bufferTape v (p - z.workTapePos j) else z.workTapes j p} ∧
      (∀ t < cost, ∀ b, ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state ≠
        some (.done b)) ∧
      (∀ j t, t ≤ cost → if j = Fin.last k then
        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j ∈
          Finset.Icc (z.workTapePos j - 1) (z.workTapePos j + (w.length : ℤ))
        else ((decrementTM (k + 1) (Fin.last k)).runFrom z t).workTapePos j = z.workTapePos j) := by
    cases hd : decFixed w with
    | none =>
      have hs := counter_dec_spec w
      rw [hd] at hs
      have hp : (w.takeWhile not).length = w.length := by
        conv_lhs => rw [hs]
        simp
      simpa [cost, v, hd, hp] using decrementTM_run_underflow_ofCfg (Fin.last k) w hd z rfl hz
    | some u =>
      obtain ⟨he, hc, hh⟩ := decrementTM_run_succ_ofCfg (Fin.last k) w u hd z rfl hz
      refine ⟨by simpa [v, hd] using he, hc, ?_⟩
      intro j t ht
      have h := hh j t ht
      split_ifs at h ⊢ with hj
      · simp only [Finset.mem_Icc] at h ⊢
        have hlen := (List.takeWhile_sublist (p := not) (l := w)).length_le
        exact ⟨h.1, by omega⟩
      · exact h
  let emb : FlagPhase ↪ CounterLoopState S := ⟨counterLoopDecExit a, counter_dec_injective a⟩
  have run (t : ℕ) (ht : t ≤ cost) :
      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t =
        ((decrementTM (k + 1) (Fin.last k)).runFrom z t).mapState emb := by
    refine MultiTapeTM.runFrom_mapState_of_agreeOn
      (decrementTM (k + 1) (Fin.last k)) (counterLoopTM M a exit) emb
      (fun f => ∀ b, f ≠ .done b) ?_ z t ?_
    · intro f hf inp work
      cases f with
      | run => rfl
      | rewind b => rfl
      | done b => exact False.elim (hf b rfl)
    · intro u hu f hf b he
      exact spec.2.1 u (by omega) b (hf.trans (congrArg some he))
  have vl : v.length = w.length := by
    have hs := counter_dec_spec w
    cases hd : decFixed w <;> simp [v, hd] at *
    exact hs.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [run cost le_rfl, spec.1]
    apply Cfg.ext <;> try rfl
    · cases hd : decFixed w <;> simp [Cfg.mapState, emb, counterLoopDecExit, counterLoopCfg]
    · funext j p
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [z, Cfg.mapState, counter_cfg_eq, Fin.lastCases_last,
          true_and, counterPatch]
        change _ = if cp ≤ p ∧ p < cp + (v.length : ℤ) then FinTM.bufferTape v (p - cp) else ct p
        rw [vl]
      · simp [z, Cfg.mapState, counter_cfg_eq, Fin.castSucc_ne_last]
  · intro t ht
    rw [run t (by omega)]
    have hc := spec.2.1 t ht
    cases hs : ((decrementTM (k + 1) (Fin.last k)).runFrom z t).state with
    | none => simp [Cfg.mapState, hs]
    | some f =>
      cases f with
      | run => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
      | rewind b => simp [Cfg.mapState, hs, emb, counterLoopDecExit]
      | done b => exact False.elim (hc b hs)
  · intro t ht
    rw [run t ht]
    simpa [Cfg.mapState, z, counter_cfg_eq] using spec.2.2 (Fin.last k) t ht
  · intro t ht j
    rw [run t ht]
    simpa [Cfg.mapState, z, counter_cfg_eq, Fin.castSucc_ne_last] using
      spec.2.2 j.castSucc t ht

/-- The body phase executes its entry action once, then uses guarded transport.
**Proof sketch.** The entry action reads the forwarding embedding. After that
step, all strict intermediate states avoid both redirections, and the RB5
transport lemma applies. R1 identifies every transported configuration and
therefore preserves the counter frame and all body-head trajectories. -/
private lemma counter_body {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) (width t : ℕ)
    (hc : c.state = some a) (ht : 0 < t)
    (hmid : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧
      s ≠ a ∧ exit ≠ some s) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) t =
      counterLoopCfg ((M.runFrom c t).state.map (counterLoopRedirect a exit))
        (M.runFrom c t) ct cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.body a)) c ct cp)
      t cp width (fun p => ∃ u ≤ t, ∀ j, p j = (M.runFrom c u).workTapePos j) := by
  let E := embedEmitTM Fin.castSuccEmb M
  let ec := embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c
  let emb : S ↪ CounterLoopState S :=
    ⟨counterLoopRedirect a exit, counter_redirect_injective a exit⟩
  have first : (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) 1 =
      (E.runFrom ec 1).mapState emb := by
    change (counterLoopTM M a exit).step (counterLoopCfg (some (.body a)) c ct cp) =
      (E.step ec).mapState emb
    have hec : ec.state = some a := hc
    simp only [MultiTapeTM.step, hec, counterLoopCfg, Cfg.mapState]
    rfl
  have run (u : ℕ) (hu : 0 < u) (hut : u ≤ t) :
      (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.body a)) c ct cp) u =
        counterLoopCfg ((M.runFrom c u).state.map (counterLoopRedirect a exit))
          (M.runFrom c u) ct cp := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    rw [Nat.succ_eq_add_one, Nat.add_comm n 1, MultiTapeTM.runFrom_add, first]
    have tr := MultiTapeTM.runFrom_mapState_of_agreeOn E (counterLoopTM M a exit) emb
      (fun s => s ≠ a ∧ exit ≠ some s)
      (by intro s hs inp work; simp [emb, counterLoopRedirect, hs.1, hs.2, counterLoopTM, E])
      (E.runFrom ec 1) n (by
        intro v hv s hs
        have he := embedEmitTM_runFrom Fin.castSuccEmb M (fun _ => ct) (fun _ => cp) [] c (1 + v)
        change E.runFrom ec (1 + v) = _ at he
        rw [MultiTapeTM.runFrom_add] at he
        have hstate := congrArg Cfg.state he
        change (E.runFrom (E.runFrom ec 1) v).state = (M.runFrom c (1 + v)).state at hstate
        obtain ⟨s', hs', ha, hx⟩ := hmid (1 + v) (by omega) (by omega)
        have eqs : s = s' := Option.some.inj (hs.symm.trans (hstate.trans hs'))
        simpa [eqs] using And.intro ha hx)
    rw [tr, ← MultiTapeTM.runFrom_add]
    change (E.runFrom ec (1 + n)).mapState emb = _
    rw [show E.runFrom ec (1 + n) =
      embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] (M.runFrom c (1 + n)) from
      embedEmitTM_runFrom Fin.castSuccEmb M _ _ [] c (1 + n)]
    rfl
  refine ⟨run t ht le_rfl, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counterLoopCfg]
    · rw [run u (by omega) (by omega)]
      obtain ⟨s, hs, ha, hx⟩ := hmid u (by omega) hu
      simp [counterLoopCfg, hs, counterLoopRedirect, ha, hx]
  · intro u hu
    by_cases hz : u = 0
    · subst u; simp [counter_cfg_eq, Finset.mem_Icc]
    · rw [run u (by omega) hu]
      simp [counter_cfg_eq, Finset.mem_Icc]
  · intro u hu
    refine ⟨u, hu, ?_⟩
    by_cases hz : u = 0
    · subst u; simp [counter_cfg_eq]
    · rw [run u (by omega) hu]
      simp [counter_cfg_eq]

/-- An orbit successor is the completed current body round. -/
private lemma counter_orbit_succ {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) :
    counterLoopOrbit M τ c (r + 1) =
      M.runFrom (counterLoopOrbit M τ c r) (τ (counterLoopOrbit M τ c r)) :=
  Function.iterate_succ_apply' _ _ _

/-- The shared round invariant, with the final body state left unrestricted.
Returning prefixes are exactly the configurations before the next decrement.
**Proof sketch.** Induct once on the number of rounds. The current word has
positive value, so the framed decrement succeeds. Append its transported
segment and the forwarding body segment. Equal-width overwrites keep the
original counter frame, and the two cost recurrences give the exact elapsed
time. Earlier starts at the anchor supply all returns needed by the induction. -/
private lemma counter_rounds {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (n : ℕ) (hn : n ≤ Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r < n, (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s)) :
    let elapsed := ∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r) + counterOverhead w n
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) elapsed =
      counterLoopCfg (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit))
        (counterLoopOrbit M τ c n) (counterPatch ct cp (counterWord w n)) cp ∧
    counterSpan (counterLoopTM M a exit) (counterLoopCfg (some (.dec .run)) c ct cp)
      elapsed cp w.length (fun p => ∃ r u,
        ((r < n ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = n ∧ u = 0)) ∧
        ∀ j, p j = (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, counterOverhead, Finset.sum_empty,
      Nat.zero_add, MultiTapeTM.runFrom_zero, ite_true]
    have hpatch : counterPatch ct cp (counterWord w 0) = ct := counter_patch_initial w ct cp hw
    rw [hpatch]
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro u hu; omega
    · intro u hu; have hz : u = 0 := by omega
      subst u; simp [counter_cfg_eq, Finset.mem_Icc]
    · intro u hu; have hz : u = 0 := by omega
      subst u
      exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩, by simp [counter_cfg_eq, counterLoopOrbit]⟩
  | succ n ih =>
    obtain ⟨before, span⟩ := ih (by omega) (fun r hr => hround r (by omega))
    obtain ⟨ha, ht, hg⟩ := hround n (by omega)
    have control : (if n = 0 then some (.dec .run) else
        (counterLoopOrbit M τ c n).state.map (counterLoopRedirect a exit)) =
        some (CounterLoopState.dec FlagPhase.run) := by
      split_ifs <;> simp [ha, counterLoopRedirect]
    rw [control] at before
    let cn := counterLoopOrbit M τ c n
    let wn := counterWord w n
    let pn := counterPatch ct cp wn
    let nextTape := counterPatch ct cp (counterWord w (n + 1))
    let cost := 2 * (wn.takeWhile not).length + 2
    have hd := counter_word_decrement w n (by omega)
    have hf := counter_patch_frame w wn ct cp (counterWord_length w n) hw
    obtain ⟨debit, ds⟩ := counter_debit M a exit cn wn pn cp hf
    change decFixed wn = some (counterWord w (n + 1)) at hd
    simp only [hd, Option.getD_some, Option.isSome_some, ite_true] at debit
    rw [counter_patch_twice ct cp wn (counterWord w (n + 1))
      (by simp only [wn, counterWord_length])] at debit
    obtain ⟨body, bs⟩ := counter_body M a exit cn nextTape cp w.length (τ cn) ha ht hg
    have round : (counterLoopTM M a exit).runFrom
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) =
        counterLoopCfg ((counterLoopOrbit M τ c (n + 1)).state.map (counterLoopRedirect a exit))
          (counterLoopOrbit M τ c (n + 1)) nextTape cp := by
      rw [MultiTapeTM.runFrom_add, debit, body, counter_orbit_succ]
    have rs : counterSpan (counterLoopTM M a exit)
        (counterLoopCfg (some (.dec .run)) cn pn cp) (cost + τ cn) cp w.length
        (fun p => ∃ u ≤ τ cn, ∀ j, p j = (M.runFrom cn u).workTapePos j) := by
      apply counter_span_append _ _ cost (τ cn) cp w.length _ _ _
        (by simpa only [wn, counterWord_length] using ds) (by rw [debit]; exact bs)
      · intro p hp; exact ⟨0, Nat.zero_le _, by simpa using hp⟩
      · exact fun _ h => h
    have time : (∑ r ∈ Finset.range (n + 1), τ (counterLoopOrbit M τ c r)) +
        counterOverhead w (n + 1) =
        ((∑ r ∈ Finset.range n, τ (counterLoopOrbit M τ c r)) + counterOverhead w n) +
          (cost + τ cn) := by
      simp [counterOverhead, Finset.sum_range_succ, cost, wn, cn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    dsimp only
    rw [time]
    refine ⟨?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, before, round]
      rfl
    · apply counter_span_append _ _ _ (cost + τ cn) cp w.length _ _ _ span
        (by rw [before]; exact rs)
      · intro p hp
        obtain ⟨r, u, hr, heads⟩ := hp
        refine ⟨r, u, Or.inl ?_, heads⟩
        rcases hr with ⟨hr, hu⟩ | ⟨rfl, rfl⟩
        · exact ⟨by omega, hu⟩
        · exact ⟨by omega, Nat.zero_le _⟩
      · intro p hp
        obtain ⟨u, hu, heads⟩ := hp
        exact ⟨n, u, Or.inl ⟨by omega, hu⟩, heads⟩

/-- **The counter-driven loop, every round returns** (design §12.7, C2).
Start the host at its decrement phase, with body configuration `c` and the
delimited counter word `w`, of value `d`, at `cp`. Suppose each of the `d`
rounds starts at the anchor `a`, lasts its exact time `τ > 0`, avoids the
anchor, the exit and halting in between, and returns to `a`. Then the host
reaches `done` at exactly `T`: the `d` round times plus the exact decrement
overhead, including the final underflow sweep. Its body part is the orbit
after `d` rounds, its counter is all `true`, and its counter head is back at
`cp`. Earlier, neither exit anchor occurs. Throughout, the counter head stays
within `[cp - 1, cp + |w|]`, and the body heads are the body's own heads at
some point of some round. With `exit = none`, the hypotheses do not mention an
exit at all.

**Proof sketch.** Induct on the round. Each decrement is
`Turing.decrementTM_run_succ_ofCfg` at the counter tape, with the body tapes
idle; the final one is `Turing.decrementTM_run_underflow_ofCfg`. The
redirection is applied at the exit step. Each round is the R1 run
`Turing.embedEmitTM_runFrom` with its states renamed by
`Turing.CounterLoopState.body`. The host agrees with that renamed run step by
step while the body's next state is neither the anchor nor the exit, which
the round hypothesis guarantees before the final step; the final step is the
redirection. The counter word before round
`r` is `Turing.counterWord w r` (`Turing.counterWord_value`), and the decrement
costs add to `Turing.counterOverhead w (d + 1)`. -/
theorem counterLoopTM_run_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨before, span⟩ := counter_rounds M a exit τ c w ct cp hw d (by omega)
    (fun r hr => ⟨(hround r hr).1, (hround r hr).2.1, (hround r hr).2.2.1⟩)
  have control : (if d = 0 then some (.dec .run) else
      (counterLoopOrbit M τ c d).state.map (counterLoopRedirect a exit)) =
      some (CounterLoopState.dec FlagPhase.run) := by
    by_cases hz : d = 0
    · simp [hz]
    · have ret := (hround (d - 1) (by omega)).2.2.2
      rw [show d - 1 + 1 = d by omega] at ret
      simp [hz, ret, counterLoopRedirect]
  rw [control] at before
  let wd := counterWord w d
  have width : wd.length = w.length := counterWord_length w d
  have empty : wd = List.replicate w.length false := by
    simpa only [hd] using counter_word_exhausted w
  have under : decFixed wd = none := (counter_dec_zero wd).mpr (by simp [empty])
  have framed := counter_patch_frame w wd ct cp width hw
  obtain ⟨debit, ds⟩ := counter_debit M a exit (counterLoopOrbit M τ c d) wd
    (counterPatch ct cp wd) cp framed
  simp only [under, Option.getD_none, Option.isSome_none, Bool.false_eq_true, ite_false,
    width] at debit
  rw [counter_patch_twice ct cp wd (List.replicate w.length true)
    (by simp [width])] at debit
  have fill : counterPatch ct cp (List.replicate w.length true) =
      (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) := by
    funext q
    simp only [counterPatch, List.length_replicate]
    split_ifs with h
    · have hp : 0 ≤ q - cp := by omega
      have hn : (q - cp).toNat < w.length := by omega
      simp [FinTM.bufferTape, h.1, hn]
    · rfl
  rw [fill] at debit
  have time : (∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) +
      counterOverhead w (d + 1) =
      ((∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r)) + counterOverhead w d) +
        (2 * (wd.takeWhile not).length + 2) := by
    simp [counterOverhead, Finset.sum_range_succ, wd, Nat.add_assoc]
  rw [time]
  refine ⟨?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add, before, debit]
  · exact counter_span_append _ _ _ _ cp w.length _ _ _ span
      (by rw [before]; simpa only [width] using ds) (fun _ h => h)
      (fun p hp => ⟨d, 0, Or.inr ⟨rfl, rfl⟩, by simpa using hp⟩)

/-- **The counter-driven loop, early exit** (design §12.7, C2). As
`Turing.counterLoopTM_run_done`, except that round `r₀`, below the counter's
value, ends at the designated exit `e ≠ a` while every earlier round returns
to `a`. Then the host reaches `escape` at exactly the `r₀ + 1` round times plus
the cost of the `r₀ + 1` decrements before them. Its body part is the orbit
after round `r₀`, and its counter holds `Turing.counterWord w (r₀ + 1)`.
Earlier, neither exit anchor occurs, and the trajectory clauses hold as in
the returning case.

**Proof sketch.** The induction of `Turing.counterLoopTM_run_done`, stopped at
round `r₀`: every decrement before it succeeds, since `r₀` is below the value
(`Turing.counterWord_value`), and the redirection sends round `r₀`'s final
step to `escape`. -/
theorem counterLoopTM_run_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  subst T
  obtain ⟨he, hs⟩ := counter_rounds M a (some e) τ c w ct cp hw (r₀ + 1)
    (by omega) (by
      intro r hr
      obtain ⟨ha, ht, hg⟩ := hround r (by omega)
      refine ⟨ha, ht, ?_⟩
      intro u hu hut
      obtain ⟨s, hst, hsa, hse⟩ := hg u hu hut
      exact ⟨s, hst, hsa, fun h => hse (Option.some.inj h).symm⟩)
  refine ⟨?_, hs.1, hs.2.1, ?_⟩
  · unfold counterPatch at he
    simp only [counterWord_length] at he
    simpa [hexit, hea, counterLoopRedirect] using he
  · simpa only [Nat.lt_succ_iff] using hs.2.2

/-- **Uniform per-round bound** (design §12.7, decision 12.7.3). If each of
the `d` rounds costs at most `B`, the returning run's exact time is at most
`d·B + 4d + 2|w| + 2`.

**Proof sketch.** Bound the round sum termwise by `B`
(`Finset.sum_le_card_nsmul`) and the decrement share by
`Turing.counterOverhead_le`. -/
theorem counterLoop_time_le {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range d)
    (fun r => τ (counterLoopOrbit M τ c r)) B
    (fun r hr => hB r (Finset.mem_range.mp hr))
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hc := counterOverhead_le w
  rw [hd] at hc
  calc
    _ ≤ d * B + (4 * d + 2 * w.length + 2) :=
      Nat.add_le_add (by simpa using hsum) hc
    _ = _ := by omega

/-! ## R8.6 — the expansion (§12.8) -/

/-- **R8.6, the expansion** (design §12.8a). The counter loop whose round is
the advancing writer: with a counter of value `d` on the last tape, it writes
the pattern `pat` on tape `i` `d` times, contiguously from the head, and leaves
the head after the last copy. Its uses are lengths given in binary: the
window halves of a record, of length `d·|pat|` for a radius counter `d`. -/
def expandTM (k : ℕ) (i : Fin k) (pat : List Bool) :
    MultiTapeTM (k + 1) Bool (CounterLoopState (Fin (pat.length + 1))) :=
  counterLoopTM (writeAdvTM k i pat) 0 none

/-- **R8.6, the expansion, framed** (design §12.8a). Start the expansion at its
decrement phase with body configuration `c` at the writer's state `0` and the
delimited counter word `w`, of value `d`, at `cp`. It reaches `done` at exactly
`d·(|pat| + 1) + counterOverhead w (d + 1)` and neither exit anchor earlier.
At that point the interval `[pos, pos + d·|pat|)` of tape `i` holds `d` copies
of `pat`, whatever it held before, the head of tape `i` is at `pos + d·|pat|`,
the counter is all `true` with its head back at `cp`, and every other cell,
every other head, the input position and the output are unchanged. Throughout,
the counter head stays within `[cp - 1, cp + |w|]`, the head of tape `i`
within `[pos, pos + d·|pat|]`, and every other body head is fixed.

**Proof sketch.** Apply `Turing.counterLoopTM_run_done` with the constant round
time `τ := |pat| + 1`. The round hypotheses are `Turing.writeAdvTM_run_ofCfg`
at the orbit's `r`-th configuration, which by induction on `r` has `r` copies
of `pat` written from `pos` and its head at `pos + r·|pat|`. The round sum is
`d·(|pat| + 1)`. The head clauses follow from the loop's trajectory clause and
the writer's. -/
theorem expandTM_run_ofCfg {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfg (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) := by
  sorry

end Turing

## ===== audits/evidence/s12-8/r80b-fill/R80bInstances.lean.txt =====

import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Turing

-- Base statement: counterLoop_time_le
example {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 :=
  counterLoop_time_le M τ c w d hd B hB

-- Base statement: counter_cfg_eq
example {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ :=
  counter_cfg_eq q c ct cp

-- Base statement: counterLoopTM_run_done
example {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) :=
  counterLoopTM_run_done M a exit τ c w ct cp hw d hd hround T hT

-- Base statement: counterLoopTM_run_escape
example {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) :=
  counterLoopTM_run_escape M a e hea τ c w ct cp hw r₀ hr₀ hround hexit T hT

-- Base statement: expandTM_run_ofCfg
example {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfg (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) :=
  expandTM_run_ofCfg i pat c hc w ct cp hw d hd

/-! ## Part 4 — executed instances over a rich alphabet -/

section Checks

/-- Digits `0`, `1`; the symbol `2` is foreign. -/
def eD : Bool ↪ Fin 3 := ⟨fun b => cond b 1 0, by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- A one-tape body configuration at the writer's anchor `0`, body head at `4`, a foreign
symbol at `3` (left of the written interval). -/
def cD : Cfg 1 (Fin 3) (Fin 2) [2, 1] :=
  ⟨some 0, 1, fun _ p => if p = 3 then some 2 else none, fun _ => 4, []⟩

/-- The counter tape: `w` at `cp = 5`, blank delimiters at `4` and `5 + |w|`, foreign symbols
at `3` and at `6 + |w|`. -/
def ctD (w : List Bool) : ℤ → Option (Fin 3) := fun q =>
  if q = 3 ∨ q = 6 + (w.length : ℤ) then some 2 else FinTM.bufferTape (w.map eD) (q - 5)

/-- Returning case: `w = [false, true]` (value 2, leading zero), round `writeAdvTM [2]`
(time 2), `T = 2·2 + counterOverhead w 3 = 4 + 12 = 16`. The counter ends `e true`, both
foreign frame cells survive, the pattern is written twice, the body head ends at `6`. -/
example :
    let z := counterLoopCfg (some (.dec .run)) cD (ctD [false, true]) 5
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 none
    counterOverhead [false, true] 3 = 12 ∧
    (H.runFrom z 16).state = some .done ∧ (H.runFrom z 15).state ≠ some .done ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 6 = some (eD true) ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 3 = some 2 ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 8 = some 2 ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 7 = none ∧
    (H.runFrom z 16).workTapes 0 4 = some 2 ∧ (H.runFrom z 16).workTapes 0 5 = some 2 ∧
    (H.runFrom z 16).workTapes 0 3 = some 2 ∧ (H.runFrom z 16).workTapes 0 6 = none ∧
    (H.runFrom z 16).workTapePos 0 = 6 ∧ (H.runFrom z 16).workTapePos (Fin.last 1) = 5 ∧
    (H.runFrom z 16).inputPos = 1 := by
  decide

/-- Escape case: the same body with exit `1`, so round `0` escapes after one step
(`τ := 1`): `T = 1 + counterOverhead w 1 = 1 + 4 = 5`, counter `counterWord w 1 =
[true, false]` mapped by `e`. -/
example :
    let z := counterLoopCfg (some (.dec .run)) cD (ctD [false, true]) 5
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 (some 1)
    counterWord [false, true] 1 = [true, false] ∧ counterOverhead [false, true] 1 = 4 ∧
    (H.runFrom z 5).state = some .escape ∧ (H.runFrom z 4).state ≠ some .escape ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 6 = some (eD false) ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 8 = some 2 := by
  decide

/-- A body with no tapes (`k = 0`), one stationary step per round: `w = [true]` (value 1),
`T = 1 + counterOverhead [true] 2 = 1 + 2 + 4 = 7`. -/
def unitBodyD : MultiTapeTM 0 (Fin 3) Unit := ⟨(), fun _ _ _ => ⟨0, fun j => j.elim0, none, some ()⟩⟩

example :
    let c0 : Cfg 0 (Fin 3) Unit [2] := ⟨some (), 1, fun j => j.elim0, fun j => j.elim0, []⟩
    let z := counterLoopCfg (some (.dec .run)) c0 (ctD [true]) 5
    let H := counterLoopTMVia eD unitBodyD () none
    (H.runFrom z 7).state = some .done ∧ (H.runFrom z 6).state ≠ some .done ∧
    (H.runFrom z 7).workTapes (Fin.last 0) 5 = some (eD true) ∧
    (H.runFrom z 7).workTapes (Fin.last 0) 7 = some 2 := by
  decide

/-- Zero counters: `w = [false]` reaches `done` at `counterOverhead [false] 1 = 4` with the
counter `e true`; `w = []` at `counterOverhead [] 1 = 2`. -/
example :
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 none
    let z₁ := counterLoopCfg (some (.dec .run)) cD (ctD [false]) 5
    let z₀ := counterLoopCfg (some (.dec .run)) cD (ctD []) 5
    (H.runFrom z₁ 4).state = some .done ∧ (H.runFrom z₁ 3).state ≠ some .done ∧
    (H.runFrom z₁ 4).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z₀ 2).state = some .done ∧ (H.runFrom z₀ 1).state ≠ some .done ∧
    (H.runFrom z₀ 2).workTapes (Fin.last 1) 6 = some 2 := by
  decide

/-- R8.6 boundary checks: a zero-valued counter, a zero-width counter,
and a positive counter with an empty pattern. These compute the actual host. -/
example :
    let c : Cfg 1 Bool (Fin 3) [] :=
      ⟨some 0, 0, fun _ p => if p = 3 then some true else none, fun _ => 4, []⟩
    let z := counterLoopCfg (some (.dec .run)) c (FinTM.bufferTape [false]) 0
    (expandTM 1 0 [true, false] |>.runFrom z 4).state = some .done ∧
    (expandTM 1 0 [true, false] |>.runFrom z 4).workTapePos 0 = 4 ∧
    (expandTM 1 0 [true, false] |>.runFrom z 4).workTapes 0 3 = some true := by
  decide

example :
    let c : Cfg 1 Bool (Fin 2) [] := ⟨some 0, 0, fun _ _ => none, fun _ => 4, []⟩
    let z := counterLoopCfg (some (.dec .run)) c (FinTM.bufferTape []) 0
    (expandTM 1 0 [true] |>.runFrom z 2).state = some .done ∧
    (expandTM 1 0 [true] |>.runFrom z 2).workTapePos 0 = 4 := by
  decide

example :
    let c : Cfg 1 Bool (Fin 1) [] :=
      ⟨some 0, 0, fun _ p => if p = 4 then some false else none, fun _ => 4, []⟩
    let z := counterLoopCfg (some (.dec .run)) c (FinTM.bufferTape [true]) 0
    (expandTM 1 0 [] |>.runFrom z 7).state = some .done ∧
    (expandTM 1 0 [] |>.runFrom z 6).state ≠ some .done ∧
    (expandTM 1 0 [] |>.runFrom z 7).workTapePos 0 = 4 ∧
    (expandTM 1 0 [] |>.runFrom z 7).workTapes 0 4 = some false := by
  decide

end Checks

end Turing

## ===== audits/evidence/s12-8/r80b-fill/declaration-freeze.md =====

# Declaration freeze comparison

- Action.mapWorkSymbols: unchanged statement and body: True
- Cfg.mapWorkSymbols: unchanged statement and body: True
- MultiTapeTM.mapWorkSymbols: unchanged statement and body: True
- MultiTapeTM.mapWorkSymbols_runFrom: unchanged statement and body: True
- decFixed: unchanged statement and body: True
- decrementTM: unchanged statement and body: True
- decrementTM_run_succ_ofCfg: unchanged statement and body: True
- decrementTM_run_underflow_ofCfg: unchanged statement and body: True
- counterWord: unchanged statement and body: True
- counterOverhead: unchanged statement and body: True
- counterWord_length: unchanged statement and body: True
- counterWord_value: unchanged statement and body: True
- counterOverhead_le_of_le: unchanged statement and body: True
- counterOverhead_le: unchanged statement and body: True
- CounterLoopState: unchanged statement and body: True
- counterLoopStateFintype: unchanged statement and body: True
- counterLoopRedirect: unchanged statement and body: True
- counterLoopDecExit: unchanged statement and body: True
- counterLoopTM: unchanged statement and body: True
## counterLoopCfg — type-only: True

```diff
--- base
+++ after
@@ -1,3 +1,3 @@
-def counterLoopCfg {k : ℕ} {S : Type} {x : List Bool}
-    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
-    (ct : ℤ → Option Bool) (cp : ℤ) : Cfg (k + 1) Bool (CounterLoopState S) x+def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
+    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
```

## counterLoopOrbit — type-only: True

```diff
--- base
+++ after
@@ -1,2 +1,2 @@
-def counterLoopOrbit {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
-    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) : Cfg k Bool S x+def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
+    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
```

- counter_cfg_eq: frozen statement, authorized body swap; statement identical: True
- counterLoopTM_run_done: frozen statement, authorized body swap; statement identical: True
- counterLoopTM_run_escape: frozen statement, authorized body swap; statement identical: True
## counterLoop_time_le — type-only: True

```diff
--- base
+++ after
@@ -1,5 +1,5 @@
-theorem counterLoop_time_le {k : ℕ} {S : Type} {x : List Bool}
-    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
+theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
+    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
     (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
     (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
     ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
```

- expandTM: unchanged statement and body: True
- expandTM_run_ofCfg: frozen statement, authorized body swap; statement identical: True
- lastEmb: new public declaration; authorized: True
- counterLoopTMVia: new public declaration; authorized: True
- counterLoopTMVia_run_done: new public declaration; authorized: True
- counterLoopTMVia_run_escape: new public declaration; authorized: True
- counterLoopTMVia: exact new brief text: True
- counterLoopTMVia_run_escape: exact new brief text: True
- counterLoopTMVia_run_done: exact new brief text: True
- lastEmb: exact new brief text: True

Surviving ordered declaration sequence identical: True

## Private ledger

Base 24; after 23.

- rewritten: counter_buffer_complement
- removed: counter_last_unselected
- rewritten: counterSpan
- rewritten: counter_span_append
- rewritten: counterPatch
- removed: counter_patch_initial
- rewritten: counter_patch_twice
- rewritten: counter_patch_frame
- rewritten: counter_debit
- rewritten: counter_body
- removed: counter_orbit_succ
- rewritten: counter_rounds
- added: counter_layout
- added: counter_refl_agree

Raw symbol-transport/decrement/arithmetic block identical except authorized complement body: True

Added imports: ['TCSlib.Complexity.TuringMachine.SymbolLift']
Removed imports: []
Final size: 1697 lines; 87771 bytes.

Failures: []

## ===== audits/evidence/s12-8/r80b-fill/private-ledger.md =====

# Private ledger

**24 → 23:** two additions, three removals. Every change is listed below; all other privates are unchanged.

| Private | Disposition and role |
|---|---|
| `counter_layout` | Added: the existing layout proof moved to its generic form; `counter_cfg_eq` instantiates it. |
| `counter_refl_agree` | Added: table agreement of the prescribed hosts at the identity embedding. |
| `counter_last_unselected` | Removed: its one-use proof is inlined into `counter_layout`. |
| `counter_patch_initial` | Removed: its one-use proof is inlined into the round-zero case. |
| `counter_orbit_succ` | Removed: its one-use invocation is replaced by `Function.iterate_succ_apply'`. |
| `counter_buffer_complement` | Rewritten: direct public buffer-map instance, disposition (i). |
| `counterSpan` | Rewritten: alphabet-generic trajectory predicate; body unchanged. |
| `counter_span_append` | Rewritten: alphabet-generic segment composition; proof unchanged. |
| `counterPatch` | Rewritten: alphabet-generic counter interval overwrite. |
| `counter_patch_twice` | Rewritten: alphabet-generic equal-width overwrite identity. |
| `counter_patch_frame` | Rewritten: alphabet-generic delimiter preservation. |
| `counter_debit` | Rewritten: one-tape decrement through overlay, R1 and guarded state transport. |
| `counter_body` | Rewritten: generic types/host/layout substitutions; same guarded R1 route. |
| `counter_rounds` | Rewritten: the existing single induction, with embedded counter words. |


Final source: 1,697 lines; 87,771 bytes.

## ===== audits/evidence/s12-8/r80b-fill/axiom-comparison.txt =====

All 28 base axiom-print lines are byte-identical after the change.
The 4 new declarations use only propext, Classical.choice and Quot.sound.
'Turing.expandTM_run_ofCfg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.lastEmb' depends on axioms: [propext]
'Turing.counterLoopTMVia' depends on axioms: [propext, Quot.sound]
'Turing.counterLoopTMVia_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTMVia_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== audits/evidence/s12-8/r80b-fill/axioms-base.log =====

'Turing.Action.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.Cfg.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols_runFrom' depends on axioms: [propext, Quot.sound]
'Turing.decFixed' does not depend on any axioms
'Turing.decrementTM' depends on axioms: [Quot.sound]
'Turing.decrementTM_run_succ_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.decrementTM_run_underflow_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord' does not depend on any axioms
'Turing.counterOverhead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.CounterLoopState' does not depend on any axioms
'Turing.instDecidableEqCounterLoopState' does not depend on any axioms
'Turing.counterLoopStateFintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopRedirect' does not depend on any axioms
'Turing.counterLoopDecExit' does not depend on any axioms
'Turing.counterLoopTM' depends on axioms: [Quot.sound]
'Turing.counterLoopCfg' does not depend on any axioms
'Turing.counterLoopOrbit' depends on axioms: [propext, Quot.sound]
'Turing.counter_cfg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoop_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.expandTM' depends on axioms: [propext, Quot.sound]
'Turing.expandTM_run_ofCfg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== audits/evidence/s12-8/r80b-fill/axioms-after.log =====

'Turing.Action.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.Cfg.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols_runFrom' depends on axioms: [propext, Quot.sound]
'Turing.decFixed' does not depend on any axioms
'Turing.decrementTM' depends on axioms: [Quot.sound]
'Turing.decrementTM_run_succ_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.decrementTM_run_underflow_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord' does not depend on any axioms
'Turing.counterOverhead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.CounterLoopState' does not depend on any axioms
'Turing.instDecidableEqCounterLoopState' does not depend on any axioms
'Turing.counterLoopStateFintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopRedirect' does not depend on any axioms
'Turing.counterLoopDecExit' does not depend on any axioms
'Turing.counterLoopTM' depends on axioms: [Quot.sound]
'Turing.counterLoopCfg' does not depend on any axioms
'Turing.counterLoopOrbit' depends on axioms: [propext, Quot.sound]
'Turing.counter_cfg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoop_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.expandTM' depends on axioms: [propext, Quot.sound]
'Turing.expandTM_run_ofCfg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.lastEmb' depends on axioms: [propext]
'Turing.counterLoopTMVia' depends on axioms: [propext, Quot.sound]
'Turing.counterLoopTMVia_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTMVia_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== audits/evidence/s12-8/r80b-fill/screen-delta.md =====

# Copy-text screen delta

declarations screened: 539; copy pairs (target reproduces >= half of source): 414; reproduced text: 121,876 chars
declarations screened: 543; copy pairs (target reproduces >= half of source): 418; reproduced text: 123,184 chars

New pairs total: 4; removed pairs: 0.
New CounterLoop cross-file pairs: 0.

## New CounterLoop in-file pairs

CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%

## All added pairs

CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%

## All removed pairs


## ===== audits/evidence/s12-8/r80b-fill/screen-base.txt =====

declarations screened: 539; copy pairs (target reproduces >= half of source): 414; reproduced text: 121,876 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%

## ===== audits/evidence/s12-8/r80b-fill/screen-after.txt =====

declarations screened: 543; copy pairs (target reproduces >= half of source): 418; reproduced text: 123,184 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%

## ===== audits/evidence/s12-8/r80b-fill/sorries-base.txt =====

TCSlib/Complexity/TuringMachine/Build/Seam.lean :: seamCompTM₂_run_ofCfg
TCSlib/Complexity/SpaceComplexity/Constructible.lean :: spaceConstructible_logSpace
TCSlib/Complexity/SpaceComplexity/Constructible.lean :: spaceConstructible_linear
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: NSPACE_subset_exp_dtime
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: NL_subset_P
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: polyTimeReducible_of_mem_NL
TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: NP_subset_PSPACE
TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: SAT3_mem_PSPACE
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: fieldsTape_field
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: compareTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: skipTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: skipBackTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: seekEndTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: seekStartTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_fold
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_map
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_shiftRight
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_shiftLeft
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_carry
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: writeConstTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: writeAdvTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: inputCopyTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: inputFoldTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: expandTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: exists_inputCallTM
TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: exists_inputSeekTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: cfgRecord_inj
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: recordValid_iff
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordStepTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordEqTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordTestTM
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: exists_adjacency_codec_cnf
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_mem_PSPACE
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_PSPACEHard
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_PSPACEComplete
TCSlib/Complexity/TuringMachine/NDCodes.lean :: exists_effectiveNDMachineCode

## ===== audits/evidence/s12-8/r80b-fill/sorries-after.txt =====

TCSlib/Complexity/TuringMachine/Build/Seam.lean :: seamCompTM₂_run_ofCfg
TCSlib/Complexity/SpaceComplexity/Constructible.lean :: spaceConstructible_logSpace
TCSlib/Complexity/SpaceComplexity/Constructible.lean :: spaceConstructible_linear
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: NSPACE_subset_exp_dtime
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: NL_subset_P
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: polyTimeReducible_of_mem_NL
TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: NP_subset_PSPACE
TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: SAT3_mem_PSPACE
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: fieldsTape_field
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: compareTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: skipTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: skipBackTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: seekEndTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: seekStartTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_fold
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_map
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_shiftRight
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_shiftLeft
TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: scanResult_carry
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: writeConstTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: writeAdvTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: inputCopyTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/Scan.lean :: inputFoldTM_run_ofCfg
TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: exists_inputCallTM
TCSlib/Complexity/TuringMachine/Build/InputCall.lean :: exists_inputSeekTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: cfgRecord_inj
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: recordValid_iff
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordStepTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordEqTM
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: exists_recordTestTM
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: exists_adjacency_codec_cnf
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_mem_PSPACE
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_PSPACEHard
TCSlib/Complexity/ClassPSPACE/TQBF.lean :: TQBF_PSPACEComplete
TCSlib/Complexity/TuringMachine/NDCodes.lean :: exists_effectiveNDMachineCode

## ===== audits/evidence/s12-8/r80b-fill/agent-downstream-replay.log =====

Extracted, in order, from the successful full 74-module final-sweep.log.
CHECK TCSlib/Complexity/TuringMachine/Build/CounterLoop
CHECK TCSlib/Complexity/TuringMachine/Build/InputCall
TCSlib/Complexity/TuringMachine/Build/InputCall.lean:63:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/InputCall.lean:103:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/Build/CfgRecord
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:175:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:206:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:261:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:303:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:331:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE/TQBF.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:222:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:274:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:282:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassPSPACE
CHECK TCSlib/Complexity/TuringMachine

## ===== audits/logs/s12-8-fill-D-freeze.log =====

# §12.8 fill D (R8.0b): statement freeze, maintainer's own check against the campaign tip aed5b4ff; body changes authorized for the brief's four swaps; the three STATEMENT CHANGED lines are the brief's authorized type-only generalizations (bodies verified identical, see the record)
## CounterLoop.lean (base aed5b4ff → be1b7691)
public before/after: 27 31 private before/after: 24 23
public added: ['counterLoopTMVia', 'counterLoopTMVia_run_done', 'counterLoopTMVia_run_escape', 'lastEmb']
public removed: []
STATEMENT CHANGED: counterLoopCfg
STATEMENT CHANGED: counterLoopOrbit
authorized body change: counterLoopTM_run_done
authorized body change: counterLoopTM_run_escape
STATEMENT CHANGED: counterLoop_time_le
authorized body change: counter_cfg_eq
authorized body change: expandTM_run_ofCfg
private removed: ['counter_last_unselected', 'counter_orbit_succ', 'counter_patch_initial']
private added: ['counter_layout', 'counter_refl_agree']
private changed: ['counterPatch', 'counterSpan', 'counter_body', 'counter_buffer_complement', 'counter_debit', 'counter_patch_frame', 'counter_patch_twice', 'counter_rounds', 'counter_span_append']
imports: 4 before, 5 after
+import TCSlib.Complexity.TuringMachine.SymbolLift
forbidden tokens in added lines (sorry/admit/axiom/native_decide/implemented_by/extern/unsafe):
  none
lines: 1697

## ===== audits/logs/s12-8-fill-D-replay.log =====

# fill integration replay D at be1b7691: downstream closure of the changed files, fresh .oleans on a snapshot of a tip-consistent olean tree
TCSlib/Complexity/TuringMachine/Build/CounterLoop exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputCall exit=0 errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Build/CfgRecord exit=0 errors=0 sorry=5
TCSlib/Complexity/ClassPSPACE/TQBF exit=0 errors=0 sorry=4
TCSlib/Complexity/ClassPSPACE exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine exit=0 errors=0 sorry=0
# modules=6 failed=0

## ===== audits/logs/s12-8-fill-D-axioms.log =====

# s12-8-fill-D: #print axioms for every public declaration of the owned files, from audits/evidence/s12-8/S128FillDAxioms.lean.txt (generated by the maintainer), elaborated read-only (no olean output) against the replay's olean tree; exit 0, 0 errors
'Turing.Action.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.Cfg.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols' depends on axioms: [Quot.sound]
'Turing.MultiTapeTM.mapWorkSymbols_runFrom' depends on axioms: [propext, Quot.sound]
'Turing.decFixed' does not depend on any axioms
'Turing.decrementTM' depends on axioms: [Quot.sound]
'Turing.decrementTM_run_succ_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.decrementTM_run_underflow_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord' does not depend on any axioms
'Turing.counterOverhead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterWord_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterOverhead_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.CounterLoopState' does not depend on any axioms
'Turing.counterLoopStateFintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopRedirect' does not depend on any axioms
'Turing.counterLoopDecExit' does not depend on any axioms
'Turing.counterLoopTM' depends on axioms: [Quot.sound]
'Turing.lastEmb' depends on axioms: [propext]
'Turing.counterLoopTMVia' depends on axioms: [propext, Quot.sound]
'Turing.counterLoopCfg' does not depend on any axioms
'Turing.counterLoopOrbit' depends on axioms: [propext, Quot.sound]
'Turing.counter_cfg_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTMVia_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTMVia_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoopTM_run_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.counterLoop_time_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.expandTM' depends on axioms: [propext, Quot.sound]
'Turing.expandTM_run_ofCfg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== audits/logs/s12-8-fill-D-admissions.log =====

# §12.8 fill stream D (R8.0b): admission walk of R8.6, read-only against the replay olean tree of be1b7691; probe audits/evidence/s12-8/S128FillDAdmissionWalk.lean.txt; exit 0
Turing.expandTM_run_ofCfg: direct sorryAx users in closure: [Turing.writeAdvTM_run_ofCfg]

## ===== audits/logs/s12-8-fill-D-instances.log =====

# R80bInstances.lean.txt re-run by the maintainer: elaborated read-only (no olean output) against the replay olean tree of be1b7691; exit 0, no output (0 errors, 0 warnings). A control copy with an appended false 'decide' example reports exactly that error, so the file is genuinely checked.

## ===== audits/logs/s12-8-fill-D-stylelint.log =====

# §12.8 fill stream D (R8.0b): style lint at the integration head be1b7691 (maintainer's run)
## TCSlib/Complexity/TuringMachine
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  11970 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              1697 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1023 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     4980 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               6309 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1191 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     1014 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  11970 lines; 89 public / 379 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                346 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              1697 lines; 31 public / 23 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1023 lines; 24 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean                120 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     4980 lines; 8 public / 185 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               6309 lines; 18 public / 241 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     276 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     815 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     815 lines; 18 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean             508 lines; 16 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines; 10 public / 19 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1191 lines; 38 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     575 lines; 45 public / 3 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     467 lines; 41 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     550 lines; 9 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines; 8 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 448 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  430 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines; 30 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         354 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines; 21 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodes.lean                        182 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               265 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean          160 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         682 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         682 lines; 40 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                375 lines; 9 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   149 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         412 lines; 25 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   884 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   884 lines; 2 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines; 4 public / 96 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     1014 lines; 52 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/SymbolLift.lean                     382 lines; 22 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations

style_lint: 0 FAIL, 14 WARN over 52 files
## TCSlib/Complexity/TuringMachine/Build
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean        11970 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean    1697 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean          1023 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean           4980 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean     6309 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean           1191 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean        11970 lines; 89 public / 379 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean      346 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean     157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean    1697 lines; 31 public / 23 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean          1023 lines; 24 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean   909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean   909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean  326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean      120 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean           4980 lines; 8 public / 185 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean     182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean     6309 lines; 18 public / 241 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean           276 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean           815 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean           815 lines; 18 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean   508 lines; 16 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean       739 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean       739 lines; 10 public / 19 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean           1191 lines; 38 public / 16 private declarations

style_lint: 0 FAIL, 6 WARN over 16 files

## ===== audits/logs/s12-8-fill-D-screen-after.txt =====

declarations screened: 543; copy pairs (target reproduces >= half of source): 418; reproduced text: 123,184 chars
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/171 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 237/318 = 75%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::f2_space_radius  reproduces  Catalog.lean::catalog_space_bound: 140/190 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::catalog_space_bound: 139/190 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   Catalog.lean::f2_counter_space  reproduces  Catalog.lean::catalog_space_bound: 138/190 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/171 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/171 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/174 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::a2_map_space  reproduces  Catalog.lean::catalog_space_bound: 115/190 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 315/573 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 311/573 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 315/581 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Simulation.lean::bufferedFirstCfg_run: 92/171 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 223/434 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%

## ===== audits/evidence/s12-8/R80bPreShip.lean.txt =====

import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Stream D pre-ship probe: R8.0b, `counterLoopTMVia` (§12.8 fill) — pre-issue-2 variant

The variant for `oleans-pre2` (`s12-8/fill-preissue-2`, `5afed90b`): Part 3(f) cites the
landed overlay layer of `SymbolLift` instead of defining it, and Part 3(h) adds the generic
layout with the now-public `counter_cfg_eq` as its `Bool` instance. Run on `oleans-pre2`: `probe-D-pre2.out`.

Elaborated read-only against the s12.8 round-2 olean tree (`oleans-s128r2`) with
`tools/leanelab.sh`; no olean is written. The probe imports `SymbolLift` next to
`Build/CounterLoop`, which is the import edge the fill adds.

Expected result: **0 errors; exactly two `declaration uses 'sorry'` warnings**, on the
two generic contracts of Part 2, which are the fill's targets. Every other
declaration and example is proved.

* **Part 1** — the three in-place generalizations, as probe-local copies `…D` (the
  landed `Bool` declarations exist in the olean, so the real names would clash):
  types only, bodies verbatim. At `Symbol := Bool` each copy is the landed
  declaration by `rfl`, the landed `counterLoop_time_le` follows from the copy, and
  the landed `expandTM_run_ofCfg` statement, restated over the copies, is the landed
  theorem.
* **Part 2** — the new surface under its real names: `lastEmb`, `counterLoopTMVia`
  (a real definition), `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape`
  (sorried). The generic contracts are stated over the Part 1 copies.
* **Part 3** — the fill route, checked: (a) the decrement table is input-oblivious
  and writes no blank; (b) its lift at `Function.Embedding.refl Bool` is the same
  table; (c) R1's action at `lastEmb k`, computed from Embed's public surface; (d) the
  dec-phase table agreement and the whole-host `AgreeOn` at `refl`; (e) the two landed
  `Bool` contracts, statements copied verbatim, re-derived from Part 2 through
  `MultiTapeTM.runFrom_eq_of_agreeOn` (Z5); (f) the frame-respecting lift (overlay)
  transport, the bridge the generic decrement phase needs and `SymbolLift` lacks: the
  overlay (defined through `Cfg.liftSymbols`), its one-step and run forms (the run form
  by `Function.Semiconj.iterate_right`, no induction), the decoded shadow of an
  arbitrary rich configuration, and the decoding of a lifted framed word; (g) the
  decrement-phase host configuration as an R1 configuration at `lastEmb k`.
* **Part 4** — executed instances (`decide`) of the new host over `Fin 3`, with a
  foreign symbol in the input, on the body tape and in the counter tape's frame:
  the returning case (value 2, leading-zero counter), the escape case, `k = 0`, and
  the zero counters `w = [false]` and `w = []`.
-/

namespace Turing

/-! ## Part 1 — in-place generalizations (probe-local copies; types only, bodies verbatim) -/

/-- `counterLoopCfg` with the alphabet generalized (body verbatim). -/
def counterLoopCfgD {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

/-- `counterLoopOrbit` with the alphabet generalized (body verbatim). -/
def counterLoopOrbitD {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-- `counterLoop_time_le` with the alphabet generalized (proof body verbatim, with the
orbit name substituted). -/
theorem counterLoop_time_leD {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbitD M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbitD M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 := by
  have hsum := Finset.sum_le_card_nsmul (Finset.range d)
    (fun r => τ (counterLoopOrbitD M τ c r)) B
    (fun r hr => hB r (Finset.mem_range.mp hr))
  simp only [Finset.card_range, nsmul_eq_mul] at hsum
  have hc := counterOverhead_le w
  rw [hd] at hc
  calc
    _ ≤ d * B + (4 * d + 2 * w.length + 2) :=
      Nat.add_le_add (by simpa using hsum) hc
    _ = _ := by omega

section Instances

/-- At `Bool` the generalized configuration is the landed one. -/
example {k : ℕ} {S : Type} {x : List Bool} (q : Option (CounterLoopState S))
    (c : Cfg k Bool S x) (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfgD q c ct cp = counterLoopCfg q c ct cp := rfl

/-- At `Bool` the generalized orbit is the landed one. -/
example {k : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM k Bool S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x) (r : ℕ) :
    counterLoopOrbitD M τ c r = counterLoopOrbit M τ c r := rfl

/-- The landed `counterLoop_time_le`, statement copied verbatim, from the generalized one. -/
example {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2 :=
  counterLoop_time_leD M τ c w d hd B hB

/-- The landed `expandTM_run_ofCfg` call sites elaborate over the generalized
configuration with the alphabet inferred (`Bool`), and the statement is the landed
one. -/
example {k : ℕ} {x : List Bool} (i : Fin k) (pat : List Bool)
    (c : Cfg k Bool (Fin (pat.length + 1)) x) (hc : c.state = some 0)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) :
    (expandTM k i pat).runFrom (counterLoopCfgD (some (.dec .run)) c ct cp)
        (d * (pat.length + 1) + counterOverhead w (d + 1)) =
      counterLoopCfgD (some .done)
        { c with
          workTapes := fun j q =>
            if j = i ∧ c.workTapePos j ≤ q ∧
                q < c.workTapePos j + ((d * pat.length : ℕ) : ℤ)
              then FinTM.bufferTape (List.replicate d pat).flatten (q - c.workTapePos j)
            else c.workTapes j q
          workTapePos := Function.update c.workTapePos i
            (c.workTapePos i + ((d * pat.length : ℕ) : ℤ)) }
        (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((expandTM k i pat).runFrom (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1),
        ((expandTM k i pat).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ d * (pat.length + 1) + counterOverhead w (d + 1), ∀ j : Fin k,
        if j = i then
          ((expandTM k i pat).runFrom
              (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos j.castSucc ∈
            Finset.Icc (c.workTapePos j) (c.workTapePos j + ((d * pat.length : ℕ) : ℤ))
        else
          ((expandTM k i pat).runFrom
              (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            c.workTapePos j) :=
  expandTM_run_ofCfg i pat c hc w ct cp hw d hd

end Instances

/-! ## Part 2 — the new surface (real names; contracts sorried) -/

/-- The last host tape as a one-tape selection: `Fin 1 ↪ Fin (k + 1)`, `0 ↦ Fin.last k`. -/
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

/-- **R8.0b**, the counter loop over any alphabet. -/
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

/-- **R8.0b, every round returns**: `counterLoopTM_run_done` over `Γ`. -/
theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbitD M τ c r).state = some a ∧
      0 < τ (counterLoopOrbitD M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbitD M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbitD M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbitD M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbitD M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfgD (some (.dec .run)) c ct cp) T =
        counterLoopCfgD (some .done) (counterLoopOrbitD M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbitD M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbitD M τ c r) u).workTapePos j) := by
  sorry

/-- **R8.0b, early exit**: `counterLoopTM_run_escape` over `Γ` (the exit state is
named `ex`, since `e` is the embedding). -/
theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbitD M τ c r).state = some a ∧
      0 < τ (counterLoopOrbitD M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbitD M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbitD M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbitD M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbitD M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfgD (some (.dec .run)) c ct cp) T =
        counterLoopCfgD (some .escape) (counterLoopOrbitD M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbitD M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfgD (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbitD M τ c r) u).workTapePos j) := by
  sorry

/-! ## Part 3 — the fill route, checked -/

section Route

/-- (a) The decrement table never reads its input. -/
example {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (f : FlagPhase) (inp inp' : Option Γ)
    (work : Fin 1 → Option Γ) :
    ((decrementTM 1 0).liftSymbols e).tr f inp work =
      ((decrementTM 1 0).liftSymbols e).tr f inp' work := rfl

/-- (a) The decrement table writes no blank. -/
theorem probe_dec_noBlank (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) (j : Fin 1) :
    (((decrementTM 1 0).tr f inp work).workTapes j).1 ≠ some none := by
  rcases f with _ | b | b <;>
  rcases h : work 0 with _ | b' <;> (try cases b') <;>
  simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
  split_ifs <;> simp

/-- (b) The lift at `refl` is the same table. -/
theorem probe_lift_refl_tr (f : FlagPhase) (inp : Option Bool) (work : Fin 1 → Option Bool) :
    ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool)).tr f inp work =
      (decrementTM 1 0).tr f inp work := by
  have hd : ∀ o : Option Bool, o.bind (decodeBool (Function.Embedding.refl Bool)) = o := by
    intro o; cases o with
    | none => rfl
    | some b => cases b <;> rfl
  simp only [MultiTapeTM.liftSymbols, hd]
  cases ((decrementTM 1 0).tr f inp work) with
  | mk i w o s =>
    simp only [Action.liftSymbols]
    congr 1
    · funext j
      cases w j with
      | mk a m => cases a with
        | none => rfl
        | some b => cases b <;> rfl
    · cases o <;> rfl

/-- Field-wise equality of actions (probe helper; `Action` has no `@[ext]`). -/
theorem probe_action_eq {k : ℕ} {Sy Q : Type} {A B : Action k Sy Q}
    (h1 : A.inputTape = B.inputTape) (h2 : A.workTapes = B.workTapes)
    (h3 : A.output = B.output) (h4 : A.state = B.state) : A = B := by
  cases A; cases B; simp_all

/-- (c) R1's action at the last-tape selection, computed from Embed's public surface:
`conv => whnf` exposes the private core's body, and `show` restates the private slot
search by its defining term. No private name is used. -/
theorem probe_embedEmit_lastEmb_tr {k : ℕ} {Sy Q : Type} (N : MultiTapeTM 1 Sy Q) (q : Q)
    (inp : Option Sy) (work : Fin (k + 1) → Option Sy) :
    (embedEmitTM (lastEmb k) N).tr q inp work =
      ⟨(N.tr q inp fun _ => work (Fin.last k)).inputTape,
        fun j => if j = Fin.last k then (N.tr q inp fun _ => work (Fin.last k)).workTapes 0
          else (none, 0),
        (N.tr q inp fun _ => work (Fin.last k)).output,
        (N.tr q inp fun _ => work (Fin.last k)).state⟩ := by
  apply probe_action_eq
  · rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [if_true]
      conv_lhs => whnf
      split
      · rename_i i h
        rw [Subsingleton.elim i 0]
        rfl
      · rename_i h
        revert h
        show ((List.finRange 1).find? fun i => decide ((lastEmb k) i = Fin.last k)) = none → _
        simp [lastEmb]
    · simp only [Fin.castSucc_ne_last, if_false]
      conv_lhs => whnf
      split
      · rename_i i' h
        revert h
        show ((List.finRange 1).find? fun i' => decide ((lastEmb k) i' = Fin.castSucc i)) =
          some i' → _
        simp only [lastEmb, Function.Embedding.coeFn_mk, (Fin.castSucc_ne_last i).symm,
          decide_false]
        intro h
        rw [List.find?_eq_none.mpr (fun _ _ => by simp)] at h
        cases h
      · rfl
  · rfl
  · rfl

/-- (d) The decrement-phase tables agree at `refl`. -/
theorem probe_dec_refl_tr (k : ℕ) (f : FlagPhase) (inp : Option Bool)
    (work : Fin (k + 1) → Option Bool) :
    (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols (Function.Embedding.refl Bool))).tr
        f inp work =
      (decrementTM (k + 1) (Fin.last k)).tr f inp work := by
  rw [probe_embedEmit_lastEmb_tr, probe_lift_refl_tr]
  apply probe_action_eq
  · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
      simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
  · funext j
    rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
      simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h] <;>
      split_ifs <;> simp_all
  · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
      simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]
  · rcases f with _ | b | b <;> rcases h : work (Fin.last k) with _ | b' <;> (try cases b') <;>
      simp [decrementTM, MultiTapeTM.mapWorkSymbols, incrementTM, Action.mapWorkSymbols, h]

/-- (d) The whole hosts agree on every control at `refl` (Z5's hypothesis). -/
theorem probe_refl_agree {k : ℕ} {S : Type} [DecidableEq S] (M : MultiTapeTM k Bool S)
    (a : S) (exit : Option S) :
    (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn
      (counterLoopTM M a exit) Set.univ := by
  intro q _ inp work
  cases q with
  | body s => rfl
  | dec f => exact congrArg (Action.mapState (counterLoopDecExit a)) (probe_dec_refl_tr k f inp work)
  | done => rfl
  | escape => rfl

/-- (e) The landed `counterLoopTM_run_done`, statement copied verbatim, re-derived from
the generic contract at `refl` through Z5 (modulo Part 2's sorry). -/
theorem probe_rederive_done {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a : S) (exit : Option S)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some true else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .done ∧
        ((counterLoopTM M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠
          some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a exit).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (probe_refl_agree M a exit) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  simp only [z5]
  exact counterLoopTMVia_run_done (Function.Embedding.refl Bool) M a exit τ c w ct cp hw'
    d hd hround T hT

/-- (e) The landed `counterLoopTM_run_escape`, statement copied verbatim, re-derived
likewise. -/
theorem probe_rederive_escape {k : ℕ} {S : Type} [DecidableEq S] {x : List Bool}
    (M : MultiTapeTM k Bool S) (a e : S) (hea : e ≠ a)
    (τ : Cfg k Bool S x → ℕ) (c : Cfg k Bool S x)
    (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ e))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some e)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTM M a (some e)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape (counterWord w (r₀ + 1)) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTM M a (some e)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTM M a (some e)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j) := by
  have z5 (z : Cfg (k + 1) Bool (CounterLoopState S) x) (t : ℕ) :
      (counterLoopTM M a (some e)).runFrom z t =
        (counterLoopTMVia (Function.Embedding.refl Bool) M a (some e)).runFrom z t :=
    MultiTapeTM.runFrom_eq_of_agreeOn (probe_refl_agree M a (some e)) z t
      (fun _ _ _ _ => Set.mem_univ _)
  have hw' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      ct (cp + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    simpa [Function.Embedding.coe_refl] using hw
  have h := counterLoopTMVia_run_escape (Function.Embedding.refl Bool) M a e hea τ c w ct cp
    hw' r₀ hr₀ hround hexit T hT
  simp only [Function.Embedding.coe_refl, List.map_id] at h
  simp only [z5]
  exact h

/-- (f) The landed overlay transport (`SymbolLift`, pre-issue 2) applies to the decrement
from an **arbitrary** rich start: the run is the overlay of the `Bool` run from the decoded
shadow. -/
theorem probe_dec_runFrom_over {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (D : Cfg 1 Γ FlagPhase x) (t : ℕ) :
    ((decrementTM 1 0).liftSymbols e).runFrom D t =
      Cfg.liftOver e (by simp) D ((decrementTM 1 0).runFrom (Cfg.decodeSymbols e D) t) := by
  conv_lhs => rw [← Cfg.liftOver_decodeSymbols e D]
  exact MultiTapeTM.liftSymbols_runFrom_over e _ (fun _ _ _ _ => rfl)
    (fun q inp work j => probe_dec_noBlank q inp work j) _ D _ t

/-- (f) The shadow of a framed lifted counter word satisfies the `Bool` contracts' `hw`
(landed `FinTM.bufferTape_map_decode`). -/
example {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ} (D : Cfg 1 Γ FlagPhase x)
    (w : List Bool)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      D.workTapes 0 (D.workTapePos 0 + p) = FinTM.bufferTape (w.map e) p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      (Cfg.decodeSymbols e D).workTapes 0 ((Cfg.decodeSymbols e D).workTapePos 0 + p) =
        FinTM.bufferTape w p := by
  intro p hl hr
  change (D.workTapes 0 (D.workTapePos 0 + p)).bind (decodeBool e) = _
  rw [hw p hl hr, FinTM.bufferTape_map_decode]

/-- (g) The decrement-phase host configuration, state-renamed to the decrement's phase, is an
R1 configuration at `lastEmb k`: the counter tape is the selected tape, the body tapes are
R1's frame. Public R1 surface only (`embedEmitCfg_selected_tape`/`_pos`, and
`embedEmitTM_frame` at time `0`, as `counter_cfg_eq` does). -/
theorem probe_dec_cfg_eq {k : ℕ} {Γ S : Type} {x : List Γ} (f : FlagPhase)
    (c : Cfg k Γ S x) (ct : ℤ → Option Γ) (cp : ℤ) :
    (counterLoopCfgD (some (CounterLoopState.dec f)) c ct cp).mapState (fun _ => f) =
      embedEmitCfg (lastEmb k) (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) []
        (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ : Cfg 1 Γ FlagPhase x) := by
  have hl : ∀ i : Fin k, Fin.castSucc i ∉ Set.range (lastEmb k) := by
    rintro i ⟨j, hj⟩
    exact Fin.castSucc_ne_last i hj.symm
  have hf (i : Fin k) := (embedEmitTM_frame (lastEmb k)
    (⟨FlagPhase.run, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ :
      MultiTapeTM 1 Γ FlagPhase)
    (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) []
    (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ : Cfg 1 Γ FlagPhase x) 0).1
    (Fin.castSucc i) (hl i)
  have hc := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Γ Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1 (Fin.last k) (by
      rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · refine (?_ : _ = ct).trans (embedEmitCfg_selected_tape (lastEmb k) _ _ []
        (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ : Cfg 1 Γ FlagPhase x) 0).symm
      simpa only [counterLoopCfgD, Cfg.mapState, MultiTapeTM.runFrom_zero] using hc.1
    · rw [show (embedEmitCfg (lastEmb k) (Fin.lastCases ct c.workTapes)
          (Fin.lastCases cp c.workTapePos) []
          (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ :
            Cfg 1 Γ FlagPhase x)).workTapes (Fin.castSucc i) = c.workTapes i by
        simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (hf i).1]
      simpa only [counterLoopCfgD, Cfg.mapState] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · refine (?_ : _ = cp).trans (embedEmitCfg_selected_pos (lastEmb k) _ _ []
        (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ : Cfg 1 Γ FlagPhase x) 0).symm
      simpa only [counterLoopCfgD, Cfg.mapState, MultiTapeTM.runFrom_zero] using hc.2
    · rw [show (embedEmitCfg (lastEmb k) (Fin.lastCases ct c.workTapes)
          (Fin.lastCases cp c.workTapePos) []
          (⟨some f, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩ :
            Cfg 1 Γ FlagPhase x)).workTapePos (Fin.castSucc i) = c.workTapePos i by
        simpa only [MultiTapeTM.runFrom_zero, Fin.lastCases_castSucc] using (hf i).2]
      simpa only [counterLoopCfgD, Cfg.mapState] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · rfl

/-- (h) The generic layout (the fill's private `counter_layout`): `counter_cfg_eq`'s body with `Bool ↦ Symbol` and
`counter_last_unselected` inlined. -/
theorem probe_layout {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) :
    counterLoopCfgD q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ := by
  have hf := (embedEmitTM_frame Fin.castSuccEmb
    (⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ : MultiTapeTM k Symbol Unit)
    (fun _ => ct) (fun _ => cp) [] (c.mapState (fun _ => ())) 0).1
    (Fin.last k) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
  apply Cfg.ext <;> try rfl
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfgD, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.1
    · simpa only [counterLoopCfgD, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_tape Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [counterLoopCfgD, Cfg.mapState, MultiTapeTM.runFrom_zero,
        Fin.lastCases_last] using hf.2
    · simpa only [counterLoopCfgD, Cfg.mapState, Fin.lastCases_castSucc] using
        embedEmitCfg_selected_pos Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c i

/-- (h) The public `Bool` `counter_cfg_eq` (pre-issue 2), statement verbatim, as an instance
of the generic layout: its body swap. -/
example {k : ℕ} {S : Type} {x : List Bool}
    (q : Option (CounterLoopState S)) (c : Cfg k Bool S x)
    (ct : ℤ → Option Bool) (cp : ℤ) :
    counterLoopCfg q c ct cp =
      ⟨q, c.inputPos, Fin.lastCases ct c.workTapes,
        Fin.lastCases cp c.workTapePos, c.output⟩ :=
  probe_layout q c ct cp

end Route

#print axioms counterLoop_time_leD
#print axioms counterLoopTMVia
#print axioms counterLoopTMVia_run_done
#print axioms counterLoopTMVia_run_escape
#print axioms probe_embedEmit_lastEmb_tr
#print axioms probe_dec_refl_tr
#print axioms probe_refl_agree
#print axioms probe_rederive_done
#print axioms probe_rederive_escape
#print axioms probe_dec_runFrom_over
#print axioms probe_layout
#print axioms probe_dec_cfg_eq

/-! ## Part 4 — executed instances over a rich alphabet -/

section Checks

/-- Digits `0`, `1`; the symbol `2` is foreign. -/
def eD : Bool ↪ Fin 3 := ⟨fun b => cond b 1 0, by intro a b h; cases a <;> cases b <;> simp_all⟩

/-- A one-tape body configuration at the writer's anchor `0`, body head at `4`, a foreign
symbol at `3` (left of the written interval). -/
def cD : Cfg 1 (Fin 3) (Fin 2) [2, 1] :=
  ⟨some 0, 1, fun _ p => if p = 3 then some 2 else none, fun _ => 4, []⟩

/-- The counter tape: `w` at `cp = 5`, blank delimiters at `4` and `5 + |w|`, foreign symbols
at `3` and at `6 + |w|`. -/
def ctD (w : List Bool) : ℤ → Option (Fin 3) := fun q =>
  if q = 3 ∨ q = 6 + (w.length : ℤ) then some 2 else FinTM.bufferTape (w.map eD) (q - 5)

/-- Returning case: `w = [false, true]` (value 2, leading zero), round `writeAdvTM [2]`
(time 2), `T = 2·2 + counterOverhead w 3 = 4 + 12 = 16`. The counter ends `e true`, both
foreign frame cells survive, the pattern is written twice, the body head ends at `6`. -/
example :
    let z := counterLoopCfgD (some (.dec .run)) cD (ctD [false, true]) 5
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 none
    counterOverhead [false, true] 3 = 12 ∧
    (H.runFrom z 16).state = some .done ∧ (H.runFrom z 15).state ≠ some .done ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 6 = some (eD true) ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 3 = some 2 ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 8 = some 2 ∧
    (H.runFrom z 16).workTapes (Fin.last 1) 7 = none ∧
    (H.runFrom z 16).workTapes 0 4 = some 2 ∧ (H.runFrom z 16).workTapes 0 5 = some 2 ∧
    (H.runFrom z 16).workTapes 0 3 = some 2 ∧ (H.runFrom z 16).workTapes 0 6 = none ∧
    (H.runFrom z 16).workTapePos 0 = 6 ∧ (H.runFrom z 16).workTapePos (Fin.last 1) = 5 ∧
    (H.runFrom z 16).inputPos = 1 := by
  decide

/-- Escape case: the same body with exit `1`, so round `0` escapes after one step
(`τ := 1`): `T = 1 + counterOverhead w 1 = 1 + 4 = 5`, counter `counterWord w 1 =
[true, false]` mapped by `e`. -/
example :
    let z := counterLoopCfgD (some (.dec .run)) cD (ctD [false, true]) 5
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 (some 1)
    counterWord [false, true] 1 = [true, false] ∧ counterOverhead [false, true] 1 = 4 ∧
    (H.runFrom z 5).state = some .escape ∧ (H.runFrom z 4).state ≠ some .escape ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 6 = some (eD false) ∧
    (H.runFrom z 5).workTapes (Fin.last 1) 8 = some 2 := by
  decide

/-- A body with no tapes (`k = 0`), one stationary step per round: `w = [true]` (value 1),
`T = 1 + counterOverhead [true] 2 = 1 + 2 + 4 = 7`. -/
def unitBodyD : MultiTapeTM 0 (Fin 3) Unit := ⟨(), fun _ _ _ => ⟨0, fun j => j.elim0, none, some ()⟩⟩

example :
    let c0 : Cfg 0 (Fin 3) Unit [2] := ⟨some (), 1, fun j => j.elim0, fun j => j.elim0, []⟩
    let z := counterLoopCfgD (some (.dec .run)) c0 (ctD [true]) 5
    let H := counterLoopTMVia eD unitBodyD () none
    (H.runFrom z 7).state = some .done ∧ (H.runFrom z 6).state ≠ some .done ∧
    (H.runFrom z 7).workTapes (Fin.last 0) 5 = some (eD true) ∧
    (H.runFrom z 7).workTapes (Fin.last 0) 7 = some 2 := by
  decide

/-- Zero counters: `w = [false]` reaches `done` at `counterOverhead [false] 1 = 4` with the
counter `e true`; `w = []` at `counterOverhead [] 1 = 2`. -/
example :
    let H := counterLoopTMVia eD (writeAdvTM 1 0 [(2 : Fin 3)]) 0 none
    let z₁ := counterLoopCfgD (some (.dec .run)) cD (ctD [false]) 5
    let z₀ := counterLoopCfgD (some (.dec .run)) cD (ctD []) 5
    (H.runFrom z₁ 4).state = some .done ∧ (H.runFrom z₁ 3).state ≠ some .done ∧
    (H.runFrom z₁ 4).workTapes (Fin.last 1) 5 = some (eD true) ∧
    (H.runFrom z₀ 2).state = some .done ∧ (H.runFrom z₀ 1).state ≠ some .done ∧
    (H.runFrom z₀ 2).workTapes (Fin.last 1) 6 = some 2 := by
  decide

end Checks

end Turing

## ===== audits/s12-counter-fill-findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1 | minor | `Build/CounterLoop.lean:64–65` · module’s “Main definitions” | The declared historical status labels are **not the only remaining documentation issue**: the module summary still describes unrestricted physical decrement cost. | For `w = [true]`, `counterOverhead w 3 = 2 + 4 + 4 = 10`, whereas three restarted physical decrements cost `2 + 4 + 2 = 8`. The declaration docstring correctly restricts physical interpretation to `r ≤ value + 1`; the module summary does not. This is a residual SC-1 wording defect, not an unsound proof use. | Apply the same range qualification to the module summary during the scheduled documentation refresh. |
| F2 | minor | Bundle · comparison sources and delivery evidence | The bundle is not self-contained for every requested verification. | It omits `copy-text-screen.py` and the comparison sources `Build/{Loop,Primitives,Seam,Wrappers}.lean`. Thus the full screens, the comparison with `emitterP2_call_phase`, and the two Seam source bodies cannot be independently checked. The delivery ZIP and `SHA256SUMS` are also absent. Equality and arithmetic consistency of supplied screen outputs are independently verifiable; archive integrity and historical claims about which scripts the maintainer executed remain attestations. | Attach the pinned comparison sources, screen script, and archive/checksum evidence; distinguish supplied attestations from independently reproduced checks. |
| F3 | note | `counter_work_step`, `counter_decrement_run`; both decrement contracts | Symbol transport and decrement follow the binding routes, with one decrement run argument and no borrow re-trace. | `counter_work_step` proves inverse-read cancellation and write-update commutation directly; `runFrom_comm_of_step` supplies iteration. Its argument differs from the attached `relabelState_step`. Both decrement contracts invoke the corresponding framed increment contract through `counter_decrement_run`. Complement identity, double complement, buffer commutation including blanks, and the leading-prefix length identity are all present. The word inductions establish arithmetic, not another machine trace. | None. |
| F4 | note | `counter_rounds`; both host contracts | There is genuinely one round induction with an unrestricted final body state. | The sole host induction is `induction n` in `counter_rounds`. For positive `n`, its endpoint is the final orbit state mapped through `counterLoopRedirect`; it need not be the anchor, exit, or even live. The successor case combines only `counter_debit` and `counter_body`, using `counter_span_append`. Both public host proofs instantiate this lemma. The trajectory-witness disjunction distinguishes completed rounds from the final boundary; it does not hide two inductions. | None. |
| F5 | note | `counter_dec_injective`, `counter_redirect_injective`, `counter_debit`, `counter_body` | Both embeddings are injective, and their transport guards correctly exclude endpoints. | The five decrement controls have distinct images. Body redirection sends the anchor to `dec run`, at most one distinct designated exit to `escape`, and all remaining states injectively to `body`; when `exit = some a`, anchor priority preserves injectivity. Decrement transport requires the guard only at `u < t ≤ cost`. Body transport executes the first step explicitly, then obtains suffix guards from strictly intermediate original times. Neither transport requires the redirected endpoint to remain good. | None. |
| F6 | note | Counter arithmetic · `counter_dec_spec` through `counterOverhead_le`; `counterLoop_time_le` | The potential argument and every physical interpretation stay within the SC-1 range. | `counter_potential` proves exactly `counterOverhead w r + 2 * w.count true = 4 * r + 2 * (counterWord w r).count true` under `r ≤ value`. Exhaustion gives the all-false word; adding its full-width underflow proves the whole-run bound. The host induction uses successful decrements only below exhaustion; completion adds one underflow, while escape stops at `r₀ + 1 ≤ value`. Unrestricted width preservation makes no physical-run claim. The uniform bound uses the prescribed termwise sum argument. Independent finite checks passed for 511 words and 43,946 prefix identities. | None. |
| F7 | note | `counterSpan`, `counterPatch`; phase and final-configuration helpers | The new configuration and trajectory machinery preserves the intended framing and exact boundary behavior. | `counterSpan` excludes exits strictly before the endpoint and bounds counter position and the **whole body-head vector** inclusively through it. `counterPatch` overwrites only the word interval; equal-width composition and delimiter preservation are proved separately. At value zero, `counter_rounds` uses its zero branch and completion invokes underflow without any assumption on `c.state`. At `r₀ = value − 1`, escape specializes the successful-round invariant directly, leaving the zero word without a trailing underflow. Successor redirection adds no dispatch step. Independent framed-decrement checks passed for 1,533 configurations, including empty words and negative head positions. | None. |
| F8 | note | `s12-counter-fill.patch` · frozen surface | The freeze attestation is independently confirmed from the attached patch and source. | Reversing and validating all 15 hunks reconstructs Git blob `3c0d10f6653d0e56461c9cdfe9bbf7416062a976`; the supplied result is `c60fdefe9631a846077f71001036b498cea85529`, matching both patch hashes. All 24 explicit public declaration signatures are byte-identical; exactly the ten sanctioned theorem bodies differ. The 12 definitions, inductive type, explicit instance and deriving clause remain unchanged. There are exactly 25 new private declarations, unchanged imports, and one changed file. The source SHA-256 matches the report. | None. |
| F9 | note | Duplication · supplied screens and four in-file candidates | The supplied screen delta is correct; the four in-file candidates are interface glue, not duplicated routine proofs. | The two after-outputs are byte-identical; every before-pair and measurement survives unchanged. Totals satisfy `682 + 4 = 686` and `282115 + 67 + 62 + 94 + 448 = 282786`. The two complement overlaps repeat short extensionality/simplification steps; the word-value overlap eliminates underflow using the shared zero characterization; the `448/750` decrement overlap assembles parallel framed conclusions around the single shared transport. No additional trace or round argument is reproduced. The supplementary log contains **two directed Seam matches**, both `79/135`, representing one identical source-template family. Their idiom-versus-copy classification cannot be independently finalized without those source bodies (F2). | No factoring required for the four inspected in-file candidates. Complete the supplementary source comparison using F2’s attachments. |
| F10 | note | Three docstring appendices; file-size justification | The appendices accurately describe the delivered proofs, and the temporary size exception is justified. | Original documentation is retained except for the three authorized appendices. They correctly identify the shared transport, unrestricted-final-state induction, and potential-based amortization. The historical “statement skeleton” and “All sorried” labels are explicitly disclosed; F1 identifies the additional wording issue. The source has exactly 1,205 lines. Exclusive ownership and the frozen surface support retaining it until the recorded §12.2c reorganization. | Perform the scheduled documentation refresh and retain the recorded split obligation. |
| F11 | note | Replay, axiom and lint attestations | The attached logs support the reported results, but this audit is not a fresh kernel or repository-wide replay. | The maintainer log reports exit 0 for CounterLoop and the facade, with no matching error/sorry lines. All 24 public axiom prints lie within the standard triple; six list no axioms, and none lists `sorryAx`. The agent additionally prints the unchanged derived instance. Lint reports 0 FAIL and six size warnings. The modified source contains no admissions or foreign/unsafe implementation hooks, and the patch references no C/shim file. Commit ancestry, tip identity, repository-wide import absence, archive contents, and historical execution claims cannot be independently established from these attachments. | Preserve these as maintainer attestations; do not describe this audit as independently rerunning Lean, lint, or archive verification. |

**Overall verdict: PASS for the attached fill surface — 0 blockers, 0 majors, 2 minors, 9 notes. Full screen reproduction, the supplementary source comparison, and archive-integrity verification remain limited as recorded above.**

## ===== audits/s12-8-statements-findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | Build/CfgRecord.lean · `exists_recordStepTM`; Build/InputCall.lean · `exists_inputSeekTM` | The contracts are too weak for their named space-bounded consumers. | They bound time and restore the final tapes, but impose no bound on visited work cells. Concrete admissible detour: when the native head reads a symbol, move it left to position 0, recording one unary scratch mark per move; retrace and erase the marks while restoring the input head and scratch head. At a blank input position, skip this detour. It costs O(pos + 1), restores everything, and visits pos + 1 scratch cells. Prepending it preserves both stated time bounds. For record stepping, take the identity source machine with k = 0 and identity tag update: the detour followed by `yes` already satisfies the whole functional contract, but at pos = n its space is Θ(n), while the record length L = `posWidth n + 4` is Θ(log n). Thus restoration and O(L + n) time do not yield the O(L) workspace required by the advertised Savitch route; the analogous seek contract does not yield logspace either. | Strengthen the same existential witnesses with trajectory/visited-set bounds through the verdict: O(L + 1) for record stepping and O(w.length + 1) for input seeking, independent of native-head travel. Prefer fixed intervals about entry heads so repeated calls compose. Re-audit the strengthened statements before fill. |
| 2 | minor | Build/InputCall.lean · `exists_inputSeekTM` proof sketch | The literal existence statement is true, but its cited rewind route is off by one. | The statement asks for input position p, restored work tapes/heads/output, and a first exit within C·(w.length + pos + p + 1). `Simulation.lean::timed_rewind` returns to position 1, with bound pos + 2; it does not stop at position 0. For x = [false], w = [], p = 0, the sketched rewind followed by zero right moves leaves position 1. After one extra left move, copy–rewind–countdown–clear gives the claimed statement: the costs are bounded by `6*w.length + pos + 5*p + 13` with four seam dispatches, so a fixed coefficient suffices. Boundary checks: empty input/empty counter, leading-zero counters, and p = n + 1 all work. | Insert the left move after `timed_rewind`, correct its quoted bound, and retain the finite first-exit construction. Add the space guarantee in finding 1. |
| 3 | minor | Build/InputCall.lean · `FinTM.exists_inputCallTM` proof sketch | The statement is true, but the proposed inherited first-return proof lacks the callee's time-zero cut. | The requested module copies x from the blank seam, computes f x, and installs it on genuine tape 0 within c·(T(n) + n + (f x).length + 1), with positive return time. The copy establishes the exact entry seam of `exists_installCallTM`. However, that theorem excludes exits only at `0 < t' < t`, whereas `seamCompTM_firstReturn_ofCfg` also needs t' = 0. A stationary identity callee with `entry = exit` and return time 1 satisfies the install-call interface, but the proposed composite visits its final exit immediately after dispatch, before the proposed total time. Split on `entry = exit`; in that branch, `seamReleaseTM_firstReturn` supplies a fresh entry before composition. Empty input/result, identity f, and a constant-output zero-work-tape source then present no obstruction; the returned module still has positive tape count. | Add the entry/exit case split and release adapter to the sketch. Do not infer a time-zero cut from a first-positive-return contract. |
| 4 | minor | Build/CfgRecord.lean · `recordValid_iff` docstring | The claim that every conjunct is a one-field fold needs a uniformity qualification. | The equivalence itself is correct (finding 27). A fixed finite-state fold can check symbol kinds and zero/one/multiple marks, but cannot uniformly enforce the variable length `2*s + 1`, width `posWidth n`, or comparison with n + 1 from that field alone without receiving those bounds. For example, the same singleton cell field is valid at s = 0 and invalid at s = 1. The landed design's §8 item 10 already recognizes the need for a width template and defers the validator. | Say that the shape characterization supports a validator using finite-state folds together with supplied width/bound templates or counters. Preserve the explicit deferral. |
| 5 | minor | Build/CfgRecord.lean · `Cfg.InWindow` added docstring | A windowed record determines the configuration core, not the full configuration. | The predicate bounds every work head by s and forces every work cell outside the window to be blank. Take two configurations identical in all those components and in state/input position, but with outputs [] and [false]. Both are windowed and have equal `cfgRecord` for the same tag, yet are unequal configurations. The actual `cfgRecord_inj` correctly excludes output equality. | Replace “determines its configuration” by “determines its configuration core, together with its separately supplied tag.” |
| 6 | minor | Build/Catalog.lean · `fieldOffset` docstring | The asserted end-offset formula has an empty-list exception. | The definition sums `field.length + 1` over `fs.take j`. For nonempty fs, `fieldOffset fs fs.length = (joinFields fs).length + 1`. But `fieldOffset [] 0 = 0` and `(joinFields []).length + 1 = 1`; the unconditional prose is false. The seek-end contract correctly excludes this case. | Qualify the formula by `fs ≠ []` and state the empty offset separately. |
| 7 | minor | audits/logs/s12-8-statements-declfreeze.log · promotion citation count | The freeze is supported, but the log's “4 occurrences” should be 3. | The supplied patch reverses cleanly against the attached sources. `Cfg.InWindow`'s declaration and body are byte-identical across the move; replacing only visibility/kind/name makes the promoted seam declaration and proof byte-identical. The only old proof-body edits are one name substitution in each of `seamComp_right`, `seamComp_firstReturn_general`, and `seamComp_visited_general`: three occurrences. Existing signatures and all other old bodies remain unchanged in the patch. | Correct the occurrence count to 3 in the resolutions/errata record; preserve the issued evidence. |
| 8 | minor | audits/duplication-ledger.md · Catalog cumulative denominator | The standing Catalog accounting needs a post-statement-layer denominator. | The ledger prints 318/428 = 74.3%, while the freeze inventory and source show 75 public + 384 private = 459 textual declarations after this change. The 31 additions remove none of the recorded old members. Under the ledger's existing membership classification, the resulting fraction is 318/459 = 69.3%. This is accounting within the already acknowledged family, not new debt requiring a major. | Append the current denominator/fraction and date, retaining the historical snapshot and scheduled 12.2c resolution. |
| 9 | note | Build/Catalog.lean · `joinFields`, `fieldsTape`, `fieldsTape_field` | The layout and framed-field statement are true, including empty fields. | `joinFields` inserts one `none` between lists of `some` symbols; `fieldsTape` places that list at 0 and is blank outside it. Each valid field index therefore has its own contents at its offset, a separator or exterior blank immediately before, and a separator or exterior blank immediately after. The first field, last field, and an empty field all satisfy the stated inclusive interval from −1 through the field length; `fs = []` supplies no valid index. | No statement change. |
| 10 | note | Build/Catalog.lean · `compareTM_run_ofCfg` | The framed comparison returns the correct verdict at exactly `2*δ + 2`, restoring the entire configuration except control. | Choose δ as the first unequal index or the first exhausted word length. The table takes δ matching right moves, one left turn carrying the verdict, δ left moves across the intact common prefix, and one right move from the left delimiter. These phases exclude every `done` state before the stated time and keep both heads between their start minus 1 and start plus δ. Checks: two empty words, first-symbol disagreement, and a proper prefix; displaced heads and arbitrary exterior cells do not affect these reads. | No statement change; generalize the existing compare trace and derive the canonical row at fill. |
| 11 | note | Build/Catalog.lean · `SeekPhase`, `skipTM`, `skipTM_run_ofCfg` | Skip is a read-only forward traversal ending one cell beyond the right delimiter. | Each of the w.length nonblank cells causes one right move in `run`; the delimiter causes one further right move into `done`. Thus time is w.length + 1, the stated head interval is exact, and no earlier exit occurs. Empty words take one step; singleton words take two; a displaced word with nonblank cells immediately outside the required interval behaves identically. The unused seek phases are stationary. | No statement change. |
| 12 | note | Build/Catalog.lean · `skipBackTM`, `skipBackTM_run_ofCfg` | Skip back is the position inverse of skip, with time u.length + 3. | Two unconditional left moves cross the current cell and preceding separator, reaching the previous word's last cell, or its left delimiter when u is empty. Then u.length left moves and one right move return to that word's first cell. This proves the exact time, cut, unchanged tapes/input/output, and interval from start − u.length − 2 through start. Checks: empty previous field, singleton previous field, and an arbitrary nonblank current cell with displaced heads. | No statement change; see recommendation 41. |
| 13 | note | Build/Catalog.lean · `seekEndTM`, `seekEndTM_run_ofCfg` | The nonempty-table end seek has the stated `D + 1` time and head displacement D. | Here D is the sum of field lengths plus one delimiter per field. Every cell through the first terminal blank costs one right move, and the second terminal blank costs one stationary move into `done`; nonempty fields prevent an earlier double blank. Checks: one singleton field, several unequal-length nonempty fields, and arbitrary nonblank framing beyond the second terminal blank. For an empty table the actual machine instead takes two steps and moves right once, explaining the necessary `ws ≠ []` hypothesis. | No statement change; settle the empty-table layout as in recommendation 42. |
| 14 | note | Build/Catalog.lean · `seekStartTM`, `seekStartTM_run_ofCfg` | The start seek is true on its stated entry domain, with exact time `D + 4`. | The current nonblank cell and preceding field layout give D + 2 left moves to the second blank before the table; two right moves finish at its start. This proves the cut and stated trajectory. Checks: no preceding fields gives four steps; one preceding singleton gives six; several preceding fields add exactly their lengths and separators. A head on the blank returned by `seekEndTM` does not satisfy `hcur` and must first be repositioned. | No statement change; make the end-to-start adapter explicit in table consumers. |
| 15 | note | Build/Catalog.lean · `mealyRun`, `scanResult`, `ScanPhase`, `scanTM_run_ofCfg` | The two-pass semantics and exact `2*w.length + 2` contract are correct. | `mealyRun` threads the accumulator while producing one symbol per input symbol. `scanResult` applies the backward transducer to the reversed forward output, starting from the forward final accumulator, then reverses the output back. The machine performs w.length forward writes, a delimiter turn, w.length backward writes, and the left-delimiter return; it writes only inside the word and reaches `done` only on the final step. Checks: empty word, singleton word, and forward/backward Boolean negation (the backward pass must read the rewritten cell, giving the original word again). | No statement change. Finite-state consumers must instantiate the accumulator with a finite type. |
| 16 | note | Build/Catalog.lean · `scanKeep`, `scanFold`, `scanResult_fold` | The fold instance returns `(w.foldl δ a₀, w)`. | `scanFold` changes only the accumulator, so induction on w gives that pair after the forward pass; `scanKeep` changes neither component on the return. Empty words return a₀, a singleton applies δ once, and a noncommutative update preserves left-to-right order. Word contents and length are unchanged in all cases. | No statement change. |
| 17 | note | Build/Catalog.lean · `scanMap`, `scanResult_map` | The map instance returns `(a₀, w.map f)`. | `scanMap` changes each symbol by f while leaving the accumulator fixed; the identity return restores list order without another application of f. The same calculation covers an empty list, a singleton, and a noninjective constant map. No injectivity or inverse hypothesis on f is needed. | No statement change. |
| 18 | note | Build/Catalog.lean · `scanShift`, `scanResult_shiftRight` | The right-shift identity is true for arbitrary get/set functions. | At a forward step, the old cell's `get` value becomes the next accumulator and the current cell becomes `set cell previous`. Induction gives exactly the displayed `zipWith`, with the old final mark left in the accumulator. Checks: empty word, singleton receiving b₀, and marks [true, false, false] with b₀ = false, producing [false, true, false] for a lawful mark setter. The algebraic identity needs no setter laws; the interpretation as a mark shift does. | No statement change; instantiate get/set with the actual mark projection and update. |
| 19 | note | Build/Catalog.lean · `scanResult_shiftLeft` | The left-shift identity has the correct order and boundary value. | The forward identity leaves `(b₀, w)`; applying the preceding delay argument to `w.reverse` and reversing back gives successor marks, with b₀ in the last cell and the original first mark as final accumulator. Checks: empty word, singleton, and marks [false, false, true] with false boundary, producing [false, true, false]. The `zipWith` truncation correctly handles the empty-list case. | No statement change. |
| 20 | note | Build/Catalog.lean · `scanCarry`, `scanResult_carry` | The carry identity describes exactly the top prefix, first non-top digit, and unchanged suffix. | While carry is true the transition applies `next` and retains carry exactly on a top digit; after the first non-top digit, every later transition is the identity. Hence precisely the top prefix and, if present, its successor cell change, and the final carry is `w.all top`. Checks: empty word gives `(true, [])`, first digit non-top changes only that digit, and an all-top word changes every digit and retains carry. An arithmetic odometer interpretation additionally uses the intended top/next digit enumeration. | No statement change. |
| 21 | note | Build/Scan.lean · `WritePhase`, `writeConstTM_run_ofCfg` | The constant writer overwrites exactly its word interval and returns in `2*w₀.length + 2` steps. | The finite state counter performs w₀.length writes/right moves, one stationary phase change, w₀.length left moves, and one stationary exit. It never reads the old cells, so arbitrary old contents and exterior frames are preserved as stated, with the head confined to the declared interval. Checks: empty pattern takes two steps, singleton takes four, and a displaced overwrite into a nonblank interval leaves both exterior cells untouched. | No statement change. |
| 22 | note | Build/Scan.lean · `writeAdvTM_run_ofCfg` | The advancing writer has a first positive return to state 0 at w₀.length + 1. | States 0 through w₀.length count the writes; the last stationary transition returns to 0. For a nonempty pattern all intermediate states are nonzero, and the head advances exactly by the pattern length. Checks: empty pattern is one stationary round, singleton is a two-step round, and two consecutive rounds write two contiguous copies. The empty-pattern cut is correctly over strictly positive intermediate times. | No statement change; retain the cyclic convention as in recommendation 43. |
| 23 | note | Build/Scan.lean · `inputCopyTM_run_ofCfg` | The native-input copier restores both heads and has exact time `2*x.length + 2`. | From input position 1, x.length lockstep writes copy the input; the right marker turns both heads left; x.length left moves and the left-marker right move restore their entry positions. The work-tape return is guided by the native input, so it needs no destination delimiter and overwrites only the prescribed interval. Checks: empty input gives two steps, singleton gives four, and a nonblank destination frame at start − 1 is preserved despite being visited. | No statement change. |
| 24 | note | Build/Scan.lean · `inputFoldTM_run_ofCfg` | The native fold returns the left fold verdict, restores input position 1, and moves no work head. | The forward input scan accumulates `x.foldl δ a₀`; the backward scan preserves that accumulator. The same marker accounting gives `2*x.length + 2` and excludes an earlier `done`. Checks: empty input, zero work tapes, and a foreign symbol in the middle of a rich input. The latter is seen as an ordinary nonblank rich symbol by this validator, so it can set a persistent rejection flag. | No statement change; this supports O6. |
| 25 | note | Build/CounterLoop.lean · `expandTM`, `expandTM_run_ofCfg` | The expansion is the stated counter-loop instance, with the correct exact time and final counter. | Use `writeAdvTM` at anchor 0 with constant positive round time pat.length + 1. After r rounds its head has advanced by r·pat.length and its written interval contains r contiguous copies; `counterLoopTM_run_done` supplies d rounds followed by the first underflow, so the total is `d*(pat.length + 1) + counterOverhead w (d + 1)`, and every counter digit is true. Its no-exit and head clauses transfer directly. Checks: d = 0, empty pattern with d > 0, and nonzero d with leading-zero counter digits and nonblank exterior frames. | No statement change; retain the single existing loop induction. |
| 26 | note | Build/CfgRecord.lean · `cfgRecord_inj` | The record is injective on cores and tags under the two window hypotheses. | State/tag constructors are injective, and `2^(posWidth n) > n + 1` makes the fixed-width input-position digits injective on every possible input position. Tape-field equality gives all in-window contents and the unique marked head; both window predicates give equality outside. Checks: k = 0, s = 0, and configurations with different outputs but the same core/tag. Dropping either configuration's outside-blank requirement permits an unrecorded nonblank cell at s + 1; dropping both head bounds permits distinct outside heads with no marks. The hypotheses are sufficient and protect the necessary information, though their individual conjuncts need not be logically minimal. | No statement change. |
| 27 | note | Build/CfgRecord.lean · `RecordValid`, `recordValid_iff` | The validity equivalence is true in both directions. | Forward, read the field count, bounded input position, contents, and unique head mark from a windowed configuration. Backward, choose input `List.replicate n false`, input position v (valid because v ≤ n + 1), head `m - s` for each tape, the supplied contents inside the window, blank contents outside, and arbitrary empty output. This reconstructs exactly the supplied fields. Checks: n = 0 permits positions 0 and 1 with one digit; k = 0 removes the tape-field clauses; s = 0 forces a single marked cell. No-mark/multiple-mark fields and a representable value n + 2 are correctly rejected. | No statement change; correct only the uniform-validator prose in finding 4. |
| 28 | note | Build/CfgRecord.lean · `exists_recordStepTM` functional content | The functional/time statement is constructible; its missing space guarantee is separate. | Read the finite state/tag/scanned-cell/edge data before writing; the next configuration is outside the window exactly when a moved work head crosses an edge, so that branch can return `no` with the original record. Otherwise rewrite the scanned cells, marks, state, tag, and clamped input position; the layout length on both sides is `k*(2*s + 1) + posWidth n + k + 4`, so the in-place interval is sufficient. To satisfy arbitrary host input positions, explicitly save the original position in binary, perform the simulated read, and restore it; when n = 0, detected by the one-digit position width, the input is known blank and need not be moved. Fixed many scans and amortized counter operations give O(L + n + 1). Checks: halted c uses `outputSymbol = none` and hupd, s = 0 with an outward move takes `no`, and k = 0 only updates state/input position/tag. | Add finding 1's bound and name the saved-input-position and clamping obligations in the construction sketch. |
| 29 | note | Build/CfgRecord.lean · `exists_recordEqTM` | Empty fields do not make the equality statement false; the one-sided length bound is adequate. | The fixed field count k + 3 lets finite control compare exactly that many fields, counting consecutive delimiters individually rather than treating a double blank as table termination. Every successful field comparison is followed by skips; at the first failure both heads have already returned to that field's starts, and only the preceding equal fields need to be crossed back. Each failed comparison costs at most twice the current fs field length plus two, so an arbitrarily longer gs does not violate the bound. Checks: all fields empty, unequal first fields, and equal prefixes followed by a short fs field versus a very long gs field. | Keep the stronger arbitrary-field-list contract; neither nonempty fields nor `RecordValid` is necessary. |
| 30 | note | Build/CfgRecord.lean · `exists_recordTestTM` | The state/tag test needs neither a window hypothesis nor any relation between host input y and recorded input x. | The first and last fields contain exactly the state and tag; k + 2 forward skips, two folds, and inverse skips read them and restore the head and tape. Their total length is O(L), and finite Q/T make dispatch on P finite. Checks: k = 0, a nonwindowed c, and a completely different native input y. A constant predicate may validly use an immediate verdict; it is still a reached, correct verdict. | No statement change. |
| 31 | note | Build/Seam.lean · `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | Both branches have exactly one dispatch step and support arbitrarily long continuations. | The definition nests the e₁ seam inside the e₂ seam. On e₁, the outer exit `Sum.inl e₂` is avoided before the host exit by hcut, at the exit by e₁ ≠ e₂, and afterwards because the inner continuation lives in the other summand (or is halted). On e₂, the inner seam stays on its host prefix and the outer seam dispatches directly. Checks: T₀ = 0, an immediately halting continuation, and a continuation run longer than the host time; all give the displayed state embeddings and `T₀ + 1 + t`. | No statement change; reuse the promoted prefix lemma and the existing right lockstep. |
| 32 | note | TuringMachine/SymbolLift.lean · complete R8.0 public surface | The transport statements are correctly restricted and preserve exact time and work space. | `decodeBool` is a partial inverse of the embedding; actions map writes and emissions, configurations map tapes/output/input while preserving state and head coordinates, and lifted transitions decode reads before applying the original table. Thus the step square commutes on lifted configurations, iteration gives `liftSymbols_runFrom`, and equal head trajectories give equal visited sets and `spaceUsed`; initialization and the computation-via-e corollary follow on encoded inputs. Checks: zero tapes, halted configurations, and arbitrary nonempty output prefixes remain covered. Mixed record tapes are not globally lifted configurations: use R1 to isolate dedicated digit tapes and put the other tapes/output prefix in its frame. Keep `liftSymbols_step` public as the useful local form. | No transport statement change. Do not apply the run or space theorem directly to a configuration with foreign symbols on its selected tapes. |
| 33 | note | machine-library-design.md · O6; SymbolLift/Scan/AlphabetReduction | Mandatory native-input validation is the right resolution for the currently exported alphabet-reduction space theorem. | A concrete binary machine can scan right to the first blank, move right once, then halt if it still reads blank and otherwise move a work head right forever. On every binary input the first blank is the clamped right boundary, so its work space is constant. On rich input `[foreign, e false]`, the lifted machine sees the foreign symbol as the first blank, then a digit, and uses unbounded work space. `inputFoldTM` can reject every input containing a foreign symbol with fixed work heads, while accepted inputs have the form `x.map e`. This supplies the domain split required by `alphabet_reduction_spaceUsed`'s all-rich-input hypothesis, provided the subsequent modules also have the bounds missing in finding 1. | Retain O6; input validation alone does not repair the missing valid-input workspace contracts. |
| 34 | note | Build/CfgRecord.lean · `RecSym`, `recSymFintype`, `digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length`, `RecordAt` | The carrier, width, field-count, and local framing definitions match the rich-record design. | The alphabet is a disjoint union of digits, content/mark pairs, optional states, and tags; finiteness follows from finite Q/T, and the digit constructor is an embedding. `binDigits` takes low bits; `posWidth` is the bit length of n + 1, which is positive even at n = 0. `cfgRecord` has one state field, one position field, k tape fields of length 2s + 1, and one tag field, hence k + 3 fields; all are nonempty. `RecordAt` constrains only the layout and its two delimiters, leaving the exterior arbitrary. The output is deliberately omitted and the tag is separately supplied; a consumer still proves that its chosen tag tracks emissions. | No definition change; use the core/tag invariant when connecting to graph vertices. |
| 35 | note | Build/CfgRecord.lean and Build/InputCall.lean · existential quantifiers and exit clauses | The modules are not satisfiable by a nonterminating implementation on an admissible entry. | Each record contract supplies a finite t and an exact verdict configuration; for stepping, the window predicate and its negation exhaust the two implications. `yes ≠ no` makes the verdicts observable. For `inputSeek`, entry ≠ exit follows globally: choose x = [], w = [], p = 0 and an entry configuration with input position 1; the required movement forces t > 0, and then the u = 0 cut excludes equality. It does not follow from the cut alone when t = 0. Empty tag types give no admissible tagged records, but the named consumer uses inhabited `Fin 3`; constant tests or identity steps may legitimately return at time 0. The input-call row's positive tape count prevents an empty-domain fake installation. | No extra termination hypothesis is needed. Describe the input-seek nonvacuity argument with the required witness. |
| 36 | note | audits/logs/s12-8-statements-{merged-replay,replay,replay-base}.log; preship evidence | The supplied replay and pre-ship counts are internally consistent. | The detailed base log has 14 module exits and 10 sorry warnings; the pre-merge log has 17 exits and 35 = 10 + 25 warnings. The merged summary has 18 distinct module rows, all exit=0/errors=0, totaling 35 sorries, with SymbolLift at 0; its order matches the supplied order list. The new source distribution is Catalog 12, Scan 4, CfgRecord 5, CounterLoop 1, InputCall 2, Seam 1. Non-sorry output counts match exactly: Hardness 300, Catalog 338, Seam 10. The pre-ship source has 35 examples (30 `decide` proofs, four `simp` proofs, one application of `cfgRecord_length`), matching the no-error attestation and the listed coverage; it does not execute the existential modules or prove their universal contracts. | Accept the counts as checked log/source facts, with the execution boundary in finding 39. |
| 37 | note | audits/evidence/s12-8/R80TransportProbe.*; draft probe; axiom and lint logs | The axiom and lint attestations are supported by the attached outputs. | The R8.0 probe prints exactly 14 public declarations; every reported dependency is among propext, Classical.choice, and Quot.sound, with no sorryAx. The separate prints for `cfgRecord_length` and `seamCompTM_runFrom_left` report propext and Quot.sound. The superseded draft output has exactly 12 sorry warnings and no errors; it is not evidence that the landed existential contracts were filled. Both transport and statement style logs contain 0 FAIL and the same 14 file-size WARN paths; the PSPACE run has 0 FAIL/0 WARN. Catalog and CounterLoop's attached lengths are 11,789 and 1,275. | Accept these reported results; keep the draft explicitly superseded and the two admitted/proved inventories distinct. |
| 38 | note | Build/Catalog.lean · action helpers/seek family; Build/Scan.lean · writers; copy-text evidence | No new wholesale duplication of proved material is established by the twelve new pairs. | Rerunning the supplied script on the attached after-sources and patch-reconstructed screen base reproduces both outputs byte-for-byte: 520 declarations/396 pairs/119,207 characters before; 535/408/120,748 after. The 12 new directed pairs are exactly the disclosed same-file pairs, with none across files and none removed after promotion-name matching. `tapeAction` genuinely constructs one selected-tape action; `inputMoveAction` genuinely constructs an input-only action, shared by all new tables. The seek machines have different stop/return behavior, so 100% tiled coverage of the short skip text is not equality of transition tables; the two writers likewise have different return control. These are small related definitions, with no copied new proofs. The historical first-attempt 17 cross-file pairs cannot be reproduced because that intermediate source/output is not attached. | No new debt major. Record the same-file similarities, preserve the existing ledger acknowledgments, and enforce the promised shared trace at fill; do not treat a text-screen zero as a semantic no-duplication proof. |
| 39 | note | audits/s12-8-statements-pack.md · evidence boundary / missing independent-replay inputs | Some attestations cannot be independently re-executed or established from this bundle. | The bundle supplies the changed sources, the stated supporting layers, and a patch that applies in reverse, but not git ancestry/merge records, the complete dependency graph and consumer sources, the check/lint executables, or a Lean toolchain/dependency installation. Therefore fresh olean production, the asserted commit ancestry/clean merge, and completeness of the full downstream closure remain repository-side execution attestations; I verified their supplied counts/order and source consistency, not a new Lean run. In particular the absent `ConfigGraph.lean`/Savitch consumer interfaces and the facade/root files prevent certification of exact consumer elaboration and root reachability beyond the attached design. No missing content has been assumed. | If independent replay, exact consumer-interface matching, or root reachability is required at this gate, attach those specific inputs. Keep this report's evidence boundary explicit. |
| 40 | note | Build/Catalog.lean, Build/CfgRecord.lean, TQBF.lean · placement and naming | The landed namespace and local dependency choices are coherent; the added import weight is real. | The seek signatures use the field-layout definitions, so their shared placement in Catalog avoids a dependency on the richer record carrier. CfgRecord imports Catalog and SymbolLift, with no CounterLoop import; TQBF directly imports CfgRecord after deleting its old `InWindow` declaration. `RecSym` and its operations live under Turing, and transport operations live under their owning type namespaces. This matches the recorded relocation decision and introduces no cycle in the supplied dependency edges, although TQBF now inherits the large Catalog layer. The new machine/contract sketches describe prospective fills rather than claiming these 25 admissions are proved. | Accept this placement for the recorded phase; move low carriers/layouts into small shared modules during the scheduled per-theme split, and settle facade wiring in recommendation 46. |
| 41 | note | machine-library-design.md §12.8a §8 · open question 1 | Recommendation: retain skip back as the inverse of skip. | Record consumers naturally finish a forward skip at the next field's first cell. The landed inverse accepts exactly that position, works even for an empty previous field, and restores the original head; a mirror starting at the last symbol would require an extra entry adapter. | Human decision: retain the inverse convention and its u.length + 3 cost. |
| 42 | note | machine-library-design.md §12.8a §8 · open question 2 | Recommendation: give tables a fixed nonempty header and specify both boundary sentinels. | A header makes the physical field list nonempty even when the record list is empty, so seek-end's precondition is uniform; use two blanks before the first header cell and after the final field. This does not itself turn the second terminal blank into a valid seek-start entry. From that blank, skip back over the final field first, then apply seek start at its nonblank first cell; a header ensures there is always such a field. For S1b alone, retaining the initial vertex forever is another valid nonemptiness invariant. | Human decision: adopt the header for the shared table abstraction and include the repositioning adapter in its contracts. |
| 43 | note | machine-library-design.md §12.8a §8 · open question 3 | Recommendation: retain the cyclic advancing writer. | Its first positive return time is always pat.length + 1, including the empty pattern, exactly the counter-loop round discipline. A separate stationary done state would require the loop to adapt the routine back to its anchor; one-shot callers already have `seamReleaseTM`. | Human decision: retain the cyclic definition and document the release adapter at one-shot uses. |
| 44 | note | machine-library-design.md §12.8a §8 · open question 4 | Recommendation: retain the fixed tape layouts and use R1 for host selection. | The step module can reserve a finite existential scratch bank with record on local tape 0; equality needs two selected tapes and testing needs one. R1 embeds these banks injectively into larger hosts while preserving unselected tapes, arbitrary head offsets, and output prefixes. Hosts can establish `RecordAt` using the field-layout lemma and provide a blank scratch bank, which the exit restores for reuse. | Human decision: retain the local layouts. Add the space clauses in finding 1 before fixing their interfaces; accept the later precise InputCall import when the fill actually uses it. |
| 45 | note | machine-library-design.md §12.8a §8 · open question 5 | Recommendation: audit deferred validity/init/next/table rows with S1b's concrete layout. | Their uniform contracts depend on headers, radius/width templates, enumeration order, and find/append entry positions, none of which is fixed by the present existential rows. The current gate can review the landed subset without pretending that these omitted rows, `inputLengthTM`, or `counterLoopTMVia` already exist. | Human decision: keep them deferred, with a separate statement gate before S1b fill consumes them. Track R8.0b and input-length construction as explicit prerequisites. |
| 46 | note | machine-library-design.md §12.8a §8 · open question 6 | Recommendation: wire the new modules into the facade at this gate. | Policy §1 requires complete facade exports, and an explicit replay list does not establish reachability from the repository root. SymbolLift's indirect arrival through TQBF is not a substitute for listing it in the topic facade; Scan/InputCall likewise need deliberate export coverage. The missing facade/root sources are identified in finding 39. | Human decision: add the precise imports and Contents entries, then verify root reachability; otherwise record an explicit temporary exception with its integration deadline. |
| 47 | note | machine-library-design.md §12.8a §8 · open question 7 | Recommendation: keep scanTM as G2's one-tape core and retain mapped cross-tape rows for G3/G4 if their documented plan remains. | The identities cover folds, in-place maps, one-cell mark delays, and carry passes on a single delimited word. Section 13d's G4 plan separately requires writing `merge destination (extract source)` while retaining other destination tracks; `scanTM`'s transition reads only tape i and therefore does not itself provide that operation on an independent source tape. Plain whole-symbol copying also cannot preserve those other tracks. | Human decision: affirm the already recorded scan core; retain `copyMapTM`/`transferMapTM` for the cross-tape consumers, with blank-destination-aware merge and a shared trace, unless a separately audited replacement composition is supplied. |

FAIL — 0 blockers, 1 major, 7 minors, 39 notes.


## ===== audits/s12-8-statements-r2-findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `audits/evidence/s12-8/S128R2SpaceProbe.lean.txt` · final example | The record-step probe’s conclusion does not require reaching a verdict. | Its conclusion is merely `∃ t, spaceUsed d t ≤ …`. For any machine, choose `t = 0`: `spaceUsed d 0 = K + 1 ≤ (K + 1) * (2 * (C * (L + 1)) + 1)`. In particular, a stationary machine with distinct entry/yes/no states satisfies this conclusion without ever reaching either verdict. The supplied proof uses the correct exit-time witness, but the example’s statement loses that fact; the actual repaired contract retains it. | Include the time bound and `(R.runFrom d t).state = some yes ∨ (R.runFrom d t).state = some no` in the probe’s conclusion. |
| 2 | minor | `Build/Scan.lean` · module documentation, “The input sweeps” | The overview incorrectly attributes work-head movement to the input fold. | It says the input sweeps move the native head “in lockstep with the work heads.” For `inputFoldTM`, every transition uses `inputMoveAction`, which fixes all work heads. On a singleton input, its first step moves the input head from 1 to 2 while every work head remains fixed. The definition and theorem are correct. | Restrict the lockstep description to `inputCopyTM`; say that `inputFoldTM` moves only the input head. |
| 3 | note | `Build/CfgRecord.lean` · `exists_recordStepTM` | The strengthened step contract is true and repairs the missing workspace guarantee. | The record has length \(L=k(2s+1)+\operatorname{posWidth}(n)+k+4\). Initialize a scratch counter of the position-field width, save the native position by binary counting, seek to the recorded position, read, and restore; binary carry accounting gives total time linear in native travel plus the width, with workspace linear in the width. For nonempty input, a one-step right probe distinguishes the two blank boundaries; for empty input, the one-digit width identifies that case and no native movement is needed. Finite control collects the scanned work symbols and edge flags; reject an outward head move before modifying the record, otherwise rewrite the fixed-length record and clean scratch. Checks: zero source tapes, halted source, radius zero, both clamped input boundaries, and empty input. | No statement change. Preserve the saved-position, clamping, cleanup, and trajectory obligations in the fill. |
| 4 | note | `Build/InputCall.lean` · `exists_inputSeekTM` | The strengthened seek contract is true, including its native-travel-independent head bound. | Copy, rewind to position 1, move left once, count down while moving the native head right, then clear scratch. The stated component bounds and four dispatches give \(t\le6\,w.length+d.inputPos.val+5p+13\), while every work head stays between its entry position minus 1 and entry position plus `w.length`. Thus one fixed coefficient satisfies both bounds. Empty counters, leading-zero counters, empty input, and \(p=n+1\) all satisfy the construction. | No statement change. |
| 5 | note | `Build/CfgRecord.lean` · `exists_recordEqTM` | Equality remains true with empty fields and with a second record much longer than the first. | Compare corresponding fields; a mismatch is detected after at most the first field’s length, and only equal fields are skipped. Therefore both traversals are bounded by the first layout’s length; the crossed fields have equal lengths and can be traversed backward to restore both heads. The fixed field count prevents adjacent blanks from being mistaken for an early table end. Checks: all fields empty, first-field mismatch against an arbitrarily long field, and disagreement in the last field. | No statement change. |
| 6 | note | `Build/CfgRecord.lean` · `exists_recordTestTM` | The strengthened test contract is true without a window hypothesis or any relationship between native input `y` and source input `x`. | Read the state field, cross the intervening fields, read the tag, and reverse those crossings; all work occurs within the record and its delimiters. The finite predicate determines the verdict, and the native input is unused. Checks: constant predicates, a non-windowed source configuration, and unrelated or foreign-symbol native inputs. | No statement change. |
| 7 | note | Four repaired contracts; `S128R2SpaceProbe` · head-range lemma; `Build/Embed`, `Build/Seam` | The repaired bounds imply the required workspace bounds and compose at restored entry heads. | A head-radius bound \(R\) gives `visitedByTapeHead d t j ⊆ Icc (d.workTapePos j − R) (d.workTapePos j + R)`, hence at most \(2R+1\) visited cells per tape and total space at most \(k(2R+1)\). Repeated calls with restored entry heads and uniformly bounded sizes remain in the same intervals; stationary dispatches add no cells. R1 preserves selected-tape visited sets and leaves unselected heads fixed. Consequently records of length \(O(S+1)\) use \(O(S+1)\) workspace per frame, and logarithmic-width seeks use logarithmic workspace; movement between frames must still be charged to the host’s bounded layout. A common coefficient can be enlarged to cover both time and radius. | No further clause required. Consumers must intercept the verdicts; these contracts do not bound an unconnected module after its verdict time. |
| 8 | note | `Build/InputCall.lean` · `FinTM.exists_inputCallTM` | The statement and corrected first-return construction are sound; this remains a time-only interface. | Copying native input onto tape 0 establishes the install-call entry seam. If the callee’s entry equals its exit, `seamReleaseTM_firstReturn` supplies a fresh entry without changing the positive-time run; otherwise the time-zero cut follows from inequality. This covers empty input/result, identity functions, and constant functions computed with zero source tapes, while the callable witness retains positive tape count. No small-space conclusion follows: the sketched input copy alone visits linearly many work cells. | No space clause is needed for its advertised time-only use. A future space-preserving call requires a separately specified interface. |
| 9 | note | Round-1 resolutions · findings 2–8 | The recorded minor repairs are supported by the supplied text and patches. | `timed_rewind` returns to position 1 within `pos + 2`; the extra left move is now explicit. The input-call case split, validator width/bound templates, core-only injectivity wording, and nonempty-layout qualification are correct. The promotion changes exactly three citations, and the updated ledger fractions are \(318/459=69.3\%\) and \(283/459=61.7\%\). | No further correction to these dispositions. |
| 10 | note | `Build/Catalog.lean` · action helpers, field layout, `fieldsTape_field` | The helpers and layout definitions have their stated meanings, and every valid field is framed correctly. | `tapeAction` changes only the selected work tape, specified input movement, and control; `inputMoveAction` fixes every work tape. `joinFields` intercalates one blank, `fieldsTape` extends the resulting list by blanks, and `fieldOffset` sums preceding field lengths plus separators. At each valid field index, positions −1 and the field length are blank and interior cells are precisely the field. Checks: first field, last field, adjacent empty fields; an empty field list has no valid index. | No statement change. |
| 11 | note | `Build/Catalog.lean` · `compareTM_run_ofCfg` | Comparison has the stated verdict, restoration, first-exit time, and trajectory. | Let \(\delta\) be the first mismatch or exhaustion index. There are \(\delta\) matching right moves, one left turn, \(\delta\) return moves, and one final right move: \(2\delta+2\). The common prefix guides both heads home without writes, inside the stated intervals. Checks: both words empty, first-symbol mismatch, and a proper prefix at displaced heads. | No statement change; generalize the existing trace at fill. |
| 12 | note | `Build/Catalog.lean` · `SeekPhase`, `skipTM_run_ofCfg` | Skip advances beyond the right delimiter in exactly `w.length + 1` steps. | Each symbol gives one right move, and the delimiter gives one final right move into `done`; all other configuration components are preserved. Checks: empty word, singleton, and nonblank cells immediately outside the constrained interval. The four-constructor phase type and stationary unused phases match the definition. | No statement change. |
| 13 | note | `Build/Catalog.lean` · `skipBackTM_run_ofCfg` | Skip back is the stated inverse-position operation, with time `u.length + 3`. | Two unconditional left moves reach the previous word’s last cell, or its left delimiter if empty; crossing the word and moving right from its left delimiter costs another `u.length + 1`. The minimum position is entry minus `u.length + 2`, and nothing is written. Checks: empty previous field, singleton, and arbitrary nonblank current cell. | No statement change. |
| 14 | note | `Build/Catalog.lean` · `seekEndTM_run_ofCfg` | The nonempty-table contract has exact time \(D+1\) and displacement \(D\). | All cells through the first terminal blank cause \(D\) right moves; the second terminal blank causes one stationary transition into `done`. Nonempty fields exclude an earlier double blank. Checks: one singleton field, several unequal-length fields, and nonblank exterior framing. For `ws = []`, the actual machine moves right once and takes two steps, so the exclusion is necessary. | No statement change. |
| 15 | note | `Build/Catalog.lean` · `seekStartTM_run_ofCfg` | Start seeking has exact time \(D+4\) on its stated entry domain. | Starting on the required nonblank cell, the machine makes \(D+2\) left moves to the second leading blank, then two right moves to the table start. The trajectory and unchanged-tape clauses follow directly. Checks: no preceding fields, one singleton field, and several preceding fields. The blank returned by `seekEndTM` still requires the recorded repositioning adapter. | No statement change. |
| 16 | note | `Build/Catalog.lean` · `mealyRun`, `scanResult`, `ScanPhase`, `scanTM_run_ofCfg` | The two-pass semantics and framed scan contract agree. | `mealyRun` updates the accumulator and emits one symbol per input symbol; `scanResult` feeds the reversed forward output to the backward pass and reverses its output back. The machine executes `w.length` forward writes, one turn, the same number of backward writes, and one return step, totaling `2*w.length + 2`. Checks: empty word, singleton, and two symbol-negating passes, which restore the original symbols. Raw accumulator types may be arbitrary; finite-machine consumers must instantiate them finitely. | No statement change. |
| 17 | note | `Build/Catalog.lean` · `scanKeep`, `scanFold`, `scanResult_fold` | The fold identity is true. | Induction gives forward result `(w.foldl δ a₀, w)`; the identity return changes neither component except reversing and restoring list order. Empty input, a singleton, and a noncommutative accumulator update confirm initialization and left-to-right order. | No statement change. |
| 18 | note | `Build/Catalog.lean` · `scanMap`, `scanResult_map` | The map identity is true without injectivity assumptions. | Each forward step keeps the accumulator and writes `f` of its symbol; the return does not apply `f` again. Empty words, singleton words, and constant noninjective maps yield exactly `(a₀, w.map f)`. | No statement change. |
| 19 | note | `Build/Catalog.lean` · `scanShift`, `scanResult_shiftRight` | The right-delay identity is true for arbitrary supplied `get` and `set`. | Each cell receives the preceding accumulator, while its original `get` value becomes the next accumulator; induction gives the displayed `zipWith` and last-value result. Checks: empty word, singleton, and a three-cell mark moving right. Interpreting the result as a mark update requires the intended setter laws, although the algebraic identity does not. | No statement change. |
| 20 | note | `Build/Catalog.lean` · `scanResult_shiftLeft` | The left-delay identity has the correct boundary value and order. | The forward identity leaves the word unchanged; the backward delay is the preceding argument on its reversal. Reversing back gives successor marks and the supplied boundary value at the final cell. Checks: empty word, singleton, and a three-cell mark moving left. | No statement change. |
| 21 | note | `Build/Catalog.lean` · `scanCarry`, `scanResult_carry` | The carry identity correctly separates the top prefix, first non-top digit, and unchanged suffix. | While carry is set, `next` is applied and carry persists exactly on a top digit; after the first non-top digit, subsequent transitions are identities. Thus the final carry is `w.all top`. Checks: empty word, first digit non-top, and every digit top. Arithmetic interpretation additionally requires the intended digit enumeration. | No statement change. |
| 22 | note | `Build/Scan.lean` · `WritePhase`, `writeConstTM_run_ofCfg` | The constant writer has the stated overwrite interval, return, and exact time. | Its finite index counts `w₀.length` writes, one stationary turn, that many left moves, and one stationary exit: `2*w₀.length + 2`. No old contents are read, and no exterior cell is written. Checks: empty pattern, singleton, and displaced overwriting of a nonblank interval. | No statement change. |
| 23 | note | `Build/Scan.lean` · `writeAdvTM_run_ofCfg` | The advancing writer satisfies the first-positive-return discipline. | States count writes from zero through the pattern length; the final stationary step returns to zero after `w₀.length + 1` steps. Intermediate positive times have nonzero states, and the head advances by precisely the pattern length. Checks: empty pattern, singleton, and two successive rounds producing adjacent copies. | No statement change. |
| 24 | note | `Build/Scan.lean` · `inputCopyTM_run_ofCfg` | Native-input copying has exact time `2*x.length + 2` and restores both heads. | The forward pass copies in lockstep; the right input marker turns both heads, and the left input marker supplies the final right move. The return is guided by input, so destination delimiters are unnecessary. Checks: empty input, singleton, and a nonblank destination cell immediately left of entry, which is visited but preserved. | No statement change. |
| 25 | note | `Build/Scan.lean` · `inputFoldTM_run_ofCfg` | Native folding produces the stated verdict with stationary work heads. | The forward scan accumulates `x.foldl δ a₀`; the backward scan preserves it, and marker accounting gives `2*x.length + 2`. Every action fixes work heads and contents. Checks: empty input, zero work tapes, and a foreign rich symbol that sets a persistent rejection flag. | No theorem change; correct only finding 2’s overview sentence. |
| 26 | note | `Build/CounterLoop.lean` · `expandTM`, `expandTM_run_ofCfg` | Expansion is the correct counter-loop specialization. | Substitute the cyclic writer with round time `pat.length + 1`; after each round its head advances by the pattern length and another adjacent copy has been written. Summing rounds gives `d*(pat.length + 1) + counterOverhead w (d + 1)`; the final underflow leaves the counter all true, and the loop supplies both first-exit and trajectory clauses. Checks: zero counter, empty counter word, and empty pattern with positive counter. | No statement change. |
| 27 | note | `Build/CfgRecord.lean` · carrier definitions, `Cfg.InWindow`, `cfgRecord_length`, `RecordAt` | The record carrier and framing definitions match the design. | `InWindow` bounds work heads and makes exterior cells blank. `RecSym` is the disjoint digit/content-and-mark/state/tag alphabet; finiteness follows from finite state and tag types, and `digitEmb` is injective. `binDigits` records low bits, while `posWidth n` distinguishes all positions through `n+1`; `cfgRecord` consequently has `k+3` nonempty fields. `RecordAt` constrains only the layout and its two delimiters. Checks: zero tapes, radius zero, and empty input; outputs remain deliberately omitted. | No definition change. |
| 28 | note | `Build/CfgRecord.lean` · `cfgRecord_inj` | The injectivity statement is true on configuration cores and tags. | Equal fields give equal states, input positions, window contents, unique marked head positions, and tags; both window hypotheses extend tape equality outside the window. Conversely, equality of those components gives identical records. Checks: zero tapes, different outputs with the same core, and differing exterior tape cells when a window hypothesis is removed—the latter shows why the hypothesis matters. | No statement change. |
| 29 | note | `Build/CfgRecord.lean` · `RecordValid`, `recordValid_iff` | Validity is exactly the stated shape condition. | Forward, decode the fields of a windowed configuration. Backward, choose `List.replicate n false`, use the supplied position value, put each head at `m − s`, install the supplied window contents, and make exterior cells blank; this constructs the required witness. Checks: radius-zero singleton fields, zero or multiple marks, and an out-of-range position value. The corrected documentation properly requires external width/bound information for a uniform validator. | No statement change. |
| 30 | note | `Build/Seam.lean` · promoted prefix theorem, `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | The two-exit composition and its one-step dispatch bound are correct. | The promoted prefix theorem follows the source until and including the first exit time. At `e₁`, the inner seam dispatches into its right summand, which can never equal the outer exit `Sum.inl e₂`; at `e₂`, the outer seam dispatches directly. Therefore either continuation runs exactly from time `T₀ + 1`, including subsequent halting. Checks: `T₀ = 0`, either exit, and a continuation that halts immediately. | No statement change. |
| 31 | note | `SymbolLift.lean` · R8.0 public surface | The transport definitions and exported run, time, and space statements have the correct domain and strength. | Decoding inverts the embedding on digits; action/configuration lifting maps symbols while retaining state and head positions. One-step commutation gives run commutation, and identical head trajectories give equal visited sets and space. Initialization and `ComputesFunInTimeVia` follow on encoded inputs. Checks: zero tapes, halted configurations, and nonempty output prefixes. Mixed rich tapes require R1 isolation of dedicated digit tapes, rather than direct application of the globally lifted-configuration theorem. | Keep the public one-step lemma and the stated domain restriction. |
| 32 | note | Design O6; `SymbolLift`, `inputFoldTM`, `alphabet_reduction_spaceUsed` | Mandatory validation remains a sufficient and necessary safeguard for the chosen reduction interface. | The exported reduction requires a bound on all rich inputs, whereas lift transport controls encoded inputs. For example, a binary machine can stop after seeing blank twice, but move a work head forever if a symbol follows its first blank; binary inputs cannot exhibit the latter pattern, while `[foreign, e false]` can after decoding. A native fold rejects foreign symbols with fixed work heads; accepted inputs are encoded binary inputs. Correct consumers must also connect the repaired modules’ verdicts and final halt so their workspace bounds hold at every time. | Retain O6 and the dedicated-digit-tape discipline. |
| 33 | note | Full and delta patches; declaration-freeze logs | The authorized freeze claims are supported by reconstruction. | Both patches apply cleanly in reverse to the attached final sources. Comment-stripped round-2 comparison changes exactly the four strengthened signatures; Catalog is identical in all 475,616 comment-stripped characters. Against the reconstructed campaign base, old signatures are preserved, `InWindow` moves byte-identically, and the promoted seam declaration/proof is identical after its authorized visibility/kind/name change. Exactly three old proof citations change names. | No correction required. Commit ancestry remains an execution-history attestation, as distinguished in finding 36. |
| 34 | note | `TuringMachine.lean`, `TCSlib.lean`, `ConfigGraph.lean` · exports and placement | The five requested exports and Contents entries are present, with direct root reachability and no observed declaration clash. | The root imports the topic facade, which imports all five modules exactly once; `OracleCall` is already present in the reconstructed post-merge base. `ConfigGraph`’s private `InWindow` and public `Turing.Cfg.InWindow` are distinct declarations. Their predicates are mathematically equivalent by contraposition, but are not duplicate public names. The supplied import edges contain no cycle; complete transitive verification is limited as in finding 36. | No wiring change required. Retain the scheduled split of the large Catalog dependency. |
| 35 | note | `machine-library-design.md` · §12.8a §9 and §13d G2 | Q1–Q7 accurately record the adopted recommendations. | They retain inverse skip back, the cyclic writer, fixed local tape layouts, separate gates for deferred rows, and current facade wiring. The nonempty header and two boundary blanks make empty record tables usable; skip back from seek-end’s second blank reaches the last field’s nonblank start before seek start. G2 records the scan core and retains cross-tape mapped rows with blank-aware `merge`, which a one-tape scan does not itself supply. | No record change required. Deferred rows, R8.0b, and input-length construction remain prerequisites, not results certified here. |
| 36 | note | Pack · evidence boundary; `backlog.md` · FAC-1 | Some completeness and execution claims cannot be independently established from the bundle. | All nine FAC-1 names are absent from the facade’s 43 distinct imports; \(43+9=52\) agrees with the lint’s reported population, but no complete topic manifest is supplied. Transitive checking also reaches missing `Build/Wrappers`, `Composition`, `Encoding`, and `StateRenaming`; the exact Savitch/logspace consumer sources and executable Lean/check/lint environment are absent. Thus full import-cycle/closure completeness, fresh olean production, ancestry, and exact consumer elaboration remain attestations. The absent round-1 lint outputs also prevent an independent comparison of all warning paths. | Attach the topic manifest/import graph and relevant consumer or execution inputs if these claims require independent certification. Do not infer their contents from the reported counts. |
| 37 | note | Replay, probe, axiom, and lint evidence | The supplied current counts and source inventories are internally consistent. | The replay has 18 distinct rows in exactly the listed order, all exits/errors zero, totaling \(32=7+25\) sorry warnings. The new-source distribution is Catalog 12, Scan 4, CfgRecord 5, InputCall 2, CounterLoop 1, Seam 1, SymbolLift 0. The old probe contains 35 examples: 30 `decide`, four `simp`, and one `cfgRecord_length` application; both probe runs are attested clean. The 14 transport axiom outputs and two retained theorem outputs contain only the allowed standard axioms; current lint reports 0 FAIL and 14 size WARNs. These are not independent proofs of the admitted existential contracts. | Accept the checked counts and source consistency, subject to finding 36 and the probe correction in finding 1. |
| 38 | note | Copy-text evidence; `audits/duplication-ledger.md` | No new unacknowledged duplication debt is established. | Independently rerunning the supplied screen reproduces the reconstructed before output byte-for-byte: 520 declarations, 396 pairs, 119,207 characters. The repaired output also reproduces byte-for-byte: 535 declarations, 408 pairs, 120,748 characters, exactly equal to round 1’s after output. Promotion-name normalization leaves 12 added same-file pairs, zero added cross-file pairs, and none removed. The repaired clauses are repeated interface requirements, not copied proofs; the small related transition tables have different behavior, and the corrected Catalog denominator remains within the acknowledged family and scheduled resolution. | No debt major. Preserve the existing acknowledgments and enforce the promised shared traces during fill. |

Notation: \(n\) is input length; \(L\) is record-layout length; \(D=\operatorname{fieldOffset}(ws,ws.length)\); \(\delta\) is the first comparison mismatch/exhaustion index; \(R\) in finding 7 is the work-head radius. Other identifiers retain their bundle meanings.

PASS — 0 blockers, 0 majors, 2 minors, 36 notes.

## ===== machine-library-design.md =====

# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `audits/ch1-infra-findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 9c. Round-3 repairs (2026-10-03, after `audits/ch1-infra-r2-findings.md`)

Round 2 passed the redesigned loops, P13/P14/C1, and the §9b tables, and
discharged both round-1 refutations; its one major (finding 1) showed the
loop's *final-answer* conclusion cannot discharge the frozen
`enumMachine_contracts`, which is a *configuration-level* contract — the
auditor's delay machine answers correctly yet violates every per-round
bound. Repairs:

**The configuration-level export.** `exists_loopCfgTM` (same hypotheses
as the decision form) concludes with the host's round-configuration
family: startup ≤ `c·(T+1)` reaching `cfg 0`, empty output at rounds
`0…R`, per-round accept-or-advance segments each within `c·(T+1)`, and
the halted `[false]` terminal at index `R+1`. The decision form becomes a
fill-time corollary through an already-halted-terminal summation lemma
plus monotonicity (R3-1: the frozen `loop_run` requires an empty-output
terminal, so it is not invoked directly on the exported family). **Index/budget
translation to `enumMachine_contracts`** (under the §9b enumerator
instantiation, `w := m n`): candidates `2^w = R n + 1`, so the terminal
index matches; the customer's uniform bound `b·(n + w + 1)^e` dominates
`c·(T n + 1)` once `T` is chosen as a polynomial in `n + w` and `b, e`
absorb `c` and its degree; the per-round indicator matches via the fill's
orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i` (little-endian rank
enumeration, `incFixed` = `enumInc` per the round-2 vocabulary note).

**Vocabulary coefficient shift (round-2 note 5, adopted).** The proved
equalities are `splitAtLastTrue = stripCertificate`, `incFixed = enumInc`,
and `solveSplit (C+1) c = certificateSplit C c` — the split-search
equality is false without the shift (R3-3 corrected this pointer). Consequently the padded-verifier pipeline uses P10 at
`(C + 1, c)` while P8 keeps `(C, c)` for the original witness bound.

**General pairing assembly (round-2 item 10's derivation, adopted
verbatim as the canonical recipe).** For computed `f, g`:
`H x := pairEncode (f x) []` (P14 + C1 at the constant-empty function);
`s x := pairEncode x (H x)`; `t x := pairEncode (s x) (g x)` (P14 + C1,
the second with `g ∘ pairFst`); then
`pairSnd (pairConcat (t x)) = pairEncode (f x) (g x)` — the
self-delimiting grammar makes concatenation-into-payload well-formed at
every stage. A C1 call on `pairEncode a b` computes `g b` only; any
cross-component operation goes through this retained-whole-request
pattern, never through C1 directly (round-2 item 10's D-MEM caveat).

**D5 scope (round-2 items 6/10).** The disposition is re-issued for the
epoch-2 frontiers and P10 only; the E3/E4 rows are component-level
plausibility and their full coverage check is deferred to those epochs'
brief audits, where the six-stage/boundary/ledger tables are in scope.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.

## 11. The emitter increment (proposed 2026-10-05, post-E3 integration)

**Evidence.** E3's outcome maps the library boundary exactly: everything
recognizer-shaped closed in one round through the catalog (3B's memberships
via `computesFunInTime_splitSolve 1 1` + capture + the audited wrappers; 3D
via P10 + capture + composition), while both stalls sit on the producer
side — 3B at a streaming transducer (`satRedTM` states 9–34, defined,
unproved), 3A at a loop body that must internally run an evaluator and emit
a payload, over a width family the catalog's split instance doesn't cover.
The loop contracts deliberately require **empty output through every round**
(round-2/3 audit repairs), and composition offers only input-pipelining —
there is no output-append mode anywhere in the library. E4's summit
(`SAT_NPHard`, 15 pts, continuation certain) is an emitter of exactly this
shape: a per-index loop appending clause groups under the six-stage
output-silence contract with an exact serialization-length ledger.

**Rule of admission check** (§4): every item below has at least two named
customers among 3B-cont, 4A, 4B, and 3A-cont.

### E1. `emitLoop` — the emitting loop (control layer)

The loop engine's output clause generalized: rounds append exact per-round
emissions instead of staying silent. Shape (final quantifiers at spec time,
audited):

```
-- SHAPE ONLY. Sibling of exists_loopCfgTM, sharing its host machinery.
Inv, s0, stepF as in the decision loop; additionally
  emitF : input → σ → List Bool        -- the exact chunk of round i
contract: startup ≤ c(T+1); per-round segments ≤ c(T+1); positive
  first-return; for every i ≤ R:
    (cfg i).output = (List.range i).flatMap (fun j => emitF x (stepF^[j] s0))
  terminal: halted, output = the full concatenation (no verdict bit — the
  machine COMPUTES the concatenation; a deciding variant is NOT included).
```

Body obligations unchanged (accept-or-advance becomes advance-and-emit;
scratch restore per §3/9.2). The summation lemma is `loop_run`'s template
with the output clause threaded. **Customers:** 4A (the per-snapshot clause
emitter — the design driver), 3B-cont (`satRedTM`'s streaming core as an
instantiation), 4B (dual reduction emitter).

### E2. `emitPhase` — the forwarding wrapper (control layer)

The dual of W1: run an embedded transducer `T` (a `ComputesFunInTime`
contract) inside a host, with `T`'s emissions landing on the **host's**
output tape, source tapes isolated, halt redirected to a live return state;
lockstep lemma in `capture_run`'s mold with "physical output = host prefix
++ T's output so far". This is what lets a catalog transducer serve as one
emission stage of a larger machine — today's only option is whole-machine
input-pipelining. **Customers:** E1's per-round chunk calls (4A emits each
clause group through a sub-transducer), 3B-cont (fresh-literal chain
emission), 3A-cont marginally (the success payload `pairEncode` emission).

### E3′. Stream primitives (catalog rows P16–P18)

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P16 | `tokenStepTM` | consume one self-delimiting token (unary index / marker) from the input head, land head after it, expose the token in control | harvest: 3B's proved `satScanTM`/`satSyntaxStep`, 3D's six-state scan, 2D's parsers (fourth re-derivation otherwise) | 3B-cont, 4A, 4B |
| P17 | `chunkEmitTM w` / parametric | append a control-determined word to output, `\|w\|` steps, no tape movement | new (trivial); the per-token emission atom | E1 bodies, 4A |
| P18 | `unaryAccTM` | dedicated-tape unary accumulator: append one, read-length-in-binary via P4 composition, rewind | harvest: 3B's proved counter stages (`satRedCounter_write`, `satRed_maxOnes`, startup to state 9) | 3B-cont, 4A fresh indices |

### E4′. `splitSolveWith` — width-parametric split search (control layer)

Generalize P15's split search from the hardwired polynomial family to a
hypothesis-supplied width evaluator: given a machine `E` with a captured
`ComputesFunInTime (fun s => bits (f s.length)) T_E` contract and
monotonicity of `n ↦ n + f n`, a machine solving `n + f n = m` (first
success payload `pairEncode (take n) (drop n)`, exhaustion verdict) within
the loopFind envelope over `T_E`. **Harvest source:** 3A-cont's bespoke
body, whose contracts are already displayed in its REPORT — build the
parametric form against that template once it lands (or directly, if this
increment executes first). **Customers:** 3A-cont's equation (plug the
proved `e3_exp_bits_timed`), every future padding argument (ch3+ time
hierarchy pads the same way).

### Placement, cost, open decisions

- **Placement:** E1 extends `Loop.lean` **in-file** to reuse the audited
  `loopHost` privates (a separate `Build/Emit.lean` cannot see them — the
  D7 cross-file-privates qualification; re-deriving the host would be a
  second 2,500-line proof). `Loop.lean`'s size exception grows and the D7
  split trails as already recorded. E2 joins `Wrappers.lean`; P16–P18 join
  `Primitives.lean`; E4′ joins `Loop.lean` beside P15's engine.
- **Non-goals:** no deciding variant of the emitting loop (compose E1 with
  the existing decision layer instead); no general transducer algebra; no
  speculative tape-embedding (unchanged from §5's deferral).
- **Cost estimate:** spec layer 4; one shared-infra audit round (the ch1
  pattern, expected lighter — one host extension, not a new host); fills:
  E1 8, E2 4, P16–P18 5, E4′ 6 — **≈ 27 points**, roughly the L batch.
- **Sequencing:** freeze this section → spec statements → audit round →
  fills → 3B-cont consumes E1/E2/P16–P18; 4A's brief cites the layer
  instead of a bespoke emitter. **3A-cont dispatches in parallel, bespoke**
  (disjoint ownership; its body becomes E4′'s harvest template; later
  dedup is a recorded E5-style maintainer task, never the fill's).
- **Open decisions (user):** (11.1) approve the increment and this scope;
  (11.2) E1 as a sibling contract beside `exists_loopCfgTM` (recommended)
  vs a generalization replacing it (touches audited statements — not
  recommended); (11.3) whether 4A's brief waits for this gate to close
  (recommended) or anticipates it.

## 11a. Spec-phase refinements (2026-10-05, recorded when the emitter spec landed)

Decisions 11.1–11.3 resolved by the user (2026-10-05): increment approved;
E1 is a **sibling** contract beside `exists_loopCfgTM` (no audited statement
is generalized or touched); 4A's brief **waits** for this gate.

Refinements against §11 as drafted, all narrowing:

1. **P17 is subsumed** (no new statement): a constant chunk emission is
   `emitPhase` (E2) applied to the existing P2 `constTM` — recorded here
   the way D4 recorded the prefix/fixed-pair subsumptions.
   *[Superseded by §11b item 6 and §11c: the discharging rule is body
   finite control for fixed words, or `exists_emitCallTM` for computed
   chunks — never the private `constTM` (round-2 audit, finding 3).]*
2. **P18 narrowed to `computesFunInTime_appendBit`**: the drafted
   accumulator row conflated the append atom with cross-phase persistence,
   and persistence is already the loop engine's state-word mechanism; the
   catalog takes only the atom.
3. **E4′ lives in `Primitives.lean`**, not `Loop.lean`: its conclusion
   speaks `pairEncode`, which `Loop.lean` does not import, and P15's own
   public contract already lives there — the engine/contract split follows
   P15 exactly. Its pure vocabulary `solveSplitWith` joins `Convention.lean`
   beside `solveSplit`, which it definitionally generalizes.
4. **E1 is function-level only** (`exists_emitLoopTM` concluding a
   `ComputesFunInTime` of the chunk concatenation): all three named
   customers deliver `PolyTimeComputable` reductions, i.e. function-level
   contracts, and in-host composition of an emitter is E2's job, which
   takes function-level transducers. The round-2 lesson (final-answer vs
   configuration gap) was checked against each customer before choosing
   this form; a configuration-level export would follow the round-3
   precedent if a consumer ever surfaces.
5. **No emission-size hypothesis on E1**: the round seam equality itself
   bounds each chunk by the round's duration (output grows by at most one
   symbol per step), so the statement carries no redundant bound to drift.

Spec surface: **five sorried contracts** (`Turing.emit_run`,
`Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit`), two real transformers
(`emitAction`, `emitCfg`), two pure vocabulary definitions
(`solveSplitWith`, `unaryTokenSplit`). Convention's module-docstring
vocabulary bullets extend at fill time (append-only).

## 11b. Round-2 repairs (2026-10-05, after `audits/emitter-infra-findings.md`)

Round 1: **0 blockers, 2 majors, 3 minors** — no false statement among
the five contracts; both majors are adequacy obligations, repaired here.

1. **The clean-call bridge (finding 1, major).** A function-level
   contract cannot deliver the loop seam: a witness may dirty scratch or
   leave heads displaced on its final transition and still compute `f`
   within `T`. Two new sorried bridge contracts supply the
   prepared-input/clean-return interface, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit discipline, and envelopes charged to `T + |arg| + |f arg| + 1`:
   `Turing.FinTM.exists_installCallTM` (result installed as the
   tape-resident word, nothing emitted) and
   `Turing.FinTM.exists_emitCallTM` (argument preserved, the computed
   chunk forwarded to physical output). Both live in `Loop.lean` beside
   the seams they serve (`stateWord` is defined there). Fill route: the
   A-continuation's proved log/undo pattern around the capture wrapper,
   with virtual-input preparation from the tape-resident argument.
   `emitCfg`'s docstring now states explicitly that it does not
   normalize terminal configurations — the bridges do.
2. **The 3B normalization mapping (finding 1, required resolution).**
   The reported `satRedTM` is **not** the promised instantiation as it
   stands (its permanent position-−1 marker contradicts the blank
   `ofWords` seam; its raw head positions cannot cross seams). The
   committed instantiation plan: loop state word encodes
   `(cursor, consumed-prefix length, phase tag)` via the audited pairing
   vocabulary — the raw streaming position is re-derived each round by
   advancing past the consumed prefix, and **the permanent marker is
   eliminated** (round-local buffering restores its tape by round end).
   Per round: decode the state word; `exists_installCallTM` over
   `computesFunInTime_unaryToken` reads the next token of the remaining
   serialization; finite control classifies marker/polarity bits; the
   emitted clause fragment goes out through `exists_emitCallTM` (chunks
   are of token-bounded length) or directly by finite control for
   fixed fragments; the fresh-variable counter updates through
   `computesFunInTime_appendBit` + install. Rounds have positive
   duration and input-length-only budget; `R` = the serialized input
   length (each round consumes at least one input position); once the
   formula terminator is consumed, an **absorbing finished phase emits
   empty chunks** for all remaining rounds. Token output is decoded by
   `pairDecode`-side vocabulary (proved); append output becomes the
   next state word by the install call. The banked `satReduction_*`
   semantics close the function identity; `satRed_start`'s proved
   maximum-pass survives as the `s0` computation.
3. **The 4A stage mapping (finding 2, required resolution — recorded
   here, certified against the attached phase-4 records in round 2).**
   All-string validation runs **before any irreversible emission**: the
   validation stages run as a decision prefix (the audited conditional
   W3 over the parser/boundary checks); only the valid branch enters
   the emitting loop, and the invalid branch emits the fixed fallback
   through finite control. Logical round count: `R` = the
   snapshot-index bound of the six-stage contract (an input-length-only
   polynomial), one clause group per round through `exists_emitCallTM`;
   the exact serialization-length ledger is the sum of the per-round
   chunk lengths — never constant-per-clause, exactly as the phase-4
   ledger demands. Serialization terminators: the final terminator is
   the last round's chunk tail (or a post-loop constant emission by
   finite control); both options keep the concatenation exact.
4. **Host routing correction (finding 3, minor).**
   `exists_emitLoopTM`'s construction sketch now specifies the
   **forwarding host variant** (body dispatched through `emitAction`;
   fuel/countdown machinery reused; contracts proved over
   arbitrary-accumulated-output configurations; a **new**
   prefix-summation lemma modeled on `loop_run`) — the unchanged
   find-mode host is refuted by the auditor's one-state witness, since
   `captureAction` suppresses the body's physical output.
5. **Token conventions (finding 4, minor).** `unaryTokenSplit`'s
   docstring now states it consumes unary tokens only, with the
   auditor's separating example; standalone markers and polarity bits
   are scanner grammar states.
6. **P17's actual rule (finding 1's visibility note).** Fixed
   finite-control chunks are emitted directly by body control (no
   primitive, no appeal to the private `constTM`); unbounded
   tape-dependent chunks go through `exists_emitCallTM`. §11a item 1 is
   corrected accordingly: the subsumption's discharging rule is body
   finite control, or the emit call, never the private constant
   machine.
7. **Documentation (finding 5, minor).** The four definitions now carry
   customers and construction notes; attestation 4's "every new
   declaration" claim is restated in the round-2 pack as exactly what
   each class of declaration carries.

Spec surface after round 2: **seven sorried contracts** (round 1's five
plus the two bridges), two transformers, two vocabulary definitions.

## 11c. Round-3 repairs (2026-10-05, after `audits/emitter-infra-r2-findings.md`)

Round 2: **0 blockers, 2 majors, 1 minor** — round-1 findings 3–5 closed;
the bridge construction and the 3B normalization validated (r2 findings
4–5, including a 5,908-case finite corroboration of the normalized
schedule); the two cumulative majors repaired here.

1. **Positive tape count on both bridges (r2 finding 1, major).** At
   `C.k = 0`, `stateWord 0 a = stateWord 0 b` by empty domain, so the
   install conclusion was satisfiable by a two-state zero-tape machine
   for an arbitrary — even noncomputable — `f`: vacuous as a data
   interface. Both conclusions now carry `0 < C.k`, making the seam
   equality yield the genuine `bufferTape` content at index zero. The
   auditor's r2 finding 4 confirms the log/undo construction delivers
   the strengthened interface at the stated envelope.
2. **The 4A mapping rewritten (r2 finding 2, major) — this supersedes
   §11b item 3 in full.** §11b item 3 wrongly substituted parser
   validation for Cook–Levin's silent preparation stages: the 4A source
   is an arbitrary `NP` language, every binary word is a legitimate
   instance, and there is no CNF well-formedness condition on `x` (the
   auditor's empty-language witness: validation-plus-fallback would
   emit the satisfiable `serialize [] = [false]` for a no-instance).
   Parse-before-emission belongs to the 3B/4B decode-based transducers
   only. The corrected stage-to-seam mapping:
   - **Silent preparation (inherited stages s1–s5).** A silent startup
     phase computes and packs the preparation records into `s0 x`:
     exact `Q(n)`, `m = n + Q(n)`, and the horizon `T` (s1, exact
     arithmetic, certificate length never enlarged); the virtual
     reference input `false^m` with clamped virtual head, source
     writes/moves executed on the halting transition, source output
     suppressed and halt internalized (s2–s3, through the capture and
     install-call interfaces at positive tape count); the inclusive
     trajectory records for **all** times `0..T` with administrative
     transitions outside simulated time and frozen positions after an
     early halt (s4); greatest-strictly-earlier-visit records with
     sequential comparison costs (s5). All of s1–s5 end with empty
     physical output and the packed records as the clean persistent
     word — the emitting loop's `s0`.
   - **Ordered emission (s6).** One **family member per round**, the
     cursor walking the fixed family order of the phase-4 contract.
     With `T + 1` snapshot times and `k` work tapes, the six families
     have `n, 1, T, T+1, k(T+1), T` members; the round count is their
     sum: `R = n + (k+3)·T + k + 1` (an input-length-only polynomial).
     Rounds with empty template output still take positive time. The
     single final formula terminator is appended to the last round's
     chunk. The serialization-length ledger is the exact sum
     `1 + 2·#clauses + Σ (v+3)` over literal occurrences — total
     output `O_M(T²)`, never constant-per-clause.
   - The alternative `R = T` time-major grouping is **not** adopted:
     it would need a separate proof that its interleaving reserializes
     to the fixed family order.
   Certification of this mapping against the phase-4 round-2
   boundary-check table is round 3's business — that table
   (`audits/ch2-phase4-reaudit-findings.md`) rides in the r3 bundle,
   and the 4A brief inherits it verbatim per the standing rule.
3. **P17 cross-reference (r2 finding 3, minor).** §11a item 1 now
   carries an explicit supersession marker pointing at §11b item 6;
   the historical text is preserved as history.
4. **Provenance upgrades for round 3.** The log/undo fill route now has
   fresh in-repo provenance beyond the epoch-2 enumerator: the
   A-continuation checkpoint (integrated 2026-10-05) banked exactly the
   track/clear/compare phase family the r2 finding-4 construction
   describes (`e3cTrackTM`/`e3c_track_run`/`e3cClearTM`/`e3c_clear_run`
   — logged simulation over a visited interval with origin markers,
   exact single-triple cleanup at `6T+7`, positive first returns), as
   proved privates in `Nondeterminism.lean`; its REPORT and source ride
   in the r3 bundle.

Spec surface after round 3: unchanged in count — **seven sorried
contracts** (the two bridges now carrying `0 < C.k`), two transformers,
two vocabulary definitions.

## 11d. Gate close (2026-10-05, after `audits/emitter-infra-r3-findings.md`)

Round 3: **0 blockers, 0 majors, 1 minor, 4 notes — GATE CLOSED**
(`audits/emitter-infra-resolutions.md`). Both cumulative majors
discharged: the positive-tape bridges export the data interface (the
auditor's projection-table derivation), and §11c's 4A mapping is
certified against the inherited boundary table, including the exact
per-member chunk rule. The minor — swept in the closing commit — was an
attribution error of §11b item 1/§11c item 4 and the install-call
sketch: the A-continuation's delivered provenance is
**visited-interval tracking and clearing** (`e3cTrackTM`/`e3cClearTM`),
not an overwritten-symbol history/undo implementation; at a clean
entry seam, clearing is restoring, so the track/clear route fills the
bridges directly, and history/undo stands only as the independently
derived alternative (r2 finding 4). Two clarifications from r3
finding 3 bind the 4A brief: `R = n+(k+3)T+k+1` is the last round
index (member count `R + 1`), and the chunk rule emits per-member
flatMaps with the single terminator on the last chunk only. Fill
batches proceed under the resolutions' binding section, partitioned
Loop / Primitives / Wrappers.

## 12. The routine layer (proposed 2026-10-08, pre-ch3/4 campaign)

**Mandate** (user decisions 2026-10-06 and 2026-10-08, recorded in `backlog.md` §2
and `AroraBarakChapters3-4Plan.md` §4a/§8): built after the Chapter-2 closure and
**before the chapter-3/4 fill epochs**, in parallel with their statement phases;
scoped to **amply support the chapter-1/2 retrofit**, not merely the new
consumers; and — superseding §1's "no space bounds" non-goal for this increment —
**every item below carries a space clause alongside its time cost**, so that the
chapter-4 campaign and the P4.x statements consume the layer without a second
pass. The space measure is the house one: `Turing.MultiTapeTM.spaceUsed`
(work-tape cells visited; input and output tapes excluded).

**Evidence.** The 4A chain is the measurement: roughly half of the A2/A3
deliveries' 202 native privates are hand-rebuilt bank/relocation/dispatch
routines; the `emitterBank*`/`emitterP2*` relocation family was privately
re-harvested three times; and A3's proved costs (`3|w| + 3` copy, `2|w| + 2`
clear) match the external prior art's `3w + 2`/`2w + 2` to within one step —
independent convergence on the same catalog, discovered in the 2026-10-06
survey. The emitter round-1 finding stands: *function-level* contracts cannot
deliver clean-return seams, so the gap is configuration-level. §5 deferred the
general tape-embedding transformation "until a third site needs it"; the third,
fourth, and fifth sites have now arrived (the retrofit families, the
Hennie-Stearns conversion, the two-work-tape universal machine).

**What already exists and is consumed, not duplicated** (colleague modules,
Hydroxyi/Jason Dong, on `main` since `f70c57c2`): the *function-level half* —
`TuringMachine/CounterProg{,Run}.lean` (goto programs over unary registers
compiled once into `FinTM`, `t` abstract steps within `t(2t+3)` machine steps,
FP bridge via `ClassNP/CounterProgPolyTime.lean`), `ClassNP/Transducer.lean`,
`ClassNP/{PolyTimePairing,PClosure}.lean`, `TuringMachine/UnaryTape.lean`; and,
on the space side, `SpaceComplexity/Machines/` (the `LogProg` register-program
compiler with `compile_space`/`arm_decides`). §12 supplies the
configuration-level half those layers sit on.

### R1. Bank embedding (the §5 deferral, promoted)

A verified routine on its own `m`-tape set runs on any injectively selected
subset of a `k`-tape host's work tapes, cost unchanged, everything else framed.
Spec shape (final quantifiers fixed at spec time, audited): for an embedding
`ι : Fin m ↪ Fin k`, transported actions and configurations with

* **lockstep** — transported `runFrom` commutes with the source `runFrom`;
* **frame** — tapes outside `range ι` are byte-identical before and after, their
  heads unmoved; input position tracks the source; emission policy is a
  parameter (suppressed or forwarded — the W1/E2 pair fixes the two modes;
  whether this is one transformer with a mode or two transformers is open
  decision 12.4);
* **time** — step count preserved exactly;
* **space** — cells visited on host tape `ι i` equal cells visited on source
  tape `i`; unselected tapes visit nothing new.

Generic form of: `emitterBank*`, the `emitterP2*` relocation family,
`clBank*`/`clSlot*` (4A chain), and their chapter-1 analogues in
`Build/Primitives.lean`/`Build/Loop.lean` internals.

### R2. Seam composition

Sequential composition of two controllers at a canonical `Turing.Cfg.ofWords`
seam (Convention.lean's ABI notion): if `M₁` carries seam `c₀` to seam `c₁`
within `T₁` under a first-return cut, and `M₂` carries `c₁` to `c₂` within
`T₂`, the dispatch-glued machine carries `c₀` to `c₂` within `T₁ + T₂ + O(1)`,
with the glue state-sum and dispatch lemmas owned by the combinator. Space
clause: visited sets union, so per-tape space is bounded by the sum of the
parts' per-tape spaces (whether the spec states the sharper per-tape `max` for
disjointly-owned tapes is open decision 12.1). Generic form of the per-batch
dispatch gluing re-proved in every A-chain and emitter batch.

### R3. Catalog promotion, with space costs

Promotion of the remaining audited A-chain privates as public machines with
exact time *and* space costs: transfer (word from tape `i` to tape `j`,
`3|w| + 3`), copy (`3|w| + 3`), clear (`2m + 2`, = P12's engine), compare, and
increment — D6-style promotion, not new proof work, seeded from the named
private families. Additionally, the existing catalog rows (P1-P12, P16-P18)
and the W/L/E combinators are **retro-annotated with space theorems** — new
`spaceUsed` lemmas beside the existing specs, no signature changes, so the
audited statement surface is untouched (additive growth; open decision 12.3 on
doing this here versus lazily per consumer — the amply-support mandate argues
for here).

### Consumers (rule-of-admission check, §4: two named customers per item)

| Consumer | Uses |
|---|---|
| Chapter-1/2 retrofit (backlog §2) | R1 for the bank/relocation families; R2 for the dispatch families; R3 for `clCopy*`/`clCmp*`/`clRead*`/`clCount*` and the `Build/` harvest families |
| Hennie-Stearns `k`→2 conversion ([AB09] §1.7; ch3-4 plan §2.1) | zones as banks (R1), shifts as R3 transfers, seam discipline (R2); the amortization is mathematics on top |
| Two-work-tape universal machine (ch3-4 plan §2.1, §4a) | R1 + R2 throughout; the retrofit pilot; candidate space-bounded variant feeding Thm 4.8 / Ex 4.1 |
| Chapter-4 ARM extensions (ch3-4 plan §2.5: nondeterministic and polynomial-width variants of `LogProg`) | R1/R2 at their `FinTM` compilation boundary; R3 space rows |

### Placement, sequencing, cost

* New files `Build/Embed.lean` (R1) and `Build/Seam.lean` (R2); R3's new rows in
  a new `Build/Catalog.lean` (`Primitives.lean` is already over the size policy;
  final name is open decision 12.2, settled before the spec audit per §9.6).
  Namespace `Turing.FinTM`; order list after `Build/Loop`.
* Process per `workflow.md`: maintainer-serial spec layer (quantifier-sensitive,
  as §10), statement gate, fills as harvest-adaptation batches, fill audit. The
  gate must close before the first chapter-3/4 fill epoch (plan §4a); statement
  phases of chapters 3-4 run in parallel.
* Estimate (campaign points): R1 spec+fill ≈ 10 (the lockstep is the risk
  concentration, L-style), R2 ≈ 8, R3 promotions + space retro-annotation ≈ 12,
  serial spec layer ≈ 6. Total ≈ 36, one mid-size batch equivalent.

### Open decisions (human review; audit verifies, never disposes)

* **12.1** R2 space accounting — **answered (user, 2026-10-08): the sharper
  form.** The spec states per-tape bounds, with the max for disjointly-owned
  tapes (sharpest available; downstream applications may depend on the
  sharpness).
* **12.2** R3's file layout — **answered (user, 2026-10-08): option (a)**, a
  new `Build/Catalog.lean` holding the new rows and the space lemmas for the
  old rows, keeping `Primitives.lean` byte-identical; a backlog item records
  the later refactor toward the symmetrical per-theme layout (option (c)),
  via the D7 split window.
* **12.3** Space retro-annotation — **answered (user, 2026-10-08): the refined
  now-option**: the primitives as realized (P1-P15), wrappers (W1-W3) and the
  loop (L) get `spaceUsed` theorems in this increment; the emitter combinators
  (E1-E4′) stay lazy until a space consumer appears, **and the E3′ stream rows
  P16-P18 ride with that lazy scope** (their only consumers are the emitters —
  scope clarification recorded at skeleton time, 2026-10-08, flagged to the
  §12 statement-gate audit and reversible there if the gate reads the
  original "P1-P18" wording as binding).
* **12.4** R1 emission policy — **answered (user, 2026-10-08): two named
  transformers** (suppressing and forwarding) over a shared private core, so
  each spec stays crisp and downstream applications cite whichever fits.

### Citations (policy.md §2, *Design adaptation*)

The configuration-level design is adapted from — with nothing transcribed —
**Édouard Bonnet's `classical-complexity`** (Lax Archive lax-434930), module
`proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`: `StackProgram`'s
`compile_correct`, `StackRename`'s `rename_executes`/`executes_in_sum` (the
bank-embedding and seam-composition shapes), and the
transfer/clear/copy/for/repeat routine catalog; commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0; examined 2026-10-05,
different toolchain (Lean 4.33 vs our 4.25) and machine model (TM2-style keyed
stacks vs `FinTM` tapes with heads). Suggested tag: `[Bon26]`. The R-modules'
docstrings and their blueprint entries must carry this citation, alongside the
existing `[Balbach22]` (AFP `Cook_Levin`) for the composition architecture and
the in-repo credits to the colleague modules named above.

### 12.5 Round-1 audit repairs (2026-10-09)

The §12 statement-gate round 1 (`audits/routine-infra-findings.md`: 0
blockers, 4 majors) drove four repairs, landed with the round-2 pack:

* **R1 → the returning embeddings** `embedSilentRetTM`/`embedEmitRetTM`
  (states `S ⊕ Unit`): the closed transformers lose a final halting
  emission to either the halt or a premature seam dispatch — the audit's
  formal trace. The returning flavors execute every source action through
  the halting transition and land in the live anchor `Sum.inr ()`.
* **R2 → general-configuration seam composition**
  (`seamCompTM_run_ofCfg` + first-return and visited forms): the canonical
  `Cfg.ofWords` theorems cannot consume arbitrary frames, displaced
  inactive heads, or accumulated output; the general form starts phase two
  from phase one's returned configuration with only the control state
  replaced.
* **R3 → the fresh-entry/release adapter** `seamReleaseTM`: positive
  calls returning to their own anchor are now seam-consumable (the entry
  action executes unconditionally from a fresh start state).
* **R4 → the threaded-map witness** is re-commissioned as a forwarding
  controller (validate/buffer, emit prefix, forward payload output);
  the received captured-payload machine is refuted as a witness for the
  linear-administration bound.

Scope notes R9 (physical-tape selection is not zone multiplexing) and R10
(loop sibling contracts not exported) are recorded at their definition
sites.

### 12.6 Framed catalog contracts (2026-10-10, after ZF-A2's escalation)

**The gap.** The R3 rows (`transferTM`, `copyTM`, `clearTM`, `compareTM`,
`incrementTM`) are stated only from `Cfg.ofWords`: every head at the origin,
every tape a globally buffered word. The zone shift machines (`Build/Zone.lean`,
`exists_zoneShiftInTM`/`OutTM`) have **exactly two tapes**. One is the zoned data
tape; the other is a scratch tape that starts and ends as the unary level word.
Their staging, cleanup and binary navigation counter therefore all run at
**displaced heads beside unrelated data**, where no canonical contract applies.

ZF-A2 (`audits/zone-agent-reports/f1-A2-REPORT.md`) showed the gap concretely,
with a kernel-checked regression. On a valid three-level carrier, a bare transfer
from a displaced head reads past the word's end and erases a cell that belongs
to the next zone. The cure is a delimited word: blanks at relative positions
`-1` and `|w|`, installed by the consumer, which saves the overwritten cells in
finite control and restores them afterwards. Correspondingly, the contract must
quantify over an arbitrary surrounding frame.

**Decision (user, 2026-10-10).** A small §12 extension: maintainer-drafted
statements, a short statement gate, then a fill batch; ZF-A3 follows. The
routines are local, since each step reads only the scanned cells of the touched
tapes, so a framed contract is the faithful generalization. No new machine is
defined.

**The five statements** (`Build/Catalog.lean`, after the R3 rows, sorried):

| Contract | Exact time | Effect on the touched tapes |
|---|---|---|
| `transferTM_run_ofCfg` | `2·|w| + 2` | source interval blank; destination interval `w` (old destination contents arbitrary) |
| `copyTM_run_ofCfg` | `2·|w| + 2` | destination interval `w`; source intact |
| `clearTM_run_ofCfg` | `2·|w| + 2` | the word interval blank |
| `incrementTM_run_succ_ofCfg` | `2·p + 2`, where `p = (w.takeWhile id).length` | the word interval holds `v`, where `incFixed w = some v` |
| `incrementTM_run_overflow_ofCfg` | `2·|w| + 2` | the word interval all `false` |

In every case the routine reaches its `done` anchor exactly at the stated time
and not earlier. Every cell outside the word intervals, every head, the native
input position and the output are unchanged. Up to the exit the touched heads
stay within `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1,
pos + p]`) and all other heads are fixed. Space bounds follow from the
trajectory clause through `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
`incrementTM`'s carry-sensitive `2p + 2` is the per-step cost that makes the zone
machines' anchored binary countdown sum geometrically, the audited `O(2^i)`
navigation ledger. The canonical `2|w| + 2` public bound is too loose for that,
as ZF-A2 flagged.

**Specialization and dedup.** With the origin heads and globally buffered words
of `Cfg.ofWords`, each framed contract specializes to its canonical R3 row. The
fill batch therefore proves the framed form and **re-derives each canonical row
from it**, through a sanctioned proof-body swap with the public statement
unchanged. That generalizes the private trace lemmas rather than duplicating
them. `compareTM` is not framed here, since no current consumer needs it; it
follows the same pattern on request.

**Pre-ship execution check (mandatory practice).** Every statement was executed
on concrete configurations with displaced heads, a nonblank outer frame and the
edge cases (`w = []`, `p = 0`, all-`true` overflow). The exact final
configuration, the no-earlier-exit clause and the trajectory were compared:
63 cases, all pass, and a wrong-time negative control fails
(`audits/evidence/s12-framed/`).

### 12.7 Counter-driven loops (design, 2026-10-10, after ZF-B3's escalation; decisions 12.7.1–12.7.6 taken by the user the same day)

**The gap.** ZF-B3 (`audits/zone-agent-reports/f1-B3-REPORT.md`,
`f1-B3-CONTINUATION.md`) stopped on two shared-interface requests:

- a public fixed-width **decrement** routine with a framed contract;
- a loop whose number of rounds is a **binary counter read from a tape**,
  with the body's state kept on **persistent, arbitrarily positioned tapes**.

Every public loop host (`exists_loopTM`, `exists_loopCfgTM`,
`exists_loopFindTM`, `exists_emitLoopTM`) does something else. It runs
`R x.length` rounds, a count fixed by the input's *length* through a fuel
machine, and every round runs between canonical
`Cfg.ofWords anchor (stateWord …)` seams. A simulator would therefore have to
re-serialize its two simulated work tapes every round, which ZF-B3 rightly
refused.

**This is a shared need, not a ZF-B3 one.**

| Consumer | Status | What it needs |
|---|---|---|
| `Codes2Tape.exists_uniformMachineCode2` | ZF-B3's open target | Simulate at most `t` source steps, `t` in binary on a tape, over two persistent source tapes; one joint polynomial |
| `Diagonalization/EXPCOM.lean` | sorried | The same pattern ("simulate at most `t` source transitions under a binary countdown") |
| `Diagonalization/NTimeHierarchy.lean` | sorried | A **fused** countdown at **linear** overhead: one tick per simulated step, the borrow cost amortized by `Σⱼ ν₂(j) ≤ t` (round-1 finding 5). It needs an **amortized total**, not a per-tick worst case |
| `SpaceComplexity/Hierarchy.lean` | sorried | A configuration-count clock |

**Existing clocks, all private or super-linear.** These are 12.2c candidates
for re-derivation as consumers of the shared host, not inputs to copy:

- `Build/Loop.lean`'s fuel debit: `loopDebit`, `loopValue`, `loopHost_borrow*`.
- `Build/Catalog.lean`'s `f2_loopDebitTM` / `f2_loopBorrow_correct`. This is a
  clean 1-tape little-endian decrement: exact `2·(borrow position) + 2`
  steps, zero wraps to all-`true` with an underflow verdict. It is stated
  only canonically.
- `Universal.lean`'s private deadline interpreter `timedUniversalTM`, the
  quadratic one-tape clock behind `timed_universal`.
- `TimeHierarchy/ClockMachine.lean`'s `clockTM`, the deterministic quadratic
  re-scan. These are colleagues' files; under the user's standing preference
  any dedup there is 12.2c work, not theirs.

**Proposed components.**

**C1 — `decrementTM k i : MultiTapeTM k Bool FlagPhase`**, an R3-family row,
the mirror of `incrementTM`. It scans `false` cells to `true` moving right; the
first `true` becomes `false`, with the success verdict; reaching the right
blank, the word is all `false`, so the value is `0`, and the verdict is
underflow, leaving the word all `true`. It returns to the origin through a
`rewind` phase. Framed contracts, in the §12.6 shape:

- `decrementTM_run_succ_ofCfg`, at exact time `2q + 2` where
  `q = (w.takeWhile (· = false)).length`;
- `decrementTM_run_underflow_ofCfg`, at `2|w| + 2`.

The **proof route must not copy the increment proof.** `decrementTM` is
`incrementTM` conjugated by bit complement, so its contracts are derived from
increment's proved framed contracts by a public symbol-complement transport
lemma (decision 12.7.4).

**C2 — `counterLoopTM`, the counter-driven loop host.** Given a body
`B : MultiTapeTM k Bool S` with a re-entry anchor `a`, the host has
`k + 1` tapes, the last one the counter, and states `S ⊕ FlagPhase`.

- At the anchor it runs `decrementTM` on the counter.
- On success it re-enters the body at `a`.
- On underflow it exits to a live `done` anchor.
- If a body round reaches a designated body exit (for a simulator: the
  simulated machine halted), the host exits to a second live `escape`
  anchor.

Its contract `counterLoopTM_run` is stated over **arbitrary configurations**
and has three parts:

- **The body's hypotheses.** A body invariant `P`. A round contract: from any
  `c` with `P c` at `a`, the body reaches, at the exact time `τ c > 0`, either
  the anchor again (with `P`, giving `next c`) or the exit (giving
  `exitCfg c`), without revisiting `a` earlier. And the body never touches the counter
  tape, which the host's embedding enforces.
- **The conclusion.** From the host configuration carrying `c` and a counter
  word `w` of value `d`, delimited:
  - if no round exits early, the host reaches `done` after exactly `d`
    rounds, with body part `next^[d] c` and counter `List.replicate |w| true`;
  - otherwise it reaches `escape` at the first exiting round `r < d`.
- **Total time, exact:** `Σ_{r<d} τ(next^[r] c)` plus the decrement costs
  `Σ_{v=1}^{d} (2ν₂(v) + 2) + (2|w| + 2)` (amortized, at most `4d + 2|w| + 2`)
  plus explicit per-round dispatch constants, fixed when the statements are
  drafted, in the first case; correspondingly in the second. **Uniform-bound
  corollary:** if `τ c ≤ B` whenever `P c`, the total is at most
  `d·B + 4d + 2|w| + O(d)`. Both cases come with no earlier exit and with trajectory
  bounds (counter head within `[pos − 1, pos + |w|]`, body heads as the body's
  own).

C2 is assembled from the §12 layer: the embedding for the body's tape
selection, seams for the anchor/decrement alternation, and the C1 contracts.
No loop-host proof is copied.

**Decisions (user, 2026-10-10).**

1. **Counter placement: a dedicated extra tape**, the host's last tape.
2. **Exits: two live anchors**, `done` and `escape`. A consumer attaches one
   continuation to each with two `seamCompTM` applications, so no new
   composition lemma is needed. A corollary drops the `escape` hypothesis for
   bodies that never exit early. The outermost machine adds its halt once.
3. **Round cost: an exact per-round cost function `τ` of the body
   configuration at the round's start.** The total time is stated exactly as
   the sum over the run's rounds. A round-indexed cost is the special case
   `σ r := τ(next^[r] c)`. A consumer that knows only a bound takes `τ` to be
   the first-return time, which is unique since the contract excludes earlier
   returns. The **uniform bound `B`** is a corollary. This is the
   sensitivity downstream consumers need, for example simulations whose step
   cost grows with tape content.
4. **Decrement proof route: a symbol-complement transport lemma** (option a).
   The §12.6 fill has landed, so increment's framed traces stay as they are.
   The lemma is generic over machines conjugated by a symbol involution, and
   it lives with C1.
5. **Home: a new `Build/CounterLoop.lean`**, importing Catalog, Embed and
   Seam. The 12.2c per-theme reorganization of `Build/` regroups it later.
6. **Scope: the amortized total is stated over the whole run**, not only
   per round.

**Statement phase (2026-10-10).** `Build/CounterLoop.lean` landed with 13
definitions and 10 sorried theorems. The refinements made while drafting:

- **The exit is an `Option S`.** The no-escape corollary is the
  instantiation `exit = none`, so no separate statement is needed.
- **The round hypotheses are stated along the orbit**, not through an
  invariant `P`. This is weaker and so more general; a consumer with an
  invariant derives them.
- **The uniform-bound corollary is pure arithmetic** over the exact time
  (`counterLoop_time_le`). Two amortization lemmas are stated: one for
  prefixes (`4r + 2|w|`) and one for the whole run (`4d + 2|w| + 2`).
- **`decrementTM` is defined as the conjugate** of `incrementTM` by
  `Equiv.boolNot`, through a generic `MultiTapeTM.mapWorkSymbols`. The C1
  contracts are therefore transports of the §12.6 ones.
- **The host has no dispatch steps.** Transitions into the anchor and the
  exit are redirected in place, so the time is exactly the round times plus
  `counterOverhead`.
- **Imports.** Seam is not imported, since consumers compose through
  `seamCompTM_run_ofCfg`. As with `Build/Zone.lean`, the file stays out of
  the `TuringMachine` facade during the statement phase.
- **The counter value** is Mathlib's `Nat.ofDigits 2 (w.map Bool.toNat)`,
  written inline; no new value function is defined.

The executed pre-ship check is `audits/evidence/s12-counter/`, and the gate
pack is `audits/s12-counter-{pack,bundle}.md`.

**Statement gate CLOSED (round 1, 2026-10-10: 0 blockers, 0 majors, 1 minor,
5 notes; `audits/s12-counter-findings.md`).** No false theorem and no missing
soundness hypothesis. Three notes correct or extend this design:

- **SC-4: two continuations need a public prefix lemma.** Two `seamCompTM`
  applications do wire both exits. The escape path through the first
  composite, however, needs the pre-dispatch prefix correspondence, which
  `seamCompTM_run_ofCfg`'s `hexit` cannot provide. The existing private
  `seamComp_left` (`Build/Seam.lean`) proves exactly that. It is to be
  promoted when the first two-continuation consumer is assembled, not copied.
  This corrects decision 12.7.2's claim that "no new composition lemma is
  needed."
- **SC-3: the NTIME consumer needs a nondeterministic lifting.** The host's
  contracts are deterministic (`MultiTapeTM`, `runFrom`). Before the NTIME
  hierarchy fill, a choice-stream lifting contract is needed, with branch
  alignment through the bookkeeping pauses.
- **SC-5: an optional visited-set corollary.** A public `spaceUsedByTape` or
  visited-set corollary of the trajectory clauses would save the space
  consumers repeated bookkeeping.

Next: the fill batch, after RB5 merges so the host proof can cite the
promoted `MultiTapeTM.runFrom_mapState_of_agreeOn`. ZF-B3's continuation
follows that fill. The existing private
clocks are on the 12.2c tasklist as re-derivation targets (plan §4d,
item 12).


### 12.8 Configuration-graph rows (design draft, 2026-10-10; for the statement phase)

*Drafted from the S1 research (maintainer-commissioned), recorded for the user's decisions 12.8.1–12.8.6. The maintainer's alternative for 12.8.1 is at the end.*

**Why.** The user chose design A for S1b, the summit of `ConfigGraph.lean`:
a configuration-level simulator built on §12 rows (decision log, 2026-10-10).
The S1 research found six capabilities that no public row provides.

| Gap | Missing capability |
|---|---|
| GAP-1 | a native-input-dependent clean seam |
| GAP-3 | a framed compare |
| GAP-4 | a configuration codec with transition application |
| GAP-5 | writing a word at a displaced head |
| GAP-6 | seek over delimited records |
| GAP-7 | two continuations after `counterLoopTM` |

This note proposes reusable rows for all six. Their consumers are every
configuration-graph walker of the campaign:

- S1b (`NSPACE ⊆ DTIME(2^{O(S)})`, hence `NL ⊆ P`);
- Savitch;
- the `PATH` reduction;
- the space hierarchy;
- `TQBF ∈ PSPACE`;
- `NP ⊆ PSPACE`.

**Constraints.**

- (i) **G1** is generalizing `Build/Embed`, `Build/Seam`, Catalog's R3
  sweeps and `FinTM.bufferTape` to `{Symbol : Type*}` in place. A row that
  extends those files' private traces waits for the G1 gate.
- (ii) **G2** (`copyMapTM`/`transferMapTM`) owns the mapped-sweep scanner in
  Catalog. Rows of that family are coordinated with it: one trace per routine
  family.
- (iii) Every row has a framed contract in the §12.6/§12.7 shape (template
  below).
- (iv) The campaign deciders are `FinTM Bool`. `incrementTM`, `decrementTM`,
  `counterLoopTM`, the compare contracts and the Loop hosts stay at `Bool` after
  G1. The record layer is therefore **binary**: decision 12.8.1.

#### Contract template (all rows)

For a tape `i` and a word `w`, write **`Delim d i w`** for the §12.6
hypothesis `∀ p, -1 ≤ p → p ≤ |w| → d.workTapes i (d.workTapePos i + p) =
bufferTape w p`. That is, `w` sits at the head with blanks at `-1` and `|w|`.
Each row `R` states, from any `d` in its start phase:

1. **Exact time** `τ`: `R.runFrom d τ = finish`, where `finish` is `d` with only
   the listed cells and control changed. Every other cell, every head, the
   native input position and the output are unchanged unless the row says
   otherwise.
2. **No earlier exit:** `∀ t < τ, state ≠ done`. (For verdict anchors, this is
   `∀ b`.)
3. **Trajectory:** touched heads stay in a stated interval, typically
   `[pos − 1, pos + |w|]`, and the other heads are fixed. Space follows by
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma lives in
   `Build/Zone.lean`, so Catalog rows cannot cite it; 12.2c item 9's Zone split
   is its natural moment to move down.

The time constants below are indicative. The statement phase fixes them by
the executed pre-ship check, as in §12.6 practice.

Where an exact closed form is unnatural (R8.7's step row), the contract is the
first-return form instead: `∃ t ≤ B`, plus the no-earlier-exit clause.
`counterLoopTM` consumes it with `τ :=` that `t`, which is unique (decision
12.7.3).

#### R8.1 Framed compare (GAP-3)

- `compareTM_run_ofCfg (fst snd) (hne : fst ≠ snd) (u v) (d)
  (hstate : d.state = some .run) (hu : Delim d fst u) (hv : Delim d snd v)`.
  - Exact time `2·δ + 2`, with `δ` the first index where `u` and `v` differ or
    either word ends (`δ ≤ min |u| |v|`, the private `catalog_compare_stop`).
  - Finish: `d` with state `done (decide (u = v))`, every tape unchanged.
  - No earlier `done b`. Trajectory: both heads in `[pos−1, pos+δ]`.
- **Alphabet:** generic with `[DecidableEq Symbol]`. G1 makes `compareTM`'s
  definition generic and keeps its contracts at `Bool`, so the framed row is
  stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.
- **Trace:** generalize `catalog_compare_trace`, `catalogCompareF` and
  `catalogCompareR` over an outer frame and two start coordinates, on the
  shared `catalog_trace_run` skeleton. No second trace.
- **Home:** `Build/Catalog.lean`, **after the G1 gate**.
- **Note:** a record is a list of blank-separated fields (R8.7), so
  `recordEqTM` is `F` framed compares with R8.3 seeks between them.

#### R8.2 Fold: a finite-state scan with a verdict (new family member)

- `foldTM (i) (δ : A → Symbol → A) (a₀ : A) [Fintype A] [DecidableEq A]`.
  Phases are the forward pass `scan a`, the return `rewind a`, and the anchor
  `done a`.
- `foldTM_run_ofCfg (hw : Delim d i w)`:
  - exact time `2|w| + 2`;
  - finish: `d` with state `done (w.foldl δ a₀)`, all tapes unchanged;
  - no earlier `done`; trajectory `[pos−1, pos+|w|]`.
- **Why a row:** every read of a record field into finite control is a fold.
  That covers the state field, the tag field, "find the marked cell and its
  content and whether it sits at a field end", record validity, and
  acceptance tests. Validators elsewhere (TQBF's well-formedness pass, the
  `PATH` shape checks) are folds too.
- **Alphabet:** generic. **Trace:** `catalog_trace_run` with a read-only
  forward family, as for `copyTM` without the destination. **Home:** Catalog,
  after G1.

#### R8.3 Seek over delimited words and records (GAP-6)

- `skipTM i`: from `Delim d i w`, move right to the word's right delimiter
  and one cell beyond, the next word's first cell. Exact time `|w| + 1`; no
  write; trajectory `[pos, pos+|w|+1]`. `skipBackTM i` is the mirror, starting
  on the cell after the left delimiter of the previous word.
- `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` have the template shape, with
  the finish `{d with workTapePos i := pos + |w| + 1}`.
- `seekFieldsTM i m` (`m` fixed) composes `m` skips by `seamCompTM_run_ofCfg`.
  `seekEndTM i` skips until the next word is empty (two consecutive blanks);
  it is a fold-guarded loop, under the same skeleton.
- **Consumers:** record navigation (R8.7, S1b's table, Savitch's frame stack),
  and **G4**, which "scans outward across zones, using the separators". Both
  skip blank-separated words, so G4 should cite `skipTM` rather than trace its
  own scan.
- **Trace:** this is the forward half of the R3 trace. Add a forward-only
  sibling of `catalog_trace_run` (`catalog_forward_run`, private), to be shared
  with R8.2's forward phase.
- **Alphabet:** generic. **Home:** Catalog, after G1, **coordinated with G2/G4**.

#### R8.4 Writing words at displaced heads (GAP-5)

- **Computed words** are G2's `copyMapTM`/`transferMapTM` (`merge` and
  `extract`). With `extract := fun _ => b` they fill a blank-free interval with
  a constant (`fillTM i b` is the in-place case `src = dst`, which G2 must
  admit or state separately). Nothing new: G2.
- **Fixed words**: `writeConstTM i (w₀ : List Symbol)` writes the hardwired
  `w₀` from the head and returns.
  - `writeConstTM_run_ofCfg`: exact time `2|w₀| + 1`; finish: cells
    `[pos, pos+|w₀|)` hold `w₀` (old contents arbitrary), head back at `pos`;
    trajectory `[pos, pos+|w₀|]`.
  - The machine is a straight-line chain; its proof uses the public
    `FinTM.emit_run` pattern adapted to writes, so it shares no Catalog trace.
  - **Home:** new `Build/Scan.lean`; **can land now**.
  - **Consumers:** record field initializers (state code, tag code), marker
    cells, per-round patterns inside R8.6's body.

#### R8.5 Native-input rows (GAP-1)

All three are generic over `Symbol`, cite the public `FinTM.rewind_scan` and
`timed_rewind`, and live in new `Build/Scan.lean` (**now**). EmitIterBody's
private startup (`body_start`, `copy_step`, `rwTape_*`, `rwInput_*`) is the
same routine and should be re-derived from `inputCopyTM` in 12.2c T2 (CH7-D2,
coordinated with Aparna).

- `inputCopyTM i`: copy the native input onto tape `i` from the head, then
  rewind both heads.
  - Start: input head at `1`, `Delim`-free destination (old contents
    arbitrary).
  - Exact time `2|x| + c`. Finish: `[pos, pos+|x|)` holds `x`, input head at
    `1`, tape head at `pos`.
  - Trajectory: input head in `[0, |x|+1]`, tape head in `[pos−1, pos+|x|]`.
- `inputLengthTM i`: count `|x|` into a fixed-width binary counter on tape `i`
  (one `incrementTM` per input symbol, cited at its framed carry-sensitive cost).
  - Exact time `Σ_v (2·ν₂(v) + 2) + |x| + c`, amortized at most `4|x| + c`
    (§12.7's potential).
  - Finish: the counter holds `bits |x|` padded to its width, and the input head
    is back at `1`.
  - Bool only, because it uses `incrementTM`. Its home is `Build/CounterLoop.lean`
    or `Scan` importing it.
- `inputSeekTM i c`: move the input head to the binary position `p` held at
  tape `i`.
  - Mechanism: copy `p` to the counter tape `c` (`copyTM_run_ofCfg`), rewind the
    input (`timed_rewind`), then `counterLoopTM` with the one-step body "input
    right".
  - Exact time: the copy (`2|p| + 2`), the rewind (`≤ pos + 2`), then
    `p + counterOverhead w (p + 1)`.
  - Finish: input position `p`, counter tape all-`true` (`counterLoopTM_run_done`).
    Callers clear it (`clearTM_run_ofCfg`).
  - Bool only.
  - **Consumers:** R8.7's input read, `PATH_mem_NL`'s matrix indexing (`u·n + v`),
    virtual-input callers needing random access.
- Packaged combinator **`exists_inputCallTM`** = `inputCopyTM` +
  `exists_installCallTM`: call a function-level machine on the native input at a
  clean seam. It is GAP-1's general form. **Home:** new `Build/InputCall.lean`,
  importing Loop, **now**. It touches no G1 file, but must not collide with
  12.2c T1 item 11's Loop edits.

#### R8.6 Counter-driven expansion

- `expandTM (pat : List Bool)` = `counterLoopTM` around `writeConstTM pat`
  followed by a `skipTM`-like advance. From a counter word of value `d` at the
  counter tape and a blank region on tape `i`, it writes `pat` `d` times
  contiguously.
  - Exact time `Σ_{r<d} τ_pat + counterOverhead w (d+1)`, by
    `counterLoopTM_run_done` and `counterLoop_time_le`.
  - The written word is `pat`ⁿ with `n = d`, which is a framed `Delim` for later
    rows.
- **Consumers:**
  - S1b and Savitch: blank tape fields of `2s+1` cell codes, with `s` given in
    binary by the constructor;
  - `spaceConstructible_logSpace`/`_linear`/`_poly` (binary ↔ unary);
  - the space hierarchy's budget loop;
  - the §12.7 clocks.
- Bool. **Home:** `Build/CounterLoop.lean` (not G1-owned). **Can land now**,
  once R8.4's `writeConstTM` exists.

#### R8.7 Configuration records (GAP-4)

**Pure layer** (new `Build/CfgRecord.lean`; statements now).

- **Parameters:** a source `M : MultiTapeTM k Bool Q`, `[Fintype Q]`, a window
  radius `s`, an input length `n`, and a finite **tag** type `T` with an update
  `upd : T → Option Bool → T`. The tag carries emission history; the
  configuration graph instantiates `T := OutSummary` and `upd` := the Q1 append
  table. A Build-level row cannot mention `OutSummary`, which is defined
  downstream in `ConfigGraph.lean`; hence the parameter.
- **`cfgRecord n s (c : Cfg k Bool Q x) (τ : T) : List (List Bool)`**, a list of
  `k + 3` **blank-separated fields**, each a blank-free Bool word:
  - **F0** state: a one-hot code of `c.state : Option Q`, width `|Q|+1`;
  - **F1** input position: `c.inputPos` in little-endian binary at the fixed
    width `|bits (n+1)|`;
  - **F2…F(k+1)** tape `i`: `2s+1` three-bit cells
    `(nonblank, value, head-here)` for `z = −s … s`;
  - **F(k+2)** tag: a one-hot code of `τ`.

  Field lengths depend only on `(n, s)`, so records compare field-wise and
  enumerate by counting.
- **`recordTape`** lays the fields out with one blank between fields (and
  between records); the G3 carrier's separator discipline.
- **Window predicate.** `Turing.Cfg.InWindow s` already exists, defined in
  `ClassPSPACE/TQBF.lean`, *downstream* of every Build file. **Decision
  12.8.2:** relocate it verbatim (same name and body) to `CfgRecord.lean` and
  delete TQBF's copy. That is a surface move in a C1d-owned file, so it waits
  for C1d. The alternative is a second predicate under another name, a
  definitional duplicate.
- **`cfgRecord_inj`:** for `InWindow s c` and `InWindow s d` on the same input,
  `cfgRecord n s c τ = cfgRecord n s d τ' ↔ core c = core d ∧ τ = τ'`. It
  follows `ConfigCount.coreCode_inj`.
- **`cfgRecord_valid`:** a word list is a record iff a fold (R8.2) accepts each
  field. One-hot fields, three-bit cells with exactly one head mark per tape
  field, and `F1 ≤ n+1` (the last by `compareTM` against `bits (n+1)` or by
  a fold).

**Rows** (`Build/CfgRecord.lean`). The statements can be drafted now. The
fills need R8.1–R8.3, so they come after the G1 gate.

| Row | Effect (framed; record at the head of tape `r`; scratch tapes blank) | Built from |
|---|---|---|
| `recordReadTM` | Verdict `done (q, ι, σ, τ, edge)`: state, the input symbol at the coded position, the `k` scanned symbols, the tag, and which tape heads sit at a field end. Record unchanged; input head restored | R8.2 folds per field, R8.3 seeks, R8.5 `inputSeekTM` on a copy of F1, `clearTM` |
| `recordApplyTM a` (`a : Action k Bool Q` fixed, `upd` fixed) | Rewrites the record of `c` into that of `a.apply c`, with the tag updated by `a.output`. Per tape it rewrites the marked cell and moves the mark; F1 gets `incrementTM`/`decrementTM` (framed), with the clamp read off the edge data; F0 and the tag go through `writeConstTM`. Precondition: no mark leaves its field (checked by the read) | R8.4, R8.3, Catalog `incrementTM_run_*_ofCfg`, CounterLoop `decrementTM_run_*_ofCfg`, and one local `markShiftTM` per tape field (new, record-specific) |
| **`recordStepTM M upd`** | **The GAP-4 row.** Verdict `done true` with the record of `M.step c` (tag updated) if that configuration is in the window. Verdict `done false` with the record unchanged otherwise, or if `c` is halted (`done true`, unchanged: a halted vertex is its own successor). First-return contract, `t ≤ C_M·(L + n + 1)` with `L` the record length; trajectory inside the record interval and `[0, n+1]` on input | `recordReadTM` ; finite dispatch on `M.tr` ; `recordApplyTM a`, glued by `seamCompTM_run_ofCfg` and two-continuation dispatch (R8.8). An NDTM is consumed per choice bit through `NDTM.fixChoice` (S1a's promotion) |
| `recordInitTM` | Writes the record of `M.initCfg x` with tag `τ₀`, from a radius word (binary `s`) and the input length counter | R8.4, R8.5 `inputLengthTM`, R8.6 `expandTM` |
| `recordEqTM` | Verdict: the two records at the heads of tapes `r`, `r'` are equal | `k + 3` R8.1 compares with R8.3 seeks |
| `recordTestTM P` (`P` a finite predicate on `(state, tag)`) | Verdict `P (c.state, τ)`. Acceptance is `P := (· = none) ∧ (· = accept)` | R8.2 on F0 and the tag field |
| `recordNextTM` | Lexicographic successor among *valid* records (odometer over all field bits, skipping invalid ones), or an overflow verdict | `incrementTM` per field, carry cascade, `recordValidTM` |
| `recordValidTM` | Verdict `cfgRecord_valid` | R8.2 |

**Space.** Every record row is framed inside its record interval plus
`O(L)` scratch. `L = O(k·s + log n + |Q|)`, which is `O(S n)` for Savitch at
`S ≥ logSpace`. This is why F1 is **binary**: a one-hot input track would make
`L = Θ(n)` and break `SPACE(S²)` at `S = log`.

#### R8.8 Two continuations after a two-exit host (GAP-7)

- Promote the existing private `Turing.seamComp_left` (`Build/Seam.lean:173`)
  as **`seamCompTM_runFrom_left`**, statement unchanged. This is SC-4's
  resolution: "expose the existing prefix lemma … do not copy its induction".
- Add one corollary, **`seamCompTM₂_run_ofCfg`**: for a host with two live
  anchors `e₁`, `e₂` (`counterLoopTM`'s `done` and `escape`), nesting two
  `seamCompTM`s attaches a continuation to each. It states the run along
  whichever exit is reached, with the other continuation's summand
  unreachable.
- Generic after G1. **Home:** `Build/Seam.lean`, **after the G1 gate**.
- **Consumers:** every `counterLoopTM` user with an early exit. S1b's BFS
  (queue empty / counter exhausted), the space hierarchy's budget loop
  (success / cap), and `recordStepTM`'s internal dispatch.

#### Placement and timing

| Row(s) | Home | Touches a G1-owned file? | When |
|---|---|---|---|
| R8.4 `writeConstTM`; R8.5 `inputCopyTM`, `inputSeekTM`, `inputLengthTM` | new `Build/Scan.lean` (imports CounterLoop) | no | **now** |
| R8.5 `exists_inputCallTM` | new `Build/InputCall.lean` (imports Loop, Scan) | no | **now** (coordinate with 12.2c item 11) |
| R8.6 `expandTM` | `Build/CounterLoop.lean` | no | **now**, after `writeConstTM` |
| R8.7 pure layer, `InWindow` relocation | new `Build/CfgRecord.lean`; `ClassPSPACE/TQBF.lean` | no; TQBF is C1d's | statements now; relocation after C1d |
| R8.1 framed compare; R8.2 fold; R8.3 seek | `Build/Catalog.lean` | **yes** | **after the G1 gate**, with G2 (shared scanner) |
| R8.4 fill (in-place mapped sweep) | Catalog (G2) | **yes** | with G2 |
| R8.8 seam promotion + corollary | `Build/Seam.lean` | **yes** | **after the G1 gate** |
| R8.7 record rows (fill) | `Build/CfgRecord.lean` | no, but cites R8.1–R8.3 | fill after R8.1–R8.3 land |

The process is the house one: maintainer-drafted statements; an executed
pre-ship check (concrete configurations, displaced heads, nonblank outer
frames, `w = []`, `s = 0`, `k = 0`, a halted source); a short statement gate;
fill batches split now/after-G1; a fill gate.

#### Consumers: which rows each walker uses

| Consumer (audited sketch) | Rows |
|---|---|
| **S1b** `NSPACE_subset_exp_dtime` (BFS; then `NL_subset_P` and Ex 4.3 by the binding route) | R8.7 `recordInitTM`, `recordStepTM` (×2 choice bits), `recordEqTM`, `recordTestTM`; R8.3 table navigation; R8.4/G2 append and counter initialization; R8.6 window fields; R8.8; existing `counterLoopTM`, `embedSilentRetTM_run` (constructor capture), `seamCompTM_run_ofCfg`, `copyTM_run_ofCfg` |
| **Savitch** `savitch` ("frame stack … catalog copy/compare/increment … one extra bank runs the vertex-adjacency test") | `recordStepTM` + `recordEqTM` for `adj(u, v)` (`u = v ∨ step u = v`, both choice bits); `recordNextTM` + `recordValidTM` for the midpoint enumerator; R8.3 seek over the frame stack; `copyTM`/`clearTM` for frame push/pop at **fixed intervals** (note 7); `incrementTM` for the depth field; R8.8 for the recursion's two returns. Space contracts of every row are load-bearing |
| `spaceConstructible_poly`/`_logSpace`/`_linear` | R8.5 `inputLengthTM`; R8.6 `expandTM`; `incrementTM` |
| **`PATH_NLComplete`** hardness (adjacency "by one local transition-table check", logspace) | The sketch's engine is the ARM layer (`arm_decides`). Optionally, a TM route: `recordStepTM`'s space clause with binary F1 gives `O(log n)`-space adjacency deciders for the index languages. Decision 12.8.4 |
| **`PATH_mem_NL`** (matrix indexing) | R8.5 `inputSeekTM` (once a nondeterministic host exists, SC-3) |
| **Space hierarchy** `space_universal`, `space_hierarchy` (interval counters, core-count clock, budget loop, probe/replay over fixed banks) | `incrementTM`/`decrementTM` (interval counters), `counterLoopTM` + R8.6 (clock and budget loop), R8.8 (success/cap exits), R8.1 (`max − min + 1 > s` against the budget word), `clearTM` resets. It simulates a *coded* machine, so not R8.7 |
| **`TQBF_mem_PSPACE`** (validate-first, depth-first assignment walker, per-clause CNF evaluation) | R8.2 folds (validation, clause evaluation), R8.5 `inputSeekTM` (re-reading prefix bits and matrix bytes), `incrementTM` / a trit odometer (`recordNextTM`'s carry discipline) for the walker, R8.3 seek on the assignment word |
| `NP_subset_PSPACE` | existing `incrementTM` (certificate enumerator) and `vhostEmitTM` (virtual input); R8.8 for accept/exhaust |

#### S1b's machine plan as a composition of these rows

**Host.** A `FinTM Bool`. It has the native input; the constructor's embedded
tapes plus a capture tape; tape `Tab` (the record table); `Cur₀` and `Cur₁`
(successor workspaces); `Rad` (radius and length words); scratch for
`recordStepTM`; and `Cnt`, the counter, which is the last tape, as
`counterLoopTM` requires.

1. **Radius.** Run `M_S` (from `hS`) under `embedSilentRetTM_run`, with its
   output `bits (S n)` captured, then rewind the input (`timed_rewind`). Its time
   is at most `M_S.configBound n (a·S n)` (`ComputesInTime.of_spaceUsed_le`).
   Multiplying by `c₀` is a fixed binary shift-and-add or `c₀` copies.
2. **Initial table.** Lay down `recordInitTM` (via `inputLengthTM` and
   `expandTM`) on `Tab`, with tag `empty` and a one-bit flag field `[false]`
   ("unprocessed") appended to each record.
3. **Counter.** Copy `Tab`'s first record's fields to `Cnt` contiguously
   (`copyTM_run_ofCfg` + `skipTM`), then fill it with `true` (G2 in-place map).
   Its value `2^{bits(record)} − 1` exceeds the record count `V`, so `done` is
   unreachable before `escape` (or is wired anyway by R8.8).
4. **Round** (the `counterLoopTM` body, anchor `a`). `seekFieldsTM` finds the first
   record whose flag is `false`; if there is none, it reaches the body's exit, and
   the host escapes. Otherwise:
   - copy that record to `Cur₀` and `Cur₁`;
   - run `recordStepTM (N.fixChoice false)` on `Cur₀` and
     `recordStepTM (N.fixChoice true)` on `Cur₁`;
   - for each successor in the window, scan `Tab` with `recordEqTM`, and if it
     is absent, append it at `seekEndTM` with flag `[false]`;
   - set the processed record's flag (`incrementTM` on the one-bit field);
   - clear the workspaces, rewind `Tab` (`skipBackTM` to the table start), and
     return to `a`.

   The round's first-return time `τ` is at most `C·(|Tab| + n + L)` with
   `|Tab| ≤ V·(L + F)`.
5. **Verdict.** From either exit (R8.8), fold `recordTestTM accept` over
   `Tab`'s records and emit `[true]` or `[false]`; then halt (a fixed emission
   tail; `FinTM.emit_run` pattern).
6. **Correctness:**
   - The table is the windowed-reachable set: the BFS invariant, with each record
     identified with a `coreSum` by `cfgRecord_inj` at `T := OutSummary`.
   - Membership follows by S1a's targets 1–4 and the audit's note-6 bridge
     (canonical decoding, outside-window rejection by `recordStepTM`'s false
     verdict, path lifting from the true initial configuration, all accepting
     vertices tested, the initial vertex in the table).
7. **Time:**
   - `counterLoop_time_le`: `V·B + 4V + 2|w| + 2` with `B = O(V·L + n)`. Add the
     constructor and startup.
   - Everything is at most `K·2^{c'(S n+1)}`, by the generalized `configBound`
     arithmetic and `n + 2 ≤ 2^{S n + 1}`.
   - All budgets are evaluated at `n` itself. **No monotonicity of `S` is used.**

#### Decisions for the user (12.8.x)

1. **Binary records** (recommended). The rows stay on the `Bool` counter stack,
   with no generic increment or `counterLoopTM`. The alternative is a
   rich-alphabet record: one cell per simulated cell, a simpler step machine, and
   `alphabet_reduction{,_spaceUsed}` at the end. It needs `incrementTM`,
   `decrementTM` and `counterLoopTM` generalized over two designated digit
   symbols (Catalog is G1-owned; CounterLoop is not).
2. **`Cfg.InWindow` relocation** from TQBF to `Build/CfgRecord.lean`, after C1d.
3. **`recordStepTM`'s contract form:** first-return with a bound (recommended),
   or an exact closed form.
4. **`PATH` hardness engine:** ARM (as sketched) or TM record rows with space
   clauses.
5. **Fold and seek in Catalog** (one trace family, after G1), or in `Scan` now
   with their own private skeleton. The latter is faster, but it is a second
   trace of the R3 forward pass.
6. **EmitIterBody dedup** onto `inputCopyTM` in 12.2c T2 (coordinate with
   Aparna).

#### Decisions 12.8.1–12.8.6 (2026-10-10)

1. **Rich-alphabet records** (user): multi-track record cells, mark moves as
   G2 mapped sweeps, and Bool counter rows on rich tapes through **one new
   embedding transport**. Finished by `alphabet_reduction` and
   `alphabet_reduction_spaceUsed`. The maintainer's alternative below is
   adopted, and the binary plan above is superseded where they differ.
2. **`Cfg.InWindow` moves** verbatim to `Build/CfgRecord.lean` after C1d
   (default).
3. **`recordStepTM` has a first-return contract with a bound** (default).
4. **`PATH`-hardness stays on the ARM engine**, as audited (default). The
   record-row route remains an option.
5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
   R3/G2 trace, one trace per routine family.
6. **EmitIterBody's private input-copy startup is re-derived** from the new
   input rows in 12.2c T2, with the ch7 owner (default).

**Next.** A revised statement draft for the rich design. What can start
now: the embedding transport and the alphabet-generic input and
constant-write rows. The record rows, fold and seek wait for G1 and G2.

#### Maintainer's alternative for 12.8.1: rich-alphabet records through one embedding transport

Records could follow the §13d pattern instead of being bit-coded. Each record
cell is one rich symbol with tracks (content `Option Bool`, head mark, field
separators), as in the G3 `ZoneCell` carrier. Moving a head mark is then a G2
mapped sweep on one track, and no per-tape `markShiftTM` is needed. Fields
compare through the generic framed compare, and folds read one symbol per
cell.

The binary rows (`incrementTM`, `decrementTM`, `counterLoopTM`, the compare
contracts) need not be generalized. **One new transport lemma** runs them on
rich tapes: the embedding analogue of §12.7's `mapWorkSymbols`, which lifts a
`Bool` machine along `e : Bool ↪ Γ`. Its contract holds from configurations
whose work cells all lie in the image of `e` or are blank, which a dedicated
counter tape satisfies.

The simulator is finished by `alphabet_reduction` for time and by
`alphabet_reduction_spaceUsed` for space (space at most `(N+1)·space + k`).
The latter keeps Savitch and the space hierarchy within their bounds. The
input-position field stays binary over designated digits, so record length
stays `O(k·s + log n + |Q|)`.

The cost is the transport lemma, and records that wait for G2's mapped sweeps
(after the G1 gate). The gain is that the record machines become compositions
of generic rows instead of bit-group machines, and §12.8 and §13d share one
multi-track discipline.


### 12.8a Statement draft for the rich-alphabet design (2026-10-10)

*Recorded from the S1 agent's draft. Its probe is `audits/evidence/s12-8/S128StatementsProbe.lean.txt`; run by the maintainer against the G1 side-branch tree it gives 0 errors and 12 sorry warnings, one per statement left to the fill. Maintainer decisions O1, O4, O5, O6 and the user's O2, O3, O7 are recorded at the end (§8).*

*Landed as statements on 2026-10-11, branch `integrate/s12-8-statements`: §8 lists the landed names, which supersede the draft's below where they differ, the changes from the draft, the R8.0b target signatures, and the open questions for the statement gate.*

*Draft for the statement phase, 2026-10-10. Base: campaign `19964447`; G1 side branch `s13d/g1`
(`10c2c08d`, PR #15, awaiting its gate).*

**Probe.** `drafts/s12-8-probe.lean`, with its output in `s12-8-probe.out`. It contains the
exact Lean of everything below.

- Against the G1 tree (`tools/leanprobe-g1.sh`): **0 errors, 0 warnings other than 12
  `declaration uses 'sorry'`**, one per proposed statement whose proof is fill work.
- Part A, the transport, is fully proved and also elaborates at the campaign HEAD
  (`tools/leanprobe.sh`, extracted as `s1work/p8/partA-head.lean`): 0 errors, 0 warnings.
- Every exact time below that the probe could execute was checked by `decide` on concrete
  configurations (§12.6 practice). That covers seek, the constant writer, the scan with a
  mark-shift instance, the input copier, and the framed compare at displaced heads.

#### 0. What the rich design needs, and the one gap in the decision as worded

Decision 12.8.1 adopts rich record cells, with the `Bool` counter rows run on rich tapes
through one embedding transport. The transport (R8.0) does what was asked:

- it lifts **any** `Bool` machine along `e : Bool ↪ Γ`;
- the lifted increment and decrement rows run on a dedicated digit tape inside a rich host,
  through G1's generic R1 (Part B of the probe).

**It cannot lift a loop with a rich body.** `counterLoopTM M` requires
`M : MultiTapeTM k Bool S`, so lifting it only serves `Bool` bodies. S1b's BFS round, Savitch's
frame step and every record row have rich bodies. After G1, no loop host exists over a
non-`Bool` alphabet. Decision 13d.7 generalized only Seam, Embed, `bufferTape` and the R3
sweeps. It deferred the loop hosts "only when a large-alphabet consumer needs them", and
§12.8's records are that consumer.

The rich design therefore needs **R8.0b, `counterLoopTMVia`**, a counter loop over any
alphabet:

- the body runs through R1 on the first `k` tapes;
- the counter is a dedicated last tape of digits `e b`, decremented by the lifted
  `decrementTM 1 0`, also through R1.

No new trace is needed. The existing round induction is generalized in place, and the
`Bool` contracts are re-derived from the generic ones: at `e = Function.Embedding.refl Bool`
the two tables agree, so Z5's `MultiTapeTM.runFrom_eq_of_agreeOn` transfers. This is the one
substantive addition to the decision; see §5 for its sequencing.

Two smaller findings:

- **The tag type.** `alphabet_reduction` needs `[Fintype Γ]`, and
  `Γ = RecSym N.State T` is `Fintype` only when `T` is. `Turing.OutSummary`, which is frozen,
  derives only `DecidableEq`. So S1b uses `T := Fin 3` through a code of the summary, as S1a's
  private counting already does, or sanctions a `Fintype OutSummary` export. Open decision O4.
- **Space on foreign inputs.** `alphabet_reduction_spaceUsed` hypothesizes
  `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, that is, over **all** rich inputs, including
  non-`Bool` ones. A lifted `Bool` machine reads a foreign symbol as a blank (`decodeBool`), so
  its space on such inputs is not controlled. Every rich space-bounded simulator (Savitch, the
  space hierarchy) must therefore start with a native **input validation fold**, R8.5d, and stop
  on a foreign symbol.

#### 1. R8.0 — the embedding transport

**Home: a new low file `TuringMachine/SymbolLift.lean`, importing `TuringMachine/Finite`.**
The alternative was CounterLoop's `SymbolTransport` section. The transport uses only
`Configuration`/`Deterministic`/`Finite`, and it has consumers below `Build/`: the G3 carrier
(`ZoneSym := Bool ⊕ …` with `e := Sum.inl`) and the Robustness layer. A low home also keeps it
out of `CounterLoop.lean` while that file's §12.7 fill gate is open.

- **Imports:** `Finite` imports `Deterministic`, which imports `Configuration`. Its up-closure
  contains no `Build/` module, so no cycle is possible.
- **Facade:** the `TuringMachine` facade gains one import.
- `mapWorkSymbols` (CounterLoop) can join it at 12.2c's per-theme split.

**Exact declarations** (verbatim in probe Part A, proved):

```lean
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) : decodeBool e (e b) = some b
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State   -- writes/emission mapped by e
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) : Cfg k Γ State (x.map e)
  -- state, heads unchanged; inputPos := Fin.cast _ c.inputPos; cells and output mapped by e
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State   -- reads through decodeBool e, writes through e
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M) (e) {x} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e
lemma MultiTapeTM.liftSymbols_initCfg : (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e
lemma MultiTapeTM.liftSymbols_spaceUsed : (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t
@[simp] lemma Cfg.liftSymbols_state, Cfg.liftSymbols_workTapePos   -- rfl
lemma Cfg.liftSymbols_inputSymbol : (c.liftSymbols e).inputSymbol = c.inputSymbol.map e
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ
theorem FinTM.liftSymbols_computesFunInTimeVia (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T
```

The one-step lemma `MultiTapeTM.liftSymbols_step`, and `moveInputPos_cast`, are `private` in
the real file.

**Proof notes.**

- `MultiTapeTM.runFrom_comm_of_step` (vendored `Deterministic.lean`) is single-alphabet, so the
  run lemma is a direct induction with `runFrom_succ_eq_step`.
- The one-step lemma decodes the input symbol through
  `Cfg.liftSymbols_inputSymbol`, which needs `Fin.cast` care on the boundary tests.
- The work reads decode by `decodeBool_apply`. Writes commute with `Function.update`.
- The output is `(Option.map e o).toList = o.toList.map e`.

**Corollaries after the G1 merge** (probe Part B, proved). These touch no G1 file:

- `FinTM.bufferTape_map (e) (w) (p) : bufferTape (w.map e) p = (bufferTape w p).map e`. It lives
  in `SymbolLift.lean`, which then imports `Simulation`.
- **Framed lifted rows are one-line consequences.** The probe proves the increment success case:
  `((incrementTM k i).liftSymbols e).runFrom (d.liftSymbols e) (2p+2) = (finish).liftSymbols e`.
  So no per-row lifted statement is proposed; consumers rewrite with
  `liftSymbols_runFrom` and cite the `Bool` row.
- **Dedicated digit tape inside a rich host:**
  `(embedEmitTM ι ((incrementTM 1 0).liftSymbols e)).runFrom (embedEmitCfg ι tapes heads pre
  (d.liftSymbols e)) t = embedEmitCfg ι tapes heads pre ((… .runFrom d t).liftSymbols e)`. The
  host's other tapes (rich records) are R1's frame, so the transport's in-range hypothesis is
  only about the dedicated tape. This is the "dedicated counter tape" discipline of decision
  12.8.1, in usable form.

**Finishing.** Two cases:

- **Time.** A rich decider `D : FinTM Γ` with
  `D.ComputesFunInTimeVia e (fun x => [indicator L x]) T` becomes `FinTM Bool` by
  `FinTM.alphabet_reduction e D f T`, which gives `∃ c M', M'.ComputesFunInTime f (c·(T+1))`.
  The constructor and every `Bool` subroutine enter `D` as `FinTM.liftSymbols` /
  `MultiTapeTM.liftSymbols`, with unchanged time (`liftSymbols_computesFunInTimeVia`) and space
  (`liftSymbols_spaceUsed`).
- **Space.** Use `alphabet_reduction_spaceUsed`, subject to the foreign-input caveat of §0.

##### R8.0b — `counterLoopTMVia`, the counter loop over any alphabet

**Home:** `Build/CounterLoop.lean`. **When:** after the G1 gate (it needs generic
`embedEmitTM`/`embedEmitCfg`) **and** after the §12.7 fill gate. The probe's Part E has the
exact text.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1)
def counterLoopTMVia {k} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : (embedEmitTM Fin.castSuccEmb M) redirected by counterLoopRedirect a exit
  -- .dec f  : (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)) redirected by counterLoopDecExit a
  -- .done / .escape stationary
theorem counterLoopTMVia_run_done   -- counterLoopTM_run_done verbatim with Bool ↦ Γ, plus:
    (hw : ∀ p, -1 ≤ p → p ≤ |w| → ct (cp + p) = bufferTape (w.map e) p)   -- w : List Bool
    -- finish counter cells: `some (e true)`; time `Σ τ + counterOverhead w (d+1)` (unchanged)
theorem counterLoopTMVia_run_escape -- counterLoopTM_run_escape likewise; counter
    -- `bufferTape ((counterWord w (r₀+1)).map e)`
```

- **In-place generalizations (types only, bodies verbatim, G1 rule 2):** `counterLoopCfg` and
  `counterLoopOrbit` become `{Symbol : Type}`. The probe states them as `…Via` copies only to
  avoid a clash.
- `counterLoopTM`, its definition and all `Bool` statements stay byte-identical. Their **proof
  bodies** are swapped to instantiate the generic contracts. The route is
  `runFrom_eq_of_agreeOn` between `counterLoopTM M a exit` and
  `counterLoopTMVia (Function.Embedding.refl Bool) M a exit`. Their dec-phase tables agree
  pointwise (`decodeBool refl γ = some γ`, `Option.map refl = id`, and R1's single-tape action
  equals `decrementTM (k+1) (Fin.last k)`'s), and the other phases agree definitionally.
- **One round induction; net private count down.** `counterLoop_time_le` and the counter
  arithmetic are alphabet-free and reused as they are.

#### 2. The record carrier — `Build/CfgRecord.lean`

**Imports:** `Build/CounterLoop` (for R8.0b) and `TuringMachine/SymbolLift`. **No
`SpaceComplexity` import:** injectivity is stated componentwise rather than through
`ConfigCount.core`, and ConfigGraph converts. **When:** after the G1 merge, since `fieldsTape`
uses generic `bufferTape`. The window predicate lands with the 12.8.2 relocation (after C1d).
The probe's Part F has the exact text.

```lean
inductive RecSym (Q T : Type) where
  | digit (b : Bool)                          -- the `e` of the lift: input, position field, counters
  | cell (content : Option Bool) (mark : Bool)-- one simulated work cell: content track + head-mark track
  | st (q : Option Q)                         -- the state cell
  | tag (τ : T)                               -- the tag cell (emission summary)
deriving DecidableEq
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) := derive_fintype% _
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit       -- little-endian, fixed width
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length                      -- 2 ^ posWidth n > n + 1
def cfgRecord {k Q T} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) : List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::                                                     -- F0
  ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::       -- F1, binary over digits
  (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>     -- F2 … F(k+1)
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
  [[RecSym.tag τ]])                                                          -- F(k+2)
def joinFields (fs : List (List Γ)) : List (Option Γ) := List.intercalate [none] (fs.map (List.map some))
def fieldsTape (fs : List (List Γ)) (z : ℤ) : Option Γ := if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none
def fieldOffset (fs : List (List Γ)) (j : ℕ) : ℕ := ((fs.take j).map (·.length + 1)).sum
theorem fieldsTape_field (fs) (j) (hj : j < fs.length) : ∀ p, -1 ≤ p → p ≤ |fs[j]| →
    fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p   -- each field is a framed word
theorem cfgRecord_inj (s) (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ'
theorem cfgRecord_length : (cfgRecord s c τ).length = k + 3   -- proved in the probe
def RecordValid (k n s : ℕ) (Q T) (fs) : Prop :=
  ∃ x (c : Cfg k Bool Q x) τ, x.length = n ∧ c.InWindow s ∧ cfgRecord s c τ = fs
theorem recordValid_iff (n s fs) : RecordValid k n s Q T fs ↔ fs.length = k + 3 ∧ (∃ q, fs[0] = [.st q]) ∧
    (fs[1] is posWidth n digits of value ≤ n + 1) ∧ (each tape field: 2s+1 `.cell`s, exactly one mark) ∧
    (∃ τ, fs[k+2] = [.tag τ])            -- the scan-checkable form, for `recordValidTM`
def RecordAt (d : Cfg K Γ S x) (r : Fin K) (fs) : Prop :=
  ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p
```

- **Layout discipline.** One blank between fields and between records; no field is empty (F0
  and the tag have one cell, F1 has `posWidth n ≥ 1` cells, each tape field `2s+1` cells). So
  two consecutive blanks mark the end of a table, and every field is a §12.6-delimited word.
  This is the G3 separator discipline, so the generic framed rows apply field by field with no
  save/restore.
- **Space.** A record has `k(2s+1) + posWidth n + 2` cells plus `k + 2` separators, which is
  `O(k·s + log n + 1)`. That is `O(S n)` at `s = c₀·S n` with `S ≥ logSpace`. With
  `alphabet_reduction_spaceUsed`'s `c·(space+1)`, Savitch stays in `SPACE(S²)`.
- **Window predicate.** The probe uses `WindowedP`, a verbatim copy of TQBF's
  `Turing.Cfg.InWindow`. The real file uses `Cfg.InWindow`, relocated here (12.8.2). It **must
  land in the same change** that deletes TQBF's copy: once ConfigGraph imports `CfgRecord` (at
  S1b), TQBF, which is downstream, would otherwise see two definitions.

#### 3. The rows, restated for the rich design

Template (from the §12.8 note), with one change of form:

- **Machines that are single sweeps are defined** and get the §12.6 framed contract: exact
  time, finish configuration, no earlier exit, trajectory.
- **Composite modules are existential**, in the `exists_installCallTM` style
  (`∃ R entry exit C, …`): a first-return time `t ≤ C·(size)`, no earlier exit, an exact finish
  configuration, and the scratch tapes and heads restored.

The constants are indicative; the statement phase fixes them by execution. Tags: **[now]**
can land on the campaign branch before G1 merges. **[G1-merge]** touches no G1 file but uses
G1's generic statements. **[Catalog/G1]** goes in a G1-owned file, after the G1 gate. **[G2]**
is proposed as a G2 statement. **[rec]** is a record row, filled after G2 and the
Catalog/G1 rows.

| Row | Tag | Statement (probe part) | Contract |
|---|---|---|---|
| **R8.0** transport | **[now]** | `MultiTapeTM.liftSymbols_runFrom` and the rest of §1 (A) | proved |
| R8.0 corollaries | [G1-merge] | `FinTM.bufferTape_map`; the R1 composition (B) | proved |
| **R8.0b** `counterLoopTMVia` | [Catalog/G1]+§12.7 gate (CounterLoop) | `counterLoopTMVia_run_done/_escape` (E) | exact, as §12.7 |
| **R8.1** framed compare | [Catalog/G1] | `compareTM_run_ofCfg {Symbol} [DecidableEq Symbol]` (D) | `∃ δ ≤ min |u| |v|`, exact time `2δ+2`, finish `{d with state := done (decide (u = v))}`, no earlier verdict, trajectory `[pos−1, pos+δ]`. Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace` |
| **R8.2** `scanTM δf δb a₀` (two-pass transducer) | **[G2]** | `scanTM_run_ofCfg` (D) | exact `2|w|+2`; interval rewritten to `(scanResult δf δb a₀ w).2`, verdict `done (scanResult …).1`; trajectory `[pos−1, pos+|w|]` |
| **R8.3** `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` | [Catalog/G1] | `skipTM_run_ofCfg` (D); landed with `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | skip: exact `|w|+1`, head to `pos+|w|+1`. Landed: skip back is skip's inverse, exact `|u|+3` from the next field's first cell to `u`'s; seek end exact `D+1` to `pos+D`, `D = fieldOffset ws |ws|`, `ws ≠ []`; seek start exact `D+4` back to the table start. Nothing written; the seeks stop at two consecutive blanks (table ends) |
| **R8.4** `writeConstTM i w₀` | [G1-merge] (Scan) | `writeConstTM_run_ofCfg` (C) | exact `2|w₀|+2` (executed), old contents arbitrary, head returns |
| R8.4′ `writeAdvTM i w₀` | [G1-merge] (Scan) | landed: `writeAdvTM_run_ofCfg` | writes `w₀` and leaves the head at `pos + |w₀|`, exact `|w₀| + 1`; the advancing round of `expandTM`. Landed cyclic, over `Fin (|w₀|+1)`: it returns to its start state `0`, the counter-loop round shape |
| **R8.5a** `inputCopyTM i` | [G1-merge] (Scan) | `inputCopyTM_run_ofCfg` (C) | from input position 1, exact `2|x|+2` (executed); both heads return in lockstep (no left delimiter needed) |
| **R8.5b** `exists_inputSeekTM` (`Bool`) | **[now]** | (C) | `∃ R … C`; moves the input head to the binary value on a dedicated tape, `t ≤ C·(|w| + pos + p + 1)`; tapes restored |
| **R8.5c** `exists_inputLengthTM` (`Bool`) | statement now; fill after R8.3 (it needs `skipTM` for the width extension) | — | writes `Nat.bits |x|` on a dedicated tape: per input symbol, `incrementTM` with width extension on overflow (`seekEnd` + `writeConst`), `t ≤ C·(|x|+1)` amortized (§12.7 potential) |
| **R8.5d** `inputFoldTM δ a₀` | [G1-merge] (Scan) | — | native scan of the input with a finite fold, verdict `done (x.foldl δ a₀)`, exact `2|x|+2`; the foreign-symbol validator of §0 |
| **R8.5e** `exists_inputCallTM` | [G1-merge] (`Build/InputCall.lean`; needs R8.5a) | — | `inputCopyTM` (at `Bool`, or lifted) + `exists_installCallTM`: a function-level machine on the native input at a clean seam |
| **R8.6** `exists_expandTM pat` (`Bool`); landed as the definition `expandTM` | [G1-merge] (CounterLoop; needs R8.4′) | landed: `expandTM_run_ofCfg` | `counterLoopTM` round = `writeAdvTM pat`; writes `pat` `d` times contiguously; exact `d(|pat|+1) + counterOverhead w (d+1)` |
| **R8.7** record rows | **[rec]** | `exists_recordStepTM`, `exists_recordEqTM` (G); landed with `exists_recordTestTM`; the rest below | first-return form; landed with `yes ≠ no` in each existential |
| **R8.8** `seamCompTM_runFrom_left` (promotion) + `seamCompTM₂_run_ofCfg` | [Catalog/G1] (Seam) | §12.8 note | statement unchanged from the private `seamComp_left` |

**R8.2 replaces fold, map, mark shift and odometer: one row, one trace.** It is proposed **as a
G2 statement**. Its instances:

- **fold:** `δf a γ := (δ a γ, γ)`, `δb` the identity;
- **in-place map** `f`: `δf a γ := (a, f γ)`;
- **head-mark shift right:** `δf prev γ := (mark γ, setMark γ prev)`, the forward delay (the probe
  checks a concrete shift);
- **shift left:** the same delay on the backward pass;
- **record odometer:** a carry transducer;
- **validity checks:** folds.

G2's planned two-tape `copyMapTM`/`transferMapTM` (§13d) are not needed by §12.8: records move
by plain generic `copyTM`. If G2 keeps them, one request: let `merge` take `Option Γ`, so that
blank destinations (scratch) are admitted. **Decision 12.8.5 is honored:** fold, and with it map,
is a Catalog row sharing the R3/G2 trace (`catalog_trace_run`), since G2 lives in Catalog.

**R8.7, the record rows.**

- All are existential modules over `RecSym Q T`.
- **Entry conditions:** the record at tape `0` (`RecordAt`), the scratch tapes `j ≠ 0` blank,
  and the native input `x.map RecSym.digitEmb`.
- **Exit conditions:** heads, input position, scratch and output restored.
- They are built from R8.0/R8.0b, R8.1–R8.5 and R2 seams, with **no private re-trace**.

| Module | Verdict / effect | Composition |
|---|---|---|
| `exists_recordStepTM M upd (hupd : ∀ τ, upd τ none = τ)` (GAP-4, exact text in G) | `yes` and record of `M.step c` with tag `upd τ (M.outputSymbol c)` if `(M.step c).InWindow s`; else `no`, nothing changed; `t ≤ C·(L + |x| + 1)` | read: `scanTM` folds on F0, the tag and the tape fields (scanned symbols and edge flags) via `skipTM`; copy F1 to a dedicated digit tape (`copyTM`), run the lifted `inputSeekTM`, read the input symbol, restore; finite dispatch on `M.tr`; apply: `scanTM` maps (content at the mark, F0, tag) and delay shifts (marks), F1 `±1` by the lifted increment/decrement on the dedicated tape with copy back, clamp from the edge data |
| `exists_recordEqTM` (G) | `yes` iff the two field lists are equal | `k+3` framed compares (R8.1) with `skipTM`s |
| `exists_recordTestTM P` | `P (state, tag)` | two `scanTM` folds |
| `exists_recordValidTM` | `RecordValid` via `recordValid_iff` | `scanTM` folds per field |
| `exists_recordInitTM` | writes `cfgRecord s (initCfg x) τ₀` from `bits (S n)`-style radius digits | `exists_inputLengthTM` (lifted), `exists_expandTM` (lifted) for the window halves, `scanTM` maps, `writeConstTM` |
| `exists_recordNextTM` | next valid record in odometer order, or overflow | `scanTM` carry over all fields + `exists_recordValidTM` filter, under `counterLoopTMVia` |
| `exists_tableAppendTM`, `exists_tableFindTM P` | append at `seekEndTM`; first record satisfying a fold, with an escape if none | `copyTM`, `seekEndTM`, `scanTM`, `counterLoopTMVia` |

#### 4. S1b's machine plan, recomposed (rich)

**Parameters.** `Γ := RecSym N.State (Fin 3)`, with the tag being the output summary through
its `Fin 3` code (O4), and `e := RecSym.digitEmb`. The host is a `FinTM Γ`.

**Tapes:**

- `Tab`, the table;
- `Cur₀` and `Cur₁`, the successor workspaces;
- scratch for the record modules;
- dedicated digit tapes: `Rad` (radius), `Len`, `Cnt` (the outer counter, last tape) and
  `Cnt'` (inner loops);
- the lifted constructor's bank and capture tape.

1. **Validate** with `inputFoldTM`. On a foreign symbol, emit `e false` and halt. This is needed
   only for space, but it is cheap.
2. **Radius.** Run `M_S.liftSymbols e` under generic `embedSilentRetTM` with its output
   captured on `Rad`, then rewind. Time at most `M_S.configBound n (a·S n)`
   (`of_spaceUsed_le` plus `liftSymbols_runFrom`).
3. **Window template.**
   - Lifted `exists_expandTM` with counter `bits (S n)` and pattern `false^{c₀}` writes the left
     half.
   - `writeConstTM [.cell none true]` writes the center.
   - `expandTM` again writes the right half.
   - A `scanTM` map turns the digits into `.cell none false`.

   No multiplication by `c₀` is needed: the pattern length carries it.
4. **Initial record.** `exists_recordInitTM` writes it, plus a one-digit flag field `[digit
   false]` ("unprocessed").
5. **Outer counter.** Copy the template fields `c_N` times onto `Cnt` (`copyTM` + `skipTM`),
   then map every cell to `digit true` (`scanTM`). Its value `2^{c_N·W} − 1` exceeds the record
   count `V` with `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`. Here `W` is the record's cell count, and the
   proof uses `2^{posWidth n} ≥ n+2` and `8^{2s+1} ≥ 3^{2s+1}(2s+1)`.
6. **BFS** with `counterLoopTMVia e Round a (some ex)`. A round:
   - `exists_tableFindTM` finds the first record with flag `false` (escaping to `ex` if none),
     and copies it to `Cur₀` and `Cur₁`;
   - `exists_recordStepTM (N.fixChoice false)` runs on `Cur₀`, and
     `exists_recordStepTM (N.fixChoice true)` on `Cur₁`. The upd is the summary's append table
     on the code;
   - for each `yes`, an inner `counterLoopTMVia` over the table with `exists_recordEqTM`
     decides membership, and `exists_tableAppendTM` appends a new record with flag `false`;
   - the processed record's flag is set (`scanTM` map), the workspaces are cleared
     (`clearTM`), and the table head is rewound (`seekStartTM`).

   Both exits are wired by R8.8.
7. **Verdict.** `exists_tableFindTM (accept)` scans for a record with state `none` and tag
   `accept`. Emit `e true` or `e false`, then halt.
8. **Finish.** `alphabet_reduction` gives a `FinTM Bool` within `c·(T + 1)`.
9. **Correctness** is §12.8's chain, with `cfgRecord_inj` in place of the bit codec:
   - `T := Fin 3` identifies records with `coreSum`s;
   - note-6's bridge applies, the outside-window rejection being `recordStepTM`'s `no`;
   - S1a's four lemmas finish.
10. **Time.**
    - `counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
      nested table loop.
    - Add the startup terms: the constructor bound, `O(S n)`-cost expansions, and
      `O(n log n)` input length.
    - Then `alphabet_reduction`'s `c(T+1)`. The result is at most `K·2^{c'(S n+1)}`.
    - Every budget is evaluated at `n`; no monotonicity of `S` is used.

#### 5. Sequencing — what can be issued before the G1 gate closes

| Item | Lands | Blocked on |
|---|---|---|
| **R8.0 transport** (`SymbolLift.lean`) | **now**. The probe's Part A *is* the proof; a maintainer pre-issue landing or a tiny batch | nothing |
| **R8.5b** `exists_inputSeekTM` (`Bool`; composed of `copyTM`, `timed_rewind`, `counterLoopTM`, `clearTM`, all public at HEAD) | **now**, as a statement phase plus a fill batch | nothing; it lifts to rich hosts by R8.0 |
| R8.5c, R8.5e, R8.6 (`Bool` rows needing Scan or seek) | statements now; fills after the G1 merge (R8.5e, R8.6) or after R8.3 (R8.5c) | G1 merge / R8.3 |
| Statements of **everything else** | **draft now** (this document, probe green on `s13d/g1`) | — |
| R8.0 corollaries, R8.4, R8.5a/d, the `CfgRecord` pure layer | after **G1 merges** (no G1 file edited) | G1 gate; CfgRecord's `InWindow` also on C1d |
| R8.1, R8.3, R8.8 | after the **G1 gate**, in Catalog/Seam | G1 gate; coordinate with G2/G4 (one trace) |
| R8.2 `scanTM` | with **G2** | G1 gate; G2's statement phase adopts it |
| **R8.0b** `counterLoopTMVia` | after the **G1 gate and the §12.7 fill gate** | both gates |
| R8.7 record rows | after the R8.2 fill (G2) and the R8.1/R8.3 fills | G2 fill |
| S1b | after R8.7 | — |

**The sequencing change versus the note:** R8.0b is new, and it sits on two gates (G1, §12.7).
It is the long pole for every rich consumer, since no rich loop exists without it. Some things
can be issued before the G1 gate closes:

- R8.0, which the probe proves;
- R8.5b;
- the statement phase of every other row (the probe is green on `s13d/g1`).

The critical path is then the G1 gate, then R8.0b with R8.2 (G2) and R8.1/R8.3, then R8.7,
then S1b. Two items that the note called "landable now" in fact need the G1 merge, because
their statements use the generic `bufferTape`: `writeConstTM` and the input rows. `expandTM`
needs the advancing writer R8.4′.

#### 6. Per-consumer rows (updated)

| Consumer | Rows |
|---|---|
| **S1b** | §4: R8.0, R8.0b, R8.1–R8.5, R8.6, R8.7 (step, eq, test, init, table rows), R8.8, `alphabet_reduction` |
| **Savitch** | Rich records with binary F1 (`O(S)` cells); frame stack on a rich tape; R8.7 `recordStepTM` (both choice bits) + `recordEqTM` for adjacency; `recordNextTM` + `recordValidTM` for midpoints; R8.3 over frames; `copyTM`/`clearTM` at fixed intervals (note 7); R8.0b loops; R8.8; R8.5d validation; `alphabet_reduction_spaceUsed` |
| `spaceConstructible_*` | `Bool` only: R8.5c, R8.6, `incrementTM` |
| `PATH_NLComplete` (hardness) | ARM engine (12.8.4); no §12.8 row |
| `PATH_mem_NL` | R8.5b, once the nondeterministic host exists (SC-3) |
| Space hierarchy | `Bool` counters lifted by R8.0 on a rich simulator, or unlifted on a `Bool` one; R8.0b (budget loop), R8.8 (success/cap), R8.1 (budget comparison), `clearTM` resets, R8.5d. It simulates a coded machine, so it does not use R8.7 |
| `TQBF_mem_PSPACE` | R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3 |
| `NP_subset_PSPACE` | `incrementTM`, `vhostEmitTM`, R8.8 |
| **G3/G4 (§13d)** | R8.3 (zone scanning across separators), R8.2 (per-track maps), R8.0 (Bool counters on `ZoneSym` tapes via `e := Sum.inl`) |

#### 7. Open decisions

- **O1, transport home.** New `TuringMachine/SymbolLift.lean` (recommended), or CounterLoop's
  `SymbolTransport` section (during its open gate).
- **O2, R8.0b route.** In-place proof generalization with the `Bool` contracts re-derived by Z5
  (recommended; one round induction). The alternative is a second host with its own induction,
  which is a duplicated trace.
- **O3, `scanTM` as a G2 statement.** It needs G2's agreement. Separately, the optional
  `merge : Option Γ → Δ → Γ` request for `copyMapTM`.
- **O4, the S1b tag type.** `Fin 3` code (recommended; no frozen-surface change), or a sanctioned
  `Fintype OutSummary` export in ConfigGraph.
- **O5, table seeks.** `seekEndTM` and `seekStartTM` (double-blank stops) in the skip family, or
  as `counterLoopTMVia` loops over `skipTM` (slower, no new row).
- **O6, input validation (R8.5d).** Mandatory for rich space-bounded consumers. Confirm, or
  require every rich row's space bound to be input-independent instead (harder to state).
- **O7, R8.0 now.** Whether the transport lands as a maintainer pre-issue lemma, since the
  probe proof is complete (one file, about 120 lines), or through a statement gate plus fill
  like the other §12 rows.

#### 8. Decisions and the landed statement layer (2026-10-11)

**Decisions.**

- **User:** O2, generalize `counterLoopTM` in place, with the `Bool` contracts
  re-derived by Z5 (R8.0b, a later batch; target signatures below); O3, G2 is
  `scanTM`; O7, the transport lands by PR plus the §12.8 statement gate.
- **Maintainer:** O1, `TuringMachine/SymbolLift.lean` (landed, PR #16); O4, the
  `Fin 3` tag code; O5, dedicated `seekEndTM`/`seekStartTM` rows; O6, input
  validation (R8.5d) is mandatory for rich space-bounded consumers.

**Landed** on `integrate/s12-8-statements` (campaign `5e438f50` with PR #16,
merged at `b28e22ea`). Every machine and carrier is a real definition. Every
contract is sorried with a proof sketch, except the two results already
proved, which keep their proofs: `seamCompTM_runFrom_left`, promoted verbatim,
and `cfgRecord_length`. There are 25 new sorries. Records:
`audits/logs/s12-8-statements-*` and
`audits/evidence/s12-8/S128StatementsPreship.lean.txt`.

| Row | File | Landed declarations | Contract |
|---|---|---|---|
| one-tape actions | `Build/Catalog.lean`, Part 3 | `tapeAction`, `inputMoveAction` | the transition-table vocabulary of every §12.8 machine |
| field layout | Catalog, Part 3 | `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field` | each field is a §12.6 delimited word in place |
| R8.1 | Catalog, Part 3 | `compareTM_run_ofCfg` | as drafted |
| R8.3 | Catalog, Part 3 | `SeekPhase`; `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg` | as in the §3 row, with trajectories |
| R8.2, the G2 core | Catalog, Part 3 | `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`, `scanResult_carry` | the scan contract as drafted. The instances are pure identities of `scanResult`, so the scan keeps one framed contract |
| R8.4, R8.4′, R8.5a, R8.5d | new `Build/Scan.lean` | `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | constant writer `2|w₀|+2`; advancing writer `|w₀|+1`, cyclic; input copy and input fold `2|x|+2` from input position `1` |
| R8.5e, R8.5b | new `Build/InputCall.lean` | `FinTM.exists_inputCallTM`, `exists_inputSeekTM` | first-return modules |
| R8.6 | `Build/CounterLoop.lean` | `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | exact `d(|pat|+1) + counterOverhead w (d+1)`, with `d` copies of `pat` from `pos` |
| R8.7 | new `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated verbatim from `ClassPSPACE/TQBF.lean`, which now imports it); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | first-return modules with distinct verdict anchors |
| R8.8 | `Build/Seam.lean` | `seamCompTM_runFrom_left` (promoted), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | one continuation per exit, each run unboundedly after the dispatch step |

**Changes from the draft.** Each was executed in the pre-ship probe where
executable.

1. **`yes ≠ no`** is part of every record row's existential. Without it, a
   module with `yes = no` satisfies `exists_recordEqTM` vacuously, and no
   consumer could branch on the verdict.
2. **The field layout lives in Catalog**, not in CfgRecord, because the seek
   rows' contracts are stated over it. CfgRecord imports Catalog and
   `SymbolLift`, not CounterLoop, since R8.0b is not in this step. TQBF's
   import closure gains Catalog, `SymbolLift` and CfgRecord; there is no
   cycle.
3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
   `0`, so it is a counter-loop round as it stands. A seam caller that runs it
   once uses `seamReleaseTM`.
4. **R8.6 is the concrete `expandTM`** with an exact contract, not an
   existential.
5. **The seek family.** Skip back is the inverse of skip (`|u|+3`, from the
   next field's first cell), not its mirror. The seeks' exact times are `D+1`
   and `D+4`, with `D = fieldOffset ws |ws|`. Every row carries the §12.6
   trajectory clause.
6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
   input fold reuses `ScanPhase`.
7. **The scan instances** are stated as identities of `scanResult` rather than
   as five machine contracts. `scanTM_run_ofCfg` turns each into the
   instance's run.
8. **`Cfg.InWindow`** replaces the probe's `WindowedP`.
9. **One-tape actions.** The §12.8 machines' tables are written with two
   named actions, `tapeAction` and `inputMoveAction`, instead of literal
   `Action` tuples. With literal tuples, the copy-text screen found 17 new
   cross-file pairs: the input copier and the input fold against the R3
   sweeps and the scan. With the helpers there are none. Twelve new same-file
   pairs remain: the four seek tables among themselves, and the two writers.
   These are distinct small machines sharing their phases, not copied
   proofs. The proved R3 tables are unchanged.
10. **Not landed**, being outside this step:
    - `FinTM.bufferTape_map` and the other R8.0 corollaries;
    - R8.5c, `exists_inputLengthTM`;
    - R8.0b;
    - the record rows `exists_recordValidTM`, `exists_recordInitTM`,
      `exists_recordNextTM`, `exists_tableAppendTM` and
      `exists_tableFindTM`. Their statements need S1b's table layout (a
      header, the radius digits, the odometer order) and a template tape
      holding the widths a validity machine compares against.
11. **`MultiTapeTM.liftSymbols_step` is public** in the landed
    `SymbolLift.lean` (PR #16), as the transport's one-step form; §1 above
    made it private. Only `moveInputPos_cast` is private.

**R8.0b target signatures.** These land in a later batch, after this
statement gate. Home `Build/CounterLoop.lean`, which then imports
`SymbolLift`.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) := ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
  -- .dec f  : ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
  --             (counterLoopDecExit a)
  -- .done, .escape : stationary
-- generalized in place (types only, bodies verbatim; existing call sites unchanged):
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol} (q : Option (CounterLoopState S))
    (c : Cfg k Symbol S x) (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol} … -- otherwise verbatim
-- the generic contracts are counterLoopTM_run_done / counterLoopTM_run_escape verbatim, with
--   M, τ, c over Γ; ct : ℤ → Option Γ; counterLoopTM M a exit ↦ counterLoopTMVia e M a exit;
--   hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p,
--     for the counter word w : List Bool;
--   done finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q;
--   escape finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
--     then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q;
--   all four clauses kept (finish, no earlier exit, counter head range, body heads).
theorem counterLoopTMVia_run_done …
theorem counterLoopTMVia_run_escape …
-- counterLoopTM and its two contracts: statements byte-identical; proofs re-derived at
-- e := Function.Embedding.refl Bool through MultiTapeTM.runFrom_eq_of_agreeOn (Z5), the
-- decrement tables agreeing pointwise (decodeBool refl γ = some γ, Option.map refl = id).
```

**Governance.** Catalog and Seam are G1-owned files, and `scanTM` is the G2
core of the §13d revision. Under the §13d rule this branch therefore lands by a
PR the user merges, with its own statement gate. Nothing is pushed by the
agent.

**Open questions for the statement gate.**

1. **Skip back.** Is the inverse convention right (from the next field's
   start, `|u|+3`), or should it be the mirror of skip (from a word's last
   cell, `|u|+1`)?
2. **The empty table.** `seekEndTM` requires `ws ≠ []`, since an empty table's
   end is its start. Should tables carry a header field, so that every seek
   precondition is uniform?
3. **The cyclic writer.** Is `writeAdvTM`'s anchor-equals-start shape
   acceptable, or should it have a stationary `done` with the loop adapting
   it?
4. **Tape layouts of the record rows.** `exists_recordStepTM` has
   `K + 1` existential tapes with the record on tape `0`; `exists_recordEqTM`
   has 2 tapes; `exists_recordTestTM` has 1. Hosts embed them by R1. Is the
   fixed layout acceptable, or should each row take a tape selection? The
   step row's fill will also import InputCall, for the input seek, which
   enlarges TQBF's import closure again.
5. **The deferred record rows.** Should validity, init, next and the table
   rows enter this gate, or S1b's statement phase, once the table layout is
   fixed?
6. **The facade.** Scan, InputCall and CfgRecord are not wired into the
   `TuringMachine` facade, following the precedent of `SymbolLift`,
   CounterLoop and Zone. Is facade wiring wanted at this gate?
7. **G2's agreement** to `scanTM` as its core, and whether the planned
   `copyMapTM`/`transferMapTM` are still wanted. §12.8 does not need them.

#### 9. Statement gate, round 1: decisions and repairs (2026-10-11)

Round 1 failed with 0 blockers, 1 major, 7 minors and 39 notes
(`audits/s12-8-statements-findings.md`).

**Decisions** (user, the auditor's recommendations, on the open questions
of §8):

1. Skip back stays the **inverse** of skip, at `|u| + 3`.
2. Shared tables get a **fixed nonempty header field**, so seek end always
   has a field to stop after. The table ends are two blank cells before the
   header and two after the last field. From seek end's stopping blank, a
   consumer reaches the table start by skipping back over the last field
   and then seeking start. The deferred table rows are stated with this
   layout.
3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.
4. The record rows keep their **fixed local tape layouts**, and hosts embed
   them by R1.
5. The deferred record rows (validity, init, next, table append and find)
   get **their own statement gate** with S1b's concrete layout, before
   S1b's fill uses them. R8.0b and R8.5c are explicit prerequisites.
6. The new modules are **wired into the `TuringMachine` facade** at this
   gate: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall`
   and `Build/CfgRecord`. Nine older files of the topic are also absent
   from the facade; they are recorded as `backlog.md` FAC-1.
7. G2's core is `scanTM`, and `copyMapTM`/`transferMapTM` stay for G3/G4
   (§13d, G2).

**Repairs** (for round 2):

- **Major 1: work-space clauses.** The record rows and the input seek
  bounded time but not the cells they visit, so they were too weak for
  Savitch and logspace consumers. Each now bounds every work head, through
  its verdict or exit, to `C·(size + 1)` cells of its entry position. The
  size is the record's layout length for the step and test rows, `fs`'s
  layout length for the equality row, and `|w|` for the seek. So the space
  does not depend on how far the native input head travels, and repeated
  calls compose. The step row's sketch now names the obligations the auditor
  identified: save and restore the host's input position in binary, and
  clamp the position field at `0` and `|x| + 1`.
- **Minor 2.** The input seek's rewind: `timed_rewind` stops at position
  `1` within `pos + 2` steps, and one left move follows.
- **Minor 3.** The input call's first-return clause splits on whether the
  callee's entry equals its exit. If it does, `seamReleaseTM` supplies a
  fresh entry first.
- **Minors 4, 5 and 6.** `recordValid_iff`'s validator needs width
  templates. A record determines the configuration *core* together with the
  tag. `fieldOffset`'s end formula needs `fs ≠ []`.
- **Minors 7 and 8.** Corrected in the records: the declfreeze log
  miscounted the promotion's citations (3, not 4), and Catalog's ledger
  denominator is now 459.

### 12.9 Oracle-machine rows (landed 2026-10-11 with epoch B1; `Build/OracleCall.lean`)

**Why.** Every §12 row is plain-machine level, and the oracle model (`TuringMachine/Oracle.lean`)
had no run algebra. The B1 one-query constructions needed three capabilities: (i) a computation
captured onto the **query tape** and submitted; (ii) the four-state **answer tail**; (iii) a way for
plain contracts to drive an oracle machine.

**Rows.**

- In `Oracle.lean`:
  - the run algebra: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`,
    `runFrom_comm_of_step`, `ComputesInTime.mono`/`output_unique`;
  - the extraction contract: `queryString_length_le_of_blank` (C1-P1) and `queryString_eq_of_cells`;
  - **the transfer bridge** `runFrom_eq_plainEmptyOracle`, after `runFrom_eq_of_forall_ne_qQuery`.
    On a run segment that avoids `qQuery`, the oracle run is the run of the plain table
    `plainEmptyOracle`, so host-parametric plain contracts apply unchanged.
- In `OracleFinite.lean`: the bundled `mono` and `output_unique`.
- In `Build/OracleCall.lean`:
  - `queryString_bufferTape`;
  - `answerAction`, with `step_of_qQuery`, `step_of_answerAction` and `runFrom_two_of_qQuery`;
  - **query capture** `capture_reaches_qQuery`: W1 with its return state taken to be `qQuery`.
    W1 writes on the host's last tape, which is the query tape.
- In `Finite.lean`, the shared guard discharge: `MultiTapeTM.exists_first_halt`.

**Consumers.**

- `mem_POracle_of_polyTimeReducible`, and through it the `SAT`-oracle corollaries and
  `EXP_subset_POracle_EXPCOM` (B5);
- `unaryWitnessLang_mem_NPOracle`, using the tail through `OracleNDTM.fixChoice`;
- `compl_mem_POracle`, using `runFrom_comm_of_step`.

**Not yet here: oracle-call hosting.** This is a plain host simulating an oracle machine that runs
a decider on the extracted query word. It is the library gap behind `POracle_eq_P_of_mem_P`
(deferred) and B5's `NPOracle_EXPCOM_subset_EXP` dispatcher. Its rows need a design note and a
statement gate:

- the headline simulation;
- the private clean call of `ClassNP/EXP.lean` promoted, without the native-input rewind;
- origin tracking for the query tape;
- query extraction with cell `-1` saved;
- the dispatch host.

The draft headline statement, `FinOracleTM.exists_plain_simulation`, is recorded in
`audits/b1-integration.md`.

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.


### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `audits/vhost-infra-findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`audits/vhost-infra-resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `audits/zone-infra-findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).

### 13d. Revision: the zone layer at the book's design (draft, 2026-10-10)

**Status: design draft for user review. No Lean change has been made.**

**Process rule (user, 2026-10-10, binding for this revision).** Every Lean change
that results from this revision goes through **both** human approval, as a PR
the user merges, **and** a separate audit gate. Nothing is pushed directly to
the campaign branch. This covers the library generalization (G1), every new
statement phase, and every fill.

#### Why

ZF-A3 (`zone-f1-A3.zip`, held and not integrated) proved infrastructure only:
a geometric counter schedule, counter-driven navigation, a counter built from
the unary level, a window readout, and counter removal, 952 lines in all.
Neither shift machine was proved. A comparison with [AB09] §1.7 traces the
cost to four of our choices, not to the mathematics:

1. **A supplied level with pairwise shifts.** Each pairwise shift starts from
   home, so the machine must count its way to level `i`. In [AB09] the index
   `i₀` is *discovered* by scanning outward, and one sweep does all the work
   between adjacent zones where the head already is.
2. **No markers.** A binary physical tape carries no zone boundaries, which
   forces the binary counter.
3. **Catalog reuse on packed zones.** The generic routines need a blank on
   each side of a word, but packed zones abut, hence the save, blank, call,
   restore cycle around every call.
4. **Exactly two tapes per row,** so the counter shares the scratch tape with
   the level word.

There is also a **gap independent of the controller**. Plan §2.1 specifies
the book's route ("parallel tracks, buffer zones of size `2^i`, amortized
shifts"), but `ZoneContents` holds **one** simulated tape, and both rows
operate on a tape dedicated to it. In a two-tape simulator only one tape can
be zoned, so the present carrier serves only machines with one work tape,
and Hennie–Stearns needs each of `k` tracks to shift independently.

#### Decisions taken (user, 2026-10-10)

- **A rich alphabet, finished by alphabet reduction.** The Hennie–Stearns
  simulator is a two-tape `FinTM Γ` over a large alphabet `Γ`, as in [AB09]
  via Claim 1.5, and the public `Turing.FinTM.alphabet_reduction`
  (`Robustness/AlphabetReduction.lean`) finishes it. That theorem preserves
  the work-tape count (`M'.k = M.k`), costs `3(|Γ|+1) + 2` steps per source
  step, and is stated at the function level (`ComputesFunInTimeVia e f T`
  gives `ComputesFunInTime f (c·(T+1))`). A space form exists
  (`alphabet_reduction_spaceUsed`).
- **Option (b): generalize the library to arbitrary alphabets** rather than
  building a parallel `Γ`-only toolkit. Large-alphabet machines will recur.

#### Components

**G1. Alphabet-generic library (in place).** Change `Bool` to an arbitrary
`{Symbol : Type*}`, with `DecidableEq` where needed, in:

- **`Build/Seam.lean`:** `seamCompTM`, `seamReleaseTM`, and their
  general-configuration theorems (the `_ofCfg` trio and the release pair).
  The canonical `Cfg.ofWords` theorems stay Bool-specific and become
  instances of the general ones.
- **`Build/Embed.lean`:** the transformers, transports and all their
  theorems, including the RB5 state-transport lemma. The capture tape's
  buffer generalizes with `bufferTape`.
- **`FinTM.bufferTape`** (`Simulation.lean`): from `List Bool` to
  `List Symbol`. The definition is unchanged.
- **The R3 sweep rows in `Build/Catalog.lean`:** `transferTM`, `copyTM`,
  `clearTM`, `compareTM`, and their §12.6 framed contracts. Their tables
  never inspect a symbol's value except for equality, so they generalize.
  `incrementTM`, the canonical rows and the Part 2 space rows stay
  Bool-specific.

**Binding constraint:** every existing Bool statement either keeps its
statement verbatim or becomes a definitional instance at `Symbol := Bool`
that its consumers elaborate unchanged. The full downstream replay is the
evidence. This is a change of audited public signatures, so it gets **its
own gate**, before anything consumes it.

**G2. Mapped sweeps (new, alphabet-generic catalog rows).** Per-track
shifting moves one *component* of each cell and leaves the other tracks in
place, which whole-symbol copying cannot do. The rows are `copyMapTM` and
`transferMapTM`, parameterized by `extract : Γ → Δ` and
`merge : Γ → Δ → Γ`: they write `merge (dst cell) (extract src cell)`. Their
framed contracts follow the §12.6 shape (exact time `2|w| + 2`, finish
configuration, no earlier exit, trajectory). At `merge := fun _ s => s` they
are the plain rows. This is the reusable large-alphabet primitive. Its proofs
must share the generalized R3 trace, not copy it (one trace per routine
family, as §12.6 established). **Decision (user, 2026-10-11; the §12.8
statement gate's Q7).** G2's one-tape core is `scanTM` (§12.8a).
`copyMapTM`/`transferMapTM` stay, for the cross-tape G3/G4 consumers. Their
`merge` takes `Option Γ → Δ → Γ`, so that blank destinations are admitted,
and they share one trace with the scan.

**G3. The multi-track zoned carrier over `Γ`.**

- **Alphabet:** `ZoneSym k := Bool ⊕ ZoneCell k`, where
  `ZoneCell k := Fin k → Option (Option Bool)`. Per track, `none` is the
  buffer symbol `⊠` (an unoccupied slot) and `some v` an occupied slot
  storing the virtual symbol `v`. `Sum.inl` embeds the binary input and
  output (the `e` of `ComputesFunInTimeVia`). It is finite, so it is a
  `Fintype`.
- **Contents:** `Fin k → ZoneContents ℓ`. **The pure layer is reused
  verbatim per track:** the codec is unneeded, but the layout arithmetic,
  `ZoneContents`, `zoneSlot`, `zoneSide`, the pairwise ops and their
  word-preservation lemmas, the head steps, and the cascade with its
  lemmas all carry over.
- **Layout:** one physical cell per virtual slot, holding the whole tuple,
  with the home at cell 0 and **one blank separator cell between consecutive
  zones** on each side (decision 13d.1). Each zone is then a blank-delimited
  nonblank word of length `zoneCapacity i`, so the generalized framed sweeps
  (G1, G2) apply directly, with **no save/restore**. The separators also mark
  zone boundaries, so **no counter** is needed.
- **The home cell** holds all `k` tracks' virtual symbols, so the simulator
  reads and writes the virtual heads in one step.

**G4. Rebalance rows.** For a direction `d` and a track `t` (`t` in finite
control, since `k` is fixed for a given simulated machine), one machine:

1. starts at home and **scans outward** across zones, using the separators,
   to find `i₀ := zoneShiftIndex d (z t)`, the least level whose zone on the
   feeding side is non-empty. This is a new pure definition;
2. realizes the pure cascade at `i₀` on track `t` in a single
   outward-then-inward sweep, with mapped sweeps between adjacent zones and
   the scratch tape as the buffer;
3. leaves every other track and the separators unchanged, and returns home.

Its contract has the same shape as the current rows: exact final tape, live
exit or halt as the consumer needs, time `O(2^{i₀})`, the head within the
level-`(i₀+1)` extent, and scratch space `O(2^{i₀})`.

- **The left-move mirror** `zoneCascadeLeft` is new. It is defined through a
  pure left/right swap of `ZoneContents`, with its lemmas derived by
  symmetry, never copied.
- **The extent:** the carrier lays out `ℓ` levels, and a separate
  **extension row** lays out level `ℓ` (separator plus a half-full fresh
  zone, as in [AB09]'s "first time we encounter it") in `O(2^ℓ)`
  (decision 13d.2).

**G5. The assembly (stage-1 consumer, sketched for fit, not part of this
layer).** One simulated step:

1. read the home tuple;
2. apply M's transition in finite control;
3. write the home tuple;
4. rebalance each track by its head's move: `k` calls of G4, plus extension
   when needed;
5. handle the input and output tapes directly.

The amortization `Σ_i T/2^{i-1} · 2^i = O(T log T)` is the consumer's
mathematics, as before. Then `alphabet_reduction` turns the two-tape
`ZoneSym k` machine into a two-tape binary machine. With the Z3 two-tape
codes and the two-tape universal machine, Thm 3.1 follows at `f log f`.

#### What stays and what goes

- **Kept unchanged:**
  - the pure zone layer in `Build/Zone.lean` (about 820 of its 1,191
    lines): layout arithmetic, carrier, represented word, pairwise ops, head
    steps, the cascade and its lemmas, and the cardinality export. Its
    statements are untouched;
  - the rest of §13: Z1, Z3, Z5;
  - §12.6 and §12.7.

  No other file imports `Zone.lean`.
- **Superseded, to be retired through the G3/G4 gate:**
  - the binary physical realization `zoneTape`, `zoneTape_empty`,
    `zoneTape_blank_outside` and `zoneTape_homeWrite`;
  - the paired-cell codec, unneeded with a rich alphabet;
  - ZF-A2's seven staging-window lemmas;
  - the two current row statements, `exists_zoneShiftInTM` and
    `exists_zoneShiftOutTM`, to be replaced by the G4 rows.
- **ZF-A3's checkpoint** is held, not integrated. Almost all of it (counter
  navigation, counter construction, the binary window readout) becomes
  unnecessary. Integrate nothing from it unless G4's design reuses a piece.

#### Sequencing (each Lean step a PR plus its own gate, per the rule above)

1. **G1:** the generalization as one batch, its statements verified as
   instances, with the full downstream replay; then a **G1 audit gate**.
2. **G2–G4 statements:** the mapped sweeps, the carrier, the rebalance and
   extension rows, the swap mirror and the index function, with an executed
   pre-ship check on concrete instances; then a **statement gate**.
3. **Fill batches** for G2 and G4, then a **fill gate**.
4. The stage-1 Hennie–Stearns assembly, which needs its own statement
   phase.

#### Open decisions (13d.x, for the user)

1. **Zone boundaries:** blank separator cells (proposed; they give the
   catalog delimiters and boundaries at once) or a boundary flag in `Γ`
   (needs predicate-stopping sweeps instead).
2. **The extent:** a laid-out `ℓ` plus an extension row (proposed), or
   rows that extend lazily themselves.
3. **Rebalance totality:** realize the total pure cascade at the scanned
   index for every input (proposed; the A-S2 totality lesson, and the pure
   ops are already total), or a contract conditional on the classical
   fullness invariant.
4. **The track index:** in finite control, one row instance per
   `(direction, track)` (proposed), or on a tape.
5. **The shape of `Γ`:** `Bool ⊕ ZoneCell k` (proposed) or a structure
   with a bit field.
6. **Retiring the superseded declarations:** delete them through the G3/G4
   gate (proposed, since nothing imports them), or deprecate them first.
7. **G1's extent:** whether `Build/Loop.lean`'s public hosts also
   generalize now, or only when a large-alphabet consumer needs them.
   Proposed: only Seam, Embed, `bufferTape` and the R3 sweeps now.

#### Decisions 13d.1–13d.7 taken (user, 2026-10-10): all as proposed

1. Zone boundaries are **blank separator cells**.
2. **A laid-out `ℓ` plus an extension row.**
3. **Total rebalance contracts**: the rows realize the total pure cascade at
   the scanned index for every input.
4. **The track index lives in finite control.**
5. **`ZoneSym k := Bool ⊕ ZoneCell k`.**
6. The superseded declarations are **deleted through the G3/G4 gate**.
7. **G1 covers only Seam, Embed, `bufferTape` and the R3 sweeps.** What this
   means for the sweeps: the *definitions* of `transferTM`, `copyTM`,
   `clearTM` and `compareTM` (the last needs `[DecidableEq Symbol]`), and the
   three framed sweep contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg`
   and `clearTM_run_ofCfg`, generalize. The canonical `Cfg.ofWords` rows,
   the space rows, the compare contracts, and everything about `incrementTM`
   stay Bool-specific. The generalized definitions instantiate at `Bool`.

The G1 brief is `briefs/s13d-g1-generalize.md`.


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

## ===== TCSlib/Complexity/TuringMachine/SymbolLift.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running `Bool` machines on rich alphabets: the embedding transport

A machine over a rich work alphabet `Γ` often needs a binary routine (a counter, a
compare) on one of its tapes. Instead of re-proving each binary routine at `Γ`, this file
**lifts** a `Bool` machine along an embedding `e : Bool ↪ Γ`. The lifted machine reads
through `decodeBool e`, where foreign symbols read as blank, and writes and emits
through `e`. From every lifted configuration and at every time it runs as the original,
everything mapped along `e` (`Turing.MultiTapeTM.liftSymbols_runFrom`). It is the
embedding analogue of the equivalence transport `Turing.MultiTapeTM.mapWorkSymbols`
(`Build/CounterLoop.lean`). Space is preserved exactly. A lifted computation is a
computation *via* `e` in the sense `Turing.FinTM.alphabet_reduction` consumes, so a
rich-alphabet construction can finish by alphabet reduction.

Design: `machine-library-design.md` §12.8 (decision 12.8.1, rich-alphabet configuration
records) and §12.8a R8.0. Consumers: the §12.8 record rows, which run the binary counter
rows on dedicated digit tapes, and §13d's zone carrier, whose alphabet embeds `Bool` by
`Sum.inl`.

## Main definitions

* `Turing.decodeBool` — decoding along `e`; foreign symbols decode to `none`.
* `Turing.Action.liftSymbols`, `Turing.Cfg.liftSymbols`, `Turing.MultiTapeTM.liftSymbols`,
  `Turing.FinTM.liftSymbols` — the lift of actions, configurations and machines.

## Main results

* `Turing.MultiTapeTM.liftSymbols_runFrom` — the transport: lifted runs are lifts of runs.
* `Turing.MultiTapeTM.liftSymbols_step` — its one-step form.
* `Turing.MultiTapeTM.liftSymbols_initCfg`, `Turing.MultiTapeTM.liftSymbols_spaceUsed` — start
  configurations and space.
* `Turing.FinTM.liftSymbols_computesFunInTimeVia` — a lifted computation is a computation via
  `e`, in the same time.
* `Turing.MultiTapeTM.liftSymbols_runFrom_over`, with `Turing.Cfg.liftOver`,
  `Turing.Cfg.decodeSymbols` and `Turing.Cfg.liftOver_decodeSymbols` — the overlay transport:
  a lifted run of an input-oblivious, blank-free table from an arbitrary rich configuration,
  keeping its rich frame (§12.8 fill, for R8.0b and the record rows).
* `Turing.FinTM.bufferTape_map`, `Turing.FinTM.bufferTape_map_decode`,
  `Turing.decodeBool_eq_some` — delimited words and decoding under the lift.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§1.2 and Claim 1.5: the alphabet of a machine can be changed at a
  constant-factor cost; this file is the cost-free direction, from `Bool` into a larger
  alphabet.)
-/

namespace Turing

section Lift
variable {k : ℕ} {Γ State : Type*}

/-- Decode a rich symbol along `e : Bool ↪ Γ`: `e b` decodes to `some b`, and every
symbol outside the image of `e` decodes to `none`, which the lifted machine reads as a
blank. -/
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none

/-- Decoding inverts `e` on its image.

**Proof sketch.** `cases b`; the two images differ by injectivity of `e`. -/
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    decodeBool e (e b) = some b := by
  cases b
  · have : e false ≠ e true := fun h => Bool.false_ne_true (e.injective h)
    simp [decodeBool, this]
  · simp [decodeBool]

/-- Lift an action along `e`: written symbols and the emission are mapped by `e`. -/
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State where
  inputTape := a.inputTape
  workTapes := fun j => ((a.workTapes j).1.map (Option.map e), (a.workTapes j).2)
  output := a.output.map e
  state := a.state

/-- Lift a configuration along `e`: input, work cells and output mapped by `e`. -/
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    Cfg k Γ State (x.map e) where
  state := c.state
  inputPos := Fin.cast (by simp) c.inputPos
  workTapes := fun j p => (c.workTapes j p).map e
  workTapePos := c.workTapePos
  output := c.output.map e

/-- Lift a machine along `e`: read through `decodeBool e`, write through `e`. -/
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State where
  q₀ := M.q₀
  tr := fun q inp work =>
    (M.tr q (inp.bind (decodeBool e)) fun j => (work j).bind (decodeBool e)).liftSymbols e

/-- The lifted configuration reads the mapped input symbol.

**Proof sketch.** The two input positions have the same value, so the end-marker cases
match; an inner position reads `(x.map e)[i] = e x[i]`. -/
lemma Cfg.liftSymbols_inputSymbol (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (c.liftSymbols e).inputSymbol = c.inputSymbol.map e := by
  have hv : ((c.liftSymbols e).inputPos : ℕ) = c.inputPos := rfl
  unfold Cfg.inputSymbol
  have e0 : ((c.liftSymbols e).inputPos = 0) ↔ (c.inputPos = 0) := by
    simp only [Fin.ext_iff, hv, Fin.val_zero]
  have e1 : ((c.liftSymbols e).inputPos = ((x.map e).length + 1 : ℕ)) ↔
      (c.inputPos = (x.length + 1 : ℕ)) := by
    simp only [hv, List.length_map]
  by_cases h0 : c.inputPos = 0
  · rw [dif_pos (e0.mpr h0), dif_pos h0]; rfl
  · rw [dif_neg (fun h => h0 (e0.mp h)), dif_neg h0]
    by_cases h1 : c.inputPos = (x.length + 1 : ℕ)
    · rw [dif_pos (e1.mpr h1), dif_pos h1]; rfl
    · rw [dif_neg (fun h => h1 (e1.mp h)), dif_neg h1]
      simp [hv]

/-- Moving the input head commutes with recasting the position type. -/
private lemma moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (p : Fin (n + 2)) (s : SignType) :
    moveInputPos (Fin.cast h p) s = Fin.cast h (moveInputPos p s) := by
  have hnm : n = m := by omega
  subst hnm
  rfl

/-- One step commutes with the lift.

**Proof sketch.** A halted configuration does not move. Otherwise the lifted machine
decodes the scanned symbols back to the original ones (`decodeBool_apply`), so it
selects the lift of the original action; applying a lifted action to a lifted
configuration is the lift of the applied action, cell by cell. -/
lemma MultiTapeTM.liftSymbols_step [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (M.liftSymbols e).step (c.liftSymbols e) = (M.step c).liftSymbols e := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.liftSymbols, hs]
  | some q =>
    have hin : (c.liftSymbols e).inputSymbol.bind (decodeBool e) = c.inputSymbol := by
      rw [Cfg.liftSymbols_inputSymbol]; cases c.inputSymbol <;> simp
    have hw : (fun j => ((c.liftSymbols e).workTapeSymbols j).bind (decodeBool e)) =
        c.workTapeSymbols := by
      funext j; simp only [Cfg.workTapeSymbols, Cfg.liftSymbols]
      cases c.workTapes j (c.workTapePos j) <;> simp
    simp only [MultiTapeTM.step,
      show (c.liftSymbols e).state = some q by simp [Cfg.liftSymbols, hs], hs]
    change ((M.tr q ((c.liftSymbols e).inputSymbol.bind (decodeBool e))
      fun j => ((c.liftSymbols e).workTapeSymbols j).bind (decodeBool e)).liftSymbols e).apply
        (c.liftSymbols e) = _
    rw [hin, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_cast (by simp) _ _
    · funext j p
      simp only [Action.apply, Action.liftSymbols, Cfg.liftSymbols]
      cases (M.tr q c.inputSymbol c.workTapeSymbols).workTapes j |>.1 with
      | none => simp
      | some v =>
        simp only [Option.map_some]
        by_cases hp : p = c.workTapePos j
        · subst p; simp
        · simp [Function.update_of_ne hp]
    · rfl
    · simp only [Action.apply, Action.liftSymbols, Cfg.liftSymbols, List.map_append]
      cases (M.tr q c.inputSymbol c.workTapeSymbols).output <;> rfl

/-- **The embedding transport** (§12.8 R8.0): from every `Bool` configuration and at
every time, the lifted machine runs as the original, with input, work cells and output
mapped along `e`.

**Proof sketch.** Induction on `t` with `liftSymbols_step`. -/
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.liftSymbols_step, ih]

/-- The lift keeps the state. -/
@[simp] lemma Cfg.liftSymbols_state (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) :
    (c.liftSymbols e).state = c.state := rfl

/-- The lift keeps the work-head positions. -/
@[simp] lemma Cfg.liftSymbols_workTapePos (e : Bool ↪ Γ) {x : List Bool}
    (c : Cfg k Bool State x) : (c.liftSymbols e).workTapePos = c.workTapePos := rfl

/-- The lifted machine starts at the lift of the original start (both blank tapes, same
heads and state). -/
lemma MultiTapeTM.liftSymbols_initCfg [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) (x : List Bool) :
    (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e := by
  apply Cfg.ext <;> rfl

/-- Space is preserved exactly: the head trajectories are the same.

**Proof sketch.** Unfold the visited sets and rewrite with `liftSymbols_runFrom`. -/
lemma MultiTapeTM.liftSymbols_spaceUsed [DecidableEq Γ] (M : MultiTapeTM k Bool State)
    (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t := by
  simp [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead,
    MultiTapeTM.liftSymbols_runFrom]

end Lift

/-- The `FinTM` layer of the lift. -/
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ :=
  ⟨M.k, M.State, M.tm.liftSymbols e⟩

/-- A `Bool` machine computing `f` computes `f` via `e` when lifted, in the same time:
the form `Turing.FinTM.alphabet_reduction` consumes.

**Proof sketch.** Rewrite the lifted run from the lifted start with
`liftSymbols_initCfg` and `liftSymbols_runFrom`; halting and the mapped output follow. -/
theorem FinTM.liftSymbols_computesFunInTimeVia {Γ : Type} [DecidableEq Γ] (M : FinTM Bool)
    (e : Bool ↪ Γ) {f : List Bool → List Bool} {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T := by
  intro x
  have hx := (FinTM.computesInTime_iff _ _ _ _).mp (h x)
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ?_
  change ((M.tm.liftSymbols e).runFrom ((M.tm.liftSymbols e).initCfg (x.map e)) _).state = none ∧
    ((M.tm.liftSymbols e).runFrom ((M.tm.liftSymbols e).initCfg (x.map e)) _).output = _
  rw [MultiTapeTM.liftSymbols_initCfg, MultiTapeTM.liftSymbols_runFrom]
  exact ⟨hx.1, congrArg (List.map e) hx.2⟩

/-! ### Overlays: a lifted run that keeps the rich frame (§12.8 fill, R8.0b)

`Turing.MultiTapeTM.liftSymbols_runFrom` transports a `Bool` run along `e` only from a
configuration that is a lift everywhere. A dedicated digit tape inside a rich host has rich
neighbours and a rich input. The overlay keeps the rich configuration's cells wherever the
`Bool` run agrees with their decoding, so a lifted run of an input-oblivious, blank-free
table transports from an arbitrary rich start. -/

section Overlay

/-- **Decoding inverts the embedding** (design §12.8a): a symbol that decodes to `b` is
`e b`. -/
theorem decodeBool_eq_some {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) (b : Bool)
    (h : decodeBool e γ = some b) : γ = e b := by
  unfold decodeBool at h
  split_ifs at h with h1 h2 <;> simp_all

/-- **A lifted delimited word is the delimited word of the lift** (design §12.8a §1,
Part B). -/
theorem FinTM.bufferTape_map {Γ : Type} (e : Bool ↪ Γ) (w : List Bool) (p : ℤ) :
    FinTM.bufferTape (w.map e) p = (FinTM.bufferTape w p).map e := by
  unfold FinTM.bufferTape
  split_ifs <;> simp

/-- **A lifted delimited word decodes to the word** (design §12.8a), delimiters
included. -/
theorem FinTM.bufferTape_map_decode {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (w : List Bool) (p : ℤ) :
    (FinTM.bufferTape (w.map e) p).bind (decodeBool e) = FinTM.bufferTape w p := by
  by_cases hp : 0 ≤ p
  · simp only [FinTM.bufferTape, hp, if_true, List.getElem?_map]
    cases w[p.toNat]? <;> simp
  · simp [FinTM.bufferTape, hp]

/-- **The overlay of a `Bool` configuration on a rich one** (design §12.8a, R8.0b). Control,
input position and heads are the lift's. A cell where `c` agrees with the decoding of `D`
keeps `D`'s symbol; any other cell is `c`'s, mapped by `e`. The output is `D`'s followed by
the lift's. -/
def Cfg.liftOver {k : ℕ} {Γ Q : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    {x' : List Bool} (hx : x'.length = x.length) (D : Cfg k Γ Q x) (c : Cfg k Bool Q x') :
    Cfg k Γ Q x :=
  ⟨(c.liftSymbols e).state, Fin.cast (by simp [hx]) (c.liftSymbols e).inputPos,
    fun j p => if c.workTapes j p = (D.workTapes j p).bind (decodeBool e) then D.workTapes j p
      else (c.liftSymbols e).workTapes j p,
    (c.liftSymbols e).workTapePos, D.output ++ (c.liftSymbols e).output⟩

/-- **One lifted step commutes with the overlay** (design §12.8a, R8.0b), for a table that
ignores its input and never writes a blank.

**Proof sketch.** The lifted table reads the overlay's cells through `decodeBool e`, which
returns `c`'s cells; input-obliviousness removes the input read. A written cell is a digit,
so it agrees with its own decoding exactly where `D`'s decoding already held it. -/
theorem MultiTapeTM.liftSymbols_step_over {k : ℕ} {Γ Q : Type} [DecidableEq Γ]
    (e : Bool ↪ Γ) (N : MultiTapeTM k Bool Q)
    (hin : ∀ q inp inp' work, N.tr q inp work = N.tr q inp' work)
    (hnb : ∀ q inp work j, ((N.tr q inp work).workTapes j).1 ≠ some none)
    {x : List Γ} {x' : List Bool} (hx : x'.length = x.length)
    (D : Cfg k Γ Q x) (c : Cfg k Bool Q x') :
    (N.liftSymbols e).step (Cfg.liftOver e hx D c) = Cfg.liftOver e hx D (N.step c) := by
  cases hs : c.state with
  | none =>
    have : (Cfg.liftOver e hx D c).state = none := hs
    rw [MultiTapeTM.step_of_halt this, MultiTapeTM.step_of_halt hs]
  | some q =>
    have hL : (Cfg.liftOver e hx D c).state = some q := hs
    have hw : (fun j => ((Cfg.liftOver e hx D c).workTapeSymbols j).bind (decodeBool e)) =
        c.workTapeSymbols := by
      funext j
      simp only [Cfg.workTapeSymbols, Cfg.liftOver, Cfg.liftSymbols]
      split_ifs with h
      · exact h.symm
      · cases c.workTapes j (c.workTapePos j) <;> simp
    unfold MultiTapeTM.step
    rw [hL, hs]
    dsimp only
    change ((N.tr q ((Cfg.liftOver e hx D c).inputSymbol.bind (decodeBool e))
      fun j => ((Cfg.liftOver e hx D c).workTapeSymbols j).bind (decodeBool e)).liftSymbols
        e).apply (Cfg.liftOver e hx D c) = _
    rw [hw, hin q _ c.inputSymbol]
    have hnb' := hnb q c.inputSymbol c.workTapeSymbols
    generalize N.tr q c.inputSymbol c.workTapeSymbols = a at hnb'
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      simp only [Action.apply, Cfg.liftOver, Action.liftSymbols, Cfg.liftSymbols, Fin.coe_cast,
        moveInputPos]
      split_ifs <;> simp <;> omega
    · funext j p
      simp only [Action.apply, Action.liftSymbols, Cfg.liftOver, Cfg.liftSymbols]
      cases ha : (a.workTapes j).1 with
      | none => simp
      | some s =>
        have hs' : s ≠ none := fun h => hnb' j (by rw [ha, h])
        obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp hs'
        simp only [Option.map_some]
        by_cases hp : p = c.workTapePos j
        · subst hp
          simp only [Function.update_self]
          split_ifs with h
          · cases hD : D.workTapes j (c.workTapePos j) with
            | none => simp [hD] at h
            | some γ =>
              simp only [hD, Option.bind_some] at h
              rw [decodeBool_eq_some e γ b h.symm]
          · rfl
        · simp [Function.update_of_ne hp]
    · rfl
    · simp only [Action.apply, Action.liftSymbols, Cfg.liftOver, Cfg.liftSymbols,
        List.map_append, List.append_assoc]
      cases a.output <;> rfl

/-- **The overlay transport over whole runs** (design §12.8a, R8.0b): the sibling of
`Turing.MultiTapeTM.liftSymbols_runFrom` that keeps the rich frame.

**Proof sketch.** The one-step lemma, iterated by `Function.Semiconj.iterate_right`. -/
theorem MultiTapeTM.liftSymbols_runFrom_over {k : ℕ} {Γ Q : Type} [DecidableEq Γ]
    (e : Bool ↪ Γ) (N : MultiTapeTM k Bool Q)
    (hin : ∀ q inp inp' work, N.tr q inp work = N.tr q inp' work)
    (hnb : ∀ q inp work j, ((N.tr q inp work).workTapes j).1 ≠ some none)
    {x : List Γ} {x' : List Bool} (hx : x'.length = x.length)
    (D : Cfg k Γ Q x) (c : Cfg k Bool Q x') (t : ℕ) :
    (N.liftSymbols e).runFrom (Cfg.liftOver e hx D c) t =
      Cfg.liftOver e hx D (N.runFrom c t) :=
  (Function.Semiconj.iterate_right (f := Cfg.liftOver e hx D)
    (fun c => (MultiTapeTM.liftSymbols_step_over e N hin hnb hx D c).symm) t c).symm

/-- **The decoded `Bool` shadow of a rich configuration** (design §12.8a, R8.0b): cells
decoded (a foreign symbol reads as blank), the input replaced by a `Bool` word of the same
length, the output empty. -/
def Cfg.decodeSymbols {k : ℕ} {Γ Q : Type} [DecidableEq Γ] (e : Bool ↪ Γ) {x : List Γ}
    (D : Cfg k Γ Q x) : Cfg k Bool Q (x.map fun _ => false) :=
  ⟨D.state, Fin.cast (by simp) D.inputPos, fun j p => (D.workTapes j p).bind (decodeBool e),
    D.workTapePos, []⟩

/-- **Every rich configuration is the overlay of its shadow on itself** (design §12.8a,
R8.0b), so the overlay transport applies from an arbitrary rich start.

**Proof sketch.** Field by field; a cell always agrees with its own decoding. -/
theorem Cfg.liftOver_decodeSymbols {k : ℕ} {Γ Q : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    {x : List Γ} (D : Cfg k Γ Q x) : Cfg.liftOver e (by simp) D (Cfg.decodeSymbols e D) = D := by
  apply Cfg.ext
  · rfl
  · apply Fin.ext; rfl
  · funext j p; simp [Cfg.liftOver, Cfg.decodeSymbols]
  · rfl
  · simp [Cfg.liftOver, Cfg.decodeSymbols, Cfg.liftSymbols]

end Overlay

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: proved.** The transformers and configuration transports below
are real definitions, and every contract is proved: the §12 fill epochs
(gates closed 2026-10-09) and the later additive exports, the last of them
the guarded state transport (retrofit RB5, 2026-10-10).

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

* `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` — injective state transport
  followed by guarded agreement on the host carrier.
* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {Symbol : Type*} {x : List Symbol}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Symbol S) : Action k Symbol S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted symbol at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes**
(design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes**
(design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Symbol S) : Action k Symbol (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Symbol S x) : Cfg k Symbol (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Symbol S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (E : Cfg m Symbol S x → Cfg k Symbol S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Symbol S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor**
(round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor**
(round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports. They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

/-! ## Guarded state transport -/

/-- An injectively renamed source run agrees with a host run through any
prefix whose live source controls satisfy `good`, provided both transition
tables agree on the renamed good states for every input and work-tape read.
**Proof sketch.** Extend the renamed source table to the entire host carrier.
Step commutation identifies its run, then same-carrier guarded agreement
transfers that run to the host on the image of the good source states. -/
theorem MultiTapeTM.runFrom_mapState_of_agreeOn {k : ℕ} {S H : Type} {x : List Symbol}
    (src : MultiTapeTM k Symbol S) (host : MultiTapeTM k Symbol H)
    (emb : S ↪ H) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work,
      host.tr (emb q) inp work = (src.tr q inp work).mapState emb)
    (c : Cfg k Symbol S x) (t : ℕ)
    (hguard : ∀ u < t, ∀ q, (src.runFrom c u).state = some q → good q) :
    host.runFrom (c.mapState emb) t = (src.runFrom c t).mapState emb := by
  classical
  letI : Nonempty S := ⟨src.q₀⟩
  let reference : MultiTapeTM k Symbol H :=
    ⟨emb src.q₀, fun q inp work => (src.tr (Function.invFun emb q) inp work).mapState emb⟩
  have step (d : Cfg k Symbol S x) :
      reference.step (d.mapState emb) = (src.step d).mapState emb := by
    cases hs : d.state with
    | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
    | some q =>
      simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
      change (reference.tr (emb q) d.inputSymbol d.workTapeSymbols).apply (d.mapState emb) = _
      dsimp only [reference]
      rw [Function.leftInverse_invFun emb.injective q]
      exact Cfg.mapState_apply emb _ d
  have transport (u : ℕ) :
      reference.runFrom (c.mapState emb) u = (src.runFrom c u).mapState emb :=
    MultiTapeTM.runFrom_comm_of_step (fun d => d.mapState emb) step c u
  have agreement : reference.AgreeOn host {q | ∃ p, good p ∧ emb p = q} := by
    intro q hq inp work
    obtain ⟨p, hp, rfl⟩ := hq
    dsimp only [reference]
    rw [Function.leftInverse_invFun emb.injective p]
    exact (hagree p hp inp work).symm
  rw [MultiTapeTM.runFrom_eq_of_agreeOn agreement]
  · exact transport t
  · intro u hu q hq
    rw [transport u] at hq
    change ((src.runFrom c u).state.map emb) = some q at hq
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hq
    exact ⟨p, hguard u hu p hp, he⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state.
* **Optional-write normalization** (`Turing.Action.apply_workTapes`): the raw
  action-application identity for work tapes, promoted at the epoch-2/epoch-3
  boundary.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing

/-- **Optional-write normalization** (promoted from the epoch-2 fill per the
epoch-2 audit, promotion recommendation 1): applying an action rewrites each
work tape at its head with the proposed write, defaulting to the existing read
when the action declines to write. An explicit `some none` write remains an
erase, while an outer `none` writes back the scanned symbol unchanged. Holds
for every alphabet, state type, action, configuration, and tape index — no
finiteness, liveness, or computation hypothesis. -/
lemma Action.apply_workTapes {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

end Turing

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- A quantitative refinement of `rewind_from_any`: its construction takes
at most the current input position plus two steps, preserving all work and output.
**Proof sketch.** The mandatory first left move puts the head at most at the
last input symbol. `rewind_scan` then takes exactly the new position plus one. -/
lemma timed_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape {Symbol : Type*} (w : List Symbol) (z : ℤ) : Option Symbol :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil {Symbol : Type*} : bufferTape (Symbol := Symbol) [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat {Symbol : Type*} (w : List Symbol) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left {Symbol : Type*} (w : List Symbol) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Appending one emitted symbol changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append {Symbol : Type*} (w : List Symbol) (b : Symbol) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    cases m <;>
      simp [virtualMove, virtualNextTag, Cfg.inputSymbol, he, VirtualTag,
        moveInputPos, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs : c.inputSymbol = none := by simp [Cfg.inputSymbol, he]
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [hs']
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [bufferedFirstCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [bufferedFirstCfg, Action.apply, ho]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · simp [bufferedFirstCfg, Action.apply]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [bufferedSecondCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [bufferedSecondCfg, Action.apply, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ b' hb' p tapes heads
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    simp only [MultiTapeTM.step, bufferedFirstCfg, hs, bufferedCompTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply, sub_eq_add_neg]
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Choose the first halting time, which is at most `t₁`.
First-phase lockstep reaches its completed configuration, and determinism
identifies the output with `y`. The exact rewind lemma supplies `|y| + 2` more
steps, retaining the first block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hh : ∃ t, (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none :=
    ⟨t₁, ((computesInTime_iff M₁ x y t₁).mp h₁).1⟩
  let t := Nat.find hh
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ t₁ := Nat.find_min' hh ((computesInTime_iff M₁ x y t₁).mp h₁).1
  have hc : M₁.ComputesInTime x c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = y := hc.output_unique h₁
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t (fun s hs => Nat.find_min hh hs)]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM

/-! ### Machine-agreement transfer (§13, Z5)

Two machines over the same tape count and state type whose transition
tables agree on a set of control states run identically for as long as the
run's control stays inside that set. This is the `hagree` genre of
`Turing.capture_run`/`Turing.emit_run` made standalone: those lemmas carry
a per-state agreement hypothesis for one specific wrapper, re-proved ad hoc
at every host; the standalone form transfers whole runs between any two
agreeing tables (design `machine-library-design.md` §13, item Z5; decision
D-R3). First customers: the forwarding loop host of `Build/Loop.lean`
(whose fourteen phase lemmas are verbatim re-proofs of the capturing
host's, since the two tables agree on every non-body state) and the
guarded `clSlot_run` agreement sites of `CookLevin/Hardness.lean`. -/

namespace Turing.MultiTapeTM

/-- The two transition tables agree on every control state in `Q`: from any
such state, both machines take the identical action on identical reads.
Nothing is assumed about states outside `Q`, about `q₀`, or about
halting. -/
def AgreeOn {k : ℕ} {Symbol State : Type*} (M N : MultiTapeTM k Symbol State)
    (Q : Set State) : Prop :=
  ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work

/-- One step transfers across an agreement: if the configuration's control
state (when live) lies in the agreement set, both machines step it to the
same configuration. Halted configurations step to themselves on both sides.

**Proof sketch.** On `c.state = none` both steps are the identity. On
`c.state = some q` with `q ∈ Q`, unfold `step`: both sides apply the same
action `M.tr q c.inputSymbol c.workTapeSymbols = N.tr q …` to `c`. -/
theorem step_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (hq : ∀ q, c.state = some q → q ∈ Q) :
    N.step c = M.step c := by
  cases hs : c.state with
  | none => simp only [step_of_halt hs]
  | some q =>
    simp only [step, hs]
    rw [h q (hq q hs)]

/-- A whole run transfers across an agreement: if every control state the
`M`-run visits strictly before time `t` lies in the agreement set, the two
runs coincide at time `t` (and hence at every earlier time, by
instantiating `t`). The endpoint itself may leave the set or halt; no
liveness is assumed, and `t = 0` is the trivial case.

**Proof sketch.** Induct on `t`. The inductive hypothesis transfers the
run at `t`; the visit hypothesis at `u = t` puts its live control in `Q`,
so `step_eq_of_agreeOn` transfers the final step. Halted intermediate
configurations step identically on both sides without the hypothesis. -/
theorem runFrom_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) (hq : ∀ u < t, ∀ q, (M.runFrom c u).state = some q → q ∈ Q) :
    N.runFrom c t = M.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih (fun u hu => hq u (by omega)),
      runFrom_succ_eq_step']
    exact step_eq_of_agreeOn h _ (hq t (by omega))

end Turing.MultiTapeTM
```

## ===== TCSlib/Complexity/TuringMachine/Build/Scan.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: constant writers and native-input sweeps (§12.8)

The single-sweep rows of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a) that touch no G1-owned file: two writers
of a fixed word (R8.4, R8.4′) and two sweeps of the native input (R8.5a,
R8.5d). They are alphabet-generic, like the G1 catalog, and they are stated in
the §12.6 framed form: exact time, finish configuration, no earlier exit, and
the trajectory of every head, from an arbitrary configuration.

**Status: statements.** The four machines and the writers' phase alphabet are
real definitions. Every contract is sorried with a proof sketch, pending the
§12.8 fill.

## Design

* **Two writers.** `Turing.writeConstTM` writes its word and returns the head,
  so it composes under `Turing.seamCompTM` like the R3 sweeps. The advancing
  writer `Turing.writeAdvTM` leaves the head after the word and returns to its
  own start state, which is the round shape of `Turing.counterLoopTM`; it is
  the round of `Turing.expandTM` (R8.6). A seam consumer that calls it once
  uses `Turing.seamReleaseTM`.
* **Tables** are written with the catalog's one-tape actions
  `Turing.tapeAction` and `Turing.inputMoveAction`.
* **The input sweeps** move the native input head and return it to position
  `1`. `Turing.inputCopyTM` moves the destination work head in lockstep with
  it; `Turing.inputFoldTM` moves only the input head, so its work heads stay
  fixed. `Turing.inputCopyTM` reuses the sweep
  alphabet `Turing.SweepPhase` and `Turing.inputFoldTM` the scan alphabet
  `Turing.ScanPhase`, so no phase type is duplicated.
* **The input fold is the validator** of design §12.8a §0: a rich
  space-bounded simulator folds its input through `decodeBool`'s domain first
  and stops on a foreign symbol, because `alphabet_reduction_spaceUsed` bounds
  space over all rich inputs (decision O6).

## Main definitions

* `Turing.WritePhase`, `Turing.writeConstTM` — write a fixed word and return.
* `Turing.writeAdvTM` — write a fixed word and leave the head after it.
* `Turing.inputCopyTM` — copy the native input onto a work tape.
* `Turing.inputFoldTM` — fold the native input with a finite-state update.

## Main results

* `Turing.writeConstTM_run_ofCfg`, `Turing.writeAdvTM_run_ofCfg`,
  `Turing.inputCopyTM_run_ofCfg`, `Turing.inputFoldTM_run_ofCfg` — the framed
  contracts (statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape model with a read-only
  input tape; the routines are folklore subroutines of the textbook's
  simulations. §4.1: the space measure that makes input validation necessary
  for the rich simulators.)
-/

namespace Turing

/-! ### R8.4 — the constant writer -/

/-- **Phase alphabet of the constant writer** (design §12.8a, R8.4), for a word
of length `n`: writing cell `j`, walking back with `j` cells to go, and the
live exit anchor. -/
inductive WritePhase (n : ℕ) where
  /-- writing cell `j` of the word -/
  | wr (j : Fin (n + 1))
  /-- walking back, `j` cells from the origin -/
  | bk (j : Fin (n + 1))
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- **R8.4, the constant writer** (design §12.8a). Write the fixed word `w₀` on
tape `i` from its head, moving right, then walk back `|w₀|` cells and enter the
live `done` anchor with the head where it started. The old contents of the
tape are never read. -/
def writeConstTM {Symbol : Type*} (k : ℕ) (i : Fin k) (w₀ : List Symbol) :
    MultiTapeTM k Symbol (WritePhase w₀.length) where
  q₀ := .wr 0
  tr := fun q _ _ =>
    match q with
    | .wr j =>
      if h : (j : ℕ) < w₀.length then
        tapeAction i 0 (some (some w₀[(j : ℕ)])) .pos (.wr ⟨j + 1, by omega⟩)
      else inputMoveAction 0 (.bk ⟨w₀.length, by omega⟩)
    | .bk j =>
      if (j : ℕ) = 0 then inputMoveAction 0 .done
      else tapeAction i 0 none .neg (.bk ⟨j - 1, by omega⟩)
    | .done => inputMoveAction 0 .done

/-- **R8.4, the constant writer, framed** (design §12.8a). From any
configuration at the writer's start phase, the writer reaches `done` at
exactly `2|w₀| + 2` and not earlier. At that point the interval
`[pos, pos + |w₀|)` of tape `i` holds `w₀`, whatever it held before, and every
other cell, the head positions, the input position and the output are
unchanged. Up to the exit the head of tape `i` stays within
`[pos, pos + |w₀|]`, and every other head is fixed.

**Proof sketch.** Induct on the cells written: `|w₀|` steps write `w₀` moving
right. One stationary step turns into the walk back, `|w₀|` steps return the
head to `pos`, and one stationary step enters `done`. No step reads a work
cell, so the old contents are irrelevant. -/
theorem writeConstTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (w₀ : List Symbol) (d : Cfg k Symbol (WritePhase w₀.length) x)
    (hstate : d.state = some (.wr 0)) :
    (writeConstTM k i w₀).runFrom d (2 * w₀.length + 2) =
        { d with
          state := some .done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w₀.length : ℤ)
              then FinTM.bufferTape w₀ (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * w₀.length + 2, ((writeConstTM k i w₀).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * w₀.length + 2 →
        if j = i then
          ((writeConstTM k i w₀).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + (w₀.length : ℤ))
        else ((writeConstTM k i w₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-! ### R8.4′ — the advancing writer -/

/-- **R8.4′, the advancing writer** (design §12.8a). Write the fixed word `w₀`
on tape `i` from its head, moving right, and return to the start state `0` with
the head just after the word. The state `j` is the number of cells written. The
writer is cyclic: started again, it writes `w₀` again after the first copy,
which makes it a round body of `Turing.counterLoopTM` with anchor `0`. -/
def writeAdvTM {Symbol : Type*} (k : ℕ) (i : Fin k) (w₀ : List Symbol) :
    MultiTapeTM k Symbol (Fin (w₀.length + 1)) where
  q₀ := 0
  tr := fun j _ _ =>
    if h : (j : ℕ) < w₀.length then
      tapeAction i 0 (some (some w₀[(j : ℕ)])) .pos ⟨j + 1, by omega⟩
    else inputMoveAction 0 0

/-- **R8.4′, the advancing writer, framed** (design §12.8a). From any
configuration at state `0`, the writer returns to state `0` at exactly
`|w₀| + 1`, and its states strictly between are not `0`. At that point the
interval `[pos, pos + |w₀|)` of tape `i` holds `w₀`, whatever it held before,
the head of tape `i` is at `pos + |w₀|`, and every other cell, every other
head, the input position and the output are unchanged. Up to the return the
head of tape `i` stays within `[pos, pos + |w₀|]`, and every other head is
fixed. These are exactly the round hypotheses of `Turing.counterLoopTM_run_done`
with round time `|w₀| + 1`.

**Proof sketch.** Induct on the cells written: the state after `j ≤ |w₀|` steps
is `j`, which is nonzero for `0 < j`, with `j` cells of `w₀` written and the
head at `pos + j`. The last step is stationary and returns to `0`. No step
reads a work cell. -/
theorem writeAdvTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (w₀ : List Symbol) (d : Cfg k Symbol (Fin (w₀.length + 1)) x)
    (hstate : d.state = some 0) :
    (writeAdvTM k i w₀).runFrom d (w₀.length + 1) =
        { d with
          state := some 0
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w₀.length : ℤ)
              then FinTM.bufferTape w₀ (q - d.workTapePos j)
            else d.workTapes j q
          workTapePos := Function.update d.workTapePos i
            (d.workTapePos i + (w₀.length : ℤ)) } ∧
      (∀ t, 0 < t → t < w₀.length + 1 → ((writeAdvTM k i w₀).runFrom d t).state ≠ some 0) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ w₀.length + 1 →
        if j = i then
          ((writeAdvTM k i w₀).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j) (d.workTapePos j + (w₀.length : ℤ))
        else ((writeAdvTM k i w₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-! ### R8.5a — the input copier -/

/-- **R8.5a, the input copier** (design §12.8a). Copy the native input onto
tape `i` from its head, the two heads moving right in lockstep, then walk both
heads back together, guided by the input tape's left end marker. The phases are
the sweep alphabet's: `sweep` copies, `rewind` returns, and `done` is the live
exit anchor. The destination needs no left delimiter. -/
def inputCopyTM {Symbol : Type*} (k : ℕ) (i : Fin k) : MultiTapeTM k Symbol SweepPhase where
  q₀ := .sweep
  tr := fun q inp _ =>
    match q with
    | .sweep =>
      match inp with
      | some s => tapeAction i 1 (some (some s)) .pos .sweep
      | none => tapeAction i (-1) none .neg .rewind
    | .rewind =>
      match inp with
      | some _ => tapeAction i (-1) none .neg .rewind
      | none => tapeAction i 1 none .pos .done
    | .done => inputMoveAction 0 .done

/-- **R8.5a, the input copier, framed** (design §12.8a). From any configuration
in the copy phase with the input head at position `1`, the copier reaches
`done` at exactly `2|x| + 2` and not earlier, where `x` is the native input. At
that point the interval `[pos, pos + |x|)` of tape `i` holds `x`, whatever it
held before, and every other cell, every head, the input position and the
output are unchanged. Up to the exit the head of tape `i` stays within
`[pos - 1, pos + |x|]`, and every other head is fixed.

**Proof sketch.** Induct on the input cells: `|x|` lockstep steps copy `x`,
and the input's right end marker turns both heads left. The return takes `|x|`
lockstep steps over the input, and the left end marker supplies the entry step,
which puts the input head back at `1` and the work head back at `pos`. -/
theorem inputCopyTM_run_ofCfg {Symbol : Type*} {k : ℕ} {x : List Symbol} (i : Fin k)
    (d : Cfg k Symbol SweepPhase x) (hstate : d.state = some .sweep) (hin : d.inputPos = 1) :
    (inputCopyTM k i).runFrom d (2 * x.length + 2) =
        { d with
          state := some .done
          workTapes := fun j q =>
            if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (x.length : ℤ)
              then FinTM.bufferTape x (q - d.workTapePos j)
            else d.workTapes j q } ∧
      (∀ t < 2 * x.length + 2, ((inputCopyTM k i).runFrom d t).state ≠ some .done) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * x.length + 2 →
        if j = i then
          ((inputCopyTM k i).runFrom d t).workTapePos j ∈
            Finset.Icc (d.workTapePos j - 1) (d.workTapePos j + (x.length : ℤ))
        else ((inputCopyTM k i).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

/-! ### R8.5d — the input fold -/

/-- **R8.5d, the input fold** (design §12.8a). Read the native input left to
right, updating a finite state by `δ` from `a₀`, then walk the input head back
and enter the live anchor `done a` with the final state `a` as the verdict.
No work tape is touched. With `δ` testing membership in the image of an
embedding, it is the input validator of design §12.8a §0. -/
def inputFoldTM {Γ : Type*} {A : Type} (k : ℕ) (δ : A → Γ → A) (a₀ : A) :
    MultiTapeTM k Γ (ScanPhase A) where
  q₀ := .fwd a₀
  tr := fun q inp _ =>
    match q with
    | .fwd a =>
      match inp with
      | some γ => inputMoveAction 1 (.fwd (δ a γ))
      | none => inputMoveAction (-1) (.bwd a)
    | .bwd a =>
      match inp with
      | some _ => inputMoveAction (-1) (.bwd a)
      | none => inputMoveAction 1 (.done a)
    | .done a => inputMoveAction 0 (.done a)

/-- **R8.5d, the input fold, framed** (design §12.8a). From any configuration
in the forward phase at `a₀` with the input head at position `1`, the fold
reaches `done (x.foldl δ a₀)` at exactly `2|x| + 2`, where `x` is the native
input, and no `done` anchor earlier. Nothing else changes: the finish is the
start configuration with only the control state replaced, so the input head is
back at `1`. Up to the exit no work head moves.

**Proof sketch.** Induct on the input cells: after `j ≤ |x|` forward steps the
state is the fold of the first `j` symbols and the input head is at `j + 1`.
The right end marker turns the head, `|x|` steps return it, and the left end
marker supplies the entry step. -/
theorem inputFoldTM_run_ofCfg {Γ : Type*} {A : Type} {k : ℕ} {x : List Γ}
    (δ : A → Γ → A) (a₀ : A) (d : Cfg k Γ (ScanPhase A) x)
    (hstate : d.state = some (.fwd a₀)) (hin : d.inputPos = 1) :
    (inputFoldTM k δ a₀).runFrom d (2 * x.length + 2) =
        { d with state := some (.done (x.foldl δ a₀)) } ∧
      (∀ t < 2 * x.length + 2, ∀ a,
        ((inputFoldTM k δ a₀).runFrom d t).state ≠ some (.done a)) ∧
      (∀ (j : Fin k) (t : ℕ), t ≤ 2 * x.length + 2 →
        ((inputFoldTM k δ a₀).runFrom d t).workTapePos j = d.workTapePos j) := by
  sorry

end Turing
```
