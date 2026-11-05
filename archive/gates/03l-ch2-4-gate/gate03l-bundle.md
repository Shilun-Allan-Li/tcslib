## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03l-pack.md =====

# Gate 03l ([PS10] ch. 2–4, machine infrastructure): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/l/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine constructions under the randomized machine model: pair splitting, unary multiplication, the iterate-and-find loop, the state loop, and the string loops. Run 3b proved them, and every frozen machine-layer statement was checked unchanged against the freeze (56/56).
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03l-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs no source pages: these are infrastructure, with [PS10] §2.1 for the machine model.

## Brief for the auditor

Pack 03a's brief applies (its pack is in the bundle), with this emphasis:
- check each **public definition** and each **public theorem statement** against its docstring;
- check each headline's proof sketch against the source's proof, and say where the formal route
  departs from it;
- flag auxiliary statements that are vacuous (unsatisfiable hypotheses), or stronger or weaker
  than their use in the headline needs.

Attempt at least **two adversarial instantiations**. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/Build/{IterateFind, IterateFindHost, PairSplit, StateLoop, StringLoops, UnaryMul}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | pack 03a's machine model; `main`'s Turing-machine layer (`Complexity/TuringMachine/`) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch2.md` §5 (the machine-layer requirements consumed by ch. 2) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/l/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 26 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 0 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 0 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 6 files.

Pack-specific notes (as drafted): elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **Statements.** Is each construction's statement (its function and time bound) what its
   users need? Is any hypothesis unsatisfiable?
2. **The load-bearing loop** (`polyTimeComputable_iterateFind`, as an instance of
   `Turing.FinTM.exists_loopFindTM`). Is the polynomial bound right for polynomially many calls with
   fresh coins?
3. **`main`'s dependencies.** `main`'s `Complexity/TuringMachine/Build/Loop.lean` carries 5
   `sorry`s. Do any of this pack's constructions depend on them? The maintainer's axiom prints
   report it at the pinned head.

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

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

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files.

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text). The two are never unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (hℓ : ∀ n, 0 < ℓ.eval n) (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for injective `ℓ`).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length.
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges /
    colour permutations); one-iteration ZK, `n`-fold protocols get soundness only (sequential
    composition is §7.2.1, out of scope); `PerfectZKAbort` stated as the perfect form.
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2): satisfied by every length-shrinking family whose
    output length does not determine `n` (e.g. the constant family), an artefact of D5's typed
    inverse; the `1^n` form `WorstCaseOneWay` is the headline.
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index, so RSA's trapdoor is `⟨N, d⟩` (text: `d`) and Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least"; Lemma 50.15: "`N > 2`
    composite" should be odd composite.
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary.
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (deferred); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== audits/pass-shelat/run3-audit-summary.md =====

# Pass–shelat Chapters 2–4 — run 3 (adversarial statement audit) re-check summary

Re-checker (integration), 2026-10-28, worktree `/Users/dehmelf/Research/tcslib-pass-shelat`
(branch `cryptography/pass-shelat-ch2-4`). Inputs: the 10 audit packs (P2–P11, 30 findings) and
the 8 repair dispositions (P2, P3, P4, P7, P8, P9, P10, P11). Method: full `lake build`, then every
blocker/major repaired declaration opened and compared with its disposition, every minor
spot-checked, `audits/pass-shelat/Checks.lean` recompiled into `run3-axioms.log`.

## 1. Build

* Full `lake build` (bare, whole library, this agent the only Lean user): exit **0**,
  `Build completed successfully (4130 jobs)`, **0 `error:` lines**. Only the root module `TCSlib`
  was rebuilt; every campaign module was replayed from an up-to-date cache (the packs rebuilt
  them), so the replayed warnings are a complete census.
* `declaration uses 'sorry'` warnings: 213 in the whole library, of which **149 in the campaign
  files** (run 2: 157) and 64 pre-existing (`BooleanAnalysis/*`, `ErrorCorrectingCodes/MRRW.lean`,
  unchanged from run 2). The `TCSlib/Complexity/TuringMachine/Build/*` files of run 3b print 0.
* No integration breakage found; nothing had to be fixed.
* `python3 scripts/style_lint.py` over all 61 campaign files (56 modules + 5 facades): **0 findings**.
* Campaign size: 61 files, 27 291 lines (run 2: 52 files, 21 546 lines; new modules
  `Asymptotic/Permutations.lean`, `Asymptotic/GoldreichLevinDomain.lean`,
  `Asymptotic/HardCorePermutation.lean`, and the six `Complexity/Randomized/Build/*.lean` of run 3b).
  No file exceeds 1000 lines; close to the cap: `HardCore.lean` 998, `Rabin.lean` 987,
  `GraphIsomorphism.lean` 965, `RSA.lean` 901, `ElGamal.lean` 890 (split candidates for run 4).

### Sorry census per file (warnings in the full-build log; run-2 value in parentheses when changed)

| File | run 3 | note |
| --- | ---: | --- |
| `Complexity/Randomized/NonUniform.lean` | 1 | optional bridge `decides_of_decidesWithAdviceInTime` |
| `Complexity/Randomized/Primitives.lean` | 0 (2) | run 3b |
| `Complexity/Randomized/Repetition.lean` | 0 (7) | run 3b |
| `Asymptotic/Collections.lean` | 1 (2) | `exists_strongOneWay` proved (P3-1) |
| `Asymptotic/Encryption.lean` | 2 | |
| `Asymptotic/Ensembles.lean` | 5 | |
| `Asymptotic/HardCore.lean` | 6 | |
| `Asymptotic/HardCorePermutation.lean` | 1 (new) | `OneWayPermutation.glHalf` (P4-1) |
| `Asymptotic/MultiMessage.lean` | 4 | |
| `Asymptotic/NextBit.lean` | 6 | |
| `Asymptotic/OneWay.lean` | 3 | |
| `Asymptotic/Permutations.lean` | 1 (new) | `permFromCoins_uniform_of_some`, moved from `Sampling.lean` |
| `Asymptotic/PRF.lean` | 5 | |
| `Asymptotic/PublicKey.lean` | 4 | |
| `Asymptotic/Sampling.lean` | 0 (1) | permutation section moved out |
| `Asymptotic/Universal.lean` | 4 (3) | + `exists_canonizerExp` (P3-4, recorded open problem) |
| `Candidates/Concrete.lean` | 1 (0) | + `statClose_rejectBlocksL` (P7-6) |
| `Candidates/DiscreteLog.lean` | 6 (4) | + `expSampler_spec` (P3-1), + `statClose_sampleBelowL` (P8) |
| `Candidates/DiscreteLogHardcore.lean` | 7 | |
| `Candidates/ElGamal.lean` | 7 | |
| `Candidates/Factoring.lean` | 8 | |
| `Candidates/Rabin.lean` | 19 (17) | + `rabinSampler_spec`, `blumSampler_spec` (P3-1) |
| `Candidates/RSA.lean` | 9 (8) | + `rsaSampler_spec` (P3-1) |
| `NumberTheory/Primality.lean` | 2 | |
| `ZeroKnowledge/Commitment.lean` | 4 | |
| `ZeroKnowledge/Defs.lean` | 1 | |
| `ZeroKnowledge/Encoding.lean` | 4 | |
| `ZeroKnowledge/Encryption.lean` | 1 | |
| `ZeroKnowledge/GraphIsomorphism.lean` | 11 (17) | P2-1 (−4), P10-1/P10-2 (−2) |
| `ZeroKnowledge/GraphIsomorphismZK.lean` | 3 | |
| `ZeroKnowledge/InteractiveProofs.lean` | 2 | |
| `ZeroKnowledge/NP.lean` | 3 | |
| `ZeroKnowledge/ThreeColoring/Language.lean` | 2 | |
| `ZeroKnowledge/ThreeColoring/Protocol.lean` | 9 | |
| `ZeroKnowledge/ThreeColoring/Simulator.lean` | 7 | |
| **Total** | **149** (157) | |

All other campaign files (Closure, PolyExpr, PPT, the six `Build/*`, Adversary, BlockEncryptor,
GoldreichLevinDomain, Pseudorandom, Arithmetic, Chebyshev, Euclid, ModExp, QuadraticResidues,
Units, Interaction, the five facades and `ThreeColoring.lean`) print 0.

## 2. Audit outcome

30 findings in 10 packs: **2 blockers** (P8-1, P11-1), **12 majors** (P2-1, P3-1, P3-2, P4-1,
P7-1, P7-2, P7-3, P8-2, P9-1, P10-1, P10-2, P11-2), **16 minors**.

* **Repaired: 28** (every disposition received is `fixed`; P3-5 and P7-6 took the documented
  fallback / partial option offered by the finding). **Rebutted: 0.**
* **Deferred: 2** — P5-1 and P6-1 (the only findings of packs P5 and P6, both minor). No repair
  pass ran for these packs; the files are unchanged (`PRF.lean:560` still says "at the finitely
  many `n` with `q n = 0`" and the advice of `exists_ggmBitsDist_nuppt`'s sketch is not clamped;
  `Primality.lean:164/177` keeps `hodd` with the Deviation "(oddness is needed)", and plan error
  item 20 / inventory Lem-50.15b still claim the text's `N > 2` should be odd; the auditor's
  argument that the lemma holds for even `N > 2` is correct — `mrExp N = 0`, so `L_N = {α | α^{N−1} = 1}`,
  and `−1` is a unit with `(−1)^{N−1} = −1 ≠ 1`). Both are sketch/docstring-level; no statement is
  false.
* **Re-check of the 14 blocker/major dispositions: all hold** (section 3). **Unresolved: none.**

## 3. Per pack

### P2 (sampling, ensembles, pseudorandom) — 1 major, 1 minor; 2 repaired
* **P2-1 (major) fixed — verified.** `Asymptotic/Permutations.lean` (new, split from `Sampling.lean`
  for the file-size cap) owns `permFromCoins`, `permBits n := Nat.size n`, `permTrials n := 2*n*n`,
  `statClose_permFromCoins` (general `n(1−1/2^k)^T`), `uprob_permFromCoins_none_le_two_pow`
  (`≤ n·2⁻¹^n`, proved, axiom-clean, via `one_sub_inv_pow_le_half`), `statClose_permFromCoins_two_pow`.
  `GraphIsomorphism.lean`: `samplePerm`/`permCoinLen`/`permFailBound n = n·2⁻¹^n` at the shared
  parameters, `permFailBound_le_exp` deleted, `permCoinLen_le` with hypothesis `2n² ≤ N`
  (every encoded instance has length `3n²+2`, `length_encInstance`), `statClose_samplePerm` and
  `negligible_mul_permFailBound` proved (print `sorryAx` only through `permFromCoins_uniform_of_some`
  resp. `negligible_inv_pow_sqrt_div`). `Encoding.polyTimeComputable_encPermFromCoins` restated at
  the campaign parameters (live again; GI's private copy derived from it).
* **P2-2 (minor) fixed — verified.** `Ensemble` has `[nonempty : ∀ n, Nonempty (σ n)]`;
  `prediction_lemma` and `NextBitUnpredictable.pseudorandom` are back to the frozen shapes.
* Statement changes: `Ensemble` (+field); `prediction_lemma` (−h₀ h₁); `NextBitUnpredictable.pseudorandom`
  (−hσ); `samplePerm`, `permCoinLen`, `permFailBound` (parameters/closed form); `permCoinLen_le`
  (hypothesis `n² ≤ N` → `2n² ≤ N`); `permFailBound_le_exp` deleted; `polyTimeComputable_encPermFromCoins`
  (`permFromCoins n n n` → campaign parameters); module move of the permutation section; new
  `StatClose.comp_pushesUniform`, `statClose_getD_of_uniform_of_some`, `one_sub_inv_pow_le_half`,
  `permBits`, `permTrials`, `le_two_pow_permBits`, `permBits_le`, `two_pow_permBits_le`;
  `ddhReal`/`ddhRandom` explicit `nonempty` (superseded by P8-1).

### P3 (oneway, collections, universal) — 2 major, 3 minor; 5 repaired
* **P3-1 (major) fixed — verified.** `Collection.sample_spec : ∀ n r s, ∃ x, decD i (sample.runAt n i s) = some x ∧ eval ⟨i, …⟩ = f i x`
  with `i = pairFstD (gen.runAt n [] r)`; `Collection.evalSampled` proved; `owfFamily_strongOneWay`
  without `hG`; **`Collection.OneWay.exists_strongOneWay` (Thm 42.2 ⇒) now proved** from the
  explicit form (prints `sorryAx` only through `owfFamily_strongOneWay`). Instances discharge the
  field (`toCollection`, `factoringCollection` via `samplePairOut`/`factoringGen`, `glPad m henc`)
  or carry sorried `*Sampler_spec` stubs (RSA, Rabin, Blum, exp); `expCollection H G hV` outputs
  `dlDefaultIndex` below `n₀`.
* **P3-2 (major) fixed — verified.** `FunFamily.WorstCaseOneWay` is the `1^n` form
  (`A.inverter n (inLen n) (outLen n) (f n x) r`, `r : A.Coins n`); the frozen literal form is
  `WorstCaseOneWayLit`; `WorstCaseOneWay.toLit` and `WorstCaseOneWayLit.toParam (hinj)` proved,
  axiom-clean. Plan D5 and DESIGN §2.9/§3/§5 updated.
* P3-3 (minor) fixed — docstring: `𝓖 := ⟨var, mul (const 2) var, g'⟩`, dichotomy obligation deleted.
* P3-4 (minor) fixed — `CanonizerExp` ratified in D11 / decision log; `exists_canonizerExp` sorried
  open problem; Checks.lean prints it.
* P3-5 (minor) fixed by the finding's fallback (B): Deviation lines on `TrapdoorCollection`, `rsaGen`,
  `blumGen`; the literal `Inv((i, t), y)` not adopted (four files outside the pack).
* Statement changes: `WorstCaseOneWay` (literal → `1^n`), new `WorstCaseOneWayLit`, `toLit`, `toParam`;
  `Collection` (+`sample_spec`); `Collection.evalSampled` (new, proved); `owfFamily_strongOneWay` (−hG);
  `exists_strongOneWay` (sorry → proved); `Collection.glPad`/`PermCollection.glPad`/`TrapdoorCollection.glPad`
  (+`henc`) and their dependents; `tdpBitScheme`, `tdpBitScheme_singleBitSecure`,
  `OneWay.glPad_tdpBitScheme_singleBitSecure` (−hS); `samplePairRaw` via `samplePairOut`, new
  `factoringGen`, `factoringSampler_spec` (proved); `rsaTrapdoor`/`rabinCollection`/`rabinBlumTrapdoor`
  (+`sample_spec` from new stubs `rsaSampler_spec`, `rabinSampler_spec`, `blumSampler_spec`);
  `expCollection H G hV` (+validity bridge, generator fallback `dlDefaultIndex`, new stub
  `expSampler_spec`), `expGen_runAt`, `expCollection_index (hn)`, `expCollection_index_of_lt`,
  `dlCollection_index (hn)`, `fullDLCollection`; `exists_canonizerExp` (new stub).

### P4 (hardcore, encryption, public key) — 1 major, 1 minor; 2 repaired
* **P4-1 (major) fixed — verified.** `Asymptotic/HardCorePermutation.lean` (new): `PermFamily.glHalf`
  (a genuine `Equiv` at every `n`: `g_n(x ‖ w) = f_{⌊n/2⌋}(x) ‖ w`), `glHalfBit`, the proved bridges
  `glHalf_f_even/odd`, `glHalfBit_even/odd`, `predProb_glHalf_even/odd`, `invProb_glHalf_even`,
  `invProb_glHalf_odd_le`, `Negligible.comp_div_two` (all axiom-clean), the sorried headline
  `OneWayPermutation.glHalf : OneWayPermutation P → OneWayPermutation P.glHalf ∧ HardCore P.glHalf.toFunFamily glHalfBit`
  under a full sketch, and the proved corollaries `exists_owp_hardCore` (exactly the consumers'
  hypothesis shape) and `exists_securePRG_of_owp`. Frozen signatures untouched; `goldreich_levin`'s
  docstring records the route.
* P4-2 (minor) fixed — verified. `Asymptotic/GoldreichLevinDomain.lean` (new, 0 sorries):
  `HardcoreBit.invProb_guessInverter_enc(_pad)` for an arbitrary finite domain with an `m`-bit
  encoding (injectivity not needed); `Collection.OneWay.glPad_hardCore`'s sketch rewritten.
* Statement changes: none to existing declarations; new declarations as listed.

### P5 (PRF, multi-message) — 1 minor; 0 repaired, **1 deferred**
* P5-1 (minor, sketch only): no disposition; `PRF.lean` unchanged. Statement fine; the sketch's advice
  must be clamped and "finitely many `n` with `q n = 0`" should read "every `n`".

### P6 (number theory) — 1 minor; 0 repaired, **1 deferred**
* P6-1 (minor): no disposition; `two_mul_card_mrLiars_le` keeps `hodd` with the incorrect
  justification "(oddness is needed)"; plan error item 20 (second clause) and inventory Lem-50.15b
  not retracted. Downstream unaffected (`uprob_millerRabin_le` rejects even `N` directly).

### P7 (candidates: factoring, RSA, Rabin) — 3 major, 4 minor; 7 repaired
* **P7-1 (major) fixed — verified.** `ArithmeticFP` gained `add : PolyTimeComputable addStr`,
  `sub : PolyTimeComputable subStr`, `size : PolyTimeComputable sizeStr` (lossless `addStr`/`subStr`,
  unary `sizeStr`; `listToNat_addStr`, `listToNat_subStr` proved); no instance exists, so all
  `(H : ArithmeticFP)` theorems are unchanged; the six "requested primitive" sketches name `H.add`/
  `H.sub`/`H.size` (modular subtraction with the extra `z mod N` reduction). D11/DESIGN wording updated.
* **P7-2 (major) fixed — verified.** `oneCallFactorer A` activates `A` at parameter `n`
  (`A.coins`, `A.adv`, `A.advice`); `coins_oneCallFactorer` (rfl); `oneCallFactorer_runAtL : … = (A.runAtL n y r).take n`
  proved, axiom-clean; `oneCallFactorer_coinLen` removed; `fmult_weakOneWay` sketch applies it directly.
* **P7-3 (major) fixed — verified.** `rabinErr n := 4·exp(−n) + 4·n/2^n`; `negligible_rabinErr`
  re-proved (axiom-clean); the three sketches cite the diagonal `≤ 4n/2^n` (odd class via Chebyshev,
  Blum class via `BlumDensity`). Cosmetic: the `rabinErr` docstring labels the class size
  "`P = |Π_n| − 1` odd primes" while its chain `1/(P−1) ≤ 2/P ≤ 4n/2^n` is for `P = |Π_n|`
  (the diagonal over the `|Π_n| − 1` odd primes is `1/(|Π_n| − 1) ≤ 2/|Π_n| ≤ 4n/2^n`); the
  statement and the sketch of `rabinCollection_invProbAt_le` are right — fill-phase note for the owner.
* P7-4 (minor) fixed — verified: `fmult_inv_factor` concludes `… = p ∨ … = q` on block 0, proved.
* P7-5 (minor) fixed — sketch of `exists_plantFactorer` with `Nat.size (m n)` bits and `3n+3`-bit blocks.
* P7-6 (minor) fixed (cheap part): `Concrete.rejectBlocksL`, `rejectBlocksL_spec` (proved),
  `statClose_rejectBlocksL` (new stub); `sampleUnitL`, `samplePrimePL P m d` instances; `DistinctPrimes`
  lemmas and `natToList_zero`/`val_units_pow` moved to Concrete/Arithmetic. Not unified (documented
  judgement): `samplePrimeL` (its lemma `statClose_samplePrime` is already proved) and
  `DiscreteLog.sampleBelowL` (other owner).
* P7-7 (minor) fixed — `samplePrimeL` falls back to the prime `2` so `statClose_samplePrime` applies.
* Statement changes: `ArithmeticFP` (+3 fields), new `addStr`/`subStr`/`sizeStr` and lemmas;
  `fmult_inv_factor` (conclusion); `oneCallFactorer` (parameter `2n` → `n`), `oneCallFactorer_coinLen`
  removed, `coins_oneCallFactorer` new, `oneCallFactorer_runAtL` (`A.runAtL (2n)` → `A.runAtL n`);
  `samplePrimeL` (fallback `[]` → `natToBits n 2`); `rabinErr` (`2n/2^n` → `4n/2^n`, changing the
  values in `rabinCollection_invProbAt_le`, `rabinBlumTrapdoor_invProbAt_le`, `blumFactorProb_le_invProbAt`);
  `samplePrimeP` removed, `samplePrimePL` (+fallback `d`), `rabinGenParams` body; `sampleUnitL` body;
  new `rejectBlocksL`, `rejectBlocksL_spec`, `statClose_rejectBlocksL`; moves without change.

### P8 (candidates: discrete log, El Gamal) — 1 blocker, 1 major, 1 minor; 3 repaired
* **P8-1 (blocker) fixed — verified.** `ddhReal`/`ddhRandom` have product seeds
  `G.gen.Coins n × ((Fin (n*n) → Bool) × …)` with exponents `ddhExpo n i b := (sampleBelowL (expOrd i) (Nat.size (expOrd i)) n n (List.ofFn b)).getD 0`
  (the very sampler of `egGenParts`/`egEncParts`); the instance marginal is the plain coin law, so
  the threshold distinguisher of the finding is gone; `DDHAssumption G := (ddhReal G).Indist (ddhRandom G)`
  unchanged in text, Deviation recorded (exponents within `2^{-n}` of uniform, D10); `ddhExpo_statClose`
  proved modulo the shared stub `statClose_sampleBelowL`; `elGamal_secure`'s hybrid 1 re-sketched.
* **P8-2 (major) fixed — verified.** `ExpGroupGen.FullLengthExcept δ := ∀ n ≥ n₀, uprob (fun r => dlP (Gen(1^n; r)) < 2^(n−1)) ≤ δ n`;
  `fullDLCollection_hardCore` and `elGamal_secure` take `hbig : ∃ δ, Negligible δ ∧ G.FullLengthExcept δ`;
  bridges `FullLength.fullLengthExcept`, `FullLength.exists_fullLengthExcept` proved, axiom-clean;
  `FullLength` kept as the deterministic special case with the open-problem note.
* P8-3 (minor) fixed — Deviation prose of `dlLoop`, `halfBit`, `majOracle`, module docstring, plan
  error item 27, DESIGN §7 item 27 and inventory-ch3 text-issue 11 corrected (line 11 literal,
  strict `half` harmless).
* Statement changes: `ddhReal`, `ddhRandom` (seeds and samples), `DDHAssumption` (meaning),
  `elGamal_secure` (`hbig`), `fullDLCollection_hardCore` (`hbig`); new `FullLengthExcept`,
  `FullLength.fullLengthExcept`, `FullLength.exists_fullLengthExcept`, `statClose_sampleBelowL` (stub),
  `ddhExpo`, `ddhExpo_statClose`.
* Not done by the pack (left to the orchestrator): a plan decision-log row for the P8 repairs.

### P9 (ZK model) — 1 major, 2 minor; 3 repaired
* **P9-1 (major) fixed — verified.** `Strategy.ReadsPrefix S m := ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval |x|)))`
  (+ `next_congr`, `mono`); `IP := {L | ∃ π m, π.V.ReadsPrefix m ∧ InteractiveProof π L}`; the false
  "total time is polynomial as well" sentence removed and Deviations added to `Strategy.Efficient`,
  `InteractiveProof`, `InteractiveProofErr`; `npProtocol T p` reads a `p(|x|)`-bit prefix,
  `npProtocol_readsPrefix` and `WitnessRelation.mem_IP` proved (axiom-clean), `NP_subset_IP`
  (`sorryAx` only through the run-2 stub `exists_witnessRelation_of_mem_NP`);
  `npProtocol_interactiveProof` still axiom-clean. The repaired class coincides with the text's IP.
* P9-2 (minor) fixed — resolved by P2-1 (Encoding lemma live at the campaign parameters); note added.
* P9-3 (minor) fixed — Deviation on `Protocol`/`outV`/module docstring and the proved lemma
  `Protocol.outV_eq_getLast_of_moverIsV`.
* Statement changes: `IP`; `npProtocol T` → `npProtocol T p` and its lemmas `npProtocol_outV`,
  `npProtocol_efficientV`, `npProtocol_efficientP`, `npProtocol_interactiveProof (p) (hp)`; new
  `Strategy.ReadsPrefix`, `ReadsPrefix.next_congr`, `ReadsPrefix.mono`, `Protocol.outV_eq_getLast_of_moverIsV`,
  `npProtocol_readsPrefix`, `WitnessRelation.mem_IP`, `NP_subset_IP`.

### P10 (ZK graph isomorphism) — 2 major, 1 minor; 3 repaired
* **P10-1 (major) fixed — verified.** `uprob_adaptive_guess (m) {W} [Fintype W] [Nonempty W] (g) : … = 2⁻¹^m`,
  now **proved** (axiom-clean); `uprob_gi_rep_cheat_le` (statement unchanged) re-proved by a case
  split on `ρ`, axiom-clean.
* **P10-2 (major) fixed — verified.** `uprob_gni_rep_cheat … [Nonempty ρ] … = 2⁻¹^m`, now **proved**
  (axiom-clean); `gni_interactiveProof`'s sketch instantiates `ρ := P'.Coins |x|`.
* P10-3 (minor) fixed — resolved by P2-1; recorded in the module docstring and DESIGN §2.15.
* Statement changes: `uprob_adaptive_guess` (+`[Nonempty W]`), `uprob_gni_rep_cheat` (+`[Nonempty ρ]`).

### P11 (ZK commitment, 3COL, NP) — 1 blocker, 1 major, 1 minor; 3 repaired
* **P11-1 (blocker) fixed — verified.** `(hLR : ∀ x ∈ L, ∃ y, R x y)` added after `h` in
  `LevinReduction.efficientProverProofErr`, `LevinReduction.efficientProverProof`,
  `zk_proof_of_levinReduction`, `zk_proof_of_owp_levinReduction`; `zk_proof_of_mem_NP` passes
  `fun x hx => (hR.mem_iff x).1 hx`; sketch `complete x hx := let ⟨y, hy⟩ := hLR x hx; ⟨y, completeWitness x y hy⟩`.
* **P11-2 (major) fixed — verified.** `zk_proof_of_mem_NP` and `zk_proof_of_mem_NP_of_owp` conclude
  `∃ (π) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧ EfficientProverProofErr π L R (fun N => 1 − 1/p(N) + (1/2)^{p(N)})`
  (proofs closed); sanity lemma `one_sub_inv_add_half_pow_lt_one` proved, axiom-clean.
* P11-3 (minor) fixed — `edgeList` ordered-pairs Deviation (`edgeCount G = 2|E|`) on the defs,
  module docstrings and the consuming theorems.
* Statement changes: the four `hLR` additions; the two `zk_proof_of_mem_NP*` conclusions; new
  `one_sub_inv_add_half_pow_lt_one`.

## 4. Axiom prints (`audits/pass-shelat/run3-axioms.log`)

* `lake env lean audits/pass-shelat/Checks.lean`: exit 0, 0 errors, **291 prints** (run 2: 243;
  48 added by the packs and by this re-check — the P8 declarations `ddhExpo_statClose`,
  `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept`,
  `statClose_sampleBelowL` and P9's `npProtocol_readsPrefix` were appended here).
* **152 clean** (`[propext, Classical.choice, Quot.sound]` or a subset; run 2: 101), **139 `sorryAx`**
  (run 2: 142), 0 other axioms; no print went from clean to `sorryAx`; no print removed.
* `sorryAx → clean` (20): the 16 machine-layer targets of run 3b (`polyTimeComputable_unaryPoly`,
  `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
  `_pairDropPoly`, `NUPPT.exists_reparam`, `exists_reparam_advice`, `exists_split`, `exists_seq`,
  `polyTimeComputable_iterateFind`, `_iterate`, `_iterateEmit`, `_majority`, `_pairXor`, `_pairEq`,
  `_blockMap`), and in the campaign `PrivateKeyScheme.not_multiMessageSecure_of_deterministic`,
  `BitPublicKeyScheme.bitwiseEncFun_poly` (both through the machine layer), `uprob_gi_rep_cheat_le`,
  `uprob_gni_rep_cheat` (P10).
* The only machine-layer `sorryAx` left is the optional bridge `Complexity.NUPPT.decides_of_decidesWithAdviceInTime`
  (D11 optional module). D11's permitted admission `polyTimeComputable_iterateFind` is proved.
* New clean prints from the repairs (26): `statClose_getD_of_uniform_of_some`, `StatClose.comp_pushesUniform`,
  `one_sub_inv_pow_le_half`, `uprob_permFromCoins_none_le_two_pow`, `Collection.evalSampled`,
  `WorstCaseOneWay.toLit`, `WorstCaseOneWayLit.toParam`, `HardcoreBit.invProb_guessInverter_enc(_pad)`,
  `glHalf_f_even/odd`, `glHalfBit_even/odd`, `predProb_glHalf_even/odd`, `invProb_glHalf_even`,
  `invProb_glHalf_odd_le`, `Negligible.comp_div_two`, `rejectBlocksL_spec`, `listToNat_addStr`,
  `listToNat_subStr`, `oneCallFactorer_runAtL`, `negligible_rabinErr`, `WitnessRelation.mem_IP`,
  `Protocol.outV_eq_getLast_of_moverIsV`, `Strategy.ReadsPrefix.mono`, `uprob_adaptive_guess`,
  `one_sub_inv_add_half_pow_lt_one`, `FullLength.fullLengthExcept`, `FullLength.exists_fullLengthExcept`,
  `npProtocol_readsPrefix`.
* New `sorryAx` prints (statement-phase stubs or dependants): `statClose_permFromCoins(_two_pow)`,
  `statClose_samplePerm`, `negligible_mul_permFailBound` (through run-2 stubs), the five `*Sampler_spec`
  (`factoringSampler_spec` is proved; it prints `sorryAx` only because `factoringSampler` is
  `NUPPT.ofPolyTimeUniform` of the sorried machine stub `polyTimeComputable_samplePairRaw`;
  the other four are statement-phase stubs), `exists_canonizerExp`,
  `OneWayPermutation.glHalf`, `exists_owp_hardCore`, `exists_securePRG_of_owp`, `statClose_rejectBlocksL`,
  `NP_subset_IP`, `ddhExpo_statClose`, `statClose_sampleBelowL`.

## 5. Follow-ups for the orchestrator (no action taken here)

1. P5-1 and P6-1 have no disposition (packs without blocker/major findings were not repaired);
   both are sketch/docstring-level and can be folded into the run-4 fills (P6-1 also touches plan
   error item 20 and inventory Lem-50.15b).
2. `Rabin.lean` `rabinErr` docstring: class-size label slip (`P = |Π_n| − 1` vs the chain's `P = |Π_n|`).
3. Plan decision log: rows exist for the P3 repairs and run 3b only; P2, P4, P7, P8, P9, P10, P11
   repairs are recorded in DESIGN.md (§2/§5) and in this file but not in the plan's log.
4. `GraphIsomorphism.permCoinLen_le` is not used by any proof yet (coin-budget lemma for the fill).
5. Files near the 1000-line cap: `HardCore.lean` 998, `Rabin.lean` 987, `GraphIsomorphism.lean` 965.

## ===== briefs/pass-shelat/inventory-ch2.md =====

# Inventory — [PS10] Chapter 2, *Computational Hardness* (§2.1–§2.13, plus the Appendix items Chapter 2 uses)

Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-shelat-2010-ch2.raw.md`
(pages 21–65) and `…-appendix.raw.md`. Read-only survey of the Lean tree; nothing under `TCSlib/` was
touched. Conventions: `n` is the security parameter; "nuPPT" is [PS10, Def 26.8] in the advice
formulation (plan D4); "PPT" is [PS10, Def 23.4/23.5] with the random tape as an input component
(plan D3); `{0,1}^n` is `Fin n → Bool` (plan D5); `Π_n = {p < 2^n | p prime}`; `Z_N^* = (ZMod N)ˣ`;
"negl" = `TCSlib.Cryptography.Negligible`. Paths are relative to the worktree
`/Users/dehmelf/Research/tcslib-pass-shelat`; Mathlib paths are relative to
`.lake/packages/mathlib/Mathlib`.

Scope labels: **core** = mandatory per the plan; **optional** = feasible and useful, or already
formalized (cite only); **deferred** = not needed downstream and/or research-level.

---

## 0. Headline findings for the planners (read first)

**F1. There are no binary-arithmetic machines in the library.** `TCSlib/Complexity` contains no
`FinTM` computing addition, comparison, multiplication, division/mod, gcd, or modular exponentiation on
binary strings (the only counters are `Turing.FinTM.computesFunInTime_incFixed`, `…_lengthBits`,
`…_polyUnary`, `…_polyBits` in `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`, which handle
lengths and fixed-width increments). Every "easy to compute / sample / evaluate / invert with
trapdoor" clause of §2.3 and §2.6–§2.12 (f_mult, Euclid, modexp, Miller–Rabin, SamplePrime, factoring/
DL/RSA/Rabin collections) needs them, and so do the *reductions* of Thms 33.5, 36.3, 55.2, 61.8
(they multiply, divide, take gcds). Building them in the `Build/` style is a research-level effort
(the pairing primitives alone are 7.6k lines). **Recommendation (Q1):** a hypothesis bundle
`TCSlib.Cryptography.Candidates.ArithmeticFP` (fields: `PolyTimeComputable` for binary `mul`,
`divMod`, `xgcd`, `modExp`, comparison, and the decoding of binary numerals), taken as an explicit
hypothesis by every candidate theorem (no axiom; `#print axioms` stays clean), with its discharge a
deferred build target. The asymptotic OWF/collection *definitions* remain machine-based; only the
number-theoretic *instances* are conditional.

**F2. Algorithm 64.2 (universal one-way function) is wrong as printed** and the proof of Theorem 63.1
does not go through for it: `f_universal(⟨M, x⟩) = M(x)` lets an inverter return `⟨M', x'⟩` with a
different machine `M'`, which yields no preimage under `M_g`. The standard (Levin/Goldreich) definition
outputs `⟨M, M(x)⟩`; with it the text's union-bound argument is valid. Formalize the corrected
function (Deviation recorded in the docstring; listed in `text_errors`).

**F3. Security parameter vs input length (Q2).** Thm 35.1's `f'` lives on `({0,1}^n)^{m(n)}` and
Thm 42.2's `g` on `{0,1}^{ℓ₁(n)+ℓ₂(n)}`; the text's `f : {0,1}* → {0,1}*` with hardness "at every n"
cannot be met by these functions at lengths outside the image of `ℓ`. Recommended shape: an
asymptotic one-way function is a family `f n : (Fin (ℓ n) → Bool) → List Bool` with an explicit
polynomial input length `ℓ n = C·(n+1)^c` (default `ℓ n = n`), "easy" = some `FinTM Bool` computes
`pairEncode 1^n (ofFn x) ↦ f n x` within `Ct·(n+1)^ct`, "hard" = for every nuPPT receiving
`pairEncode 1^n (f n x)`, negligible in `n`. For `ℓ n = n` this is the text's definition (the honest
evaluator additionally reads `1^n`, harmless). Alternative: `ℓ` strictly increasing and the evaluator
on bare `x` (recover `n` by search; `computesFunInTime_splitSolveWith` is the model primitive).

**F4. Dyadic samplers are never exactly uniform on `Π_n`, `Z_q`, `Z*_{Φ(N)}`, `Z_N^*`, `QR_N` (Q3).**
Keep the hardness experiments on the *ideal* uniform distributions (as the text), and formalize the
"easy to sample" clauses as PPT samplers within statistical distance `2^{-n}` of uniform (strict
PPT with truncated rejection loops; Deviation). One bridging lemma (any success probability moves by
at most the statistical distance; `distAdv_le_statDist` is the model) connects the two. The needed
density facts are elementary: `|Π_n| ≥ 2^n/(2n)` (Chebyshev), `φ(m)/m ≥ 1/(log₂ m + 1)` (new, for
`Z*_{Φ(N)}`), `φ(pq)/pq ≥ 1/4` (for `Z_N^*`), 4-to-1 squaring (for `QR_N`).

**F5. Rabin needs more than the text states (Q4).** Thms 60.5/60.6/61.7/61.8/63.10 need `p ≠ q`
odd; Thm 61.8 (⇐) needs square roots modulo arbitrary primes but the text only proves `p ≡ 3 (mod 4)`;
Thm 63.10's `Gen` must sample primes `≡ 3 (mod 4)`, whose density is not available in Mathlib (no
Dirichlet-type bound). Formalize the Rabin results for Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`),
with the factoring assumption restricted to that index distribution, and take the density of
`3 (mod 4)` primes as an explicit hypothesis of the `Gen`-efficiency clause of Thm 63.10.

**F6. Primality testing (Q6).** The text relies on "primality testing is in polynomial time" (AKS,
unproved here) for SamplePrime and the `Gen` of Thms 51.1/53.2/57.2/61.7/63.10, and on Miller–Rabin
whose composite-case lemma (50.15b) is deferred by the plan. Recommended: a hypothesis
`PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` inside the Q1 bundle;
Miller–Rabin is formalized as a sampler with its prime-case correctness (core) and the composite
bound (deferred). Thms 33.5 and 36.3 are formalized with the one-call / random-planting reductions
that need no primality test (plan decision).

**F7. Uniform position in Thm 35.1 (Q7).** `OneWay.yaoTry` draws `i : Fin q` uniformly; coins of
polynomial length give exact uniformity only for `q` a power of two. Choose `m(n) := 2^{⌈log₂(2n q(n))⌉}`
(any larger `m` is allowed by the theorem), or route through Q3's statistical bridge.

**F8. Concrete-layer additions.** Garg files are frozen; new concrete lemmas go in a new file
`TCSlib/Cryptography/Candidates/Concrete.lean` (reductions and probability lemmas used by the
candidates) and in `TCSlib/Cryptography/Asymptotic/OneWay.lean` itself (small ones). List in §4.

**F9. Closure/Repetition requirements consumed by Chapter 2** are listed in §5 so that the machine
layer (Randomized/Closure.lean, Repetition.lean) can be sized before the skeletons are written.

---

## 1. Inventory table

Columns: ID · kind · title · proposed file (under `TCSlib/`) · difficulty 1–5 · scope · existing Lean
(short; full paths in §2) · note key. `(cite)` = already formalized, nothing to do beyond citing.

| ID | kind | title | proposed file | diff | scope | existing Lean |
|---|---|---|---|---|---|---|
| Def-21.1 | definition | Algorithm = deterministic TM over {0,1} | (cite) `Complexity/TuringMachine/Finite.lean` | 1 | optional | `Turing.FinTM Bool` |
| Def-21.2 | definition | Running time; polynomial time | (cite) `Complexity/ClassNP/PolyTime.lean` | 1 | optional | `FinTM.ComputesFunInTime`, `Complexity.PolyTimeComputable`, `Complexity.P` |
| Def-21.3 | definition | Deterministic computation of f | (cite) | 1 | optional | `FinTM.ComputesFunInTime`, `FinTM.Computes` |
| Rem-22.1 | claim | §2.1.1 background: Halting, time hierarchy, SAT | (cite) | 1 | optional | `Complexity.HALT_not_computable`, `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete` |
| Def-23.4 | definition | PPT (randomized TM with coin input) | `Complexity/Randomized/PPT.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime` |
| Def-23.5 | definition | Running time of a randomized TM (worst case over coins) | `Complexity/Randomized/PPT.lean` | 1 | core | — |
| Def-24.6 | definition | PPT computes f with probability 1 | `Complexity/Randomized/PPT.lean` | 2 | core | — (needs C7) |
| Rem-24.2 | claim | Majority amplification 1/2+1/poly → 1−2^{-n} | `Complexity/Randomized/Repetition.lean` | 4 | deferred | — (Chernoff) |
| Def-24.7 | definition | Efficient private-key encryption | `Cryptography/Asymptotic/Encryption.lean` | 2 | core | — |
| Def-26.8 | definition | Non-uniform PPT (advice form) | `Complexity/Randomized/NonUniform.lean` | 3 | core | pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly` |
| Rem-26.2 | claim | Machine-sequence ⟺ advice formulation of nuPPT | — | 4 | deferred | `Turing.timed_universal` (for ⇒) |
| Claim-26.3 | infrastructure | nuPPT closure calculus (pre/post, pairing, coins, advice, repetition) | `Complexity/Randomized/{Closure,Repetition}.lean` | 5 | core | `computesFunInTime_comp/cond`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `PolyTimeComputable.*` |
| Def-26.1 | definition | Worst-case one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Rem-27.1 | claim | NP ⊄ BPP ⟺ worst-case OWF exist ("show this!") | — | 5 | deferred | `Complexity.NP` |
| Def-27.2 | definition | Negligible / non-negligible | (cite) `Cryptography/Foundations/Negligible.lean` | 1 | optional | `Negligible`, `not_negligible_iff`, `negligible_two_pow_neg` |
| Def-27.3 | definition | Strong one-way function | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | `invProb` |
| Rem-28.1 | claim | (t,s,ε)-one-wayness (concrete security) | (cite) | 1 | optional | `invProb` (the concrete layer is this) |
| Def-28.4 | definition | Weak one-way function | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `invProb` |
| Def-29.1 | definition | f_mult | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Rem-29.2 | claim | f_mult is not strongly one-way (3/4 attack) | — | 2 | deferred | — |
| Def-29.3 | definition | Π_n and the uniform distribution on it | `Cryptography/NumberTheory/Chebyshev.lean` | 1 | core | `Nat.primesBelow`, `Nat.primeCounting'` |
| Asm-30.1 | assumption | Factoring assumption | `Cryptography/Candidates/Factoring.lean` | 2 | core | `uprob`, `Negligible` |
| Thm-31.3 | theorem | Chebyshev: π(x) > x/(2 log₂ x) | `Cryptography/NumberTheory/Chebyshev.lean` | 4 | core | `Nat.four_pow_lt_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le`, `Nat.primesBelow_card_eq_primeCounting'` |
| Claim-32.4 | claim | p^{ν_p(C(2x,x))} ≤ 2x | (cite) | 1 | optional | `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_log` |
| Claim-33.1 | corollary | Prime density: \|Π_n\| ≥ 2^n/(2n) | `Cryptography/NumberTheory/Chebyshev.lean` | 3 | core | as Thm-31.3 |
| Rem-33.2 | claim | Primality testing in polynomial time (AKS) | hypothesis in `Cryptography/Candidates/Arithmetic.lean` | 5 | deferred | — |
| Thm-33.5 | theorem | Factoring ⟹ f_mult weakly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_and_le_mul`, `uprob_pi_forall`, `not_negligible_iff` + C1 |
| Alg-33.6 | algorithm | A′ (and the one-call A″) | `Cryptography/Candidates/Factoring.lean` | 1 | core | — |
| Claim-34.1 | claim | f_mult(x′,y′) = pq ⟹ x′ ∈ {p,q} | `Cryptography/Candidates/Factoring.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd` |
| Thm-35.1 | theorem | Weak → strong (Yao direct product) | `Cryptography/Asymptotic/OneWay.lean` | 4 | core | `OneWay.yao_amplification`, `prodFun`, `yaoInverter`, `invProb_prodFun_le`, `one_sub_invProb_yaoInverter_le` |
| Thm-35.2 | theorem | g(x,y) = (f x, f y) strong if f strong | `Cryptography/Asymptotic/OneWay.lean` | 3 | core | pattern `OneWay.invProb_pad_le` + C2 |
| Thm-36.3 | theorem | Factoring ⟹ f_mult^{4n³} strongly one-way | `Cryptography/Candidates/Factoring.lean` | 3 | core | `uprob_update`, `sum_uprob_eq_card_mul`, `uprob_pi_forall`, `uprob_and_le_mul` + C3, C8 |
| Claim-36.2 | claim | (1−1/(4n²))^{4n³} ≤ e^{−n} | `Cryptography/Candidates/Concrete.lean` | 1 | core | `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul` (pattern `yao_amplification_exp`) |
| Alg-37.4 | algorithm | A′(z′) with planting (random-position variant) | `Cryptography/Candidates/Factoring.lean` | 1 | core | `uprob_update` |
| Alg-38.5 | algorithm | A₀(f, y) and its 2nm²p(n)-fold repetition | (cite) `Cryptography/OneWayFunctions/Amplification.lean` | 1 | optional | `OneWay.yaoTry`, `OneWay.yaoInverter` |
| Claim-38.2 | claim | PS10 parameters instantiate `yao_amplification` | `Cryptography/Asymptotic/OneWay.lean` | 2 | core | `OneWay.yao_amplification`, exp bounds |
| Claim-39.1 | claim | Pr[A fails \| x good] ≤ (1−θ)^T ≈ e^{−n} | (cite) | 1 | optional | `OneWay.one_sub_invProb_yaoInverter_le` |
| Claim-39.2 | claim | Many good elements: \|G_n\| ≥ 2^n(1−1/(2q)) | (cite) | 1 | optional | `OneWay.invProb_prodFun_le` |
| Def-41.1 | definition | Collection of one-way functions | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `HardcoreBit.PushesUniform`, `invProb` (pattern) |
| Thm-42.2 | theorem | Collection of OWFs ⟺ strong OWF | `Cryptography/Asymptotic/Collections.lean` | 4 | core | `PolyTimeComputable.pairEncode/.comp`, `uprob_prod`, `PushesUniform.uprob_eq` |
| Fact-42.1 | fact | Modular arithmetic laws | (cite) | 1 | optional | `Nat.add_mod`, `Nat.mul_mod` |
| Alg-43.2 | algorithm | ExtendedEuclid | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.xgcd`, `Nat.gcdA/gcdB`, `Nat.gcd_eq_gcd_ab`, `ZMod.inv` |
| Claim-43.3 | claim | ≤ 2n recursive calls when a < 2^n | `Cryptography/NumberTheory/Euclid.lean` | 3 | core | — |
| Claim-44.4 | claim | gcd(a,b) = gcd(b, a mod b) | (cite) | 1 | optional | `Nat.gcd_rec`, `Nat.gcd_comm` |
| Claim-44.5 | claim | Correctness ax+by = gcd (induction) | `Cryptography/NumberTheory/Euclid.lean` | 2 | core | `Nat.gcd_eq_gcd_ab` (Mathlib's own xgcd) |
| Rem-43.6 | claim | Euclid runs in poly(log a + log b) (machine) | Q1 hypothesis | 5 | deferred | — |
| Alg-45.5 | algorithm | Modular exponentiation (repeated squaring) | `Cryptography/NumberTheory/ModExp.lean` | 2 | core | `Nat.pow_mod`, `Nat.ModEq.pow` |
| Thm-45.6 | theorem | ≤ 2(⌊log₂ x⌋+1) modular multiplications; O(log x log² N) | `Cryptography/NumberTheory/ModExp.lean` | 2 | optional | `TimeM` (`Cryptography/RSA.lean`) cost model, optional |
| Def-46.7 | definition | Group | (cite) | 1 | optional | `Group`, `CommGroup` |
| Ex-46.1 | example | (Z_N, +) | (cite) | 1 | optional | `ZMod N` |
| Thm-46.8 | theorem | (Z_N^*, ×) is a group; Z_N^* = {x ∈ [1,N−1] \| gcd(x,N)=1} | `Cryptography/NumberTheory/Units.lean` | 1 | optional | `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime`, `ZMod.unitOfCoprime`, `ZMod.mul_inv_eq_gcd` |
| Def-46.9 | definition | Prime | (cite) | 1 | optional | `Nat.Prime` |
| Claim-47.1 | claim | p ∣ ab ⟹ p ∣ a ∨ p ∣ b (exercise) | (cite) | 1 | optional | `Nat.Prime.dvd_mul` |
| Claim-47.2 | claim | Φ(p) = p−1; Φ(pq) = (p−1)(q−1) (p ≠ q) | `Cryptography/NumberTheory/Units.lean` | 1 | core | `Nat.totient_prime`, `Nat.totient_mul`, `Nat.coprime_primes`, `ZMod.card_units_eq_totient` |
| Thm-47.10 | theorem | Euler | (cite) | 1 | optional | `ZMod.pow_totient`, `Nat.ModEq.pow_totient` |
| Cor-48.11 | corollary | Fermat | (cite) | 1 | optional | `ZMod.pow_card_sub_one_eq_one` |
| Cor-48.12 | corollary | a^x ≡ a^{x mod Φ(N)} (mod N), a ∈ Z_N^* | `Cryptography/NumberTheory/Units.lean` | 1 | core | `ZMod.pow_totient`, `Nat.div_add_mod` |
| Rem-48.2 | claim | Given Φ(N), a^x mod N efficient for any x (machine) | Q1 hypothesis | 5 | deferred | Cor-48.12 + Alg-45.5 |
| Ex-48.3 | example | 2^{61241} mod 21 (garbled) | — | 1 | optional | `decide` |
| Def-49.1 | definition | Miller–Rabin liar set L_N (corrected) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | — |
| Alg-49.13 | algorithm | Miller–Rabin test (t rounds) | `Cryptography/NumberTheory/Primality.lean` | 2 | core | `uprob_pi_forall` |
| Thm-49.14 | theorem | MR correct on primes; errs on composites w.p. ≤ 2^{−t} | `Cryptography/NumberTheory/Primality.lean` | 2 | core (prime) / deferred (composite) | `uprob_pi_forall` |
| Lem-50.15a | lemma | N odd prime ⟹ L_N = Z_N^* | `Cryptography/NumberTheory/Primality.lean` | 3 | core | `ZMod.pow_card_sub_one_eq_one`, `mul_self_eq_one_iff`, `sq_eq_sq_iff_eq_or_eq_neg` |
| Lem-50.15b | lemma | N odd composite ⟹ \|L_N\| ≤ (N−1)/2 | `Cryptography/NumberTheory/Primality.lean` | 5 | deferred | `Subgroup.card_subgroup_dvd_card` |
| Rem-49.3 | claim | Infinitely many Carmichael numbers | — | 5 | deferred | (weaker) `Nat.exists_infinite_pseudoprimes` |
| Rem-50.2 | claim | AKS deterministic primality | — | 5 | deferred | — |
| Alg-50.16 | algorithm | SamplePrime(n) (truncated strict-PPT form) | `Cryptography/NumberTheory/Primality.lean` | 3 | core | C4, C8 |
| Lem-51.17 | lemma | SamplePrime: uniform prime, failure ≤ 2^{−n}, poly time | `Cryptography/NumberTheory/Primality.lean` | 3 (+4 machine) | core | C4; Claim-33.1; `exists_loopFindTM` |
| Thm-51.1 | theorem | Factoring collection | `Cryptography/Candidates/Factoring.lean` | 3 | core | Lem-51.17, Claim-34.1, Def-41.1 |
| Def-52.1 | definition | Generator of a group; Gen_G | (cite) | 1 | optional | `Subgroup.zpowers`, `IsCyclic.exists_generator` |
| Rem-52.2 | claim | Prime-order groups; Z_p^* order p−1; safe primes, squares subgroup | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card` |
| Asm-52.2 | assumption | Discrete-log assumption (relative to a group family) | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | — |
| Thm-52.3 | theorem | DL collection | `Cryptography/Candidates/DiscreteLog.lean` | 3 | core | Def-41.1, Asm-52.2 |
| Claim-53.1 | claim | Safe-prime generator test g ≠ ±1, g^q ≠ 1 | `Cryptography/NumberTheory/Units.lean` | 2 | optional | `orderOf_dvd_of_pow_eq_one`, `ZMod.card_units` |
| Claim-53.2 | claim | x ↦ g^x : Z_q → G_q is a bijection (DL is a permutation) | `Cryptography/Candidates/DiscreteLog.lean` | 2 | optional | `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq` |
| Asm-53.1 | assumption | RSA assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | `ZMod.unitsEquivCoprime` |
| Thm-53.2 | theorem | RSA collection | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `HardcoreBit.pushesUniform_equiv`, C9 |
| Thm-54.3 | theorem | x ↦ x^e permutes Z_N^* when e ∈ Z*_{Φ(N)} | `Cryptography/NumberTheory/Units.lean` | 2 | core | `ZMod.pow_totient`, `RSA.rsa_crt_pow`, `RSA.rsa_correctness` |
| Def-55.1 | definition | Collection of one-way permutations | `Cryptography/Asymptotic/Collections.lean` | 1 | core | Def-41.1 |
| Thm-55.2 | theorem | RSA assumption ⟹ factoring assumption | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-54.3, `ZMod.inv`/`Nat.gcdA`, `uprob_fst` |
| Alg-55.3 | algorithm | A′(N, e, y) via factoring | `Cryptography/Candidates/RSA.lean` | 1 | core | — |
| Def-56.1 | definition | Collection of trapdoor permutations | `Cryptography/Asymptotic/Collections.lean` | 2 | core | Def-55.1 |
| Thm-57.2 | theorem | RSA is a TDP collection ("exercise") | `Cryptography/Candidates/RSA.lean` | 3 | core | Thm-53.2, Thm-54.3, Alg-43.2 |
| Def-57.0 | definition | QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | `MonoidHom.range`, `powMonoidHom` |
| Lem-57.1 | lemma | QR_p subgroup of size (p−1)/2; two roots each | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `legendreSym.card_sqrts`, `ZMod.euler_criterion`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.card_units` |
| Claim-58.1 | claim | x² = y² in Z_p ⟹ x = ±y | (cite) | 1 | optional | `sq_eq_sq_iff_eq_or_eq_neg` |
| Thm-58.2 | theorem | p = 4k+3: (y^{k+1})² = y for y ∈ QR_p | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.pow_card_sub_one_eq_one` |
| Ex-58.3 | exercise | Square roots for p ≡ 1 (mod 4) | — | 4 | deferred | — |
| Thm-58.3 | theorem | Chinese Remainder (k pairwise coprime moduli) | (cite; k = 2 bridge) `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | optional | `ZMod.chineseRemainder`, `Nat.chineseRemainderOfList`, `Nat.chineseRemainder` |
| Claim-59.1 | claim | Explicit CRT inverse y = Σ b_i n_i a_i; two Euclid calls | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | optional | `Nat.chineseRemainder` |
| Ex-59.2 | example | p = 7, q = 11 | — | 1 | optional | `decide` |
| Def-59.3 | definition | QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 1 | core | — |
| Thm-59.4 | theorem | x ∈ QR_N ⟺ x mod p ∈ QR_p ∧ x mod q ∈ QR_q | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder`, `Units.map`, `RingEquiv.map_pow` |
| Thm-60.5 | theorem | Squaring on Z_N^* is 4-to-1 (p ≠ q odd) | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | Lem-57.1, Thm-59.4 |
| Cor-60.6 | corollary | \|QR_N\| = \|Z_N^*\|/4 | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Finset.card_eq_sum_card_fiberwise` |
| Claim-60.7 | claim | Roots mod N from roots mod p, q via CRT | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `ZMod.chineseRemainder` |
| Ex-60.8 | example | N = 77 example (garbled) | — | 1 | optional | `decide` |
| Thm-61.7 | theorem | Rabin collection is one-way under factoring | `Cryptography/Candidates/Rabin.lean` | 4 | core | C5, C6, Claim-62.1 |
| Thm-61.8 | theorem | Rabin one-way ⟺ factoring (Blum integers) | `Cryptography/Candidates/Rabin.lean` | 4 (⇒) / 3 (⇐, Blum) | core | Thm-58.2, Claim-60.7, C6 |
| Alg-62.9 | algorithm | Factoring adversary A′(N) from a root finder | `Cryptography/Candidates/Rabin.lean` | 1 | core | — |
| Claim-62.1 | claim | x² ≡ z², z ≢ ±x ⟹ gcd(x−z, N) ∈ {p,q} | `Cryptography/NumberTheory/QuadraticResidues.lean` | 2 | core | `Nat.Prime.dvd_mul`, `Int.gcd`, `ZMod.chineseRemainder` |
| Claim-62.2 | claim | Half the time the root differs from ±x (symmetry lemma) | `Cryptography/Candidates/Concrete.lean` | 3 | core | `uprob_comp_equiv`, `uprob_or_le` |
| Thm-63.10 | theorem | Rabin TDP on Blum integers | `Cryptography/Candidates/Rabin.lean` | 4 | core | Claim-63.1, C5, Thm-58.2, `ZMod.euler_criterion` |
| Claim-63.1 | claim | Blum N: each square has exactly one root in QR_N | `Cryptography/NumberTheory/QuadraticResidues.lean` | 3 | core | `ZMod.exists_sq_eq_neg_one_iff`, Lem-57.1, Thm-59.4 |
| Thm-63.1 | theorem | Universal one-way function (corrected) | `Cryptography/Asymptotic/Universal.lean` | 5 | core | `Turing.timed_universal(_concrete)`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `OneWay.card_log_bits_le` |
| Alg-64.2 | algorithm | f_universal (definition + poly-time computability) | `Cryptography/Asymptotic/Universal.lean` | 4 | core | `Turing.timed_universal_concrete`, `universalBlockBound`, `computesFunInTime_polyBits`, `PolyTimeComputable.pairEncode` |
| Lem-64.3 | lemma | Strong OWF computable in O(n²) (padding) | `Cryptography/Asymptotic/Universal.lean` | 3 | core | `OneWay.pad`, `OneWay.padInverter`, `OneWay.invProb_pad_le`, `FinTM.one_work_tape_binary`, `exists_codeTM` |
| Claim-65.1 | claim | PickG: Pr[code field = ⟨M_g⟩] ≥ 1/n | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_eq_one_div_card`, `OneWay.card_log_bits_le`, `decode_encode_pad` |
| Claim-65.2 | claim | Union bound 1/n³ + (1−1/n) and the contradiction | `Cryptography/Asymptotic/Universal.lean` | 2 | core | `uprob_or_le`, `not_negligible_iff` |
| App-A.1 | fact | Union bound | (cite) | 1 | optional | `uprob_or_le`, `uprob_exists_le` |
| App-A.2 | fact | Markov; Chebyshev's inequality | (cite) | 1 | optional | `HardcoreBit.uprob_mul_le_uexp`, `HardcoreBit.uprob_le_abs_le` |
| Thm-188.7 | theorem | Chernoff bound | — | 4 | deferred | `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (measure-theoretic Hoeffding) |
| Lem-189.8 | lemma | Majority vote (garbled statement) | — | 4 | deferred | — |
| App-A.3 | fact | Pairwise-independent sampling inequality | (cite) | 1 | optional | `HardcoreBit.chebyshev_pairwise(_ident)` |
| Thm-189.9 | theorem | Cauchy–Schwarz | (cite) | 1 | optional | `Finset.sum_mul_sq_le_sq_mul_sq` |
| Def-191.10 | definition | DP (= P) | (cite) | 1 | optional | `Complexity.P` |
| Def-191.11 | definition | NP (witness relation, \|y\| ≤ p(\|x\|)) | (cite) | 1 | optional | `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le` |
| Def-192.12 | definition | BPP | `Complexity/Randomized/PPT.lean` | 2 | deferred | — |

---

## 2. Statements, existing Lean, bridges, and text issues (one entry per item)

Full paths of the existing declarations cited below:

* `Turing.FinTM`, `Turing.FinTM.ComputesInTime`, `.ComputesFunInTime`, `.Computes`, `.ComputesInTime.mono`, `.computesInTime_iff` — `TCSlib/Complexity/TuringMachine/Finite.lean`.
* `Complexity.PolyTimeComputable`, `Complexity.PolyBound`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `.output_length_le` — `TCSlib/Complexity/ClassNP/PolyTime.lean`.
* `Complexity.PolyTimeComputable.pairEncode`, `.pairMapSnd`, `.append`, `Complexity.polyTimeComputable_{const,prepend,unary,polyUnary,pairFstD,pairSndD,pairConcat,pairSwap,ite,and,lenLe,lenEq,of_linear}`, `Complexity.pairFstD`, `Complexity.pairSndD`, `Complexity.pairMapSnd` — `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`.
* `Complexity.mem_P_iff_polyTimeComputable`, `preimage_mem_P`, `mem_P_of_test`, `test_of_mem_P`, `inter_mem_P`, `union_mem_P` — `TCSlib/Complexity/ClassNP/PClosure.lean`.
* `Complexity.P`, `Complexity.DTIME`, `Turing.FinTM.DecidesInTime` — `TCSlib/Complexity/ClassP/{P,DTIME}.lean`.
* `Complexity.NP`, `Complexity.P_subset_NP`, `Complexity.mem_NP_iff_exists_length_le` — `TCSlib/Complexity/ClassNP/NP.lean`.
* `Turing.FinTM.DecidesWithAdviceInTime`, `Complexity.DTIMEAdvice`, `Complexity.PAdvicePoly`, `Complexity.P_subset_PAdvicePoly` — `TCSlib/Complexity/CircuitComplexity/Advice.lean`.
* `Turing.pairEncode`, `Turing.pairDecode`, `Turing.pairEncode_injective`, `Turing.length_pairEncode`, `Turing.CodeTM`, `Turing.CodeTM.toFinTM`, `Turing.CodeTM.serialize`, `Turing.MachineCode` (`encode`, `decode`, `decode_encode_pad`), `Turing.MachineCode.decode_encode`, `Turing.EffectiveMachineCode` (`canonizer`, `canonizerTime`, `canonizer_computes`), `Turing.exists_codeTM`, `Turing.length_bits_le_self` — `TCSlib/Complexity/TuringMachine/Encoding.lean`.
* `Turing.exists_effectiveMachineCode` — `TCSlib/Complexity/TuringMachine/MathlibBridge.lean:1099`.
* `Turing.universal`, `Turing.timed_universal`, `Turing.timed_universal_concrete` — `TCSlib/Complexity/TuringMachine/Universal.lean`; `Turing.universalBlockBound` (= `3·|serialize| + 5·(numStates+1) + 20`) — `TCSlib/Complexity/TuringMachine/UniversalBlock.lean:750`.
* `Turing.FinTM.one_work_tape_binary` (`M.ComputesFunInTime f T → ∃ M' c, M'.k = 1 ∧ M'.ComputesFunInTime f (fun n => c*(T n+1)^2)`) — `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:965`.
* `Turing.FinTM.computesFunInTime_{id,const,ifEq,comp}`, `Turing.FinTM.exists_comp_on_image`, `exists_comp_partial`, `exists_cond` — `TCSlib/Complexity/TuringMachine/Composition.lean`.
* `Turing.FinTM.computesFunInTime_cond` — `TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:711`.
* `Turing.FinTM.exists_loopTM`, `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM` — `TCSlib/Complexity/TuringMachine/Build/Loop.lean` (lines 2519, 2633, 5508, 5645, 5691).
* `Turing.FinTM.computesFunInTime_{prepend,lengthBits,polyUnary,polyBits,pairEncodeFixed,pairFst,pairSnd,pairValid,pairConcat,pairDup,pairMapSnd,pairLenCheck,stripLast,splitSolve,incFixed,splitSolveWith,unaryToken,appendBit}` — `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
* `Complexity.HALT_not_computable` — `TCSlib/Complexity/Uncomputability/Halting.lean:194`; `Complexity.P_ssubset_EXP`, `Complexity.P_ne_EXP` — `TCSlib/Complexity/TimeHierarchy/Separation.lean`; `Complexity.SAT_NPComplete`, `Complexity.SAT3_NPComplete` — `TCSlib/Complexity/CookLevin/Hardness.lean`.
* `TCSlib.Cryptography.Negligible`, `Noticeable`, `Negligible.{mono,add,mul,mul_pow,const_mul}`, `negligible_two_pow_neg`, `Noticeable.not_negligible`, `not_negligible_iff`, `not_negligible_sub`, `exists_not_negligible_not_noticeable` — `TCSlib/Cryptography/Foundations/Negligible.lean`.
* `TCSlib.Cryptography.uprob`, `uexp`, `uprob_eq_card_filter`, `uprob_eq_uexp`, `uprob_nonneg`, `uprob_le_one`, `uprob_true`, `uprob_false`, `uprob_not`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `half_le_uprob_good`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` — `TCSlib/Cryptography/Foundations/Probability.lean`.
* `TCSlib.Cryptography.invProb`, `predProb`, `acceptProb`, `distAdv`, `acceptProb_comp_equiv`, `uprob_comp_eq_sum_map`, `distAdv_le_statDist` — `TCSlib/Cryptography/Foundations/Experiments.lean`.
* `TCSlib.Cryptography.OneWay.{uprob_congr,uexp_mono,uexp_add,uexp_const_mul,uexp_const,uexp_indicator,uprob_and_le_mul,sum_uprob_eq_card_mul,uprob_pi_forall,uprob_update,uprob_eq_one_div_card}` — `TCSlib/Cryptography/OneWayFunctions/Basic.lean`.
* `TCSlib.Cryptography.OneWay.{prodFun,yaoTry,yaoInverter,yaoTryProb,yaoBad,yaoInverter_spec,prodFun_update,invProb_prodFun_le,one_sub_invProb_yaoInverter_le,yao_amplification,yao_amplification_exp}` — `TCSlib/Cryptography/OneWayFunctions/Amplification.lean`.
* `TCSlib.Cryptography.OneWay.{pad,padInverter,invProb_pad_le,tableInverter,invProb_tableInverter,card_log_bits_le,exists_inverter_log_output}` — `TCSlib/Cryptography/OneWayFunctions/OutputLength.lean`.
* `TCSlib.Cryptography.OneWay.{patch,patchInverter,invProb_patch_le,invProb_patch_le_of_correction,exists_correction,invProb_update_le}` — `TCSlib/Cryptography/OneWayFunctions/Robustness.lean`.
* `TCSlib.Cryptography.HardcoreBit.{PushesUniform,PushesUniform.uprob_eq,PushesUniform.comp,pushesUniform_equiv,pushesUniform_id,pushesUniform_add_right}` — `TCSlib/Cryptography/HardcoreBit/Basic.lean`; `TCSlib.Cryptography.HardcoreBit.{uprob_mul_le_uexp,uprob_le_abs_le,chebyshev_pairwise,chebyshev_pairwise_ident}` — `TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean`.
* `RSA.{rsa_core,rsa_zmod_of_factor,rsa_zmod_p,rsa_zmod_q,rsa_crt,rsa_crt_pow,PublicKey,SecretKey,encrypt,decrypt,rsa_correctness}`, `TimeM` — `TCSlib/Cryptography/RSA.lean` (legacy; no policy header; `SecretKey` carries `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`).
* Mathlib: `Nat.xgcd`, `Nat.gcdA`, `Nat.gcdB`, `Nat.gcd_eq_gcd_ab`, `Nat.exists_mul_emod_eq_gcd`, `Nat.exists_mul_emod_eq_one_of_coprime` (`Data/Int/GCD.lean`); `Nat.gcd_rec` (Lean core `Init/Data/Nat/Gcd.lean`); `ZMod.inv` (defined through `Nat.gcdA`), `ZMod.mul_inv_eq_gcd`, `ZMod.unitOfCoprime`, `ZMod.unitsEquivCoprime`, `ZMod.chineseRemainder : ZMod (m*n) ≃+* ZMod m × ZMod n` (`Data/ZMod/Basic.lean`); `ZMod.pow_totient`, `Nat.ModEq.pow_totient`, `ZMod.pow_card_sub_one_eq_one`, `ZMod.card_units`, `FiniteField.pow_dichotomy`, `FiniteField.unit_isSquare_iff` (`FieldTheory/Finite/Basic.lean`); `ZMod.card_units_eq_totient`, `Nat.totient_prime`, `Nat.totient_mul`, `Nat.totient_eq_card_coprime` (`Data/Nat/Totient.lean`); `Nat.coprime_primes`, `Nat.Prime.dvd_mul`, `Nat.decidablePrime` (`Data/Nat/Prime/{Basic,Defs}.lean`); `Nat.primeCounting`, `Nat.primeCounting'`, `Nat.primesBelow`, `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting'_add_le` (upper bound only) (`NumberTheory/PrimeCounting.lean`, `NumberTheory/SmoothNumbers.lean`); `Nat.exists_prime_lt_and_le_two_mul`, `Nat.centralBinom_le_of_no_bertrand_prime` (`NumberTheory/Bertrand.lean`); `Nat.four_pow_lt_mul_centralBinom`, `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.centralBinom_eq_two_mul_choose` (`Data/Nat/Choose/Central.lean`); `Nat.factorization_choose_le_log`, `Nat.pow_factorization_choose_le`, `Nat.factorization_choose_le_one`, `Nat.prod_pow_factorization_choose`, `Nat.prod_pow_factorization_centralBinom` (`Data/Nat/Choose/Factorization.lean`); `primorial_le_4_pow` (`NumberTheory/Primorial.lean`); `ZMod.euler_criterion`, `ZMod.euler_criterion_units`, `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.exists_sq_eq_neg_one_iff`, `legendreSym.card_sqrts` (`NumberTheory/LegendreSymbol/Basic.lean`); `sq_eq_sq_iff_eq_or_eq_neg`, `Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff` (`Algebra/Ring/Commute.lean`); `IsCyclic.exists_generator`, `isCyclic_of_prime_card`, `orderOf_eq_card_of_forall_mem_zpowers`, `zmodCyclicMulEquiv` (`GroupTheory/SpecificGroups/Cyclic.lean`); `orderOf_dvd_card`, `pow_card_eq_one` (`GroupTheory/OrderOfElement.lean`); `instance : IsCyclic (ZMod p)ˣ` (`RingTheory/ZMod/UnitsCyclic.lean`, `RingTheory/IntegralDomain.lean`); `Nat.chineseRemainder` (`Data/Nat/ModEq.lean`), `Nat.chineseRemainderOfList`, `Nat.chineseRemainderOfFinset` (`Data/Nat/ChineseRemainder.lean`); `Nat.ProbablePrime`, `Nat.FermatPsp`, `Nat.exists_infinite_pseudoprimes` (`NumberTheory/FermatPsp.lean`); `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` (`Probability/Moments/SubGaussian.lean`); `Finset.sum_mul_sq_le_sq_mul_sq` (`Algebra/Order/BigOperators/Ring/Finset.lean`); `Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`. **Absent from this Mathlib revision:** Miller–Rabin / strong pseudoprimes, any lower bound on `π(x)`, `ZMod.prodEquivPi`, `Nat.powMod`, a density bound for primes `≡ 3 (mod 4)`, a lower bound on `φ(m)/m`.

### §2.1 Efficient computation and adversaries

**Def-21.1 (Algorithm).** An algorithm is a deterministic Turing machine with input and output over `{0,1}`. — Existing: `Turing.FinTM Bool` (bundled finite multi-tape TM, append-only output tape). No work; cite. Deviation already recorded in the complexity library (multi-tape, binary alphabet).

**Def-21.2 (Running time, polynomial time).** `A` runs in time `T` if for all `x`, `A(x)` halts within `T(|x|)` steps; polynomial time if `T(n) = n^c` for some `c`. — Existing: `FinTM.ComputesFunInTime f T`, `Complexity.PolyTimeComputable f` (bound `C·(n+1)^c`), `Complexity.P` (`n^c + 1`). The text's literal `n^c` is degenerate at `n = 0` (`Complexity.DTIME_eq_empty_of_exists_zero`); the campaign uses `C·(n+1)^c` everywhere (brief §2). Cite.

**Def-21.3 (Deterministic computation).** `A` computes `f` if for all `x`, `A(x)` outputs `f(x)`. — Existing: `FinTM.ComputesFunInTime`, `FinTM.Computes`. Cite.

**Rem-22.1 (§2.1.1 hard problems).** (i) Halting is uncomputable; (ii) the time hierarchy gives functions computable in exponential but not polynomial time; (iii) SAT is NP-complete, conjectured not in P. — Existing: `Complexity.HALT_not_computable` (relative to an `EffectiveMachineCode`), `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete`. Cite only.

**Def-23.4 (PPT).** A randomized algorithm is a TM with an extra random tape of uniform independent bits. **Formal (D3):** a structure with a `FinTM Bool` `M`, coin-length constants `(Cr, cr)` and time constants `(Ct, ct)` such that for every `x : List Bool` and every `r : Fin (Cr·(|x|+1)^cr) → Bool`, `M` halts on `pairEncode x (ofFn r)` within `Ct·(|x|+1)^ct` steps; `M.run x r` is its completed output; `M(x)` is the sampler `r ↦ M.run x r` (a `(Fin ℓ → Bool) → List Bool`, directly usable by `uprob`). Deviation: coins are an input component (reading a random tape sequentially is a bounded-cost simulation), and the coin length is an explicit polynomial. — Existing pattern: `FinTM.DecidesWithAdviceInTime` (pair input, time in `|x|`). New file `TCSlib/Complexity/Randomized/PPT.lean`. Difficulty 3 (definition + run/sampler API + basic lemmas `run_eq_of_computesInTime`, determinism via `ComputesInTime.output_unique`).

**Def-23.5 (Running time, randomized).** `A` runs in time `T` if for all `x` and *every* random tape, `A(x)` halts within `T(|x|)` steps (worst case over coins). — Folded into Def-23.4's time clause (the clause quantifies over all `r`). Expected polynomial time is not formalized (plan D8).

**Def-24.6 (PPT computes f).** `A` computes `f` if for all `x`, `A(x) = f(x)` with probability 1 over the random tape. **Formal:** `∀ x r, M.run x r = f x`. Lemma (C7): on a finite uniform coin space `uprob (fun r => M.run x r = f x) = 1 ↔ ∀ r, M.run x r = f x`, so the formal clause is the text's. Difficulty 2. Consequence: `PPT.Computes f → PolyTimeComputable (fun x => f x)`-style bridge is *not* automatic (the machine reads coins); provide `PolyTimeComputable_of_PPTComputes` by hard-wiring the all-zero coin string (`computesFunInTime_pairEncodeFixed`-style prepend of coins is on the wrong side — needs a `pairMapSnd`/`append` closure: `x ↦ pairEncode x 0^{ℓ(|x|)}` is `PolyTimeComputable.pairEncode` of `id` and `polyUnary`-then-zeros). Difficulty 2.

**Rem-24.2 (majority amplification).** If a polynomial-time randomized `A` computes `f` with probability `≥ 1/2 + 1/p(n)` on every input, then running `A` `ℓ(n)` times and taking the most frequent output computes `f` with probability `≥ 1 − 2^{−n}` (Chernoff). — Deferred: needs Thm-188.7/Lem-189.8 and Repetition; nothing in Chapters 2–4 core depends on it (Garg's concrete majority arguments use Chebyshev for pairwise independence). Difficulty 4.

**Def-24.7 (Efficient private-key encryption).** `(Gen, Enc, Dec)` are PPTs; `Gen(1^n)` outputs a key `k`; `Enc_k(m)` for `m ∈ {0,1}^n` outputs `c`; `Dec_k(c)` outputs `m ∈ {0,1}^n ∪ {⊥}`; for all `n` and `m ∈ {0,1}^n`, `Pr[k ← Gen(1^n) : Dec_k(Enc_k(m)) = m] = 1` (over the coins of `Gen` and `Enc`). **Formal:** messages `Fin n → Bool`; keys/ciphertexts `List Bool`; `Enc`/`Dec` receive `pairEncode 1^n (pairEncode k m)` (so their polynomial bounds are in `n`; the text says "polynomial in the size of their inputs" — with `|k| ≤ poly(n)` the two readings agree); `Dec` output decoded as an `n`-bit string or `⊥`. Correctness quantifies over all coin strings (Def-24.6 reading). Asymptotic/Encryption.lean (plan). Difficulty 2. Depends on Def-23.4.

**Def-26.8 (nuPPT).** A sequence `{A_i}` of probabilistic machines with `|A_i| < d(i)` and running time `< d(i)` for a polynomial `d`; `A(x)` runs `A_{|x|}(x)`. Equivalently (text): a uniform PPT with a polynomial-length advice string per input length. **Formal (D4):** a PPT `M` plus `α : ℕ → List Bool` with `|α n| ≤ Ca·(n+1)^ca`, run on `pairEncode (pairEncode x (α |x|)) r`, time `Ct·(|x|+1)^ct` for every `r`. Deviation: the machine-sequence formulation is not formalized. — Existing pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly`. New file `TCSlib/Complexity/Randomized/NonUniform.lean`. Difficulty 3. Note the standing convention "any adversarial algorithm is implicitly nuPPT" (p. 26) governs Defs 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and Assumptions 30.1, 52.2, 53.1.

**Rem-26.2 (equivalence of nuPPT formulations).** Deferred (difficulty 4): `⇒` would use `Turing.timed_universal` with the description `A_{|x|}` as advice; `⇐` hard-wires the advice. Not needed downstream under D4.

**Claim-26.3 (closure calculus; implicit throughout).** The class of nuPPT samplers is closed under: (a) post-composition with `PolyTimeComputable` maps (decoding, projections); (b) pre-composition/pairing with `PolyTimeComputable` maps of the input and of computed strings; (c) using fresh coin segments as uniform strings of polynomial length and as uniform elements of `Fin 2^k`; (d) hard-wiring advice; (e) `T(n)` fresh-coin calls of a nuPPT with "first success" (loop) or concatenated outputs; (f) Boolean tests (equality of strings, `f(z) = y`). — Existing building blocks: `Turing.FinTM.computesFunInTime_comp` (budget `c·(T₁ n + T₂ (T₁ n) + 1)`, needs `Monotone T₂`), `computesFunInTime_cond`, `exists_loopFindTM`/`exists_emitLoopTM` (loop with fuel `R |x|` and per-round body contract), `exists_installCallTM`/`exists_emitCallTM` (callable module with clean seams), `PolyTimeComputable.comp/.pairEncode/.append`, `polyTimeComputable_ite/and/lenEq`, `pairFstD/pairSndD`. The plan's `Closure.lean`/`Repetition.lean` are this item; difficulty 5 for (e) (the plan's named risk), 3 for (a)–(d),(f). Every theorem below depends on it.

### §2.2 One-way functions

**Def-26.1 (Worst-case OWF).** `f : {0,1}* → {0,1}*` is worst-case one-way if (1) some PPT computes `f` on all inputs (equivalently `PolyTimeComputable f`, by Def-24.6 and C7), and (2) there is no nuPPT `A` with `∀ x, Pr_r[f(A(f x; r)) = f x] = 1`. **Formal (D5/Q2):** for a family `f n : (Fin (ℓ n) → Bool) → List Bool`: `¬ ∃ A : NUPPT, ∀ n x, ∀ r, decode_n (A.run (pairEncode 1^n (f n x)) r) is some x' with f n x' = f n x`. Note the text gives `A` only `f(x)`; D5 adds `1^n`. Difficulty 2. Nothing downstream uses it except Rem-27.1.

**Rem-27.1.** "Assuming NP ⊄ BPP, worst-case one-way functions exist; in fact the two are equivalent (show this!)." Deferred (difficulty 5): requires Def-192.12 (BPP) and, with nuPPT adversaries (§2.1.3), the correct class is non-uniform (`NP ⊄ BPP/poly`); the text mixes uniform BPP with non-uniform inverters. Recorded as a text issue; nothing downstream.

**Def-27.2 (Negligible).** `ε` is negligible if `∀ c ∃ n₀ ∀ n > n₀, ε(n) ≤ 1/n^c`; non-negligible if `∃ c` with `ε(n_i) > 1/n_i^c` for infinitely many `n_i`. — Existing: `TCSlib.Cryptography.Negligible` (`∀ c ∃ n₀ ∀ n ≥ n₀, |μ n| < 1/n^c`; equivalent on `[0,1]`-valued functions by shifting `c`), `not_negligible_iff` (`≥` form), `negligible_two_pow_neg` (the example `2^{−n}`), `Negligible.add/mul/mul_pow/const_mul`. Optional one-line bridges `negligible_iff_le`, `not_negligible_iff_lt` if a statement needs the text's inequalities verbatim. The example `n^{−log log n}` is optional.

**Def-27.3 (Strong OWF).** (1) easy: as Def-26.1(1); (2) for every nuPPT `A` there is a negligible `ε` with, for all `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ ε(n)`. **Formal:** `StrongOWF f ℓ := PolyTimeComputable-easy ∧ ∀ A : NUPPT, Negligible (fun n => invProb (f n) (A.inverter n))` where `A.inverter n : List Bool → coins → (Fin (ℓ n) → Bool)` decodes `A`'s output as an `ℓ n`-bit string (wrong length ↦ a fixed default that only lowers the probability — D5 Deviation). — Existing: `invProb` (exactly the per-`n` experiment, with `1^n` "implicit in the fixed types"). Difficulty 3 (definition + the two decoding lemmas + the lemma that the coin space of the experiment is the nuPPT's coin type). Asymptotic/OneWay.lean.

**Rem-28.1 ((t,s,ε)-one-wayness).** The concrete layer's `invProb f A ≤ ε` at one `n` for an adversary of a given size/time *is* this notion; no new declaration. Cite.

**Def-28.4 (Weak OWF).** (1) easy; (2) there is a polynomial `q` such that for every nuPPT `A` and all sufficiently large `n`, `Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y] ≤ 1 − 1/q(n)`. **Formal:** `∃ C c, 0 < C ∧ ∀ A, ∃ n₀, ∀ n ≥ n₀, invProb (f n) (A.inverter n) ≤ 1 − 1/(C·(n+1)^c)`. Difficulty 2.

### §2.3 Multiplication, primes, factoring

**Def-29.1 (f_mult).** `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`, else `x·y`, on pairs of `n`-bit numbers (input length `2n`, output in binary). **Formal:** `fmult n : (Fin n → Bool) × (Fin n → Bool) → ℕ` (then `Nat.bits`), or on `Fin (2^n) × Fin (2^n)`. Deviation: the text's `ℕ² → ℕ` "picked uniformly from ℕ²" means `n`-bit numbers. Candidates/Factoring.lean. Difficulty 1. The "easy to compute" clause needs binary multiplication (Q1 hypothesis).

**Rem-29.2 (f_mult not strongly one-way).** The adversary `A(z) = (2, z/2)` for even `z` (else `(0,0)`) inverts with probability `≥ 3/4`. **Text issue:** `z/2` has up to `2n − 1` bits, so `(2, z/2)` is a preimage of a *different input length*; with inputs fixed to `n` bits (D5) this attack is invalid, and no typed attack is given. Deferred (difficulty 2 for the untyped reading, which is outside the campaign's model). Nothing depends on it.

**Def-29.3 (Π_n).** `Π_n = {q | q < 2^n ∧ q prime}`; the uniform distribution on it. **Formal:** `Primes n := {p : Fin (2^n) // (p : ℕ).Prime}` (a `Fintype`), `uprob` over it; cardinality `= Nat.primeCounting' (2^n) = #(Nat.primesBelow (2^n))` (`Nat.primesBelow_card_eq_primeCounting'`). Chebyshev.lean. Difficulty 1. Note `Π_n` contains `2` and small primes, and the text's later "`n`-bit primes" is loose; use `Π_n` consistently (Deviation noted at Thm-51.1).

**Asm-30.1 (Factoring).** For every nuPPT `A` there is a negligible `ε` with `Pr[p ← Π_n; q ← Π_n; N ← pq : A(N) ∈ {p, q}] < ε(n)` for all `n`. **Formal:** `FactoringAssumption := ∀ A : NUPPT, Negligible (fun n => uprob (fun (z : Primes n × Primes n × coins) => decodeℕ (A.run (pairEncode 1^n (bits (p·q))) r) ∈ {p, q}))`. Deviations: `A` receives `1^n` (the text passes only `N`, whose length is `≤ 2n`); `<` vs `≤` immaterial; `p = q` and `p = 2` are allowed by the text (probability `≤ 2n/2^n` by Claim-33.1). Difficulty 2.

**Thm-31.3 (Chebyshev).** For real `x > 1`, `π(x) > x/(2 log₂ x)`. Proof: `X = C(2x, x) = ∏_{p < 2x} p^{ν_p(X)} ≥ 2^x` and `p^{ν_p(X)} ≤ 2x`, so `2^x ≤ (2x)^{π(2x)}`, i.e. `π(2x) ≥ x/log₂(2x) = (1/2)·2x/log₂(2x)`; odd arguments via `π(2x) = π(2x−1)` (`2x` composite for `x ≥ 2`) and monotonicity of `t/log t`. — Existing Mathlib: `Nat.four_pow_lt_mul_centralBinom` (`4^n < n·centralBinom n`, `n ≥ 4`), `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.prod_pow_factorization_centralBinom`, `Nat.pow_factorization_choose_le` (`p^{ν_p(C(n,k))} ≤ n`), `Nat.primesBelow_card_eq_primeCounting'`, `Nat.primeCounting`. No lower bound on `π` exists in Mathlib. **Formal statement recommendation:** prove the integer core `2^x ≤ (2x)^{π(2x)}` for `x ≥ 1` (hence `x ≤ π(2x)·⌈log₂(2x)⌉`), derive Claim-33.1 from it, and state the real-logarithm form of the theorem as a corollary (`Real.logb`). Difficulty 4 (3 for the integer core). Text issues: `log` means `log₂`; "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`, strict for `x ≥ 2`); the odd-case step uses `t/log t` increasing for `t ≥ 3`.

**Claim-32.4.** `log(2x)/log p > ν_p(X)`, i.e. `p^{ν_p(X)} < 2x`. **Text issue:** strictness fails (`x = 1, p = 2`); the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is `Nat.pow_factorization_choose_le` (with `Nat.factorization_choose_le_log`). Cite.

**Claim-33.1 (prime density).** For `n ≥ 1`, `|Π_n| ≥ 2^n/(2n)`, i.e. a uniform `x < 2^n` is prime with probability `≥ 1/(2n)`; consequently a uniform pair is a prime pair with probability `≥ 1/(4n²)` (independence: `uprob_prod`/`uprob_pi_forall`). From Thm-31.3's integer core at `x = 2^{n−1}`: `2^{n−1} ≤ π(2^n)·n`. Chebyshev.lean. Difficulty 3. **Text issue:** §2.6.6 (p. 50) claims the probability "exceeds `(2^n/n)/2^n = 1/n`", inconsistent with the `1/(2n)` of §2.3.2 and with Thm 31.3.

**Rem-33.2 (primality testing in P).** The text uses "primality testing can be done in polynomial time" (AKS, [aks04]) in Alg-33.6/37.4 and SamplePrime. **Formal:** hypothesis `PrimalityFP : PolyTimeComputable (fun w => [decide (Nat.ofBits w).Prime])` in the Q1 bundle (`Nat.decidablePrime` gives the mathematical test; its machine is not available). Deferred (difficulty 5 to discharge). Thms 33.5/36.3 are formalized without it.

**Thm-33.5.** Factoring assumption ⟹ `f_mult` is weakly one-way: with `q(2n) := 8n²`, for every nuPPT `A` and all large `n`, `Pr[x, y ← {0,1}^n : f_mult(A(1^{2n}, xy)) = xy] ≤ 1 − 1/(8n²)`. **Reduction (one-call variant `A″`):** `A″(1^n, N) := fst(A(1^{2n}, N))`. **Concrete lemma (C1):** if `S` is the success event of `A` on uniform `(x, y)` and `E` = "both prime" with `Pr[E] ≥ δ := 1/(4n²)`, then `Pr[S | E] ≥ 1 − (1 − Pr[S])/δ`; with `1 − Pr[S] ≤ 1/(8n²)` this gives `Pr[S | E] ≥ 1/2` (the text's `1/(8n²)` is weaker than what the argument yields). The conditional distribution of `(x, y)` given `E` is uniform on `Π_n × Π_n` (the factoring distribution), and on `E` a successful answer is a factor (Claim-34.1). Asymptotic: `A″` is `A` with a `PolyTimeComputable` projection (Claim-26.3(a)); `≥ 1/2` infinitely often contradicts negligibility (`not_negligible_iff`). "Easy to compute" needs Q1 (`mul`). — Existing: `uprob_and_le_mul`, `uprob_mono`, `uprob_fst`, `uprob_prod`, `uprob_pi_forall`, `not_negligible_iff`. Difficulty 3. Text issues: Alg 33.6 line 7 writes `A(1^n, z′)` (should be `1^{2n}`); the formal theorem uses `A″`, as the text itself suggests.

**Alg-33.6 (A′ / A″).** `A′(z)`: sample `x, y ← {0,1}^n`; if both prime set `z′ := z` else `z′ := xy`; `w ← A(1^{2n}, z′)`; return `w` if both prime. `A″`: always `z′ := z`, always output `w` (no primality test). Formalize `A″` only (plan). Difficulty 1.

**Claim-34.1 (unique factorization step).** If `p, q` are primes and `x′, y′ < 2^n` with `f_mult(x′, y′) = pq`, then `x′ ∈ {p, q}` (and `y′` is the other). Proof: `pq ≠ 1` so `x′, y′ ≠ 1` and `x′y′ = pq`; `x′ ≠ 0`; `Nat.Prime.dvd_mul`, `Nat.Prime.eq_one_or_self_of_dvd`. Factoring.lean. Difficulty 2.

### §2.4 Hardness amplification

**Thm-35.1 (weak → strong).** For any weak OWF `f` (with polynomial `q`) there is a polynomial `m` (the proof takes `m(n) = 2n·q(n)`) such that `f′(x₁, …, x_{m(n)}) = (f(x₁), …, f(x_{m(n)}))` on `({0,1}^n)^{m(n)}` is strongly one-way (security parameter `n`, input length `n·m(n)`). — **Existing (concrete, complete):** `OneWay.prodFun f q` (= `f′`), `yaoTry` (= Alg 38.5's `A₀`), `yaoInverter f B T` (= the `T`-fold repetition `A`), `yaoBad` (= complement of `G_n`), `invProb_prodFun_le` (Claim-39.2), `one_sub_invProb_yaoInverter_le` (Claim-39.1), `yao_amplification` (parametric in `a, θ, T`: `(1−a)^q + qθ < μ ⟹ 1 − a − (1−θ)^T ≤ invProb f (yaoInverter f B T)`). **Bridge:** (i) Claim-38.2 instantiates PS10's parameters; (ii) `yaoInverter f (A′ n) T` is a nuPPT: `T = 2n m² p(n)` fresh-coin calls of `A′` (Claim-26.3(e)), `m − 1` evaluations of `f` per call by `f`'s machine (loop with emitted chunks, `exists_emitLoopTM`), uniform `i : Fin m` from coins (Q7: take `m` a power of two), the test `f(z_i) = y` (equality machine), decoding of `A′`'s output tuple; (iii) from "`f′` not strong" obtain `c` and infinitely many `n` with `μ_n ≥ 1/n^c` (`not_negligible_iff`), conclude `invProb f (…) > 1 − 1/q(n)` infinitely often, contradicting Def-28.4; (iv) lengths: `A′` receives `1^{n·m(n)}`; the tuple `(Fin m → Fin n → Bool)` is encoded as the `nm`-bit concatenation (`Fin.appendEquiv`-style equivalence, cf. `owpBitsEquiv` in `Pseudorandom/GeneratorFromPermutation.lean`). Difficulty 4. Asymptotic/OneWay.lean. Text issues (proof): "For each `j ∈ [1, n]`" should be `[1, m]`; the displayed chain with the factor `m` is garbled — the concrete `invProb_prodFun_le` is the correct computation.

**Thm-35.2 (simple security reduction).** If `f` is a strong OWF then `g(x, y) = (f(x), f(y))` (input length `2n`) is a strong OWF. **Concrete lemma (C2, new):** `invProb (pairFun f) A′ ≤ invProb f (pairInverter f A′)` with `pairInverter f A′ u (y, r) := (A′ (u, f y) r).1` — proof exactly as `OneWay.invProb_pad_le` (`uprob_comp_equiv (Equiv.prodAssoc)`, `uprob_mono`); the text's test "`f(a) = u`" is unnecessary for the inequality. Asymptotic: the inverter samples `y`, evaluates `f`, calls `A′`, projects (Claim-26.3(a)–(c)); `1/p(2n)` infinitely often ⟹ non-negligible. Difficulty 3 (1 concrete + 2 bridge). Note `g = prodFun f 2` up to the equivalence `Fin 2 → α ≃ α × α`, so Thm-35.1's machinery also applies but is overkill.

**Thm-36.3 (f_mult amplified).** Factoring assumption and `m_n = 4n³` ⟹ `f′((x₁,y₁), …, (x_m, y_m)) = (f_mult(x₁,y₁), …)` on `({0,1}^{2n})^{m_n}` is strongly one-way. **Reduction (random-planting, one-call; the text's exercise):** `A″(1^n, N)`: sample `i ← [m]` and fresh pairs `(x_j, y_j)` for `j ≠ i`; put `z_i := N`, `z_j := x_j y_j`; call `A(1^{n′}, z⃗)`; output the first component of its `i`-th answer. **Concrete lemma (C3, new; mirror of `invProb_prodFun_le`'s proof with bad set = "pair not both prime"):** `Pr[A″ factors] ≥ (invProb (prodFun fmult m) A − (1 − δ)^m)/m` where `δ = Pr[pair both prime] ≥ 1/(4n²)`: by `uprob_update` planting at position `i` equals the uniform experiment conditioned on pair `i` prime; `sum_uprob_eq_card_mul` makes `i` uniform; `uprob_pi_forall` bounds `Pr[no pair prime] = (1 − δ)^m`; Claim-34.1 turns an inverse into a factor. Then Claim-36.2 and `μ ≥ 1/p(n′)` infinitely often give success `≥ 1/(2 m p(n′))` infinitely often. Deviation: no primality test, planting at a uniform position (instead of "the first prime pair"). Difficulty 3. Depends on Claim-36.2, Claim-34.1, Claim-33.1, Claim-26.3, Q1. Text issues: Alg 37.4 "Output `x′_i`" should output a factor and check it; `n′ = 2n·m(n) = 8n⁴`.

**Claim-36.2.** `(1 − 1/(4n²))^{4n³} = ((1 − 1/(4n²))^{4n²})^n ≤ e^{−n}` (and `e^{−n} ≤ 2^{−n}`, negligible by `negligible_two_pow_neg`). Pattern: `yao_amplification_exp` (`Real.one_sub_le_exp_neg`, `Real.exp_nat_mul`). Concrete.lean. Difficulty 1.

**Alg-37.4.** The random-planting `A′` (above). Difficulty 1.

**Alg-38.5 (A₀ and A).** `A₀(f, y)`: pick `i ← [m]`, fresh `x_j`, `y_j = f(x_j)` for `j ≠ i`, `y_i = y`, call `A′`, output `z_i` if `f(z_i) = y` else `⊥`; `A` runs `A₀` `2nm²p(n)` times and returns the first non-`⊥` answer. — Existing: `OneWay.yaoTry` (coins `(i, xs, r)`), `OneWay.yaoInverter f B T` (first success via `List.foldr`), `yaoInverter_spec`. Cite.

**Claim-38.2 (parameter instantiation).** With `m := 2n q(n)` (or the next power of two, Q7), `p(n) := p′(n·m)`, `a := 1/(2q(n))`, `θ := 1/(2m²p(n))`, `T := 2nm²p(n)`: for all large `n`, `(1 − a)^m + mθ ≤ e^{−n} + 1/(2mp(n)) < 1/p(n)` and `1 − a − (1 − θ)^T ≥ 1 − 1/(2q(n)) − e^{−n} > 1 − 1/q(n)`; hence `yao_amplification` (with `[NeZero m]`, `[Inhabited (Fin n → Bool)]`) yields `invProb f (yaoInverter …) > 1 − 1/q(n)`. Pure real arithmetic; Asymptotic/OneWay.lean. Difficulty 2.

**Claim-39.1.** `Pr[A fails | x ∈ G_n] ≤ (1 − 1/(2m²p(n)))^{2m²np(n)} ≈ e^{−n}`. — Existing: the `(1 − θ)^T` term of `OneWay.one_sub_invProb_yaoInverter_le`. Cite.

**Claim-39.2 (many good elements).** `|G_n| ≥ 2^n(1 − 1/(2q(n)))`, else `A′` would invert `f′` with probability `< 1/(2p(n)) + e^{−n} < 1/p(n)`. — Existing: `OneWay.invProb_prodFun_le` (`μ ≤ (1 − Pr[S])^q + qθ Pr[S]`), used contrapositively inside `yao_amplification`. Cite.

### §2.5 Collections

**Def-41.1 (Collection of OWFs).** `F = {f_i : D_i → R_i}_{i ∈ I}` with: (1) a PPT `Gen` with `Gen(1^n) ∈ I`; (2) a PPT that on input `i` returns a uniformly random element of `D_i`; (3) a PPT computing `f_i(x)` from `(i, x)`; (4) for every nuPPT `A` there is a negligible `ε` with `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y] ≤ ε(n)`. **Formal design (Collections.lean):** a structure `OWCollection` with index strings `i : List Bool`, for each `i` a `Fintype` domain `D i` with an injective encoding `encD i : D i → List Bool` and a total decoder (wrong strings ↦ failure), `f i : D i → List Bool`; `Gen : PPT` (sampler of indices, coin length polynomial in `n`); `Sample : PPT` on input `i` with `PushesUniform (fun r => decode (Sample.run i r))` onto `D i` *or* (Q3) within statistical distance `2^{−n}` of uniform; `Eval : PolyTimeComputable (fun z => f (pairFstD z) (decode (pairSndD z)))`; hardness via a new per-`n` experiment `collInvProb F A n := uprob (fun (r₁, x, ρ) => let i := Gen.run 1^n r₁; f i (decode (A.run (pairEncode 1^n (pairEncode i (f i x))) ρ)) = f i x)` where `x` is uniform in `D i` (a dependent product: use `Σ`-type or the sampler's coins with `PushesUniform`). — Existing: `HardcoreBit.PushesUniform` and `.uprob_eq`, `invProb` (pattern). Difficulty 4 (design-heavy; the dependent-domain probability space is the subtle point — simplest is to define the experiment over `(r₁, r₂, ρ)` with `x := Sample i r₂` and require exact `PushesUniform`, matching the text's "uniformly random element"). Text issues: (4) says "p.p.t. `A`" against the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should read `f_i`; `R_i` is never constrained; "uniformly random element of `D_i`" presupposes `D_i` finite.

**Thm-42.2 (collection ⟺ strong OWF).** (⇐) a strong OWF `f` gives the collection with `Gen(1^n) = 1^n` (index = unary parameter), `D_{1^n} = {0,1}^n`, `f_{1^n} = f n`: difficulty 2 (the text's "`I = {0}`, `D_0 = ℕ`" is sloppy: the domain must depend on `n`; Deviation). (⇒, "left as an exercise") given a collection, `g_n(r₁, r₂) := (i, f_i(x))` with `i = Gen(1^n; r₁)`, `x = Sample(i; r₂)` is a strong OWF with input length `ℓ₁(n) + ℓ₂(n)` (Q2). Proof: `g` is `PolyTimeComputable` from `Gen`, `Sample`, `Eval` (`PolyTimeComputable.comp/.pairEncode`); an inverter `A_g` of `g` gives the collection inverter `A_F(1^n, i, y) := Sample(i; (A_g(1^{ℓ(n)}, pairEncode i y)).2)`: if `g(r₁′, r₂′) = (i, y)` then `Gen(r₁′) = i` and `f_i(Sample(i; r₂′)) = y`; the law of `(i, x)` under uniform `(r₁, r₂)` equals the law in Def-41.1(4) by `PushesUniform.uprob_eq` applied conditionally on `i` (`uprob_prod`). Difficulty 4. Depends on Def-41.1, Def-27.3, Claim-26.3.

### §2.6 Computational number theory

**Fact-42.1.** `(a mod N + b mod N) mod N = (a + b) mod N`, `((a mod N)(b mod N)) mod N = ab mod N`. — `Nat.add_mod`, `Nat.mul_mod`. Cite.

**Alg-43.2 (ExtendedEuclid).** `ExtendedEuclid(a, b)` for `a > b > 0`: if `a mod b = 0` return `(0, 1)`; else `(x, y) ← ExtendedEuclid(b, a mod b)`, return `(y, x − y⌊a/b⌋)`. **Formal:** `extEuclid : ℕ → ℕ → ℤ × ℤ` by well-founded recursion on `b`, plus `extEuclidCalls : ℕ → ℕ → ℕ` (recursive-call count). — Existing: Mathlib `Nat.xgcd`/`Nat.gcdA`/`Nat.gcdB`/`Nat.gcd_eq_gcd_ab` (Bézout, the standard extended Euclid), `ZMod.inv` (computable inverse through `Nat.gcdA`; used by `ZMod.mul_inv_eq_gcd`). The text's variant and its call count are new. Euclid.lean. Difficulty 2.

**Claim-43.3.** If `a > b ≥ 0` and `a < 2^n` then `ExtendedEuclid(a, b)` makes at most `2n` recursive calls. Induction on `n`: if `b < 2^n` the next call is in the hypothesis; if `b ≥ 2^n` then `a mod b < 2^{n+1} − b ≤ 2^n`, so two calls later the hypothesis applies. Difficulty 3. Text issues: case 2 writes `b > 2^n` (should be `≥`); the precondition `b ≥ 0` allows `b = 0`, where the recursion as written swaps arguments once more.

**Claim-44.4.** `gcd(a, b) = gcd(b, a mod b)`. — Lean core `Nat.gcd_rec` with `Nat.gcd_comm`. Cite.

**Claim-44.5 (correctness).** `ExtendedEuclid(a, b) = (x, y) ⟹ ax + by = gcd(a, b)` (strong induction on `b`; the text's regrouping). Difficulty 2. (Mathlib's `Nat.gcd_eq_gcd_ab` is the same statement for `Nat.xgcd`.)

**Rem-43.6.** "Polynomial time in `log a + log b`" at the machine level — deferred (Q1); mathematically Claim-43.3 is the step bound.

**Alg-45.5 (ModularExponentiation).** `r := 1; while x > 0: if x odd then r := r·a mod N; x := ⌊x/2⌋; a := a² mod N; return r`. **Formal:** `modExp a x N` by binary recursion on `x` (`Nat.binaryRec` or strong recursion), with `modExp_eq : N > 0 → modExp a x N = a^x % N` (`Nat.pow_mod`, `Nat.pow_succ`, `Nat.mul_mod`). ModExp.lean. Difficulty 2. No `powMod` exists in this Mathlib revision.

**Thm-45.6.** On `(a, x, N)` with `a ∈ [1, N]`, Alg 45.5 computes `a^x mod N` in time `O(log x · log² N)`. **Formal (optional):** the loop executes at most `⌊log₂ x⌋ + 1` iterations, each with at most two modular multiplications of numbers `< N` (so `≤ 2(⌊log₂ x⌋+1)` multiplications); optionally a `TimeM ℕ` version (`TCSlib/Cryptography/RSA.lean` cost monad) charging `log² N` per multiplication. Machine-level bound deferred (Q1). Difficulty 2. Text issues: the restriction `a ∈ [1, N]` is immaterial; the later remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Alg 45.5 does not have.

**Def-46.7 (Group).** Mathlib `Group`/`CommGroup`. Cite. **Ex-46.1** `(Z_N, +)` = `ZMod N` as `AddCommGroup`. Cite.

**Thm-46.8.** `(Z_N^*, ×)` with `Z_N^* = {x ∈ [1, N−1] | gcd(x, N) = 1}` is a group (closure via Def-46.9/Claim-47.1; inverses via Euclid). — Existing: `(ZMod N)ˣ`, `ZMod.unitsEquivCoprime : (ZMod n)ˣ ≃ {x : ZMod n // Nat.Coprime x.val n}`, `ZMod.unitOfCoprime`, `ZMod.inv_coe_unit`, `ZMod.mul_inv_eq_gcd`. Optional one-line bridge to the text's set (`x.val ∈ [1, N−1]` for `N ≥ 2`). Units.lean. Difficulty 1.

**Def-46.9 (Prime).** `Nat.Prime`. Cite. **Claim-47.1** `p ∣ ab ⟹ p ∣ a ∨ p ∣ b`: `Nat.Prime.dvd_mul`. Cite.

**Claim-47.2 (totient values).** `Φ(p) = p − 1` for prime `p`; `Φ(pq) = (p−1)(q−1)` for distinct primes ("show this by counting"); `|Z_N^*| = Φ(N)`. — `Nat.totient_prime`, `Nat.totient_mul` + `Nat.coprime_primes`, `ZMod.card_units_eq_totient`. Units.lean (one lemma `totient_mul_prime_prime`). Difficulty 1. Text issue: the formula needs `p ≠ q` (`Φ(p²) = p(p−1)`).

**Thm-47.10 (Euler).** `∀ a ∈ Z_N^*, a^{Φ(N)} = 1 mod N`. — `ZMod.pow_totient` (units), `Nat.ModEq.pow_totient`. Cite. **Cor-48.11 (Fermat).** `ZMod.pow_card_sub_one_eq_one`. Cite.

**Cor-48.12.** For `a ∈ Z_N^*`, `a^x ≡ a^{x mod Φ(N)} (mod N)`: write `x = Φ(N)·(x / Φ(N)) + x mod Φ(N)` (`Nat.div_add_mod`) and apply Euler. Units.lean. Difficulty 1 (used by RSA decryption exponent arithmetic). **Rem-48.2** (efficiency "for any `x` given `Φ(N)`") is machine-level: deferred (Q1). **Ex-48.3** (paper-and-pencil example, garbled in the pdftotext): optional `decide`.

**Def-49.1 (L_N, corrected).** For odd `N > 2` write `N − 1 = u·2^j` with `u` odd; `L_N := {α ∈ Z_N | α^{N−1} = 1 ∧ ∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} ∈ {1, −1}}` ("no non-trivial square root of 1 among the intermediate powers"). Primality.lean. Difficulty 2. **Text error:** the text writes "`N = u2^j`" and a condition using `i = j` only, which is vacuous (`α^{u2^{j+1}} = (α^{N−1})² = 1` always and then requires `α^{N−1} = 1`, already assumed).

**Alg-49.13 (Miller–Rabin).** Handle `N = 2` (and even `N`); repeat `t` times: `α ← Z_N`, if `α ∉ L_N` output "composite"; output "prime". **Formal:** a sampler `millerRabin N t : (Fin t → Fin N) → Bool`. Difficulty 2. The membership test "`α ∈ L_N` by repeated squaring with internal checks" is Alg-45.5 instrumented (math: trivial; machine: Q1).

**Thm-49.14.** If `N` is prime the test outputs "prime" (probability 1); if `N` is (odd) composite it outputs "composite" with probability at least `1 − 2^{−t}`. Prime case from Lem-50.15a (core, difficulty 2); composite case from Lem-50.15b via `uprob_pi_forall` (`Pr[all t samples in L_N] = (|L_N|/N)^t ≤ 2^{−t}`) — deferred with the lemma. Text issue: "with probability `1 − 2^{−t}`" should be "at least".

**Lem-50.15a.** `N` odd prime ⟹ `L_N = Z_N^*` (`|L_N| = N − 1`): Fermat gives `α^{N−1} = 1` for `α ≠ 0`; in the field `ZMod N`, `β² = 1 → β = ±1` (`mul_self_eq_one_iff`/`sq_eq_sq_iff_eq_or_eq_neg`). Difficulty 3 (the index bookkeeping). **Lem-50.15b.** `N > 2` odd composite ⟹ `|L_N| ≤ (N−1)/2` (text: `<`): the liars lie in a proper subgroup of `Z_N^*` (with the "largest index" construction for Carmichael numbers) and Lagrange (`Subgroup.card_subgroup_dvd_card`). Deferred (plan), difficulty 5. Text issue: "`N > 2` composite" should say odd composite (even `N` is handled by the base case).

**Rem-49.3 / Rem-50.2.** Infinitely many Carmichael numbers; AKS. Out of scope / deferred. (Mathlib has `Nat.exists_infinite_pseudoprimes` for Fermat pseudoprimes to a fixed base — weaker.)

**Alg-50.16 (SamplePrime).** Repeat `x ← {0,1}^n` until `x` is prime. **Formal (strict PPT, truncated):** `T(n) := 2n²` independent uniform `x_t < 2^n`; output the first prime, else `⊥`. Primality.lean. Difficulty 3. Deviation: expected running time is not formalized; the primality test is `Nat.Prime` (exact) at the concrete layer and `PrimalityFP` (Q6) at the machine layer; with Miller–Rabin instead the output is only statistically close to uniform.

**Lem-51.17.** SamplePrime outputs a uniformly random element of `Π_n` in time `poly(n)`. **Formal:** (i) `Pr[⊥] ≤ (1 − 1/(2n))^{2n²} ≤ e^{−n}` (Claim-33.1, `uprob_pi_forall`, exp bound C8); (ii) conditioned on success the output is uniform on `Π_n` (C4: for i.i.d. uniform draws the first draw landing in `E` is uniform on `E`); (iii) the sampler is a PPT given `PrimalityFP` (loop `exists_loopFindTM` with fuel `2n²`). Difficulty 3 (+4 for (iii)). Text issue: "exceeds `1/n`" (should be `1/(2n)`).

**Thm-51.1 (factoring collection).** `I = ℕ`, `D_i = {(p, q) prime, |p| = |q| = i/2}`, `f_i(p, q) = pq`; factoring assumption ⟹ collection of OWFs. **Formal:** `Gen(1^n) = 1^n` (index `2n`), `D_n = Primes n × Primes n`, `Sample` = two SamplePrime calls (Q3: within `2e^{−n}` of uniform), `Eval` = multiplication (Q1), hardness: an inverter returning `(p′, q′)` with `p′q′ = N` gives a factor (Claim-34.1), so `A_fact(1^n, N) := fst(A(1^n, 1^n, N))`. Factoring.lean. Difficulty 3. Text issue: `D_i` uses exactly-`i/2`-bit primes while Asm-30.1 uses `Π_n`; the formalization uses `Π_n` throughout (Deviation).

### §2.8 Discrete logarithm

**Def-52.1 (Generator).** `g ∈ G` is a generator if `{g, g², …} = G`; `Gen_G` is the set of generators. — `Subgroup.zpowers g = ⊤`, `IsCyclic.exists_generator`, `orderOf_eq_card_of_forall_mem_zpowers`. Cite.

**Rem-52.2.** In a group of prime order every non-identity element is a generator; `Z_p^*` has order `p − 1` (not prime); for a safe prime `p = 2q + 1` the subgroup of squares has prime order `q`; sampling safe primes has no known guarantee. — `isCyclic_of_prime_card`, `ZMod.card_units`, `orderOf_dvd_card`; the squares subgroup is `MonoidHom.range (powMonoidHom 2)` of index 2 (Lem-57.1). Optional, difficulty 2. Units.lean.

**Asm-52.2 (DL).** "If `G_q` is a group of prime order `q`, then for every nuPPT `A` there is a negligible `ε` with `Pr[q ← Π_n; g ← Gen_{G_q}; x ← Z_q : A(g^x) = x] < ε(n)`." **Formal design:** a structure `DLGroupFamily` with, for each index `(q, desc)`, a finite group `G` of order `q` with injective string encoding of elements, `PolyTimeComputable` multiplication (hence exponentiation by repeated squaring, Alg-45.5 at the group level), and a PPT index sampler `GenDL(1^n)` returning `(q, g)` with `q ∈ Π_n` prime and `g ≠ 1` (a generator since `|G| = q` prime); the assumption: `∀ A, Negligible (fun n => Pr[(q,g) ← GenDL(1^n); x ← Z_q : A(1^n, q, g, g^x) = x])`. Deviations: `A` receives `q, g` (the text passes `g^x` only); the ideal "`q ← Π_n; g ← Gen_{G_q}`" is replaced by the family's own sampler (the text itself notes that sampling `(q, g)` efficiently is not known in general — Bach/Kalai); exact uniformity of `x ← Z_q` via Q3. Difficulty 3. DiscreteLog.lean. Text issues: `G_q` unspecified; `A(g^x)` lacks `q, g`.

**Thm-52.3 (DL collection).** `I = {(q, g) | q ∈ Π_k, g ∈ Gen_{G_q}}`, `D_i = Z_q`, `R_i = G_q`, `f_{q,g}(x) = g^x`; DL assumption ⟹ collection of OWFs. **Formal:** `Gen = GenDL`, `Sample` = uniform `Z_q` (Q3), `Eval` = exponentiation; hardness: the DL experiment *is* the collection's inversion experiment since `g^{x′} = g^x ⟺ x′ = x` in `Z_q` (`pow_eq_pow_iff_modEq`, `orderOf g = q`). Difficulty 3. Text issues: `R_i = G_p` and `f_{p,g}` typos (`q`); mixes `k` and `n`.

**Claim-53.1 (safe-prime generator test).** For `p = 2q + 1` with `p, q` prime, `g ∈ Z_p^*` is a generator iff `g ≠ ±1` and `g^q ≠ 1`: the order of `g` divides `2q`, so it is `1, 2, q` or `2q`. — `orderOf_dvd_of_pow_eq_one`, `orderOf_dvd_card`, `ZMod.card_units`. Optional, difficulty 2.

**Claim-53.2 (DL functions are permutations).** If `g` generates a group `G` of order `q` then `x ↦ g^x : ZMod q → G` is a bijection. — `zmodCyclicMulEquiv`, `orderOf_eq_card_of_forall_mem_zpowers`, `pow_eq_pow_iff_modEq`. Optional (the "DL is a collection of one-way permutations" remark after Thm 52.3), difficulty 2.

### §2.9 RSA

**Asm-53.1 (RSA).** For every nuPPT `A` there is a negligible `ε` with `Pr[p, q ← Π_n; N ← pq; e ← Z*_{Φ(N)}; y ← Z_N^*; x ← A(N, e, y) : x^e ≡ y (mod N)] < ε(n)`. **Formal:** `Φ(N) := (p−1)(q−1)` (valid for `p ≠ q`; the text's distribution allows `p = q`, where `Φ(p²) ≠ (p−1)²` — restrict to `p ≠ q` or define `Φ` as `Nat.totient N`), `e` uniform in `(ZMod (Φ N))ˣ`, `y` uniform in `(ZMod N)ˣ`, `A` receives `pairEncode 1^n (bits N, bits e, bits y)`, output decoded as a number `x` with `x^e % N = y`. RSA.lean. Difficulty 3.

**Thm-53.2 (RSA collection).** `I = {(N, e) | N = pq, p, q ∈ Π_n, e ∈ Z*_{Φ(N)}}`, `D_i = R_i = Z_N^*`, `f_{N,e}(x) = x^e mod N`; RSA assumption ⟹ collection of OWFs. **Formal:** `Gen`: two SamplePrime calls, `N`, `Φ`, then `e` by rejection sampling over `[0, Φ)` with `gcd(e, Φ) = 1` (needs C9 `φ(Φ)/Φ ≥ 1/(log₂ Φ + 1)` for a polynomial truncation, Q3); `Sample`: rejection sampling of `Z_N^*` (density `≥ 1/4` for `N = pq`); `Eval` = modexp (Q1). Hardness: by Thm-54.3 `x ↦ x^e` is a bijection of `Z_N^*`, so `(e, x^e)` with `x` uniform has the law of `(e, y)` with `y` uniform (`HardcoreBit.pushesUniform_equiv`, `PushesUniform.uprob_eq`); an inverter of `f_{N,e}` is an RSA breaker with the same probability. Difficulty 3. Text issue: the proof's "`{x, e ← Z_N^* : (e, x^e mod N)}`" samples `e` from the wrong group (should be `Z*_{Φ(N)}`).

**Thm-54.3 (RSA is a permutation).** For `e ∈ Z*_{Φ(N)}`, `x ↦ x^e mod N` is a permutation of `Z_N^*` with inverse `y ↦ y^d`, `ed ≡ 1 (mod Φ(N))`: `x^{ed} = x^{cΦ(N)+1} = x` by Euler. — Existing: `ZMod.pow_totient` (units; direct), and the legacy `RSA.rsa_crt_pow`/`RSA.rsa_correctness` (all of `ZMod (p*q)` for `p ≠ q` and `e·d = 1 + k(p−1)(q−1)`, via CRT). Units.lean (or RSA.lean). Difficulty 2.

### §2.10–§2.11 Permutations and trapdoors

**Def-55.1 (Collection of OWPs).** A collection of OWFs with every `f_i` a permutation (`D_i = R_i`, `f_i` bijective). Collections.lean. Difficulty 1.

**Thm-55.2 (RSA ⟹ Factoring).** If some nuPPT `A` factors `N = pq` (random `n`-bit primes) with probability `≥ 1/p(n)` (infinitely often), then `A′` (Alg-55.3) inverts `f_{N,e}` with probability `≥ 1/p(n)` (infinitely often); hence the RSA assumption implies the factoring assumption. **Formal:** `FactoringAssumption` is implied by `RSAAssumption`, proved contrapositively: `A′(1^n, N, e, y)`: `p′ ← A(1^n, N)`, `q′ := N / p′`; if `p′q′ ≠ N` abort; `Φ := (p′−1)(q′−1)`; `d := e^{−1} mod Φ` (`ZMod.inv`, computable by `Nat.gcdA`); output `y^d`. Whenever `A` returns a factor, `A′` succeeds (Thm-54.3), and the law of `N` is the factoring law regardless of `(e, y)` (`uprob_fst`-style marginalization), so `Pr[A′ wins] ≥ Pr[A factors]`. Difficulty 3. Machine-level: Q1 (`divMod`, `xgcd`, `modExp`). Text issue: the factoring assumption's `A` outputs one factor while Alg 55.3 expects the pair (compute the other by division); "running time of `A′` is `A` plus `O(log³ n)`" is a cost-model remark.

**Alg-55.3.** The adversary above. Difficulty 1.

**Def-56.1 (Trapdoor permutations).** `F = {f_i : D_i → R_i}` with (1) each `f_i` a permutation; (2) PPT `Gen(1^n) = (i, t)`; (3) PPT uniform sampler of `D_i`; (4) PPT evaluator; (5) for every nuPPT `A` there is negligible `ε` with `Pr[(i, t) ← Gen(1^n); x ← D_i; y ← f_i(x); z ← A(1^n, i, y) : f_i(z) = y] ≤ ε(n)`; (6) PPT `Inv((i, t), y) = f_i^{−1}(y)` for `y ∈ R_i`. Collections.lean. Difficulty 2. Text issue: "`≤ e(k)`" should be `e(n)`.

**Thm-57.2 (RSA is a TDP collection; "the proof is an exercise").** With `Gen(1^n) = ((N, e), d)`, `ed ≡ 1 (mod Φ(N))`, `f^{−1}_{N,d}(y) = y^d mod N`: under the RSA assumption, RSA is a collection of trapdoor permutations. Proof: (1) Thm-54.3; (2)–(4) as Thm-53.2 plus `d` from Alg-43.2; (5) Thm-53.2; (6) `(x^e)^d = x` (Thm-54.3). RSA.lean. Difficulty 3.

### §2.12 Rabin

**Def-57.0 (QR_p).** `QR_p := {x² mod p | x ∈ Z_p^*}`, as the subgroup `MonoidHom.range (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ)`. QuadraticResidues.lean. Difficulty 1.

**Lem-57.1.** For an odd prime `p`, `QR_p` is a subgroup of `Z_p^*` of order `(p−1)/2`; every `a ∈ QR_p` has exactly two square roots `±x` with `x ≠ −x`. Proof: the squaring homomorphism has kernel `{±1}` (`Units.sq_eq_sq_iff_eq_or_eq_neg`, `mul_self_eq_one_iff`), of order 2 since `p` is odd, so the image has order `(p−1)/2` (`Subgroup.card_eq_card_quotient_mul_card_subgroup`, `QuotientGroup.quotientKerEquivRange`); alternatively `legendreSym.card_sqrts` (`#{x | x² = a} = legendreSym p a + 1`) with `ZMod.euler_criterion`. Difficulty 3. **Claim-58.1** (`x² = y² → x = ±y` in `Z_p`): `sq_eq_sq_iff_eq_or_eq_neg`. Cite.

**Thm-58.2.** If `p = 4k + 3` is prime and `y ∈ QR_p`, then `(±y^{k+1})² = y`: with `y = a²`, `(y^{k+1})² = a^{4k+4} = a^{p+1} = a²` by Fermat (`ZMod.pow_card_sub_one_eq_one`, `a ≠ 0`). Difficulty 2.

**Ex-58.3 (exercise).** Square roots modulo `p ≡ 1 (mod 4)` (Tonelli–Shanks/Cipolla). Deferred (difficulty 4): not needed for the Blum-integer Rabin results; needed only for Thm-61.8 (⇐) in the text's generality.

**Thm-58.3 (CRT).** For pairwise coprime `p₁, …, p_k`, `N = ∏ p_i`, the map `y ↦ (y mod p_i)_i : Z_N → ∏ Z_{p_i}` is a bijection. — `ZMod.chineseRemainder` (`k = 2`, ring equivalence; all uses in the chapter have `k = 2`), `Nat.chineseRemainder`, `Nat.chineseRemainderOfList`/`…OfFinset` (general `k`, existence and uniqueness). Cite; an optional `k`-fold ring-equiv bridge by induction (difficulty 2). **Claim-59.1** (explicit inverse `y = Σ_i b_i n_i a_i`, `b_i n_i ≡ 1 (mod p_i)`, two Euclid calls): optional, difficulty 2 (math); machine-level deferred. **Ex-59.2** (`p = 7`, `q = 11`): optional `decide`.

**Def-59.3 (QR_N).** `QR_N := {x² mod N | x ∈ Z_N^*}`. Difficulty 1.

**Thm-59.4.** For `N = pq` (distinct primes) and `x ∈ Z_N^*`, `x ∈ QR_N ⟺ (x mod p ∈ QR_p ∧ x mod q ∈ QR_q)`. Proof: transport squares and units along `ZMod.chineseRemainder` (`Units.map`, `RingEquiv.map_pow`). Difficulty 2. Text issues: "`zinQRq`" typo; the two directions of the proof are labelled backwards.

**Thm-60.5.** For `N = pq` with `p ≠ q` odd primes, squaring on `Z_N^*` is 4-to-1: every `y ∈ QR_N` has exactly four square roots in `Z_N^*`. Proof: roots of `y` correspond under CRT to pairs (root mod `p`, root mod `q`), `2 × 2` by Lem-57.1. Difficulty 3. Text omits `p ≠ q` and oddness (fails for `N = p²` or `p = 2`).

**Cor-60.6.** `|QR_N| = |Z_N^*|/4 = Φ(N)/4`. Fiber counting (`Finset.card_eq_sum_card_fiberwise`). Difficulty 2.

**Claim-60.7 (roots from the factors).** If `a² ≡ y (mod p)` and `b² ≡ y (mod q)` then `s := CRT^{−1}(a, b)` satisfies `s² ≡ y (mod N)`; hence with `p, q` known, square roots modulo `N` reduce to square roots modulo `p` and `q`. Difficulty 2 (math; used by Thm-61.8 (⇐) and Thm-63.10(6)); machine-level deferred (Q1). **Ex-60.8** (`N = 77` example): optional `decide`; the pdftotext numbers are garbled (`71` vs `42`, `(1,5)`, `(0,3)`).

**Thm-61.7 (Rabin collection).** `I = {N = pq | p, q ∈ Π_n}`, `D_N = Z_N^*`, `R_N = QR_N`, `f_N(x) = x² mod N`; factoring ⟹ collection of OWFs. **Formal (Q4):** indices restricted to `p ≠ q` odd (or Blum), with the factoring assumption on the same index distribution; `Gen` as in Thm-51.1 with a `p ≠ q` re-sample; `Sample` = rejection sampling of `Z_N^*`; `Eval` = squaring mod `N` (Q1); hardness = Thm-61.8 (⇒). Rabin.lean. Difficulty 4. Text issue: "`Z_n^*`" for `Z_N^*`.

**Thm-61.8 (Rabin one-way ⟺ factoring).** (⇒ direction of the text, i.e. factoring hard ⟹ Rabin one-way, proved contrapositively) if a nuPPT `A` returns a square root of `y = x²` (`x ← Z_N^*`) with probability `≥ 1/p(n)` infinitely often, then `A′` (Alg-62.9) factors `N` with probability `≥ 1/(2p(n))` infinitely often. Concrete content: Claim-62.2 (the root differs from `±x` half the time) + Claim-62.1 (`gcd(x − z, N)` is then a prime factor). Asymptotic: `A′` samples `x`, squares, calls `A`, tests, takes a gcd (Q1). Difficulty 4. (⇐, "only if": Rabin one-way ⟹ factoring hard, contrapositively) if a nuPPT `A` factors with probability `≥ 1/r(n)` i.o., then `A′(N, y)`: factor, take roots mod `p` and mod `q` (Thm-58.2 — **only for `p ≡ q ≡ 3 (mod 4)`**), combine by Claim-60.7; success `≥ 1/r(n)` i.o. Difficulty 3 for Blum integers; the general case needs Ex-58.3 (text gap). Text issues: mixes `n` and `k`; the "1/2p(k)" bound; the heuristic "A outputs one of the four roots with equal probability" is replaced by the symmetry argument of Claim-62.2.

**Alg-62.9.** `A′(N)`: `x ← Z_N^*`; `y := x² mod N`; `z ← A(1^n, N, y)`; if `z² ≢ y` abort; else output `gcd(x − z, N)`. Difficulty 1.

**Claim-62.1.** For `N = pq` (distinct primes) and `x, z ∈ Z_N^*` with `x² ≡ z² (mod N)` and `z ≢ ±x (mod N)`, `gcd(x − z, N) ∈ {p, q}` (`x − z` taken in `ℤ`, or `(x − z) mod N` in `ℕ`): `N ∣ (x−z)(x+z)` but `N ∤ (x−z)`, `N ∤ (x+z)`, so exactly one of `p, q` divides `x − z` (`Nat.Prime.dvd_mul`, CRT). QuadraticResidues.lean. Difficulty 2.

**Claim-62.2 (symmetry lemma, concrete).** Let `Z : QR_N → ρ → Z_N^*` depend on `x` only through `y = x²` (and coins). Then `Pr_{x, r}[Z(x², r)² = x² ∧ Z(x², r) ∉ {x, −x}] ≥ (1/2)·Pr_{x, r}[Z(x², r)² = x²]`. Proof: let `u := CRT^{−1}(1, −1)` and `σ(x) := ux`; `σ` is a bijection of `Z_N^*` with `σ(x)² = x²` and `σ(x) ∉ {±x}` (for `p, q` odd distinct); the events `S ∧ B` and `S ∧ B∘σ` (`B(x) := Z(x², r) ∈ {±x}`) are disjoint subsets of `S` with equal probability (`uprob_comp_equiv`), so `2·Pr[S ∧ B] ≤ Pr[S]`. New concrete lemma in `Candidates/Concrete.lean`. Difficulty 3. Used by Thm-61.7/61.8 and (with `Z` = the QR root) by Thm-63.10.

**Thm-63.10 (Rabin TDP).** `I = {N = pq | p, q ∈ Π_n, p ≡ q ≡ 3 (mod 4)}`, `D_N = R_N = QR_N`, `Gen(1^n) = (N, (p, q))`, `f_N(x) = x² mod N`, `f^{−1}_{p,q}(y)` = the unique root of `y` in `QR_N`; factoring (on Blum integers) ⟹ collection of TDPs. Components: (1) Claim-63.1; (2) `Gen` samples Blum primes — density of primes `≡ 3 (mod 4)` below `2^n` is **not available** (no Dirichlet-type bound in Mathlib): take `BlumPrimeDensity : |{p ∈ Π_n | p ≡ 3 (mod 4)}| ≥ 2^n/(C(n+1)^c)` as an explicit hypothesis of the `Gen` clause (Q4); (3) `Sample`: square a uniform `r ∈ Z_N^*` — 4-to-1 maps push uniform to uniform (C5); (4) squaring (Q1); (5) hardness: Claim-62.2 with `Z := A`'s answer (the QR root): with `r` uniform in `Z_N^*`, `r ∉ {±x}` half the time, and `gcd(r − x, N)` factors `N` (Claim-62.1); (6) `Inv`: roots mod `p`, `q` by Thm-58.2, select the residues by Euler's criterion (`ZMod.euler_criterion`, exponent `(p−1)/2`), combine by Claim-60.7. Rabin.lean. Difficulty 4. Deviation: factoring assumption restricted to Blum moduli; density hypothesis.

**Claim-63.1 ("future homeworks").** For a Blum integer `N = pq` (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`), every `y ∈ QR_N` has exactly one square root in `QR_N`; hence squaring is a permutation of `QR_N`. Proof: `−1 ∉ QR_p` for `p ≡ 3 (mod 4)` (`ZMod.exists_sq_eq_neg_one_iff`), so of the roots `±a` mod `p` exactly one is a residue; likewise mod `q`; Thm-59.4 selects exactly one of the four roots. QuadraticResidues.lean. Difficulty 3.

### §2.13 Universal one-way function

**Thm-63.1 (universal OWF).** If some (strong) one-way function exists, then the polynomial-time computable `f_universal` of Alg-64.2 is one-way. The proof shows weak one-wayness (with `q(n) = n³`) and invokes Thm-35.1. **Formal (corrected, F2):** `f_univ c (y) := let k := ⌊log₂ |y|⌋; M := y.take k; x := y.drop k; pairEncode M (U(pairEncode (pairEncode (bits ((|y|+1)³)) M) x))` where `U` is the machine of `Turing.timed_universal_concrete c` (output `true :: M(x)` on halting within the budget, `[false]` otherwise), for a fixed `c : EffectiveMachineCode` (exists: `Turing.exists_effectiveMachineCode`) satisfying `∃ A B, ∀ k, c.canonizerTime k ≤ A·2^{B·k}` (so that the simulator's code-dependent coefficient `3|M| + canonizerTime |M| + |serialize| + 2|bits numStates| + 2q₀ + 16 + universalBlockBound + 14`, with `|serialize| ≤ canonizerTime |M|` by output-length ≤ time and `numStates ≤ |serialize|`, is `poly(n)` for `|M| = ⌊log₂ n⌋`). Statement: `(∃ g, StrongOWF g) → WeakOWF (f_univ c)` with `q(n) = n³`, and `StrongOWF (prodFun-amplification of f_univ c)` by Thm-35.1. Proof: Lem-64.3 gives a strong `g′` and a `CodeTM` `M_g` computing it within `c₀·(m+1)²` (≤ `(n+1)³` for large `n`); Claim-65.1: with probability `≥ 1/n` the code field of a uniform `y` is `encode M_g` padded with `true`s (`decode_encode_pad`); on that event `f_univ(y) = pairEncode M (true :: g′(x))` with `x` uniform of length `m = n − ⌊log₂ n⌋`, and an inverse `⟨M′, x′⟩` must have `M′ = M` (the code is part of the output; `pairEncode_injective`) and `g′(x′) = g′(x)`; Claim-65.2 turns "`A` inverts with probability `> 1 − 1/n³` infinitely often" into "the inverter `B(1^m, z) := x′` from `A(1^n, pairEncode M_g (true :: z))` inverts `g′` with probability `≥ 1/n²` at `m(n) = n − ⌊log₂ n⌋` infinitely often" — non-negligible in `m` (`m ↦ n` is recovered by advice or search), contradicting strong one-wayness. — Existing: `Turing.timed_universal`, `timed_universal_concrete`, `universalBlockBound`, `EffectiveMachineCode`, `exists_effectiveMachineCode`, `MachineCode.decode_encode_pad`, `exists_codeTM`, `FinTM.one_work_tape_binary`, `pairEncode_injective`, `OneWay.card_log_bits_le`, `uprob_eq_one_div_card`, `not_negligible_iff`. Universal.lean. Difficulty 5. Text issues: output must include `M` (F2); "hardness amplification construction from §2.3" should be §2.4; `|y|³` budget becomes `(|y|+1)³`.

**Alg-64.2 (f_universal).** Interpret `y` as `⟨M, x⟩` with `|M| = log|y|`; run `M` on `x` for `|y|³` steps; output `M(x)` if it halts, else `⊥`. **Formal:** as above (corrected). Poly-time computability: `y ↦ (y.take ⌊log₂|y|⌋, y.drop ⌊log₂|y|⌋)` needs a new primitive "split at `⌊log₂ |y|⌋`" (`computesFunInTime_lengthBits` gives `bits |y|`, whose length is `⌊log₂|y|⌋ + 1`; difficulty 3), `computesFunInTime_polyBits 1 3` gives `bits ((|y|+1)³)`, `PolyTimeComputable.pairEncode` assembles `U`'s input, `computesFunInTime_comp` runs `U` (its bound is quadratic in the budget times the code-dependent coefficient), and `PolyTimeComputable.pairEncode` prepends `M`. Difficulty 4.

**Lem-64.3.** If `g` is a strong OWF then there is a strong OWF `g′` computable in time `O(n²)`: `g′(⟨a, b⟩) = ⟨a, g(b)⟩` with `|a| = n^c − n`, `|b| = n`. **Formal:** `g′ n (a, b) := (a, g k(n) b)` with `|b| = k(n)` and `|a| = n − k(n)` where `k` is chosen so that the coded machine for `g` runs within the quadratic budget on `b` (if `M_g` runs in `C(k+1)^c` multi-tape, `one_work_tape_binary` gives a one-tape binary machine in `c′(C(k+1)^c+1)²`, so take `n := ` that bound plus `k`, i.e. `k(n) ≈ n^{1/(2c)}`), and a `CodeTM` (`exists_codeTM`) computing `g′` within `c₀(n+1)²`: copy `a` (linear), parse the split (lengths known from `n`), run `M_g` on `b`. Hardness: `OneWay.invProb_pad_le` (`pad`, `padInverter`) + nuPPT closure (sample `a`, call `A`, project). Difficulty 3 (+3 for the machine time analysis). Universal.lean. Note the text's `⟨a, b⟩` pairing is immaterial when the split lengths are fixed by `n`; plain concatenation avoids `pairEncode`'s doubling.

**Claim-65.1 (PickG).** For `n` with `⌊log₂ n⌋ ≥ |encode M_g|`, `Pr_{y ← {0,1}^n}[y.take ⌊log₂ n⌋ = encode M_g ++ 1^{⌊log₂ n⌋ − |encode M_g|}] = 2^{−⌊log₂ n⌋} ≥ 1/n` (`uprob_fst`, `uprob_eq_one_div_card`, `card_log_bits_le`), and on this event `decode (y.take …) = M_g` (`decode_encode_pad`). Difficulty 2.

**Claim-65.2 (union bound).** If `Pr[Invert] > 1 − 1/n³` and `Pr[PickG] ≥ 1/n` then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + 1 − 1/n`, so for `n ≥ 2` `Pr[Invert ∧ PickG] ≥ 1/n − 1/n³ ≥ 1/n³` (text) — and in fact `Pr[Invert | PickG] ≥ 1 − 1/n²`; the `g′`-inverter's success at length `m(n)` is at least this, infinitely often, so not negligible (`not_negligible_iff`; the map `n ↦ n − ⌊log₂ n⌋` is unbounded and non-decreasing with steps `≤ 1`, so infinitely many `n` give infinitely many `m`). Difficulty 2.

### Appendix items Chapter 2 relies on

**App-A.1 (union bound).** `uprob_or_le`, `uprob_exists_le`. Cite. **App-A.2 (Markov, Chebyshev).** `HardcoreBit.uprob_mul_le_uexp` (Markov form), `HardcoreBit.uprob_le_abs_le`. Cite. **App-A.3 (pairwise-independent sampling).** `HardcoreBit.chebyshev_pairwise`, `chebyshev_pairwise_ident` (bits; the appendix states it for `|X_i| ≤ 1`). Cite.

**Thm-188.7 (Chernoff).** For independent `X_1, …, X_n` with `E X_i = μ` and `|X_i| ≤ 1`, `Pr[|Σ X_i − μn| ≥ εn] ≤ 2^{−ε²n}` (the text writes `≥ ε`, dimensionally wrong; constants "chosen for simplicity"). Deferred (difficulty 4): Mathlib's Hoeffding `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` is measure-theoretic (sub-Gaussian MGFs) and would need a `uprob`-bridge; only Rem-24.2/Lem-189.8 use it.

**Lem-189.8 (Majority vote).** `Pr[X_i = b] ≥ 1/2 + 1/p(n)`, `ℓ > p(n)²` ⟹ `Pr[majority = b] > 1 − 2^{??}` (garbled; proof unfinished "…"). Deferred (difficulty 4 via Chernoff; Chebyshev alone gives only `1 − O(1/n)` error with `ℓ = n p(n)²`).

**Thm-189.9 (Cauchy–Schwarz).** `Finset.sum_mul_sq_le_sq_mul_sq`. Cite.

**Def-191.10 (DP).** `Complexity.P`. Cite. **Def-191.11 (NP).** Witness relation `R_L ∈ P`, `|y| ≤ p(|x|)` — `Complexity.NP` (exact length `C(|x|+1)^c`, concatenation) with `Complexity.mem_NP_iff_exists_length_le` (bounded-length paired form). Cite. **Def-192.12 (BPP).** `L ∈ BPP` iff some PPT `M` has `Pr[M(x) = 1] ≥ 2/3` for `x ∈ L` and `Pr[M(x) = 0] ≥ 2/3` for `x ∉ L`. Deferred (difficulty 2 once Def-23.4 exists); only Rem-27.1 uses it.

---

## 3. Text errors and issues (consolidated)

Outright errors (also returned as `text_errors`):

1. **Algorithm 64.2 / Theorem 63.1:** `f_universal(⟨M, x⟩) = M(x)` omits the machine description from the output; the proof ("`A` must invert a hard instance of `g`") is invalid because the inverse may be `⟨M′, x′⟩` with `M′ ≠ M_g`. Correct definition: output `⟨M, M(x)⟩`.
2. **§2.6.5, definition of `L_N`:** "`N = u2^j`" should be `N − 1 = u·2^j`; the second condition is stated with `i = j` only and is vacuous; intended: for all `i < j`, `α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. **Claim 32.4** is false as a strict inequality (`x = 1`, `p = 2`); correct: `p^{ν_p(C(2x,x))} ≤ 2x`.
4. **§2.6.6 (p. 50):** "the probability that a uniformly sampled `n`-bit integer is prime exceeds `1/n`" — Theorem 31.3 (and §2.3.2's own corollary) gives `1/(2n)`.
5. **Theorem 60.5, Corollary 60.6, Theorems 61.7, 61.8, 63.10:** require `p ≠ q` odd primes; `Π_n` contains 2 and the sampling allows `p = q`. Likewise `Φ(pq) = (p−1)(q−1)` (p. 47) and `Φ(N)` in Assumption 53.1 need `p ≠ q`.
6. **Theorem 61.8 (⇐):** needs square roots modulo arbitrary primes, but only `p ≡ 3 (mod 4)` is proved (Theorem 58.2; the rest is "left as an exercise").
7. **Theorem 59.4:** "`zinQRq`" typo; the proof's `⇒`/`⇐` labels are swapped.
8. **Theorem 52.3:** `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; **Assumption 52.2:** `A` receives only `g^x` (needs `q, g`); `G_q` is unspecified.
9. **Theorem 53.2 proof:** "`x, e ← Z_N^*`" samples `e` from the wrong group (`Z*_{Φ(N)}`).
10. **Definition 56.1(5):** "`≤ e(k)`" should be `e(n)`.
11. **Definition 41.1(4):** "p.p.t. `A`" contradicts the standing nuPPT convention; "`f(A(1^n, i, y)) = y`" should be `f_i`.
12. **Theorem 42.2 proof idea:** "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n` (`{0,1}^n`).
13. **§2.4.3 proof:** "For each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra factor `m` is garbled.
14. **Algorithm 33.6, line 7:** `A(1^n, z′)` should be `A(1^{2n}, z′)`; **Algorithm 37.4:** "Output `x′_i`" should output a verified factor.
15. **Lemma 189.8:** statement garbled ("`1 − 2??`"), proof unfinished; **Theorem 188.7:** threshold `ε` should be `εn`.
16. **§2.3 attack on `f_mult`:** `A(z) = (2, z/2)` returns a preimage of a different input length; with `n`-bit inputs it does not show `f_mult` is not strongly one-way.
17. **Claim 43.3 case 2:** "`b > 2^n`" should be `b ≥ 2^n`.
18. **Example p. 61 (`N = 77`):** numbers garbled (`71`/`42`, `(1,5)`, `(0,3)`).
19. **Theorem 63.1 proof:** "hardness amplification construction from §2.3" should be §2.4.
20. **Theorem 49.14:** "with probability `1 − 2^{−t}`" should be "at least"; **Lemma 50.15:** "`N > 2` composite" should be odd composite.
21. **p. 27:** "NP ⊄ BPP ⟺ worst-case one-way functions exist (show this!)" mixes the uniform class BPP with the non-uniform adversaries of §2.1.3.
22. **Theorem 45.6 / p. 46:** the remark that Euler's theorem "removes the restriction that `x < N`" refers to a restriction Algorithm 45.5 does not have.
23. **Theorem 31.3 proof:** "each term is greater than 2" — the term `(x+x)/x` equals 2 (`X ≥ 2^x`).
24. **Theorem 61.8 / 55.2:** mix `n` and `k`; **Theorem 61.7:** `Z_n^*` for `Z_N^*`; **Theorem 51.1:** `D_i` uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.

Non-error sloppiness handled by Deviations: adversaries receive `1^n` everywhere (Assumptions 30.1/52.2/53.1 omit it); dyadic samplers approximate the ideal uniform distributions (Q3); expected polynomial time (SamplePrime) replaced by strict PPT with `2^{−n}` failure; polynomial normal form `C(n+1)^c`.

---

## 4. New concrete-layer lemmas (Garg files are frozen; put these in `TCSlib/Cryptography/Candidates/Concrete.lean` unless noted)

* **C1** `uprob_cond_ge`: for `E, S : α → Prop` with `Pr[E] ≥ δ > 0`, the probability of `S` on the uniform subtype `{a // E a}` equals `Pr[S ∧ E]/Pr[E]` and is `≥ 1 − (1 − Pr[S])/δ` (Thm-33.5). Also the identification of `uprob` on `Primes n × Primes n` with the conditional law on `Fin (2^n) × Fin (2^n)`.
* **C2** `invProb_pairFun_le` (Thm-35.2) — in `Asymptotic/OneWay.lean`.
* **C3** `invProb_prodFun_plant_le`: random-position planting with a bad set (Thm-36.3); may be stated generally enough to re-derive `invProb_prodFun_le`.
* **C4** `first_hit_uniform`: for i.i.d. uniform draws `x_1, …, x_T`, the first `x_t ∈ E` is uniform on `E` conditioned on existence, and `Pr[no hit] = (1 − Pr[E])^T` (Lem-51.17; also the rejection samplers of Q3).
* **C5** `pushesUniform_of_card_fiber`: a map all of whose fibers have the same size pushes uniform to uniform (`QR_N` sampling, Thm-63.10(3)); converse-type lemma for 4-to-1 (Cor-60.6).
* **C6** Claim-62.2 (Rabin symmetry lemma).
* **C7** `uprob_eq_one_iff_forall` (Def-24.6).
* **C8** `one_sub_inv_pow_le_exp_neg`: `(1 − 1/a)^{a·n} ≤ e^{−n}` for `a ≥ 1`, and `e^{−n} ≤ 2^{−n}` (Claim-36.2, Lem-51.17, Claim-38.2).
* **C9** `totient_div_self_ge`: `φ(m)/m ≥ 1/(log₂ m + 1)` for `m ≥ 1` (the `i`-th smallest prime factor is `≥ i + 1`, `∏_{k=2}^{K}(1 − 1/k) = 1/K`) — in `NumberTheory/Units.lean`; needed for sampling `Z*_{Φ(N)}` (Thm-53.2) by truncated rejection.
* **C10** statistical-switch lemma: replacing a sampler by one within statistical distance `δ` changes any success probability by `≤ δ` (Q3; `distAdv_le_statDist` is the model) — in `Asymptotic/Collections.lean`.

## 5. Machine-layer requirements consumed by Chapter 2 (for `Randomized/{Closure,Repetition}.lean`)

* R1 post-processing by `PolyTimeComputable` (decode `n`-bit strings, projections `pairFstD/pairSndD`, numeral decoding) — all theorems.
* R2 pre-processing: `x ↦ pairEncode 1^n (h x)` for `PolyTimeComputable h`; planting a given string into a computed tuple at a coin-chosen position (Thms 35.1, 36.3).
* R3 coin splitting: using disjoint segments of the coin string as independent uniform strings / `Fin 2^k` elements (every reduction).
* R4 advice pass-through (every reduction uses the given nuPPT's advice).
* R5 `T(n)` fresh-coin calls returning the first success (`exists_loopFindTM`): Thm-35.1, SamplePrime, rejection samplers.
* R6 `m(n)` evaluations of a `PolyTimeComputable` function with concatenated outputs (`exists_emitLoopTM`): `prodFun` evaluation in Thms 35.1/36.3/63.1 amplification.
* R7 calling the clocked universal machine with a hard-wired code (`computesFunInTime_pairEncodeFixed`, `computesFunInTime_comp`): Thm-63.1.
* R8 equality test of two computed strings and `ite` (`polyTimeComputable_ite`, `lenEq`): Thm-35.1's `f(z_i) = y`, Alg-62.9's `z² = y`.
* R9 (Q1 bundle) binary arithmetic: `mul`, `divMod`, `xgcd`, `modExp`, comparison, numeral/string decoding; (Q6) primality test. Taken as hypotheses in `Candidates/Arithmetic.lean`.

## 6. Proposed file split (changes to the plan's layout)

* Add `TCSlib/Cryptography/Candidates/Arithmetic.lean` (the Q1/Q6 hypothesis bundle, docstring explaining why it is a hypothesis) and `TCSlib/Cryptography/Candidates/Concrete.lean` (C1, C3–C6, C8). Both under the `Candidates.lean` facade.
* `Candidates/Factoring.lean` (Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Alg-37.4, Thm-51.1) is at risk of exceeding 600 lines: split `Candidates/FactoringAmplified.lean` for Thm-36.3 if needed.
* `NumberTheory/Chebyshev.lean` holds Def-29.3, Thm-31.3, Claim-33.1; `NumberTheory/Primality.lean` holds Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a/b (b sorried under a sketch, deferred), Alg-50.16, Lem-51.17.
* `Asymptotic/Universal.lean` holds Thm-63.1, Alg-64.2, Lem-64.3, Claims 65.1–65.2, plus the new log-split primitive if it is not placed in a `Complexity/Randomized` helper (it is a deterministic machine; placing it in `Complexity/TuringMachine/Build/` would touch frozen files — put it in `Asymptotic/Universal.lean` as a private construction or in a new `Complexity/Randomized/Primitives.lean`).
* Definitions 24.7 (Encryption.lean) and 192.12 (PPT.lean, deferred) sit outside the Chapter-2 files as the plan prescribes.

## 7. Build order (dependencies)

PPT.lean → NonUniform.lean → Closure.lean/Repetition.lean → Asymptotic/OneWay.lean (Defs 26.1, 27.3, 28.4; Thms 35.2, 35.1 with Claim-38.2) → Asymptotic/Collections.lean (Defs 41.1, 55.1, 56.1; Thm 42.2) → NumberTheory/{Chebyshev, Euclid, ModExp, Units, Primality, QuadraticResidues}.lean (independent of the machine layer except Lem-51.17(iii)) → Candidates/{Arithmetic, Concrete, Factoring, DiscreteLog, RSA, Rabin}.lean → Asymptotic/Universal.lean (needs OneWay.lean, Thm-35.1, and the universal machine).

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/l/replay.log =====

# closure of pack 03l's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 26 modules, extracted from g03-replay.log
TCSlib/Complexity/ClassNP/PolyTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 6s errors=0 sorry=2
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 11s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 102s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 103s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 8s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 6s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 5s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 28s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 10s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 5s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/l/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03l's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/l/admissions.txt =====

# declarations with `sorry` in pack 03l's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/l/lint.log =====

# scripts/style_lint.py on pack 03l's files, at a3c5fa8b72e50939822f22364647dc844a3914a0







0 findings in 6 files

## ===== TCSlib/Complexity/Randomized/Build/IterateFind.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine behind the repetition lemma

The finite machine behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`): iterate a polynomial-time step `g`
at most `R(|x|)` times on a polynomially bounded orbit and return the payload `out` of the first
orbit point accepted by `acc` (`[]` on exhaustion). Every theorem of [PS10, ch. 2–4] that
repeats an adversary — Algorithm 38.5's `2nm²p(n)` attempts with first success
[PS10, Theorem 35.1], the `n(2^k − 1)` calls of Goldreich–Levin [PS10, Theorem 87.3], the
truncated simulators [PS10, Algorithms 123.4 and 128.7] — reduces to this machine.

## Construction (DESIGN.md §2.6, the three panel repairs built in)

The machine is an instance of the result-bearing loop combinator
`Turing.FinTM.exists_loopFindTM` (`TCSlib.Complexity.TuringMachine.Build.Loop`).

1. *State word.* The loop state is the pair `⟨x, s⟩` (`Turing.pairEncode x s`) of the input
   and the current orbit point; the loop invariant `Inv` says the word *is* such a pair with
   `|s| ≤ P|x|`; the step is the length-guarded `Complexity.IterateFind.step`
   (`⟨x, g s⟩` if `|g s| ≤ P|x|`, else unchanged), under which the invariant is closed for
   every admissible word; on the orbit the guard never fires (the pure lemmas of
   `TCSlib.Complexity.Randomized.Repetition`).
2. *Modules.* Three clean-call modules over the state word, from
   `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` applied to FP functions: the
   **verdict** install `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of the installed
   word), the **step** install `w' ↦ step` on the pair carried by `w'`, and the **payload** emit
   `w' ↦ out (snd (snd w'))`; plus the startup module `x ↦ ⟨x, x⟩`
   (`Turing.FinTM.computesFunInTime_pairDup`) and a two-state copier that puts the native
   input on tape 0 first.
3. *Gluing.* Each module is converted into a first-halting source (a release flag stops it one
   silent step after its first positive exit), padded to the common tape count, and embedded
   into one finite host through the forwarding transformer `Turing.emitAction`; the host's own
   control has three fresh states — the loop **anchor** (never a module-internal state), a
   **branch** state reading the verdict cell of tape 0, and a **halt** state. Modules return
   to fixed host states: copier → startup install → anchor; verdict → branch; branch → payload
   emit (verdict `true`) or step install (verdict `false`); payload emit → halt; step → anchor.
4. *Budgets.* All requests are state words of length at most `Q n + 4` with
   `Q n = 2n + 2 + P n`; every module's polynomial budget on its argument is majorised by one
   common `A · (Q n + 5)^D`, which also pays for the fuel machine `x ↦ Nat.bits (R|x|)`
   (`Complexity.polyTimeComputable_unaryPoly R` composed with
   `Turing.FinTM.computesFunInTime_lengthBits`, so that the `find?` range is exactly
   `R|x| + 1`). The loop combinator returns a machine within `c (T n + 1)(R n + 2)`, which
   `PolyExpr.eval_le` puts in the normal form of `Complexity.PolyTimeComputable`.

The clean-module layer and the finite host (steps 2–3: release-flag stop, padding,
forwarding host, first-halt cutting, the copier) live in
`TCSlib.Complexity.Randomized.Build.IterateFindHost`; this file supplies the pure step, the
FP functions of the modules, the budget arithmetic, and the assembly through
`Turing.FinTM.exists_loopFindTM`.

## Main definitions

* `Complexity.IterateFind.step` — the length-guarded step on the state word (definitionally
  `Complexity.guardedStep`).

## Main results

* `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
  lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
  polynomial-time computable.
* `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
  values on the list (used to identify the guarded orbit with `g^[i] x`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The guarded step on the state word and its FP pieces -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). This is definitionally
`Complexity.guardedStep g P x w`; it is restated here because this file is imported by the
file defining `guardedStep`. -/
def step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The loop invariant used by the machine: the state word *is* a pair `⟨x, s⟩` with
`|s| ≤ P|x|` (stronger than the pure `Complexity.LoopInv`, which also admits malformed
words; the machine needs the well-formedness to bound the word's length). -/
private def Inv (P : PolyExpr) (x w : List Bool) : Prop :=
  ∃ s, w = pairEncode x s ∧ s.length ≤ P.eval x.length

/-- The initial word `⟨x, x⟩` is admissible when `|x| ≤ P|x|`. -/
private theorem inv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    Inv P x (pairEncode x x) :=
  ⟨x, rfl, h0⟩

/-- The invariant is closed under the guarded step (the guard keeps the word unchanged when
the new point would be too long). -/
private theorem inv_step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : Inv P x w) : Inv P x (step g P x w) := by
  obtain ⟨s, rfl, hs⟩ := h
  unfold step
  rw [pairSndD_pairEncode]
  split_ifs with hg
  · exact ⟨g s, rfl, hg⟩
  · exact ⟨s, rfl, hs⟩

/-- The length of an admissible state word is at most `2|x| + 2 + P|x|`. -/
private theorem inv_length (P : PolyExpr) (x w : List Bool) (h : Inv P x w) :
    w.length ≤ 2 * x.length + 2 + P.eval x.length := by
  obtain ⟨s, rfl, hs⟩ := h
  rw [length_pairEncode]
  omega

/-- The verdict word: `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell, since
`pairEncode [b] w = [b, b, false, true] ++ w`). -/
private def verdictWord (acc : List Bool → Bool) (w : List Bool) : List Bool :=
  pairEncode [acc (pairSndD w)] w

/-- The step on a verdict word: strip the verdict, then take the guarded step on the pair
`⟨x, s⟩` carried by the word, with `x` recovered from the word itself. -/
private def stepWord (g : List Bool → List Bool) (P : PolyExpr) (w' : List Bool) : List Bool :=
  if (g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length then
    pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w')))
  else pairSndD w'

/-- The payload of a verdict word: `out` of the orbit point `snd (snd w')`. -/
private def outWord (out : List Bool → List Bool) (w' : List Bool) : List Bool :=
  out (pairSndD (pairSndD w'))

/-- The first cell of a verdict word is the verdict. -/
private theorem verdictWord_head (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w)[0]? = some (acc (pairSndD w)) := by
  simp [verdictWord, pairEncode]

/-- The length of a verdict word. -/
private theorem verdictWord_length (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w).length = w.length + 4 := by
  simp [verdictWord, length_pairEncode]
  omega

/-- On the verdict word of an admissible pair, `stepWord` is the guarded step. -/
private theorem stepWord_verdictWord (g : List Bool → List Bool) (P : PolyExpr)
    (acc : List Bool → Bool) (x s : List Bool) :
    stepWord g P (verdictWord acc (pairEncode x s)) = step g P x (pairEncode x s) := by
  simp [stepWord, verdictWord, step]

/-- On the verdict word of a pair, `outWord` is `out` of the orbit point. -/
private theorem outWord_verdictWord (out : List Bool → List Bool) (acc : List Bool → Bool)
    (x s : List Bool) : outWord out (verdictWord acc (pairEncode x s)) = out s := by
  simp [outWord, verdictWord]

/-- The verdict word is polynomial-time computable (`PolyTimeComputable.pairEncode` of the
test composed with the projection and the identity). -/
private theorem verdictWord_poly {acc : List Bool → Bool}
    (hacc : PolyTimeComputable fun s => [acc s]) : PolyTimeComputable (verdictWord acc) := by
  have h := (hacc.comp polyTimeComputable_pairSndD).pairEncode polyTimeComputable_id
  exact h

/-- The step on verdict words is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_ite`: the test
`|g (snd (snd w'))| ≤ P|fst (snd w')|` is `Complexity.polyTimeComputable_lenLe` on the pair
`⟨1^{P|fst (snd w')|}, g (snd (snd w'))⟩`, built with the unary evaluator
`Complexity.polyTimeComputable_unaryPoly P` and `PolyTimeComputable.pairEncode`; the `then`
branch is the pairing of the two projections (with `g`), the `else` branch the projection
`snd`; the Boolean test is identified with the propositional `if` by `decide_eq_true_eq`. -/
private theorem stepWord_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (P : PolyExpr) : PolyTimeComputable (stepWord g P) := by
  have hs2 : PolyTimeComputable fun w' => pairSndD (pairSndD w') :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hf1 : PolyTimeComputable fun w' => pairFstD (pairSndD w') :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hgg : PolyTimeComputable fun w' => g (pairSndD (pairSndD w')) := hg.comp hs2
  have hun : PolyTimeComputable fun w' =>
      List.replicate (P.eval (pairFstD (pairSndD w')).length) true :=
    (polyTimeComputable_unaryPoly P).comp hf1
  have htest : PolyTimeComputable fun w' =>
      [decide ((g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length)] := by
    have h := polyTimeComputable_lenLe.comp (hun.pairEncode hgg)
    convert h using 1
    funext w'
    simp
  have hthen : PolyTimeComputable fun w' =>
      pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w'))) := hf1.pairEncode hgg
  have h := polyTimeComputable_ite htest hthen polyTimeComputable_pairSndD
  convert h using 1
  funext w'
  simp [stepWord]

/-- The payload map on verdict words is polynomial-time computable. -/
private theorem outWord_poly {out : List Bool → List Bool} (hout : PolyTimeComputable out) :
    PolyTimeComputable (outWord out) :=
  hout.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The duplication `x ↦ ⟨x, x⟩` is polynomial-time computable. -/
private theorem dupWord_poly : PolyTimeComputable fun x => pairEncode x x :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup

/-! ### Assembly -/

/-- Every polynomial on a bounded request fits the common power. -/
private lemma request_budget (A d D n m : ℕ) (hd : d ≤ D) (hm : m + 1 ≤ n) :
    A * (m + 1) ^ d ≤ A * n ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans (Nat.pow_le_pow_right (by omega) hd)

/-- `List.find?` depends only on the values of the predicate on the list's elements. -/
theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (by rw [ha]; exact hq), List.find?_cons_of_pos hq]
    · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
      exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
`T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.

**Proof sketch.** `2n + 7 + P n ≤ (CP + 7)(n+1)^{cP+1}` (both `7(n+1)` and `CP (n+1)^{cP}`
are at most the corresponding multiples of `(n+1)^{cP+1}`); raise to the `D`-th power
(`Nat.pow_le_pow_left`, `Nat.mul_pow`, `Nat.pow_mul`), absorb the `+ 1` with
`1 ≤ (n+1)^{(cP+1)D}`, bound `R n + 2 ≤ (CR + 2)(n+1)^{cR}` likewise, and multiply
(`Nat.mul_le_mul`, `Nat.pow_add`). -/
private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
    (hP : Pn ≤ CP * (n + 1) ^ cP) (hR : Rn ≤ CR * (n + 1) ^ cR) :
    c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2) ≤
      c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 * n + 2 + Pn + 5 ≤ (CP + 7) * (n + 1) ^ (cP + 1) := by
    have ha : n + 1 ≤ (n + 1) ^ (cP + 1) := by
      simpa using Nat.pow_le_pow_right hpos (show 1 ≤ cP + 1 by omega)
    have hb : (n + 1) ^ cP ≤ (n + 1) ^ (cP + 1) := Nat.pow_le_pow_right hpos (by omega)
    have hc := Nat.mul_le_mul_left CP hb
    calc 2 * n + 2 + Pn + 5 ≤ 7 * (n + 1) + CP * (n + 1) ^ cP := by omega
      _ ≤ 7 * (n + 1) ^ (cP + 1) + CP * (n + 1) ^ (cP + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 7 ha) hc
      _ = (CP + 7) * (n + 1) ^ (cP + 1) := by ring
  have h2 : (2 * n + 2 + Pn + 5) ^ D ≤ (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by
    calc (2 * n + 2 + Pn + 5) ^ D ≤ ((CP + 7) * (n + 1) ^ (cP + 1)) ^ D :=
          Nat.pow_le_pow_left h1 D
      _ = (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hone : 1 ≤ (n + 1) ^ ((cP + 1) * D) := Nat.one_le_pow _ _ hpos
  have h3 : A * (2 * n + 2 + Pn + 5) ^ D + 1 ≤
      (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by
    calc A * (2 * n + 2 + Pn + 5) ^ D + 1
        ≤ A * ((CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D)) + (n + 1) ^ ((cP + 1) * D) :=
          Nat.add_le_add (Nat.mul_le_mul_left A h2) hone
      _ = (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by ring
  have h4 : Rn + 2 ≤ (CR + 2) * (n + 1) ^ cR := by
    have hone' : 1 ≤ (n + 1) ^ cR := Nat.one_le_pow _ _ hpos
    calc Rn + 2 ≤ CR * (n + 1) ^ cR + 2 * (n + 1) ^ cR := by omega
      _ = (CR + 2) * (n + 1) ^ cR := by ring
  calc c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2)
      ≤ c * ((A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D)) * ((CR + 2) * (n + 1) ^ cR) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h3) h4
    _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
        rw [Nat.pow_add]; ring

/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
polynomial-time computable. This is the machine behind
`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
identification of the guarded orbit with `g^[i] x` is done there.

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the host `hostTM` over
the five clean modules (the copier, and `clean_install`/`clean_emit` of `x ↦ ⟨x, x⟩`,
`verdictWord acc`, `stepWord g P`, `outWord out`), with anchor `inl 0`, invariant `Inv P`,
step `step g P`, acceptance `acc ∘ snd`, payload `out ∘ snd`, start word `⟨x, x⟩`. The fuel
machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
`computesFunInTime_lengthBits`). `hstart`: the copier (`copy_clean`, `host_call`) then the
startup install (`host_clean`) reach the anchor seam with `⟨x, x⟩` in `2|x| + 2 + t_S` steps
with no earlier anchor visit. `hround`: from the anchor seam with an admissible word `⟨x, s⟩`,
the dispatch step, the verdict call, the branch step (`host_branch`), then either the payload
call and the halt step (`host_halt`) — state `none`, output `out s` — or the step call
returning to the anchor seam with `step g P x ⟨x, s⟩` (`stepWord_verdictWord`); the anchor
guard is `guard_add` over the segments. All requests have length at most `2|x| + 2 + P|x| + 4`,
so every call fits the common budget `T n = A (2n + 2 + P n + 5)^D` (`request_budget`), and
`final_bound` puts the combinator's bound `c (T n + 1)(R n + 2)` in normal form. -/
theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find?
          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
      | none => [] := by
  obtain ⟨S, aS, dS, hS⟩ := clean_install dupWord_poly
  obtain ⟨V, aV, dV, hV⟩ := clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := clean_emit (outWord_poly hout)
  obtain ⟨F, aF, dF, hF⟩ : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
      (polyTimeComputable_unaryPoly R)
    convert h using 1
    funext x
    simp
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K, copyTM] <;> omega
  let H := hostTM M K hk
  let anchor : H.State := .inl 0
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  have hret0 : hostRet M 0 = hostEntry M 1 := rfl
  have hret1 : hostRet M 1 = anchor := rfl
  have hret2 : hostRet M 2 = .inl 1 := rfl
  have hret3 : hostRet M 3 = anchor := rfl
  have hret4 : hostRet M 4 = .inl 2 := rfl
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor (stateWord H.k (pairEncode x x)) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean x
    obtain ⟨hcGuard, hcEnd⟩ := host_call M K hk 0 (by simp [M, copyTM]) x [] x [] [] (0 : Fin 2)
      (2 * x.length + 2) hcg (by simpa using hce)
    have hi : H.tm.initCfg x = Cfg.ofWords (hostEntry M 0) (stateWord (K + 1) []) := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i z
      simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord]
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 0) (stateWord (K + 1) []))
      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
    rw [hret0] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := host_clean M K hk 1
      (fun x => pairEncode x x) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 1) (stateWord (K + 1) x)) ts =
      Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x x)) at hsEnd
    rw [hret1] at hsEnd
    have hsB := request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact guard_add H.tm anchor _ _ _ ts hcGuard hcEnd hsGuard
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := host_dispatch M K hk x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := host_clean M K hk 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2) (stateWord (K + 1)
      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s))) at hvEnd
    rw [hret2] at hvEnd
    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (hostEntry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine guard_add H.tm anchor _ _ tv 1 hvGuard hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := host_clean M K hk 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 4) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
          (verdictWord acc (pairEncode x s))) with
            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
      rw [hret4, List.nil_append, outWord_verdictWord] at heEnd
      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
      have heB := request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : HostState M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (hostEntry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine guard_add H.tm anchor _ {Cfg.ofWords (input := x) (.inl 2 : HostState M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg heGuard
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := host_clean M K hk 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 3) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
      rw [hret3, stepWord_verdictWord] at hiEnd
      have hiB := request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (hostEntry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (hostEntry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg hiGuard
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by
    intro x
    apply (hF x).mono
    have h := request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x x)
    (fun n => R.eval n) T hFuel
    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))
    (fun x w h => inv_step g P x w h) hstart hround
  obtain ⟨CP, cP, hCP⟩ := P.eval_le
  obtain ⟨CR, cR, hCR⟩ := R.eval_le
  refine ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2), (cP + 1) * D + cR, fun x => (hL x).mono ?_⟩
  exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
    (hCP _) (hCR _)

end Complexity.IterateFind

## ===== TCSlib/Complexity/Randomized/Build/IterateFindHost.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clean-module host of the repetition machine

The generic machine layer behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Build.IterateFind` assembles it; the theorem itself lives in
`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`). Nothing here mentions the
repetition lemma's data: this file turns polynomial-time string functions into *clean
modules* and glues five of them into one finite loop body with a fresh anchor.

## Construction (DESIGN.md §2.6, steps 2–5)

* **Clean modules.** `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` deliver callable
  modules with a first-positive-visit exit; a release flag (`stopTM`) turns the first exit
  into a silent halt one step later, and minimal-halt cutting (`call_first_halt`) gives the
  uniform contract `Complexity.IterateFind.Clean`: from the seam at the start state with the
  argument as the sole tape-resident word, a first halt within a polynomial budget of the
  argument length at the seam carrying the result word, with exactly the declared chunk
  emitted (`clean_install`, `clean_emit`).
* **The copier.** A one-tape, two-state machine (`copyTM`) writes the native input on tape 0
  and returns both heads (`copy_clean`): the startup module of the loop body, since a clean
  call sees only its tape-resident argument.
* **The host.** Five modules (copier, startup install, verdict install, step install, payload
  emit) are padded to a common tape bank (`padTM`) and embedded into one finite machine
  (`hostTM`) through the forwarding transformer `Turing.emitAction`; each module's halt
  transfers control to its fixed return state (`hostRet`). The host's own control has three
  fresh states: the loop **anchor** `inl 0` (never a module-internal state, the panel repair
  J2-16/J3-6), the **branch** `inl 1`, which reads the first cell of tape 0 and dispatches on
  it (`host_branch`), and the **halt** state `inl 2` (`host_halt`). The lockstep lemma
  `host_call` (via `Turing.emit_run`) runs one module inside the host and shows that the
  anchor is never visited meanwhile; `guard_add` chains such segments.

The clean-module layer is a private copy of the module-gluing layer of
`TCSlib.Complexity.ClassNP.SAT` (`satStopTM`, `satClean_install`, `satHost_call`, …), a
template only, never a dependency.

## Main definitions

* `Complexity.IterateFind.Clean` — the uniform first-halting clean-module contract.
* `Complexity.IterateFind.copyTM` — the input copier.
* `Complexity.IterateFind.hostTM`, `hostEntry`, `hostRet`, `HostState` — the finite host over
  five modules and its entry/return states.

## Main results

* `Complexity.IterateFind.clean_install`, `clean_emit` — every polynomial-time function has a
  clean install/emit module with a polynomial budget on the argument length.
* `Complexity.IterateFind.copy_clean` — the copier's contract.
* `Complexity.IterateFind.host_call`, `host_clean` — a module call inside the host, with the
  anchor guard; `host_dispatch`, `host_branch`, `host_halt` — the host's control steps;
  `guard_add` — chaining guarded segments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1: the repeated-adversary machine this host realizes.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded multi-tape machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### Clean modules: first-halting form of the clean-call bridges

Private copy of the module layer of `TCSlib.Complexity.ClassNP.SAT` (`satStopTM`,
`satStop_clean`, `sat_call_first_halt`, `SatClean`, `satClean_install`, `satClean_emit`),
a template only. -/

/-- Convert a first-positive-exit module into a halting source: a release flag, raised after
the first step, makes the module halt silently when it is at `exit` — so an entry equal to
the exit still executes once. -/
private def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with
              state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- The release-flag embedding of a module configuration. -/
private def stopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same physical step as
the module and raises the release flag. -/
private lemma stop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, stopCfg, hs, Option.map_some]
    simp only [stopTM, hq, ↓reduceIte]
    rfl

/-- A live configuration at time `t` forces every earlier configuration to be live. -/
private lemma live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Stop a clean call one silent step after its certified first positive exit.

**Proof sketch.** Induct on prefixes, keeping the release flag false only at time zero; the
guard prevents early stopping; the final silent halt retains every seam field and every
emitted bit. -/
private lemma stop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (stopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := live_prefix C.tm c t
    (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (stopTM C entry exit).tm.runFrom (stopCfg false c) v =
      stopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        stop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = stopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, stopTM, stopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- A halting run can be cut at its first halt without changing any endpoint field
(`Nat.find` and the absorbing-halt law). -/
private lemma call_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- Uniform clean-module contract: from the seam at the start state with the argument as
the sole tape-resident word, a first halt within `B |arg|` at the seam carrying the
replacement word `result arg`, with exactly `emit arg` emitted, over every untouched native
input. -/
def Clean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Turn a clean-call bridge contract into the uniform first-halting form: the release
wrapper stops one step after the positive exit, and minimal-halt cutting retains the entire
clean configuration. -/
private lemma clean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    Clean (stopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := stop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := call_first_halt (stopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [stopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead `c (T + n + |f arg| + 1) + 1` fits one monomial of degree one
higher than the source budget `A (n+1)^d`. -/
private lemma bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- Every polynomial-time word function has a clean first-halting **install** module
(result installed as the tape-resident word, nothing emitted) with a polynomial budget on
the argument length (`Turing.FinTM.exists_installCallTM`, then `clean_stop`). -/
lemma clean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- Every polynomial-time word function has a clean first-halting **emit** module (argument
preserved, the computed chunk forwarded to the output) with a polynomial budget on the
argument length (`Turing.FinTM.exists_emitCallTM`, then `clean_stop`). -/
lemma clean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, Clean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := clean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨stopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-! ### Padding a module into the shared tape bank -/

/-- Pad an action to a larger tape count, keeping the extra tapes stationary. -/
private def padAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- A module padded into a shared bank of `K` tapes; all modules share tape zero. -/
private def padTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => padAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- Configuration embedding for the shared bank; the padding tapes are blank with heads
at the origin. -/
private def padCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with applying an action (the inactive tapes neither write nor move). -/
private lemma pad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (padAction (K := K) a).apply (padCfg c) = padCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [padAction, padCfg, Action.apply, h]

/-- The padded module runs in lockstep with the module. -/
private lemma pad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (padTM M K hk).tm.runFrom (padCfg c) t = padCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, padCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (padCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [padCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (padCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (padAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact pad_apply _ _

/-- With a positive tape count, padding a seam gives the seam with the same state word. -/
private lemma pad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    padCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [padCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    simp [padCfg, Cfg.ofWords]

/-! ### The input copier -/

/-- The input copier: a one-tape, two-state machine that writes the native input on tape 0
and returns both heads to their seam positions. State `0` copies (read a bit, write it,
advance both heads; at the right blank move both heads left into state `1`); state `1`
walks both heads left while the input head reads a bit, and at the left blank moves both
heads right and halts. -/
def copyTM : FinTM Bool where
  k := 1
  State := Fin 2
  tm := { q₀ := 0
          tr := fun q inp _ =>
            if q = 0 then
              match inp with
              | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
              | none => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
            else
              match inp with
              | some _ => ⟨.neg, fun _ => (none, .neg), none, some 1⟩
              | none => ⟨.pos, fun _ => (none, .pos), none, none⟩ }

/-- Configurations of the copier: control `q`, input head at position `i`, tape 0 holding
`w` from the origin with its head at cell `z`, nothing emitted. -/
private def copyCfg (x : List Bool) (q : Option (Fin 2)) (i : ℕ) (hi : i < x.length + 2)
    (w : List Bool) (z : ℤ) : Cfg 1 Bool (Fin 2) x :=
  ⟨q, ⟨i, hi⟩, fun _ => FinTM.bufferTape w, fun _ => z, []⟩

/-- One copying step: bit `j` is read, written at cell `j`, and both heads advance.

**Proof sketch.** The input head at position `j + 1` reads `x[j]` (`inputSymbolInner`); the
action writes it at cell `j`, which turns `bufferTape (x.take j)` into
`bufferTape (x.take (j + 1))` (`List.take_succ_eq_append_getElem`, `bufferTape_append`), and
both heads move right (`moveInputPos_pos_of_ne_right`). -/
private lemma copy_step (x : List Bool) (j : ℕ) (hj : j < x.length) :
    copyTM.tm.step (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j) =
      copyCfg x (some 0) (j + 1 + 1) (by omega) (x.take (j + 1)) ((j + 1 : ℕ) : ℤ) := by
  have hsym : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).inputSymbol = some x[j] :=
    inputSymbolInner j (by simp [copyCfg]; omega) hj
  have hs : (copyCfg x (some 0) (j + 1) (by omega) (x.take j) j).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (some (some x[j]), .pos), none, some 0⟩ :
    Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext i
    simp only [Action.apply, copyCfg]
    rw [List.take_succ_eq_append_getElem hj, FinTM.bufferTape_append, List.length_take,
      Nat.min_eq_left hj.le]
  · funext i
    simp [Action.apply, copyCfg]

/-- At the right blank the copier turns: both heads move left and the control becomes `1`.

**Proof sketch.** At position `|x| + 1` the input symbol is the right blank
(`inputSymbol_at`); the action writes nothing, moves the input head left
(`moveInputPos_neg_val`) and the work head to `|x| - 1`. -/
private lemma copy_turn (x : List Bool) :
    copyTM.tm.step (copyCfg x (some 0) (x.length + 1) (by omega) x x.length) =
      copyCfg x (some 1) x.length (by omega) x (x.length - 1) := by
  have hsym : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).inputSymbol = none := by
    rw [FinTM.inputSymbol_at _ x.length le_rfl rfl]
    simp
  have hs : (copyCfg x (some 0) (x.length + 1) (by omega) x x.length).state = some 0 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [FinTM.moveInputPos_neg_val]
    simp
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg, sub_eq_add_neg]

/-- The rewind: from input position `p ≤ |x|` in control `1`, `p` left moves of both heads
reach input position `0`.

**Proof sketch.** Induction on `p`, generalizing the work head: at position `p + 1 ≤ |x|` the
input head reads `x[p]`, so one step moves both heads left without writing, and the
induction hypothesis finishes the remaining `p` steps. -/
private lemma copy_rewind (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (z : ℤ) :
    copyTM.tm.runFrom (copyCfg x (some 1) p (by omega) x z) p =
      copyCfg x (some 1) 0 (by omega) x (z - p) := by
  induction p generalizing z with
  | zero => simp [copyCfg]
  | succ p ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : copyTM.tm.step (copyCfg x (some 1) (p + 1) (by omega) x z) =
        copyCfg x (some 1) p (by omega) x (z - 1) := by
      have hsym : (copyCfg x (some 1) (p + 1) (by omega) x z).inputSymbol = some x[p] :=
        inputSymbolInner p (by simp [copyCfg]; omega) (by omega)
      have hs : (copyCfg x (some 1) (p + 1) (by omega) x z).state = some 1 := rfl
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [hsym]
      show (⟨.neg, fun _ => (none, .neg), none, some 1⟩ : Action 1 Bool (Fin 2)).apply _ = _
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        simp only [Action.apply, copyCfg]
        rw [FinTM.moveInputPos_neg_val]
        simp
      · funext i
        simp [Action.apply, copyCfg]
      · funext i
        simp [Action.apply, copyCfg, sub_eq_add_neg]
    rw [hstep, ih (by omega)]
    simp only [copyCfg, Nat.cast_succ]
    congr 1
    funext _
    ring

/-- At the left blank the copier moves both heads right and halts. -/
private lemma copy_finish (x : List Bool) (z : ℤ) :
    copyTM.tm.step (copyCfg x (some 1) 0 (by omega) x z) =
      copyCfg x none 1 (by omega) x (z + 1) := by
  have hsym : (copyCfg x (some 1) 0 (by omega) x z).inputSymbol = none := by
    simp [Cfg.inputSymbol, copyCfg]
  have hs : (copyCfg x (some 1) 0 (by omega) x z).state = some 1 := rfl
  unfold MultiTapeTM.step
  rw [hs]
  dsimp only
  rw [hsym]
  show (⟨.pos, fun _ => (none, .pos), none, none⟩ : Action 1 Bool (Fin 2)).apply _ = _
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [Action.apply, copyCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
  · funext i
    simp [Action.apply, copyCfg]
  · funext i
    simp [Action.apply, copyCfg]

/-- **The copier's contract.** From the empty seam over native input `x`, the copier halts
after exactly `2|x| + 2` steps at the seam holding `x` on tape 0, never halting earlier.

**Proof sketch.** `|x|` copying steps (`copy_step`), the turn (`copy_turn`), `|x|` rewind
steps (`copy_rewind`), the final right move and halt (`copy_finish`); liveness before the
end from the live configuration at time `2|x| + 1` (`live_prefix`). -/
lemma copy_clean (x : List Bool) :
    (∀ v < 2 * x.length + 2,
      ¬(copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 [])) v).Halted) ∧
    copyTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []))
        (2 * x.length + 2) =
      {Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 x) with state := none} := by
  have hi : Cfg.ofWords (input := x) (0 : Fin 2) (stateWord 1 []) =
      copyCfg x (some 0) 1 (by omega) [] 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    simp [Cfg.ofWords, copyCfg, stateWord]
  have hcopy : ∀ j (hj : j ≤ x.length),
      copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) j =
        copyCfg x (some 0) (j + 1) (by omega) (x.take j) j := by
    intro j
    induction j with
    | zero => intro _; simp [copyCfg]
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), copy_step x j (by omega)]
  have hmid : copyTM.tm.runFrom (copyCfg x (some 0) 1 (by omega) [] 0) (2 * x.length + 1) =
      copyCfg x (some 1) 0 (by omega) x (-1) := by
    rw [show 2 * x.length + 1 = x.length + 1 + x.length by ring, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', hcopy x.length le_rfl]
    simp only [List.take_length]
    rw [copy_turn, copy_rewind x x.length le_rfl]
    simp only [copyCfg]
    congr 1
    funext _
    ring
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [hi]
    exact live_prefix copyTM.tm _ (2 * x.length + 1) (by rw [hmid]; simp [copyCfg]) v (by omega)
  · rw [hi, MultiTapeTM.runFrom_succ_eq_step', hmid, copy_finish]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp [copyCfg, Cfg.ofWords]
    · funext i
      simp [copyCfg, Cfg.ofWords, stateWord]
    · funext i
      simp [copyCfg, Cfg.ofWords]

/-! ### The finite host -/

/-- The host's states: three fresh control states — `0` the loop anchor, `1` the verdict
branch, `2` the halt state — and the states of the five modules (`0` copier, `1` startup
install `x ↦ ⟨x, x⟩`, `2` verdict install, `3` step install, `4` payload emit). -/
abbrev HostState (M : Fin 5 → FinTM Bool) := Fin 3 ⊕ (Σ i, (M i).State)

/-- The entry state of module `i` inside the host. -/
def hostEntry (M : Fin 5 → FinTM Bool) (i : Fin 5) : HostState M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- Return destinations of the modules: copier → startup install, startup install → anchor,
verdict → branch, step → anchor, payload emit → halt state. -/
def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : HostState M :=
  if i = 0 then hostEntry M 1 else if i = 2 then .inl 1 else if i = 4 then .inl 2 else .inl 0

/-- The finite host of the repetition machine: `K + 1` shared tapes (tape 0 carries the
state word); the anchor dispatches into the verdict module; the branch state reads the
verdict cell of tape 0 and dispatches into the payload module (`true`) or the step module
(`false`); the halt state halts; every module is padded and forwarded through
`Turing.emitAction`, its halt transferring control to its return state. -/
def hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) :
    FinTM Bool where
  k := K + 1
  State := HostState M
  tm := {
    q₀ := hostEntry M 0
    tr := fun q inp work => match q with
      | .inl c =>
        if c = 0 then FinTM.controlAction 0 (some (hostEntry M 2))
        else if c = 1 then
          FinTM.controlAction 0
            (some (if work 0 = some true then hostEntry M 4 else hostEntry M 3))
        else FinTM.controlAction 0 none
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (hostRet M i)
          ((padTM (M i) (K + 1) (hk i)).tm.tr s inp work) }

/-- Forwarding a padded clean seam produces the host's seam with the supplied output
prefix (positive tape count identifies the tape-zero word). -/
private lemma host_seam (M : Fin 5 → FinTM Bool) (K : ℕ) (i : Fin 5)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : HostState M)) (hostRet M i) pre
      (padCfg (K := K + 1) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : HostState M))).getD (hostRet M i)))
        (stateWord (K + 1) w) with output := pre ++ out} := by
  have h := pad_seam (K := K + 1) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg (K + 1) Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg (K + 1) Bool (M i).State x => c.workTapePos) h

/-- Run one clean module inside the host, forwarding exactly its output: from the host seam
at the module's entry (with any output prefix), the host reaches, at the module's first halt,
the host seam at the module's return state with the result word and the prefix followed by
the module's output, never visiting the anchor meanwhile.

**Proof sketch.** The host seam is the forwarded image (`Turing.emitCfg`) of the padded
module seam (`host_seam`); the module's live run is transferred to the padded machine
(`pad_run`) and then to the host by `Turing.emit_run`, whose agreement hypothesis holds by
definition of `hostTM`; every live prefix configuration has a state in the module's summand,
hence is not the anchor; the halting endpoint is the forwarded image of the module's
terminal seam, i.e. the host seam at the return state (`host_seam` again). -/
lemma host_call (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (i : Fin 5) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ((hostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v).state
        ≠ some (.inl 0)) ∧
    (hostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} t =
      {Cfg.ofWords (hostRet M i) (stateWord (K + 1) result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → HostState M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (hostRet M i) pre (padCfg (K := K + 1) c) =
      {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} := by
    simpa [emb, c, hostEntry] using
      host_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v =
        emitCfg emb (hostRet M i) pre (padCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (padTM (M i) (K + 1) (hk i)).tm (hostTM M K hk).tm emb (hostRet M i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [pad_run]
        exact hg u (by omega))]
    rw [pad_run]
  constructor
  · intro v hv
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, padCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact host_seam M K i hp x result pre out q none

/-- Joining two guarded segments preserves the anchor guard when the intermediate seam is
also outside the anchor. -/
lemma guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- Specialize a clean module to one call site in the host. -/
lemma host_clean (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (i : Fin 5) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : Clean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ((hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} v).state
          ≠ some (.inl 0)) ∧
      (hostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (hostEntry M i) (stateWord (K + 1) arg) with output := pre} t =
        {Cfg.ofWords (hostRet M i) (stateWord (K + 1) (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ := host_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- The anchor dispatches into the verdict module in one stationary step. -/
lemma host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w : List Bool) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) =
      Cfg.ofWords (hostEntry M 2) (stateWord (K + 1) w) := by
  change (FinTM.controlAction 0 (some (hostEntry M 2))).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]
  rfl

/-- The branch state reads the first cell of tape 0 — the verdict `b` of a verdict word —
and dispatches into the payload module (`true`) or the step module (`false`), stationary. -/
lemma host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) :
    (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) =
      Cfg.ofWords (hostEntry M (if b then 4 else 3)) (stateWord (K + 1) w) := by
  have hread : (Cfg.ofWords (input := x) (.inl 1 : HostState M)
      (stateWord (K + 1) w)).workTapeSymbols 0 = some b := by
    simp [Cfg.ofWords, Cfg.workTapeSymbols, stateWord, FinTM.bufferTape, hw]
  unfold MultiTapeTM.step
  show (FinTM.controlAction 0 (some (if (Cfg.ofWords (input := x) (.inl 1 : HostState M)
    (stateWord (K + 1) w)).workTapeSymbols 0 = some true
      then hostEntry M 4 else hostEntry M 3))).apply _ = _
  rw [hread, FinTM.controlAction_apply, moveInputPos_zero]
  cases b <;> rfl

/-- The halt state halts without emitting. -/
lemma host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1)
    (x w o : List Bool) :
    (hostTM M K hk).tm.step
        {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} =
      {Cfg.ofWords (input := x) (.inl 2 : HostState M) (stateWord (K + 1) w)
        with state := none, output := o} := by
  change (FinTM.controlAction 0 none).apply _ = _
  rw [FinTM.controlAction_apply, moveInputPos_zero]

end Complexity.IterateFind

## ===== TCSlib/Complexity/Randomized/Build/PairSplit.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.List.Induction
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The coin-splitting machine

The explicit finite machine behind `Turing.FinTM.computesFunInTime_pairSplitAt`
(`TCSlib.Complexity.Randomized.Primitives`): on a pair `⟨u, b⟩` it outputs the pair
`⟨b.take |u|, b.drop |u|⟩`, on a malformed word it outputs `[]`, and it halts within
`5 (n + 1)` steps on every input of length `n`. This is the primitive by which a reduction
cuts its coin string at a unary length and uses the two segments as independent uniform
strings ([PS10, §2.1], implicit in every reduction of chapters 2–4; foundation decision D11
of `PassShelatChapter2-4Plan.md`: the two new primitives are built in the `Build/` style).

## Construction (DESIGN.md §2.4)

One work tape and six control modes (nine states), in the idiom of the private buffered extractor of
`TCSlib.Complexity.TuringMachine.Build.Primitives` (copied privately, never edited).

* **Phase 1, `parse`.** The buffered aligned parser: aligned two-bit blocks `00`/`11` of the
  doubled first component are undoubled onto the work tape without emitting anything; the
  aligned separator `01` ends the phase; the end of the input inside a block or the aligned
  block `10` halts the machine — with empty output, since nothing has been emitted yet and
  the output tape is append-only (a malformed word must produce exactly `[]`).
* **Phase 2, `rewind`.** The work head walks back to the origin.
* **Phase 3, `copy`/`dup`.** A copy scan of the second component `b`: while the work head
  reads a stored symbol of `u` and the input head reads a bit `c` of `b`, the machine emits
  `c` twice (`dup` remembers `c` for the second emission) and advances both heads; exactly
  `min |u| |b|` bits of `b` are doubled, i.e. the first component `b.take |u|` of the output
  pair (`List.take` saturates when `b` is shorter than `u`).
* **Phase 4, `sep`/`tail`.** When the stored `u` or the input is exhausted the machine
  emits the separator `01` and copies the rest of the input verbatim (empty when `b` is
  shorter than `u`), then halts at the right blank.

Every phase is accounted for by an explicit step ledger: the parser costs two steps per
block, the rewind `|u| + 1`, the copy scan two steps per doubled bit, the separator two,
the tail one per remaining bit plus one; the total is at most `5 (n + 1)`.

## Main results

* `Turing.FinTM.exists_pairSplitTM` — a finite machine computes
  `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (and `[]` on malformed words) within `5 (n + 1)`
  steps.

## Main definitions

None public (the machine and its configuration family are private; the result is an
existence statement over `Turing.FinTM Bool`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- Finite control of the coin-splitting machine: `parse none` expects the first bit of an
aligned block and `parse (some b)` its second bit; `rewind` walks the work head back to the
origin; `copy` is the block start of the doubling scan and `dup c` its second emission of
the bit `c`; `sep` emits the second separator bit; `tail` copies the remaining input. -/
private inductive SplitControl where
  | parse (b : Option Bool)
  | rewind
  | copy
  | dup (c : Bool)
  | sep
  | tail

/-- Enumerate the control through a finite sum representation, privately. -/
private instance splitControlFintype : Fintype SplitControl :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance splitControlDecidableEq : DecidableEq SplitControl :=
  (proxy_equiv% SplitControl).symm.decidableEq

/-- The coin-splitting machine: one work tape holding the undoubled first component. The
parser (`parse`) buffers without emitting and validates the separator; `rewind` returns the
work head to the origin; `copy`/`dup` emit each input bit twice while the work head crosses
the stored first component; `sep` and `tail` emit the separator and the remaining input. -/
private def pairSplitTM : FinTM Bool where
  k := 1
  State := SplitControl
  tm :=
    { q₀ := .parse none
      tr := fun q inp work => match q with
        | .parse none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.parse (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .parse (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.parse none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some .rewind⟩
        | .rewind => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some .rewind⟩
          | none => ⟨0, fun _ => (none, .pos), none, some .copy⟩
        | .copy => match inp with
          | none => ⟨0, fun _ => (none, 0), some false, some .sep⟩
          | some c =>
            if (work 0).isSome then ⟨0, fun _ => (none, 0), some c, some (.dup c)⟩
            else ⟨0, fun _ => (none, 0), some false, some .sep⟩
        | .dup c => ⟨.pos, fun _ => (none, .pos), some c, some .copy⟩
        | .sep => ⟨0, fun _ => (none, 0), some true, some .tail⟩
        | .tail => match inp with
          | some c => ⟨.pos, fun _ => (none, 0), some c, some .tail⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The one-buffer configurations of the coin-splitting machine: control `q`, input head
after `i` input bits, work tape holding the word `a` from the origin with its head at cell
`z`, output `out`. -/
private def splitCfg (x : List Bool) (q : Option SplitControl) (i : ℕ) (hi : i ≤ x.length)
    (a : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool SplitControl x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma splitCfg_read (x : List Bool) (q : Option SplitControl) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (splitCfg x q i hi a z out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [splitCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [splitCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- Two indexed configurations with equal input indices are equal (the bound proofs are
irrelevant). -/
private lemma splitCfg_congr (x : List Bool) (q : Option SplitControl) {i i' : ℕ}
    (hi : i ≤ x.length) (hi' : i' ≤ x.length) (h : i = i') (a : List Bool) (z : ℤ)
    (out : List Bool) :
    splitCfg x q i hi a z out = splitCfg x q i' hi' a z out := by
  subst h
  rfl

/-- Doubling a word extended by one bit appends the doubled bit. -/
private lemma split_dbl_append (l : List Bool) (c : Bool) :
    dbl (l ++ [c]) = dbl l ++ [c, c] := by
  simp [dbl]

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma split_first (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    pairSplitTM.tm.step
      (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) =
      splitCfg x (some (.parse (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change (pairSplitTM.tm.tr (.parse none) _ _).apply _ = _
  rw [splitCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [splitCfg, hx])
  · funext i; simp [pairSplitTM, Action.apply, splitCfg]

/-- Equal-bit blocks append one decoded bit to the buffer; `01` begins the rewind (the work
head steps back onto the last stored cell) and `10` halts silently. Neither transition emits
physical output.
**Proof sketch.** The first step is `split_first`; the second reads the block's second bit
`c` at the input index `|pre| + 1`. Case analysis on `b` and `c`: equal bits write `some b`
at the right blank of the buffer (`bufferTape_append`) and move the work head right, `01`
moves it left into `rewind`, `10` halts; in every case the input head advances. -/
private lemma split_block (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    pairSplitTM.tm.runFrom
      (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then splitCfg x (some (.parse none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then splitCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else splitCfg x (some .rewind) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change pairSplitTM.tm.step (pairSplitTM.tm.step _) = _
  rw [split_first x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change (pairSplitTM.tm.tr (.parse (some b)) _ _).apply _ = _
  rw [splitCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [pairSplitTM, Action.apply, splitCfg])

/-- Rewinding the validated buffer from cell `j - 1` takes `j + 1` transitions and leaves
the work head at the origin in the `copy` state.
**Proof sketch.** At the left blank, move right and enter `copy`. Otherwise read a buffer
cell, move left, and invoke the induction hypothesis. -/
private lemma split_rewind (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j, j ≤ a.length →
    pairSplitTM.tm.runFrom (splitCfg x (some .rewind) i hi a ((j : ℤ) - 1) []) (j + 1) =
      splitCfg x (some .copy) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub,
      bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : pairSplitTM.tm.step
        (splitCfg x (some .rewind) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        splitCfg x (some .rewind) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The doubling scan: as long as both the stored word and the input have symbols left,
every two steps emit the current input bit twice and advance both heads.
**Proof sketch.** Induct on the number `j` of doubled bits. The `copy` step reads the
stored cell `a[j]` and the input bit `rest[j]`, emits the latter and remembers it in `dup`;
the `dup` step emits it again and moves both heads right. The output after `j` rounds is
`dbl (rest.take j)` (`List.take_succ`). -/
private lemma split_copy (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∀ j (_hja : j ≤ a.length) (hjr : j ≤ rest.length),
    pairSplitTM.tm.runFrom (splitCfg x (some .copy) pre.length (by simp [hx]) a 0 []) (2 * j) =
      splitCfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j (dbl (rest.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [Nat.mul_zero, MultiTapeTM.runFrom_zero]
    simp [splitCfg]
  | succ j ih =>
    intro hja hjr
    have hja' : j < a.length := by omega
    have hjr' : j < rest.length := by omega
    have hr : x[pre.length + j]? = some rest[j] := by
      simp [hx, hjr']
    have h1 : pairSplitTM.tm.step
        (splitCfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j))) =
        splitCfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .copy _ _).apply _ = _
      rw [splitCfg_read, hr]
      simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem hja', Option.isSome_some, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply]
    have h2 : pairSplitTM.tm.step
        (splitCfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]])) =
        splitCfg x (some .copy) (pre.length + (j + 1)) (by simp [hx]; omega) a
          ((j + 1 : ℕ) : ℤ) (dbl (rest.take (j + 1))) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr (.dup rest[j]) _ _).apply _ = _
      refine Cfg.ext rfl ?_ rfl ?_ ?_
      · show moveInputPos (⟨pre.length + j + 1, _⟩ : Fin (x.length + 2)) .pos = _
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx]; omega)]
        simp only [splitCfg, Fin.ext_iff]
        omega
      · funext k; simp [pairSplitTM, Action.apply, splitCfg]
      · show dbl (rest.take j) ++ [rest[j]] ++ (some rest[j]).toList = dbl (rest.take (j + 1))
        rw [List.take_succ, List.getElem?_eq_getElem hjr', Option.toList_some, split_dbl_append]
        simp
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', ih (by omega) (by omega), h1, h2]

/-- When the stored word or the input is exhausted, the `copy` state emits the separator
`01` in two steps (`copy` emits `false` and `sep` emits `true`) without moving any head.
**Proof sketch.** First step: if the input is exhausted, `copy` reads the blank and emits
`false`; otherwise the stored word is exhausted, the work head reads the right blank
(`bufferTape_nat`, `isSome none = false`) and the same transition fires. Second step:
`sep` emits `true` unconditionally and enters `tail`. Both steps are stationary. -/
private lemma split_sep (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (m : ℕ)
    (out : List Bool) (h : a[m]? = none ∨ x[i]? = none) :
    pairSplitTM.tm.runFrom (splitCfg x (some .copy) i hi a m out) 2 =
      splitCfg x (some .tail) i hi a m (out ++ [false, true]) := by
  have h1 : pairSplitTM.tm.step (splitCfg x (some .copy) i hi a m out) =
      splitCfg x (some .sep) i hi a m (out ++ [false]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .copy _ _).apply _ = _
    rw [splitCfg_read]
    rcases h with h | h
    · cases hxi : x[i]? with
      | none =>
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [pairSplitTM, Action.apply, splitCfg]
      | some c =>
        simp only [pairSplitTM, splitCfg, Cfg.workTapeSymbols, bufferTape_nat, h,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [Action.apply]
    · rw [h]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [pairSplitTM, Action.apply, splitCfg]
  have h2 : pairSplitTM.tm.step (splitCfg x (some .sep) i hi a m (out ++ [false])) =
      splitCfg x (some .tail) i hi a m (out ++ [false, true]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .sep _ _).apply _ = _
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    · simp [pairSplitTM, Action.apply, splitCfg]
  change pairSplitTM.tm.step (pairSplitTM.tm.step _) = _
  rw [h1, h2]

/-- The final phase copies the remaining input verbatim and halts at the right blank.
**Proof sketch.** The input prefix grows by one at each emitting transition; the buffer
and its head remain fixed. The right-blank test supplies the final halting step. -/
private lemma split_tail (x rest a : List Bool) (z : ℤ) : ∀ pre out (hx : x = pre ++ rest),
    pairSplitTM.tm.runFrom (splitCfg x (some .tail) pre.length (by simp [hx]) a z out)
        (rest.length + 1) =
      splitCfg x none x.length (le_refl _) a z (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .tail _ _).apply _ = _
    rw [splitCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairSplitTM, Action.apply, splitCfg, hx]
    · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    · simp [pairSplitTM, Action.apply, splitCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : pairSplitTM.tm.step
        (splitCfg x (some .tail) pre.length (by simp [hx]) a z out) =
        splitCfg x (some .tail) (pre ++ [b]).length (by simp [hx]) a z (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .tail _ _).apply _ = _
      rw [splitCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [splitCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairSplitTM, Action.apply, splitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once the separator has been validated, rewind, doubling scan, separator and tail cost
at most `2|a| + |rest| + 4` steps and emit exactly the output pair.
**Proof sketch.** Let `m = min |a| |rest|`. The rewind costs `|a| + 1`
(`split_rewind`), the doubling scan `2m` (`split_copy`), the separator `2` (`split_sep`;
at head `m` the stored word or the input is exhausted) and the tail `|rest| - m + 1`
(`split_tail` after re-indexing the input position past `rest.take m`). The output is
`dbl (rest.take m) ++ 01 ++ rest.drop m`, and `take`/`drop` at `m` agree with `take`/`drop`
at `|a|` because both saturate. -/
private lemma split_finish (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 4,
      (pairSplitTM.tm.runFrom
        (splitCfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (splitCfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          dbl (rest.take a.length) ++ [false, true] ++ rest.drop a.length := by
  obtain ⟨m, hm⟩ : ∃ m, m = min a.length rest.length := ⟨_, rfl⟩
  have hma : m ≤ a.length := hm ▸ Nat.min_le_left _ _
  have hmr : m ≤ rest.length := hm ▸ Nat.min_le_right _ _
  have hcases : m = a.length ∨ (m = rest.length ∧ rest.length ≤ a.length) := by
    rcases Nat.le_total a.length rest.length with h | h
    · exact Or.inl (hm ▸ Nat.min_eq_left h)
    · exact Or.inr ⟨hm ▸ Nat.min_eq_right h, h⟩
  have hsep : a[m]? = none ∨ x[pre.length + m]? = none := by
    rcases hcases with h | ⟨h, _⟩
    · left
      rw [h]
      exact List.getElem?_eq_none (le_refl _)
    · right
      rw [h, hx]
      exact List.getElem?_eq_none (by simp)
  have htake : rest.take m = rest.take a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.take_length, List.take_of_length_le hle]
  have hdrop : rest.drop m = rest.drop a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.drop_length, List.drop_of_length_le hle]
  have hlen : (pre ++ rest.take m).length = pre.length + m := by
    simp [List.length_take, Nat.min_eq_left hmr]
  have hx' : x = (pre ++ rest.take m) ++ rest.drop m := by
    rw [List.append_assoc, List.take_append_drop]
    exact hx
  refine ⟨(a.length + 1) + (2 * m + 2) + ((rest.drop m).length + 1), ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · rw [MultiTapeTM.runFrom_add _ (a.length + 1 + (2 * m + 2)) ((rest.drop m).length + 1),
      MultiTapeTM.runFrom_add _ (a.length + 1) (2 * m + 2),
      split_rewind x a _ _ a.length (le_refl _), MultiTapeTM.runFrom_add _ (2 * m) 2,
      split_copy x pre rest a hx m hma hmr, split_sep x _ _ a m _ hsep,
      splitCfg_congr x _ _ (by simp [hx]) hlen.symm,
      split_tail x (rest.drop m) a m (pre ++ rest.take m) _ hx']
    simp [splitCfg, htake, hdrop]

/-- The silent aligned parser either rejects or validates and runs the emission phases.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the already-decoded
buffer. A doubled bit costs two steps and enlarges the buffer by one; the linear potential
`3|rest| + 2|a| + 5` pays for both effects. Missing and forbidden separators halt silently
with empty output. At `01`, apply the finish ledger `split_finish`. -/
private lemma split_run (x rest : List Bool) : ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      (pairSplitTM.tm.runFrom
        (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (splitCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (u, b) => dbl (b.take (a.length + u.length)) ++ [false, true] ++
              b.drop (a.length + u.length)
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [splitCfg_read]
    simp [hx, pairSplitTM, Action.apply, splitCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change (pairSplitTM.tm.step (pairSplitTM.tm.step _)).state = none ∧
      (pairSplitTM.tm.step (pairSplitTM.tm.step _)).output = _
    rw [split_first x pre [] a b hx]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [splitCfg_read]
    cases b <;> simp [hx, pairSplitTM, Action.apply, splitCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ :=
        ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by
        simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, split_block x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases hd : pairDecode rest with
        | none => cases b <;> simpa [pairDecode, hd] using ho
        | some p =>
          obtain ⟨u, v⟩ := p
          have e : a.length + (u.length + 1) = a.length + 1 + u.length := by omega
          cases b <;> simpa [pairDecode, hd, e] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := split_finish x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, split_block x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [split_block x pre rest a true false hx]
        simp [splitCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The coin-splitting machine halts on every input within `5(|x| + 1)` steps with the
output pair `⟨b.take |u|, b.drop |u|⟩` (for `x = ⟨u, b⟩`) or `[]` (malformed `x`). The
initial buffer and decoded prefix are empty.
**Proof sketch.** Instantiate `split_run` with the empty prefix and the empty buffer; the
initial configuration is the indexed configuration at index `0` with blank work tape
(`Cfg.ext`). On a decoded pair the output `dbl (b.take |u|) ++ 01 ++ b.drop |u|` is
`pairEncode (b.take |u|) (b.drop |u|)` by `pairEncode_eq_dbl`; the ledger
`3|x| + 5 ≤ 5(|x| + 1)` is absorbed by `ComputesInTime.mono`. -/
private lemma split_computes (x : List Bool) :
    pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := split_run x x [] [] rfl
  have hinit : pairSplitTM.tm.initCfg x =
      splitCfg x (some (.parse none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairSplitTM, splitCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    refine ⟨hs, ?_⟩
    cases hd : pairDecode x with
    | none => simpa [hd] using ho
    | some p =>
      obtain ⟨u, b⟩ := p
      simpa [hd, pairEncode_eq_dbl] using ho
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-- **The coin-splitting machine exists:** a finite machine computes, on a pair `⟨u, b⟩`,
the pair `⟨b.take |u|, b.drop |u|⟩` — and `[]` on a malformed word — within `5 (n + 1)`
steps on inputs of length `n`. This is the machine behind
`Turing.FinTM.computesFunInTime_pairSplitAt` [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** The private machine `pairSplitTM` above (one work tape, six control
modes: buffered aligned parser, rewind, doubling scan, separator, tail) with the step
ledger `split_run`: `3 |x| + 5 ≤ 5 (|x| + 1)` steps from the initial configuration, output
`dbl (b.take |u|) ++ 01 ++ b.drop |u| = pairEncode (b.take |u|) (b.drop |u|)`
(`Turing.pairEncode_eq_dbl`). -/
theorem exists_pairSplitTM :
    ∃ M : FinTM Bool,
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => 5 * (n + 1) :=
  ⟨pairSplitTM, fun x => split_computes x⟩

end Turing.FinTM

## ===== TCSlib/Complexity/Randomized/Build/StateLoop.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State loops: the pure and FP layer behind the derived repetition lemmas

The derived lemmas of `TCSlib.Complexity.Randomized.Repetition` — the `R(|x|)`-fold
iteration `Complexity.polyTimeComputable_iterate`, the concatenating variant
`Complexity.polyTimeComputable_iterateEmit`, and the string functions
`Complexity.polyTimeComputable_majority`, `polyTimeComputable_pairXor`,
`polyTimeComputable_pairEq`, `polyTimeComputable_blockMap` — are all instances of one pattern,
the **state loop**: a state word `⟨x, s⟩` whose first component retains the input `x` and whose
second component `s` evolves by a polynomial-time map `step` from `start x`; a polynomial-time
test `acc` fires for the first time at a round `N x ≤ R|x|`, and a polynomial-time `out` reads
the answer off the state. The loop is run by `Complexity.polyTimeComputable_iterateFind` on the
**guarded** step `Complexity.StateLoop.gstep step B`, which refuses to move when the new state
would exceed the length bound `B|fst w|`; thus the orbit of *every* word is polynomially
bounded (the hypothesis `horbit` of the repetition lemma quantifies over all words, not only
over well-formed state words), while on the genuine orbit the guard never fires.

This file supplies everything that does not depend on the repetition lemma itself:

* a small FP toolkit (head bit, tail, Boolean connectives of one-bit tests, the emptiness test
  and the length comparison of two polynomial-time maps);
* the state orbit `Complexity.StateLoop.orbit`, the guarded step `Complexity.StateLoop.gstep`
  with its polynomial bound on arbitrary words and its agreement with the orbit on well-formed
  words, and the `List.find?` evaluation `Complexity.StateLoop.find?_range_eq_some`;
* for the two iteration lemmas, the data of their state loops (`start`, `step`, `acc`, `out`),
  their polynomial-time proofs and the closed forms of the orbits (namespaces
  `Complexity.StateLoop.IterLoop` and `Complexity.StateLoop.EmitLoop`).

The four string loops (`MajLoop`, `XorLoop`, `EqLoop`, `BlockLoop`) are in
`TCSlib.Complexity.Randomized.Build.StringLoops`; the assembly through
`Complexity.polyTimeComputable_iterateFind` and the six public theorems live in
`TCSlib.Complexity.Randomized.Repetition`.

## Main definitions

* `Complexity.StateLoop.orbit`, `Complexity.StateLoop.gstep`, `Complexity.StateLoop.gstepBound`
  — the state orbit, the length-guarded step on state words and its orbit bound.
* `Complexity.StateLoop.IterLoop`, `Complexity.StateLoop.EmitLoop` — the state-loop data of
  `Complexity.polyTimeComputable_iterate` and `polyTimeComputable_iterateEmit`.

## Main results

* `Complexity.StateLoop.gstep_poly`, `Complexity.StateLoop.length_gstep_iterate_le`,
  `Complexity.StateLoop.gstep_iterate_eq` — the guarded step is polynomial-time, its orbit
  from any word `w` stays within `3|w| + 2 + B|w|`, and on the genuine orbit it agrees with
  `orbit`.
* `Complexity.StateLoop.find?_range_eq_some` — `List.find?` on `List.range (m + 1)` returns the
  first index at which the predicate holds.
* `Complexity.StateLoop.IterLoop.orbit_eq`, `Complexity.StateLoop.EmitLoop.orbit_eq` — the
  closed forms `⟨1^i, g^[i] x⟩` and `⟨1^i, ⟨g^[i] x, emit x ++ ⋯ ++ emit (g^[i-1] x)⟩⟩`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Lemma 80.5; Theorem 87.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines; §2.2, the class FP.)
-/

namespace Complexity.StateLoop

open Turing

/-! ### An FP toolkit -/

/-- The length comparison `|g x| ≤ |f x|` of two polynomial-time maps is a polynomial-time
one-bit test (`Complexity.polyTimeComputable_lenLe` on the pair `⟨f x, g x⟩`). -/
theorem lenLe_comp {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun x => [decide ((g x).length ≤ (f x).length)] := by
  convert polyTimeComputable_lenLe.comp (hf.pairEncode hg) using 1
  funext x
  simp

/-- The unary string `1^{p(|f x|)}` of a polynomial-time map `f` is polynomial-time
(`Complexity.polyTimeComputable_unaryPoly` after `f`). -/
theorem unaryPoly_comp (p : PolyExpr) {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable fun x => List.replicate (p.eval (f x).length) true :=
  (polyTimeComputable_unaryPoly p).comp hf

/-- The first bit of a word (`false` on the empty word) as a one-bit output: `[w.headD false]`
is `(w ++ [false]).take 1`, a typed cut `Complexity.polyTimeComputable_pairTakePoly` at the
constant length `1`. -/
theorem headBit_poly : PolyTimeComputable fun w => [w.headD false] := by
  have h := (polyTimeComputable_pairTakePoly (.const 1)).comp
    ((polyTimeComputable_const []).pairEncode
      (polyTimeComputable_id.append (polyTimeComputable_const [false])))
  convert h using 1
  funext w
  cases w <;> simp

/-- The tail of a word is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at the
constant length `1`). -/
theorem tail_poly : PolyTimeComputable List.tail := by
  have h := (polyTimeComputable_pairDropPoly (.const 1)).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext w
  simp [List.drop_one]

/-- Prepending one bit is polynomial-time. -/
theorem cons_poly (b : Bool) : PolyTimeComputable fun w => b :: w :=
  polyTimeComputable_prepend [b]

/-- The emptiness test `[decide (w = [])]` is polynomial-time (the length test `|w| ≤ 0`). -/
theorem isNil_poly : PolyTimeComputable fun w => [decide (w = [])] := by
  convert lenLe_comp (polyTimeComputable_const []) polyTimeComputable_id using 1
  funext w
  simp

/-- Negation of a one-bit test is polynomial-time. -/
theorem not_poly {p : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x]) :
    PolyTimeComputable fun x => [!p x] := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext x
  cases p x <;> rfl

/-- Disjunction of two one-bit tests is polynomial-time. -/
theorem or_poly {p q : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x])
    (hq : PolyTimeComputable fun x => [q x]) : PolyTimeComputable fun x => [p x || q x] := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [true]) hq using 1
  funext x
  cases p x <;> rfl

/-- Exclusive or of two one-bit tests is polynomial-time. -/
theorem xor_poly {p q : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x])
    (hq : PolyTimeComputable fun x => [q x]) :
    PolyTimeComputable fun x => [xor (p x) (q x)] := by
  convert polyTimeComputable_ite hp (not_poly hq) hq using 1
  funext x
  cases p x <;> cases q x <;> rfl

/-- The two components of a word together are no longer than the word. -/
theorem length_pairFstD_add_pairSndD_le (z : List Bool) :
    (pairFstD z).length + (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, pairSndD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z a b h
    subst hz
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    omega

/-- The length of the concatenation of `i` chunks of length at most `M` is at most `i · M`. -/
theorem length_flatMap_range_le (f : ℕ → List Bool) (M : ℕ) :
    ∀ i, (∀ j < i, (f j).length ≤ M) → ((List.range i).flatMap f).length ≤ i * M
  | 0, _ => by simp
  | i + 1, hf => by
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton,
      Nat.succ_mul]
    have h1 := length_flatMap_range_le f M i (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have h2 := hf i (Nat.lt_succ_self i)
    omega

/-- `List.find?` on `List.range (m + 1)` returns the first index `N ≤ m` at which the predicate
holds (`List.find?_eq_some_iff_getElem`). -/
theorem find?_range_eq_some {p : ℕ → Bool} {N m : ℕ} (hN : N ≤ m)
    (hfirst : ∀ i < N, p i = false) (hlast : p N = true) :
    (List.range (m + 1)).find? p = some N := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hlast, N, by simpa using Nat.lt_succ_of_le hN, by simp, fun j hj => ?_⟩
  simp [hfirst j hj]

/-! ### The state orbit and the guarded step -/

/-- The state orbit: `orbit start step x i` is the state after `i` rounds, from `start x`,
advancing by `s ↦ step ⟨x, s⟩` (the step reads the retained input `x` off the state word). -/
def orbit (start step : List Bool → List Bool) (x : List Bool) : ℕ → List Bool
  | 0 => start x
  | i + 1 => step (pairEncode x (orbit start step x i))

/-- The orbit at round `0` is the initial state. -/
@[simp] theorem orbit_zero (start step : List Bool → List Bool) (x : List Bool) :
    orbit start step x 0 = start x := rfl

/-- The orbit at round `i + 1` is the step applied to the state word at round `i`. -/
@[simp] theorem orbit_succ (start step : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start step x (i + 1) = step (pairEncode x (orbit start step x i)) := rfl

/-- The length-guarded step on state words: advance `w` to `⟨fst w, step w⟩` if the new state
fits the bound `B|fst w|`, else stay. -/
def gstep (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool) : List Bool :=
  if (step w).length ≤ B.eval (pairFstD w).length then pairEncode (pairFstD w) (step w) else w

/-- The bound `3n + 2 + B(n)` on the guarded orbit of an arbitrary word of length `n`. -/
def gstepBound (B : PolyExpr) : PolyExpr :=
  .add (.mul (.const 3) .var) (.add (.const 2) B)

/-- The guarded step is polynomial-time: `Complexity.polyTimeComputable_ite` on the length
test `|step w| ≤ |1^{B|fst w|}|` (`lenLe_comp`, `unaryPoly_comp`), the pairing of the first
projection with `step`, and the identity. -/
theorem gstep_poly {step : List Bool → List Bool} (hstep : PolyTimeComputable step)
    (B : PolyExpr) : PolyTimeComputable (gstep step B) := by
  have htest : PolyTimeComputable fun w =>
      [decide ((step w).length ≤ B.eval (pairFstD w).length)] := by
    convert lenLe_comp (unaryPoly_comp B polyTimeComputable_pairFstD) hstep using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_pairFstD.pairEncode hstep)
    polyTimeComputable_id using 1
  funext w
  simp [gstep]

/-- Along the guarded orbit of any word `w`, every point is `w` itself or a state word
`⟨fst w, s⟩` with `|s| ≤ B|fst w|`.

**Proof sketch.** Induction on the round. From `w` itself the guarded step either stays
(first alternative) or moves to `⟨fst w, step w⟩` with the guard's bound. From a state word
`⟨fst w, s⟩` the first projection is again `fst w` (`Complexity.pairFstD_pairEncode`), so the
step either stays (the bound on `s` is inherited) or moves to `⟨fst w, step ⟨fst w, s⟩⟩` with
the guard's bound. -/
theorem gstep_iterate_cases (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool)
    (i : ℕ) :
    (gstep step B)^[i] w = w ∨
      ∃ s, (gstep step B)^[i] w = pairEncode (pairFstD w) s ∧
        s.length ≤ B.eval (pairFstD w).length := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hw | ⟨s, hs, hlen⟩
    · rw [hw]
      unfold gstep
      split_ifs with hg
      · exact Or.inr ⟨step w, rfl, hg⟩
      · exact Or.inl rfl
    · rw [hs]
      unfold gstep
      rw [pairFstD_pairEncode]
      split_ifs with hg
      · exact Or.inr ⟨_, rfl, hg⟩
      · exact Or.inr ⟨s, rfl, hlen⟩

/-- The guarded orbit of any word `w` stays within `3|w| + 2 + B|w|` (`gstep_iterate_cases`,
`Complexity.length_pairFstD_le` and the monotonicity of `B`). -/
theorem length_gstep_iterate_le (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool)
    (i : ℕ) : ((gstep step B)^[i] w).length ≤ (gstepBound B).eval w.length := by
  have hB := B.eval_mono (length_pairFstD_le w)
  have hf := length_pairFstD_le w
  simp only [gstepBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]
  rcases gstep_iterate_cases step B w i with hw | ⟨s, hs, hlen⟩
  · rw [hw]; omega
  · rw [hs, length_pairEncode]; omega

/-- On the genuine orbit the guard never fires: if the states of the first `n` rounds fit the
bound `B|x|`, the guarded orbit from `⟨x, start x⟩` is `⟨x, orbit start step x i⟩` for `i ≤ n`. -/
theorem gstep_iterate_eq (start step : List Bool → List Bool) (B : PolyExpr) (x : List Bool)
    (n : ℕ) (hb : ∀ i ≤ n, (orbit start step x i).length ≤ B.eval x.length) :
    ∀ i ≤ n, (gstep step B)^[i] (pairEncode x (start x)) = pairEncode x (orbit start step x i) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hi)]
    have hb' : (step (pairEncode x (orbit start step x i))).length ≤ B.eval x.length :=
      hb (i + 1) hi
    unfold gstep
    rw [pairFstD_pairEncode, if_pos hb']
    rfl

/-! ### `iterate`: a unary round counter next to the orbit point -/

namespace IterLoop

/-- The initial state `⟨[], x⟩`: empty counter, orbit point `x`. -/
def start (x : List Bool) : List Bool := pairEncode [] x

/-- The step on the state word `⟨x, ⟨cnt, s⟩⟩`: append a token to the counter and advance the
orbit point, giving `⟨true :: cnt, g s⟩`. -/
def step (g : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w)) (g (pairSndD (pairSndD w)))

/-- The acceptance test on `⟨x, ⟨cnt, s⟩⟩`: the counter has reached `R|x|`. -/
def acc (R : PolyExpr) (w : List Bool) : Bool :=
  decide (R.eval (pairFstD w).length ≤ (pairFstD (pairSndD w)).length)

/-- The output on `⟨x, ⟨cnt, s⟩⟩`: the orbit point `s`. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_const []).pairEncode polyTimeComputable_id

/-- The step is polynomial-time. -/
theorem step_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (step g) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    (hg.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The acceptance test is polynomial-time (`lenLe_comp` against `1^{R|x|}`). -/
theorem acc_poly (R : PolyExpr) : PolyTimeComputable fun w => [acc R w] := by
  convert lenLe_comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    (unaryPoly_comp R polyTimeComputable_pairFstD) using 1
  funext w
  simp [acc]

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The closed form of the orbit: `⟨1^i, g^[i] x⟩`. -/
theorem orbit_eq (g : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start (step g) x i = pairEncode (List.replicate i true) (g^[i] x) := by
  induction i with
  | zero => simp [start]
  | succ i ih => simp [step, ih, List.replicate_succ, Function.iterate_succ_apply']

end IterLoop

/-! ### `iterateEmit`: counter, orbit point and accumulator -/

namespace EmitLoop

/-- The initial state `⟨[], ⟨x, []⟩⟩`: empty counter, orbit point `x`, empty accumulator. -/
def start (x : List Bool) : List Bool := pairEncode [] (pairEncode x [])

/-- The step on `⟨x, ⟨cnt, ⟨s, a⟩⟩⟩`: `⟨true :: cnt, ⟨g s, a ++ emit s⟩⟩`. -/
def step (g emit : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w))
    (pairEncode (g (pairFstD (pairSndD (pairSndD w))))
      (pairSndD (pairSndD (pairSndD w)) ++ emit (pairFstD (pairSndD (pairSndD w)))))

/-- The output on `⟨x, ⟨cnt, ⟨s, a⟩⟩⟩`: `a ++ emit s`. -/
def out (emit : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD w)) ++ emit (pairFstD (pairSndD (pairSndD w)))

/-- The orbit point of the state word. -/
theorem point_poly : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD w)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_const []).pairEncode
    (polyTimeComputable_id.pairEncode (polyTimeComputable_const []))

/-- The step is polynomial-time. -/
theorem step_poly {g emit : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hemit : PolyTimeComputable emit) : PolyTimeComputable (step g emit) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    ((hg.comp point_poly).pairEncode (accum_poly.append (hemit.comp point_poly)))

/-- The output is polynomial-time. -/
theorem out_poly {emit : List Bool → List Bool} (hemit : PolyTimeComputable emit) :
    PolyTimeComputable (out emit) :=
  accum_poly.append (hemit.comp point_poly)

/-- The closed form of the orbit: `⟨1^i, ⟨g^[i] x, emit x ++ ⋯ ++ emit (g^[i-1] x)⟩⟩`. -/
theorem orbit_eq (g emit : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start (step g emit) x i =
      pairEncode (List.replicate i true)
        (pairEncode (g^[i] x) ((List.range i).flatMap fun j => emit (g^[j] x))) := by
  induction i with
  | zero => simp [start]
  | succ i ih =>
    simp [step, ih, List.replicate_succ, Function.iterate_succ_apply', List.range_succ]

end EmitLoop

end Complexity.StateLoop

## ===== TCSlib/Complexity/Randomized/Build/StringLoops.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Bool.Count
import TCSlib.Complexity.Randomized.Build.StateLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String loops: majority, pairwise xor, equality test and block map

The four string functions of `TCSlib.Complexity.Randomized.Repetition` —
`Complexity.polyTimeComputable_majority` (the vote of [PS10, Algorithm 89.6]),
`Complexity.polyTimeComputable_pairXor` (the one-time pad of [PS10, Algorithms 92.1 and 99.1]
and the mask of [PS10, Algorithm 104.3]), `Complexity.polyTimeComputable_pairEq` (the test
`f(z_i) = y` of [PS10, Algorithm 38.5]) and `Complexity.polyTimeComputable_blockMap` (the
blockwise evaluation of `prodFun` in [PS10, Theorem 35.1]) — are **state loops** in the sense
of `TCSlib.Complexity.Randomized.Build.StateLoop`: a state word `⟨z, s⟩` retains the input `z`,
the state `s` consumes the input one bit (or one block) per round, a test `acc` fires for the
first time when the input is exhausted, and `out` reads the answer off the final state.

This file supplies, for each of the four, the loop data (`start`, `step`, `acc`, `out`, the
number of rounds), the polynomial-time proofs of the data, the closed form of the orbit, its
length bound and the values of `acc` and `out` along it:

* `Complexity.StateLoop.MajLoop` — state `⟨rest, ⟨1^{#true}, 1^{#false}⟩⟩`, one bit per round;
* `Complexity.StateLoop.XorLoop` — state `⟨a', ⟨b', c⟩⟩`, one xor bit appended per round;
* `Complexity.StateLoop.EqLoop` — state `⟨a', ⟨b', flag⟩⟩`, the flag recording a mismatch;
* `Complexity.StateLoop.BlockLoop` — state `⟨rest, c⟩`, one block of `b(|fst z|)` bits per
  round, the accumulator extended by `g` of the block.

The assembly through `Complexity.polyTimeComputable_iterateFind` (the private state-loop form
`polyTimeComputable_stateFind`) and the four public theorems live in
`TCSlib.Complexity.Randomized.Repetition`.

## Main definitions

* `Complexity.StateLoop.MajLoop`, `Complexity.StateLoop.XorLoop`, `Complexity.StateLoop.EqLoop`,
  `Complexity.StateLoop.BlockLoop` — the state-loop data of the four string functions.

## Main results

* The `orbit_eq` closed forms, `orbit_length_le` bounds, `acc_orbit_false`/`acc_orbit_true`
  values and `out_orbit` identities of the four loops; `Complexity.StateLoop.EqLoop.verdict_eq`
  (equal lengths and equal prefixes is equality).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Algorithms 89.6, 92.1, 99.1 and 104.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines; §2.2, the class FP.)
-/

namespace Complexity.StateLoop

open Turing

/-! ### `majority`: consume the word, counting `true`s and `false`s in unary -/

namespace MajLoop

/-- The initial state `⟨w, ⟨[], []⟩⟩`: the whole word remains, both counters empty. -/
def start (w : List Bool) : List Bool := pairEncode w (pairEncode [] [])

/-- The step on `⟨w, ⟨rest, ⟨t, f⟩⟩⟩`: drop the first bit of `rest` and append a token to the
counter of its value. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (if (pairFstD (pairSndD v)).headD false then
      pairEncode (true :: pairFstD (pairSndD (pairSndD v))) (pairSndD (pairSndD (pairSndD v)))
    else pairEncode (pairFstD (pairSndD (pairSndD v))) (true :: pairSndD (pairSndD (pairSndD v))))

/-- The acceptance test: the remaining word is empty. -/
def acc (v : List Bool) : Bool := decide (pairFstD (pairSndD v) = [])

/-- The output: the verdict `#false + 1 ≤ #true`, i.e. a strict majority of `true`. -/
def out (v : List Bool) : List Bool :=
  [decide ((true :: pairSndD (pairSndD (pairSndD v))).length ≤
    (pairFstD (pairSndD (pairSndD v))).length)]

/-- The remaining word of the state word. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The `true` counter of the state word. -/
theorem trues_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The `false` counter of the state word. -/
theorem falses_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_id.pairEncode (polyTimeComputable_const (pairEncode [] []))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_ite` on the head bit). -/
theorem step_poly : PolyTimeComputable step := by
  have hp : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    headBit_poly.comp rest_poly
  have h := (tail_poly.comp rest_poly).pairEncode (polyTimeComputable_ite hp
    (((cons_poly true).comp trues_poly).pairEncode falses_poly)
    (trues_poly.pairEncode ((cons_poly true).comp falses_poly)))
  convert h using 1

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] :=
  isNil_poly.comp rest_poly

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  lenLe_comp trues_poly ((cons_poly true).comp falses_poly)

/-- The closed form of the orbit for `i ≤ |w|`:
`⟨w.drop i, ⟨1^{#true (w.take i)}, 1^{#false (w.take i)}⟩⟩`. -/
theorem orbit_eq (w : List Bool) : ∀ i ≤ w.length, orbit start step w i =
    pairEncode (w.drop i)
      (pairEncode (List.replicate ((w.take i).count true) true)
        (List.replicate ((w.take i).count false) true))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq w i (Nat.le_of_succ_le hi)]
    obtain ⟨c, hc⟩ : ∃ c, w[i]? = some c := ⟨_, List.getElem?_eq_getElem hi⟩
    have htake : w.take (i + 1) = w.take i ++ [c] := by rw [List.take_succ, hc]; rfl
    have hhead : (w.drop i).headD false = c := by
      rw [List.headD_eq_head?_getD, List.head?_drop, hc]; rfl
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop, hhead, htake,
      List.count_append]
    cases c <;> simp [List.replicate_succ]

/-- The states of the first `|w|` rounds have length at most `5|w| + 4`. -/
theorem orbit_length_le (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    (orbit start step w i).length ≤ 5 * w.length + 4 := by
  rw [orbit_eq w i hi, length_pairEncode, length_pairEncode, List.length_replicate,
    List.length_replicate, List.length_drop]
  have h1 : (w.take i).count true ≤ (w.take i).length := List.count_le_length
  have h2 : (w.take i).count false ≤ (w.take i).length := List.count_le_length
  rw [List.length_take] at h1 h2
  omega

/-- Before round `|w|` the remaining word is nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (w : List Bool) (i : ℕ) (hi : i < w.length) :
    acc (pairEncode w (orbit start step w i)) = false := by
  rw [orbit_eq w i hi.le]
  simp [acc, List.drop_eq_nil_iff, hi]

/-- At round `|w|` the remaining word is empty, so `acc` is `true`. -/
theorem acc_orbit_true (w : List Bool) : acc (pairEncode w (orbit start step w w.length)) = true := by
  rw [orbit_eq w w.length le_rfl]
  simp [acc]

/-- At round `|w|` the output is the majority verdict `[decide (|w| < 2 · #true w)]`
(`List.count_true_add_count_false`). -/
theorem out_orbit (w : List Bool) :
    out (pairEncode w (orbit start step w w.length)) = [decide (w.length < 2 * w.count true)] := by
  rw [orbit_eq w w.length le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, List.take_length, List.length_cons,
    List.length_replicate]
  have := List.count_true_add_count_false w
  congr 1
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩

end MajLoop

/-! ### `pairXor`: consume both components, emitting one xor bit per round -/

namespace XorLoop

/-- The initial state `⟨fst z, ⟨snd z, []⟩⟩`: both components remain, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The step on `⟨z, ⟨a, ⟨b, c⟩⟩⟩`: `⟨a.tail, ⟨b.tail, c ++ [xor (head a) (head b)]⟩⟩`. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (pairSndD (pairSndD (pairSndD v)) ++
        [xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false)]))

/-- The acceptance test: one of the two remaining components is empty. -/
def acc (v : List Bool) : Bool :=
  decide (pairFstD (pairSndD v) = []) || decide (pairFstD (pairSndD (pairSndD v)) = [])

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD (pairSndD v))

/-- The number of rounds: the length of the shorter component. -/
def rounds (z : List Bool) : ℕ := min (pairFstD z).length (pairSndD z).length

/-- The remaining first component of the state word. -/
theorem fstRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The remaining second component of the state word. -/
theorem sndRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The xor of the two head bits of the state word, as a one-bit output. -/
theorem xorBit_poly : PolyTimeComputable fun v =>
    [xor ((pairFstD (pairSndD v)).headD false) ((pairFstD (pairSndD (pairSndD v))).headD false)] := by
  have hpa : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    headBit_poly.comp fstRest_poly
  have hpb : PolyTimeComputable fun v => [(pairFstD (pairSndD (pairSndD v))).headD false] :=
    headBit_poly.comp sndRest_poly
  exact xor_poly hpa hpb

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (tail_poly.comp fstRest_poly).pairEncode
    ((tail_poly.comp sndRest_poly).pairEncode (accum_poly.append xorBit_poly))

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    isNil_poly.comp fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp sndRest_poly
  exact or_poly ha hb

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- The closed form of the orbit for `i ≤ rounds z`:
`⟨a.drop i, ⟨b.drop i, (zipWith xor a b).take i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ rounds z, orbit start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) ((List.zipWith xor (pairFstD z) (pairSndD z)).take i))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    have hzip : (List.zipWith xor (pairFstD z) (pairSndD z))[i]? =
        some (xor (pairFstD z)[i] (pairSndD z)[i]) := by
      rw [List.getElem?_zipWith, hza, hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some, List.take_succ, hzip,
      Option.toList_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 4`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ rounds z) :
    (orbit start step z i).length ≤ 5 * z.length + 4 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop,
    List.length_take, List.length_zipWith]
  have := length_pairFstD_add_pairSndD_le z
  omega

/-- Before round `rounds z` both remaining components are nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < rounds z) :
    acc (pairEncode z (orbit start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold rounds at hi
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `rounds z` one remaining component is empty, so `acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) : acc (pairEncode z (orbit start step z (rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, rounds]
  omega

/-- At round `rounds z` the output is `zipWith xor (fst z) (snd z)`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit start step z (rounds z))) =
      List.zipWith xor (pairFstD z) (pairSndD z) := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairSndD_pairEncode]
  have : rounds z = (List.zipWith xor (pairFstD z) (pairSndD z)).length := by
    rw [List.length_zipWith]; rfl
  rw [this, List.take_length]

end XorLoop

/-! ### `pairEq`: consume both components, recording the first mismatch -/

namespace EqLoop

/-- The step on `⟨z, ⟨a, ⟨b, flag⟩⟩⟩`: `⟨a.tail, ⟨b.tail, flag'⟩⟩` where `flag'` is `[true]` if the
head bits differ and `flag` otherwise (`[]` means "no mismatch so far"). -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (if xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false) then [true]
        else pairSndD (pairSndD (pairSndD v))))

/-- The output: both remaining components are empty and no mismatch was recorded. -/
def out (v : List Bool) : List Bool :=
  [decide (pairFstD (pairSndD v) = []) && decide (pairFstD (pairSndD (pairSndD v)) = []) &&
    decide (pairSndD (pairSndD (pairSndD v)) = [])]

/-- The mismatch flag after `i` rounds: `[]` if the first `i` bits agree, `[true]` otherwise. -/
def flag (a b : List Bool) (i : ℕ) : List Bool := if a.take i = b.take i then [] else [true]

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (tail_poly.comp XorLoop.fstRest_poly).pairEncode
    ((tail_poly.comp XorLoop.sndRest_poly).pairEncode
      (polyTimeComputable_ite XorLoop.xorBit_poly (polyTimeComputable_const [true])
        XorLoop.accum_poly))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    isNil_poly.comp XorLoop.fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp XorLoop.sndRest_poly
  have hc : PolyTimeComputable fun v => [decide (pairSndD (pairSndD (pairSndD v)) = [])] :=
    isNil_poly.comp XorLoop.accum_poly
  exact polyTimeComputable_and (polyTimeComputable_and ha hb) hc

/-- Two words ending in one bit each are equal iff their bodies and their last bits are. -/
theorem append_singleton_eq_iff (l₁ l₂ : List Bool) (c₁ c₂ : Bool) :
    l₁ ++ [c₁] = l₂ ++ [c₂] ↔ l₁ = l₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    exact ⟨List.append_inj_left' h rfl, List.singleton_inj.mp (List.append_inj_right' h rfl)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The flag after `i + 1` rounds: set if the `i`-th bits differ, else unchanged. -/
theorem flag_succ (a b : List Bool) (i : ℕ) (ca cb : Bool) (hca : a[i]? = some ca)
    (hcb : b[i]? = some cb) :
    flag a b (i + 1) = if xor ca cb then [true] else flag a b i := by
  unfold flag
  rw [List.take_succ, List.take_succ, hca, hcb, Option.toList_some, Option.toList_some]
  cases ca <;> cases cb <;> simp [append_singleton_eq_iff]

/-- The flag has length at most one. -/
theorem length_flag_le (a b : List Bool) (i : ℕ) : (flag a b i).length ≤ 1 := by
  unfold flag
  split_ifs <;> simp

/-- The closed form of the orbit for `i ≤ XorLoop.rounds z`:
`⟨a.drop i, ⟨b.drop i, flag a b i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ XorLoop.rounds z, orbit XorLoop.start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) (flag (pairFstD z) (pairSndD z) i))
  | 0, _ => by simp [XorLoop.start, flag]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold XorLoop.rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold XorLoop.rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    rw [flag_succ _ _ i _ _ hza hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 5`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ XorLoop.rounds z) :
    (orbit XorLoop.start step z i).length ≤ 5 * z.length + 5 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop]
  have := length_pairFstD_add_pairSndD_le z
  have := length_flag_le (pairFstD z) (pairSndD z) i
  omega

/-- Before round `XorLoop.rounds z` both remaining components are nonempty, so `XorLoop.acc`
is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < XorLoop.rounds z) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold XorLoop.rounds at hi
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `XorLoop.rounds z` one remaining component is empty, so `XorLoop.acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, XorLoop.rounds]
  omega

/-- The verdict read off the final state is the equality test. -/
theorem verdict_eq (a b : List Bool) :
    (decide (a.drop (min a.length b.length) = []) && decide (b.drop (min a.length b.length) = []) &&
      decide (flag a b (min a.length b.length) = [])) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab
    simp [flag]
  · rw [decide_eq_false hab]
    rcases Nat.lt_trichotomy a.length b.length with hl | hl | hl
    · rw [Nat.min_eq_left hl.le]
      have : ¬ (b.drop a.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]
    · rw [Nat.min_eq_left hl.le]
      have : flag a b a.length = [true] := by
        unfold flag
        rw [List.take_length, hl, List.take_length, if_neg hab]
      simp [this]
    · rw [Nat.min_eq_right hl.le]
      have : ¬ (a.drop b.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]

/-- At round `rounds z` the output is `[decide (fst z = snd z)]`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) =
      [decide (pairFstD z = pairSndD z)] := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, XorLoop.rounds]
  rw [verdict_eq]

end EqLoop

/-! ### `blockMap`: consume the second component block by block -/

namespace BlockLoop

/-- The initial state `⟨snd z, []⟩`: the whole second component remains, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairSndD z) []

/-- The block length read off the state word `⟨z, s⟩`: `b(|fst z|)`. -/
def blk (b : PolyExpr) (v : List Bool) : ℕ := b.eval (pairFstD (pairFstD v)).length

/-- The step on `⟨z, ⟨rest, c⟩⟩`: `⟨rest.drop k, c ++ g (rest.take k)⟩` with `k = b(|fst z|)`. -/
def step (b : PolyExpr) (g : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode ((pairFstD (pairSndD v)).drop (blk b v))
    (pairSndD (pairSndD v) ++ g ((pairFstD (pairSndD v)).take (blk b v)))

/-- The acceptance test: fewer than `k` bits remain, or `k = 0`. -/
def acc (b : PolyExpr) (v : List Bool) : Bool :=
  decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v) || decide (blk b v ≤ 0)

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD v)

/-- The number of rounds: the number of full blocks `|snd z| / b(|fst z|)`. -/
def rounds (b : PolyExpr) (z : List Bool) : ℕ :=
  (pairSndD z).length / b.eval (pairFstD z).length

/-- The unary parameter `fst z` of the state word. -/
theorem param_poly : PolyTimeComputable fun v => pairFstD (pairFstD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The remaining word of the state word. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD v) :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])

/-- The step is polynomial-time (the typed cuts `Complexity.polyTimeComputable_pairDropPoly`
and `polyTimeComputable_pairTakePoly` on `⟨fst (fst v), rest⟩`). -/
theorem step_poly (b : PolyExpr) {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (step b g) := by
  have hdrop : PolyTimeComputable fun v => (pairFstD (pairSndD v)).drop (blk b v) := by
    convert (polyTimeComputable_pairDropPoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  have htake : PolyTimeComputable fun v => (pairFstD (pairSndD v)).take (blk b v) := by
    convert (polyTimeComputable_pairTakePoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  exact hdrop.pairEncode (accum_poly.append (hg.comp htake))

/-- The acceptance test is polynomial-time (two length tests against `1^{k}`). -/
theorem acc_poly (b : PolyExpr) : PolyTimeComputable fun v => [acc b v] := by
  have h1 : PolyTimeComputable fun v => [decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v)] := by
    convert lenLe_comp (unaryPoly_comp b param_poly) ((cons_poly true).comp rest_poly) using 1
    funext v
    simp [blk]
  have h2 : PolyTimeComputable fun v => [decide (blk b v ≤ 0)] := by
    convert lenLe_comp (polyTimeComputable_const []) (unaryPoly_comp b param_poly) using 1
    funext v
    simp [blk]
  exact or_poly h1 h2

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- The closed form of the orbit (all rounds): with `k = b(|fst z|)` and `s = snd z`,
`⟨s.drop (i k), g (block 0) ++ ⋯ ++ g (block (i-1))⟩` where `block j = (s.drop (j k)).take k`. -/
theorem orbit_eq (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ) :
    orbit start (step b g) z i =
      pairEncode ((pairSndD z).drop (i * b.eval (pairFstD z).length))
        ((List.range i).flatMap fun j =>
          g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
            (b.eval (pairFstD z).length))) := by
  induction i with
  | zero => simp [start]
  | succ i ih =>
    rw [orbit_succ, ih, Nat.succ_mul]
    simp only [step, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop,
      List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The states of the first `rounds b z` rounds have length at most
`2|z| + 2 + |z| · C (b(|z|) + 1)^c` when `|g y| ≤ C (|y| + 1)^c`.

**Proof sketch.** By `orbit_eq` the state is `⟨(snd z).drop (i k), acc_i⟩` with `k = b(|fst z|)`
and `acc_i` the concatenation of `i` chunks `g (block j)`; each block has length at most
`k ≤ b(|z|)` (`PolyExpr.eval_mono`, `Complexity.length_pairFstD_le`), so each chunk has length
at most `C (b(|z|) + 1)^c`, and `StateLoop.length_flatMap_range_le` bounds `|acc_i|` by
`i · C (b(|z|) + 1)^c ≤ |z| · C (b(|z|) + 1)^c` since `i ≤ |snd z| / k ≤ |z|`
(`Nat.div_le_self`, `length_pairFstD_add_pairSndD_le`); `PolyExpr.eval_subst` and
`PolyExpr.eval_normal` identify the bound with the stated expression. -/
theorem orbit_length_le (b : PolyExpr) (g : List Bool → List Bool) (C c : ℕ)
    (hg : ∀ y, (g y).length ≤ C * (y.length + 1) ^ c) (z : List Bool) (i : ℕ)
    (hi : i ≤ rounds b z) :
    (orbit start (step b g) z i).length ≤
      (PolyExpr.add (.mul (.const 2) .var)
        (.add (.const 2) (.mul .var ((PolyExpr.normal C c).subst b)))).eval z.length := by
  rw [orbit_eq, length_pairEncode, List.length_drop]
  have hk : b.eval (pairFstD z).length ≤ b.eval z.length := b.eval_mono (length_pairFstD_le z)
  have hzs := length_pairFstD_add_pairSndD_le z
  have hi' : i ≤ z.length :=
    hi.trans ((Nat.div_le_self _ _).trans (by omega))
  have hchunk : ∀ j < i, (g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
      (b.eval (pairFstD z).length))).length ≤ C * (b.eval z.length + 1) ^ c := by
    intro j _
    refine (hg _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    rw [List.length_take]
    omega
  have hfm := length_flatMap_range_le _ _ i hchunk
  have hle := hfm.trans (Nat.mul_le_mul_right _ hi')
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_subst, PolyExpr.eval_normal]
  generalize z.length * (C * (b.eval z.length + 1) ^ c) = Q at hle
  omega

/-- Before round `rounds b z` at least `k` bits remain and `k > 0`, so `acc` is `false`. -/
theorem acc_orbit_false (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ)
    (hi : i < rounds b z) : acc b (pairEncode z (orbit start (step b g) z i)) = false := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  unfold rounds at hi
  have hk : 0 < b.eval (pairFstD z).length := by
    rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with h0 | h0
    · rw [h0, Nat.div_zero] at hi
      omega
    · exact h0
  have hmul := (Nat.le_div_iff_mul_le hk).mp hi
  rw [Nat.succ_mul] at hmul
  omega

/-- At round `rounds b z` fewer than `k` bits remain (or `k = 0`), so `acc` is `true`. -/
theorem acc_orbit_true (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    acc b (pairEncode z (orbit start (step b g) z (rounds b z))) = true := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_true_iff, decide_eq_true_eq, rounds]
  rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with hk | hk
  · right
    omega
  · left
    have h1 := Nat.lt_mul_div_succ (pairSndD z).length hk
    have h2 := Nat.div_mul_le_self (pairSndD z).length (b.eval (pairFstD z).length)
    rw [Nat.mul_succ, Nat.mul_comm (b.eval (pairFstD z).length)] at h1
    omega

/-- At round `rounds b z` the output is the concatenation of `g` over the full blocks. -/
theorem out_orbit (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    out (pairEncode z (orbit start (step b g) z (rounds b z))) =
      (List.range (rounds b z)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take
          (b.eval (pairFstD z).length)) := by
  rw [orbit_eq]
  simp [out]

end BlockLoop

end Complexity.StateLoop

## ===== TCSlib/Complexity/Randomized/Build/UnaryMul.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.List.Induction
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The unary-multiplication machine

The explicit finite machine behind `Turing.FinTM.computesFunInTime_unaryMul`
(`TCSlib.Complexity.Randomized.Primitives`): on a pair `⟨u, v⟩` it outputs `1^{|u| · |v|}`,
on a malformed word it outputs `[]`, and it halts within `5 (n + 1) ^ 2` steps on every
input of length `n`. This is the primitive by which every syntactic polynomial becomes
computable in unary (`Complexity.polyTimeComputable_unaryPoly`, foundation decision D9 of
`PassShelatChapter2-4Plan.md`), so that the lengths `1^{p(n)}` a reduction needs never go
through the repetition lemma ([PS10, §2.1], the closure properties of p.p.t. machines used
implicitly throughout chapters 2–4; foundation decision D11: the two new primitives are
built in the `Build/` style).

## Construction (DESIGN.md §2.4, with the roles of the two components exchanged)

One work tape and four control modes (six states), in the idiom of the coin-splitting
machine `TCSlib.Complexity.Randomized.Build.PairSplit` (whose parser is copied privately).

* **Phase 1, `parse`.** The buffered aligned parser: aligned two-bit blocks `00`/`11` of the
  doubled first component `u` are undoubled onto the work tape without emitting anything,
  so that after the aligned separator `01` the work tape holds a word of length `|u|`; the
  end of the input inside a block or the aligned block `10` halts the machine — with empty
  output, since nothing has been emitted yet and the output tape is append-only.
* **Phase 2, rounds `next`/`emit`/`back`.** The work head is first rewound to the origin
  (`back`). Then, for every symbol of the second component `v` — `next` consumes one input
  symbol, whose content is irrelevant — the machine walks across the stored word emitting
  one `true` per cell (`emit`) and rewinds the work head again (`back`); when the input is
  exhausted, `next` halts. Each round emits `1^{|u|}`, so after `|v|` rounds the output is
  `1^{|u| · |v|}`.

**Deviation from the sketch of DESIGN.md §2.4** (which stores `v` and replays it once per
token of `u`): storing `u` and replaying it once per symbol of `v` needs no input rewind,
because the second component is consumed left to right exactly once; the product is the
same, and the machine is smaller.

Every phase is accounted for by an explicit step ledger: the parser costs two steps per
block, the initial rewind `|u| + 1`, each round `2 |u| + 3`, the final halting step one.
The potential `n · |rest| + 3 |rest| + 2 |a| + 5` (where `n` is the input length, `rest` the
unread input and `a` the buffer) pays for the parser and for the rounds, and the total on
an input of length `n` is at most `n ^ 2 + 3 n + 5 ≤ 5 (n + 1) ^ 2`.

## Main results

* `Turing.FinTM.exists_unaryMulTM` — a finite machine computes `⟨u, v⟩ ↦ 1^{|u| · |v|}`
  (and `[]` on malformed words) within `5 (n + 1) ^ 2` steps.

## Main definitions

None public (the machine and its configuration family are private; the result is an
existence statement over `Turing.FinTM Bool`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- Finite control of the unary-multiplication machine: `parse none` expects the first bit
of an aligned block and `parse (some b)` its second bit; `back` walks the work head back to
the origin; `next` consumes one symbol of the second component (or halts at the end of the
input); `emit` walks across the stored word emitting one `true` per cell. -/
private inductive MulControl where
  | parse (b : Option Bool)
  | back
  | next
  | emit

/-- Enumerate the control through a finite sum representation, privately. -/
private instance mulControlFintype : Fintype MulControl :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance mulControlDecidableEq : DecidableEq MulControl :=
  (proxy_equiv% MulControl).symm.decidableEq

/-- The unary-multiplication machine: one work tape holding the undoubled first component.
The parser (`parse`) buffers without emitting and validates the separator; `back` returns
the work head to the origin; `next` consumes one input symbol or halts at the right blank;
`emit` emits one `true` per stored cell and hands over to `back` at the right blank of the
buffer. -/
private def unaryMulTM : FinTM Bool where
  k := 1
  State := MulControl
  tm :=
    { q₀ := .parse none
      tr := fun q inp work => match q with
        | .parse none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.parse (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .parse (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.parse none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some .back⟩
        | .back => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some .back⟩
          | none => ⟨0, fun _ => (none, .pos), none, some .next⟩
        | .next => match inp with
          | some _ => ⟨.pos, fun _ => (none, 0), none, some .emit⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .emit => match work 0 with
          | some _ => ⟨0, fun _ => (none, .pos), some true, some .emit⟩
          | none => ⟨0, fun _ => (none, .neg), none, some .back⟩ }

/-- The one-buffer configurations of the unary-multiplication machine: control `q`, input
head after `i` input bits, work tape holding the word `a` from the origin with its head at
cell `z`, output `out`. -/
private def mulCfg (x : List Bool) (q : Option MulControl) (i : ℕ) (hi : i ≤ x.length)
    (a : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool MulControl x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma mulCfg_read (x : List Bool) (q : Option MulControl) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (mulCfg x q i hi a z out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [mulCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [mulCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- Two indexed configurations with equal input indices are equal (the bound proofs are
irrelevant). -/
private lemma mulCfg_congr (x : List Bool) (q : Option MulControl) {i i' : ℕ}
    (hi : i ≤ x.length) (hi' : i' ≤ x.length) (h : i = i') (a : List Bool) (z : ℤ)
    (out : List Bool) :
    mulCfg x q i hi a z out = mulCfg x q i' hi' a z out := by
  subst h
  rfl

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma mul_first (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    unaryMulTM.tm.step
      (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) =
      mulCfg x (some (.parse (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr (.parse none) _ _).apply _ = _
  rw [mulCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [mulCfg, hx])
  · funext i; simp [unaryMulTM, Action.apply, mulCfg]

/-- Equal-bit blocks append one decoded bit to the buffer; `01` begins the rewind (the work
head steps back onto the last stored cell) and `10` halts silently. Neither transition emits
physical output.
**Proof sketch.** The first step is `mul_first`; the second reads the block's second bit
`c` at the input index `|pre| + 1`. Case analysis on `b` and `c`: equal bits write `some b`
at the right blank of the buffer (`bufferTape_append`) and move the work head right, `01`
moves it left into `back`, `10` halts; in every case the input head advances. -/
private lemma mul_block (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    unaryMulTM.tm.runFrom
      (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then mulCfg x (some (.parse none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then mulCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else mulCfg x (some .back) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change unaryMulTM.tm.step (unaryMulTM.tm.step _) = _
  rw [mul_first x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr (.parse (some b)) _ _).apply _ = _
  rw [mulCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [unaryMulTM, Action.apply, mulCfg])

/-- Rewinding the buffer from cell `j - 1` takes `j + 1` transitions and leaves the work
head at the origin in the `next` state; the output is untouched.
**Proof sketch.** At the left blank, move right and enter `next`. Otherwise read a buffer
cell, move left, and invoke the induction hypothesis. -/
private lemma mul_back (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    ∀ j, j ≤ a.length →
    unaryMulTM.tm.runFrom (mulCfg x (some .back) i hi a ((j : ℤ) - 1) out) (j + 1) =
      mulCfg x (some .next) i hi a 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub,
      bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : unaryMulTM.tm.step
        (mulCfg x (some .back) i hi a (((j + 1 : ℕ) : ℤ) - 1) out) =
        mulCfg x (some .back) i hi a ((j : ℤ) - 1) out := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext k; simp [Action.apply, sub_eq_add_neg]
      · simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The emission walk: from cell `j` of the buffer with `k = |a| - j` cells ahead, `k + 1`
transitions emit `1^k` and leave the work head on the last stored cell in the `back` state.
**Proof sketch.** Induct on `k`. With no cell ahead, `emit` reads the right blank
(`bufferTape_nat` at `|a|`), moves left and enters `back`. Otherwise it reads the stored
cell `a[j]`, emits `true`, moves right, and the induction hypothesis applies to cell
`j + 1`; the outputs match by `List.replicate_succ`. -/
private lemma mul_emit (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (a : List Bool) :
    ∀ k j (out : List Bool), j + k = a.length →
    unaryMulTM.tm.runFrom (mulCfg x (some .emit) i hi a (j : ℤ) out) (k + 1) =
      mulCfg x (some .back) i hi a ((a.length : ℤ) - 1) (out ++ List.replicate k true) := by
  intro k
  induction k with
  | zero =>
    intro j out hj
    obtain rfl : j = a.length := by omega
    have hnone : a[a.length]? = none := List.getElem?_eq_none le_rfl
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat, hnone]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply, sub_eq_add_neg]
    · simp [Action.apply]
  | succ k ih =>
    intro j out hj
    have hjl : j < a.length := by omega
    have hs : unaryMulTM.tm.step (mulCfg x (some .emit) i hi a (j : ℤ) out) =
        mulCfg x (some .emit) i hi a ((j + 1 : ℕ) : ℤ) (out ++ [true]) := by
      unfold MultiTapeTM.step
      simp only [unaryMulTM, mulCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem hjl]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext k; simp [Action.apply]
      · simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (j + 1) (out ++ [true]) (by omega),
      List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- One round at an input symbol: `next` consumes the symbol, `emit` walks across the buffer
emitting `1^{|a|}`, `back` rewinds; `2 |a| + 3` steps in all.
**Proof sketch.** The `next` step reads `x[i]` and advances the input head
(`moveInputPos_pos_of_ne_right`); then `mul_emit` from the origin and `mul_back` from the
last stored cell, glued with `MultiTapeTM.runFrom_add`. -/
private lemma mul_round (x : List Bool) (i : ℕ) (hi : i < x.length) (a out : List Bool) :
    unaryMulTM.tm.runFrom (mulCfg x (some .next) i hi.le a 0 out) (2 * a.length + 3) =
      mulCfg x (some .next) (i + 1) hi a 0 (out ++ List.replicate a.length true) := by
  have h1 : unaryMulTM.tm.step (mulCfg x (some .next) i hi.le a 0 out) =
      mulCfg x (some .emit) (i + 1) hi a 0 out := by
    unfold MultiTapeTM.step
    change (unaryMulTM.tm.tr .next _ _).apply _ = _
    rw [mulCfg_read, List.getElem?_eq_getElem hi]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · exact moveInputPos_pos_of_ne_right _ (by show i + 1 ≠ x.length + 1; omega)
    · funext k; simp [unaryMulTM, Action.apply, mulCfg]
    · simp [unaryMulTM, Action.apply, mulCfg]
  have h0 : unaryMulTM.tm.runFrom (mulCfg x (some .next) i hi.le a 0 out) 1 =
      mulCfg x (some .emit) (i + 1) hi a 0 out := by
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, h1]
  have h2 := mul_emit x (i + 1) hi a a.length 0 out (by simp)
  rw [Nat.cast_zero] at h2
  rw [show 2 * a.length + 3 = 1 + (a.length + 1) + (a.length + 1) by ring,
    MultiTapeTM.runFrom_add _ (1 + (a.length + 1)) (a.length + 1),
    MultiTapeTM.runFrom_add _ 1 (a.length + 1), h0, h2,
    mul_back x a (i + 1) hi _ a.length le_rfl]

/-- The rounds: `j` rounds over the input suffix `rest` cost `j (2 |a| + 3)` steps and emit
`1^{|a| · j}`.
**Proof sketch.** Induct on `j`; each round is `mul_round` at the input index
`|pre| + j < |x|`, and the outputs are glued by `List.replicate_add` and `Nat.mul_add`. -/
private lemma mul_loop (x pre rest a out : List Bool) (hx : x = pre ++ rest) :
    ∀ j (_hj : j ≤ rest.length),
    unaryMulTM.tm.runFrom (mulCfg x (some .next) pre.length (by simp [hx]) a 0 out)
        (j * (2 * a.length + 3)) =
      mulCfg x (some .next) (pre.length + j) (by simp [hx]; omega) a 0
        (out ++ List.replicate (a.length * j) true) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [Nat.zero_mul, MultiTapeTM.runFrom_zero]
    simp [mulCfg]
  | succ j ih =>
    intro hj
    have hlt : pre.length + j < x.length := by simp [hx]; omega
    rw [Nat.add_mul, Nat.one_mul, MultiTapeTM.runFrom_add, ih (by omega), mul_round x _ hlt,
      Nat.mul_succ, List.replicate_add, List.append_assoc]
    exact mulCfg_congr x _ hlt _ (Nat.add_assoc pre.length j 1) a 0 _

/-- At the end of the input, `next` halts in one step without touching anything. -/
private lemma mul_halt (x a out : List Bool) :
    unaryMulTM.tm.runFrom (mulCfg x (some .next) x.length le_rfl a 0 out) 1 =
      mulCfg x none x.length le_rfl a 0 out := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
  unfold MultiTapeTM.step
  change (unaryMulTM.tm.tr .next _ _).apply _ = _
  rw [mulCfg_read, List.getElem?_eq_none le_rfl]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [unaryMulTM, Action.apply, mulCfg]
  · simp [unaryMulTM, Action.apply, mulCfg]

/-- Once the separator has been validated, the initial rewind, the rounds and the halting
step cost `|a| + 1 + |rest| (2 |a| + 3) + 1` steps and emit exactly `1^{|a| · |rest|}`.
**Proof sketch.** `mul_back` from the last stored cell, `mul_loop` with `j = |rest|`
(re-indexing the input position to `|x|` by `mulCfg_congr`), then `mul_halt`. -/
private lemma mul_finish (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∃ t ≤ a.length + 1 + rest.length * (2 * a.length + 3) + 1,
      (unaryMulTM.tm.runFrom
        (mulCfg x (some .back) pre.length (by simp [hx]) a (a.length - 1) []) t).state =
          none ∧
      (unaryMulTM.tm.runFrom
        (mulCfg x (some .back) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          List.replicate (a.length * rest.length) true := by
  refine ⟨a.length + 1 + rest.length * (2 * a.length + 3) + 1, le_rfl, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, mul_back x a _ _ [] a.length le_rfl,
    mul_loop x pre rest a [] hx rest.length le_rfl,
    mulCfg_congr x _ _ le_rfl (show pre.length + rest.length = x.length by simp [hx]),
    mul_halt]
  simp [mulCfg]

/-- The silent aligned parser either rejects or validates and runs the rounds.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the already-decoded
buffer `a` (with `2 |a| ≤ |pre|`). A doubled bit costs two steps and enlarges the buffer by
one; the potential `|x| · |rest| + 3 |rest| + 2 |a| + 5` pays for it. Missing and forbidden
separators halt silently with empty output. At `01`, apply the finish ledger `mul_finish`;
its quadratic term `|rest| · 2 |a|` is dominated by `|x| · |rest|` because `2 |a| ≤ |x|`. -/
private lemma mul_run (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest) (_hpre : 2 * a.length ≤ pre.length),
    ∃ t ≤ x.length * rest.length + 3 * rest.length + 2 * a.length + 5,
      (unaryMulTM.tm.runFrom
        (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).state =
          none ∧
      (unaryMulTM.tm.runFrom
        (mulCfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (u, v) => List.replicate ((a.length + u.length) * v.length) true
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx _
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((unaryMulTM.tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [mulCfg_read]
    simp [hx, unaryMulTM, Action.apply, mulCfg, pairDecode]
  | singleton b =>
    intro pre a hx _
    refine ⟨2, by simp, ?_⟩
    change (unaryMulTM.tm.step (unaryMulTM.tm.step _)).state = none ∧
      (unaryMulTM.tm.step (unaryMulTM.tm.step _)).output = _
    rw [mul_first x pre [] a b hx]
    unfold MultiTapeTM.step
    change ((unaryMulTM.tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [mulCfg_read]
    cases b <;> simp [hx, unaryMulTM, Action.apply, mulCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx hpre
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ :=
        ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      refine ⟨2 + t, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, Nat.mul_add,
          Nat.mul_one] at ht ⊢
        omega
      rw [MultiTapeTM.runFrom_add, mul_block x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases hd : pairDecode rest with
        | none => cases b <;> simpa [pairDecode, hd] using ho
        | some p =>
          obtain ⟨u, v⟩ := p
          have e : a.length + (u.length + 1) = a.length + 1 + u.length := by omega
          cases b <;> simpa [pairDecode, hd, e] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := mul_finish x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, ?_, ?_⟩
        · have hx2 : 2 * a.length ≤ x.length := by simp [hx]; omega
          have hmul : rest.length * (2 * a.length) ≤ x.length * rest.length := by
            rw [Nat.mul_comm x.length]
            exact Nat.mul_le_mul_left _ hx2
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at ht ⊢
          omega
        rw [MultiTapeTM.runFrom_add, mul_block x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp only [List.length_cons]; omega, ?_⟩
        rw [mul_block x pre rest a true false hx]
        simp [mulCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The unary-multiplication machine halts on every input within `5 (|x| + 1) ^ 2` steps
with the output `1^{|u| · |v|}` (for `x = ⟨u, v⟩`) or `[]` (malformed `x`). The initial
buffer and decoded prefix are empty.
**Proof sketch.** Instantiate `mul_run` with the empty prefix and the empty buffer; the
initial configuration is the indexed configuration at index `0` with blank work tape
(`Cfg.ext`). The ledger `|x| ^ 2 + 3 |x| + 5 ≤ 5 (|x| + 1) ^ 2` is absorbed by
`ComputesInTime.mono`. -/
private lemma mul_computes (x : List Bool) :
    unaryMulTM.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => List.replicate (u.length * v.length) true
        | none => []) (5 * (x.length + 1) ^ 2) := by
  obtain ⟨t, ht, hs, ho⟩ := mul_run x x [] [] rfl (by simp)
  have hinit : unaryMulTM.tm.initCfg x =
      mulCfg x (some (.parse none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [unaryMulTM, mulCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : unaryMulTM.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => List.replicate (u.length * v.length) true
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    refine ⟨hs, ?_⟩
    cases hd : pairDecode x with
    | none => simpa [hd] using ho
    | some p =>
      obtain ⟨u, v⟩ := p
      simpa [hd] using ho
  refine hh.mono ?_
  have hsq : (x.length + 1) ^ 2 = x.length * x.length + 2 * x.length + 1 := by ring
  simp only [List.length_nil] at ht
  rw [hsq]
  omega

/-- **The unary-multiplication machine exists:** a finite machine computes, on a pair
`⟨u, v⟩`, the unary string `1^{|u| · |v|}` — and `[]` on a malformed word — within
`5 (n + 1) ^ 2` steps on inputs of length `n`. This is the machine behind
`Turing.FinTM.computesFunInTime_unaryMul` [PS10, §2.1, implicit; foundation decision D9].

**Proof sketch.** The private machine `unaryMulTM` above (one work tape, four control
modes: buffered aligned parser, rewind, consume-one-symbol, emission walk) with the step
ledger `mul_run`: at most `|x| ^ 2 + 3 |x| + 5 ≤ 5 (|x| + 1) ^ 2` steps from the initial
configuration, output `1^{|u| · |v|}` by induction on the tokens of `u` (parser) and on the
symbols of `v` (rounds). -/
theorem exists_unaryMulTM :
    ∃ M : FinTM Bool,
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => 5 * (n + 1) ^ 2 :=
  ⟨unaryMulTM, fun x => mul_computes x⟩

end Turing.FinTM
