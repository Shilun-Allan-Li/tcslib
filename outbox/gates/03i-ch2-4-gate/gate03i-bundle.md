## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03i-pack.md =====

# Gate 03i ([PS10] ch. 2–4, Goldreich–Levin and hard-core results): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/i/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the proof of the Goldreich–Levin theorem (Thm 87.3) and its collection form, the hard-core lemmas behind the PRG constructions (Thm 79.4, Lem 80.5), the hard-core bit of one-way permutation collections, and the ensemble lemmas (the hybrid and prediction lemmas, Lems 71.5, 71.6, 73.8).
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03i-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §3.1 (book pp. 69–73) and §3.3–§3.4 (pp. 77–90).

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
| Under audit | `TCSlib/Cryptography/Asymptotic/{HardCoreLemmas, HardCoreLoops, HardCoreGL, HardCoreGLColl, HardCoreGLFamily, GoldreichLevinDomain, HardCorePermutation, EnsemblesLemmas}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | packs 03a–03c's files (whose headlines these files prove) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: the proof rows of Thm-87.3 (with .a, .b, .coll), Thm-79.4, Lem-80.5, Cor-81.7, Lem-71.5, Lem-71.6, Lem-73.8 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/i/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 339 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 14 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 14 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 8 files.

Pack-specific notes (as drafted): elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **Goldreich–Levin.** Do the inverter's statements (the majority over pairwise-independent
   samples, the guessing of the `⟨x, r_i⟩`, the success bound) give the theorem at the source's
   strength, with a polynomial loss?
2. **`GoldreichLevinDomain`.** Is the padding of the domain (`|r| = |x|`) handled as the
   collection form needs?
3. **Permutations** (`HardCorePermutation`, `PermFamily.glHalf`, run-3a). Is the hard-core bit of a
   one-way permutation collection stated correctly?
4. **Ensembles.** Do the hybrid and prediction lemmas match their inventory rows, and the concrete
   layer's `predict_eq` (duplication-ledger item DL-5)?

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

## ===== briefs/pass-shelat/inventory-ch3.md =====

# Inventory — [PS10] Chapter 3, *Indistinguishability & Pseudo-Randomness* (§3.1–§3.12, plus the appendix facts its proofs cite)

Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-shelat-2010-ch3.raw.md`
(pdftotext; results numbered `<page>.<counter>`). Read-only on Lean; this file is the planners' input.

## 0. How to read this file

* **Ids.** Numbered results keep the book's number (`Def-69.4`, `Lem-71.6`, `Thm-87.3`, `Alg-92.1`,
  `Asm-105.1`). Unnumbered but substantive claims get a synthetic id `<Kind>-<page>.<letter>`
  (e.g. `Claim-73.a` = the "show this!" on p. 73). Proof cases and lemmas inside a proof are
  `<parent>.<n>` (e.g. `Thm-87.3.4`).
* **Quantifier conventions used in every statement below** (fixed by the plan, D3–D7):
  `n` is the security parameter; strings of length `n` are `Fin n → Bool`; an *ensemble* `X` is a
  family `X n : (Fin (s n) → Bool) → (Fin (ℓ n) → Bool)` of samplers from uniform coin strings of
  explicit polynomial length (D6); **PPT** = `FinTM Bool` run on `pairEncode x r`, worst-case time
  over all coin strings, computes a function when the output is the same for every coin string
  (D3); **nuPPT** = PPT + advice string `α n` of explicit polynomial length (D4); "`D` distinguishes
  `X n, Y n` with probability `ε`" means `distAdv (X n) (Y n) D > ε`; "negligible" is
  `TCSlib.Cryptography.Negligible`; "non-negligible" = `¬ Negligible`, equivalently (by
  `not_negligible_iff`) `∃ c, ∀ n₀, ∃ n ≥ n₀, 1/n^c ≤ |μ n|` ("infinitely often").
* **Concrete vs asymptotic.** Every theorem is a concrete reduction (one `n`, exact inequality,
  adversaries are plain functions of input and coins — mostly already proved in the Garg layer,
  namespace `TCSlib.Cryptography`) *plus* an asymptotic wrapper: (i) instantiate the concrete
  reduction at each `n`, (ii) show the reduction is an nuPPT by closure lemmas, (iii) negligible
  arithmetic. The column *existing Lean* names what is proved; *reuse note* says what the bridge
  must add.
* **Scope.** `core` = mandatory (plan's content or needed downstream); `optional` = feasible and
  worthwhile; `deferred` = stated without proof in the text and nothing downstream needs it, or
  out of reach.
* **Difficulty** 1 trivial … 5 research-level fill (for the asymptotic statement including its
  concrete part, unless the item is marked "concrete only").

### External dependencies referred to by label (not chapter-3 items)

| Label | Meaning | Where it will live |
| --- | --- | --- |
| `Machine-PPT` | D3: `PPT` structure, run/sampler semantics `run M n : (Fin (coins n) → Bool) → List Bool`, `ComputesFun` (same output for every coin string), typed decoding of outputs (`List Bool` → `Fin m → Bool`, wrong length = failure/`false`) | `TCSlib/Complexity/Randomized/PPT.lean` |
| `Machine-NUPPT` | D4: nuPPT = PPT + advice `α n` of length `Cα (n+1)^cα`, run on `pairEncode (pairEncode x (α |x|)) r`; Boolean output `decide (out = [true])` | `Randomized/NonUniform.lean` |
| `Machine-Closure` | pre/post-composition with a PPT, pairing of inputs, hard-wiring a per-`n` constant (index `i`, message `m_n`, sign bit) into advice, drawing extra coins, a PPT is an nuPPT | `Randomized/Closure.lean` |
| `Machine-Repetition` | polynomially many calls of an nuPPT with fresh coins and a post-processing (majority, list, XOR) — the load-bearing lemma for GL, DL, multi-message | `Randomized/Repetition.lean` |
| `Machine-Loop` | iterate a PPT-computable function `poly(n)` times (PRG expansion, GGM evaluation, Shamir/Blum–Micali) | `Randomized/Repetition.lean` (or Closure) |
| `Machine-Primitives` | poly-time string primitives not yet in `Build/Primitives.lean`: bitwise XOR of two equal-length strings, inner product mod 2, majority of a bit list, string equality, `Fin.cons`/`append`/truncation on tapes, unary/binary length bookkeeping | `TCSlib/Complexity/Randomized/Primitives.lean` (new) |
| `Ensemble-D6` | `Ensemble` structure (seed length, output length as explicit polynomials, sampler), `Samplable X` (sampler is a PPT) | `Asymptotic/Ensembles.lean` |
| `Oracle-D7` | nuPPT oracle adversaries: an nuPPT that *drives* a `QueryTree` (next query / final bit computed by the machine from `1^n`, coins, and the transcript so far), query bound `q(n)` explicit polynomial | `Asymptotic/PRF.lean` |
| `Def-24.7` | private-key encryption scheme (Gen PPT, Enc PPT, Dec PPT, correctness w.p. 1), ch. 2 inventory | `Asymptotic/Encryption.lean` |
| `Def-27.3`, `Def-41.1`, `Def-55.1`, `Def-56.1` | strong OWF; collection of OWFs; OWP collection; trapdoor permutations (ch. 2) | `Asymptotic/OneWay.lean`, `Asymptotic/Collections.lean` |
| `Asm-52.2`, `Thm-52.3`, `Thm-58.2`, `Thm-45.6` | DL assumption; the DL collection; square roots mod `p ≡ 3 (4)`; repeated squaring (ch. 2) | `Candidates/DiscreteLog.lean`, `NumberTheory/*` |
| `OWP-single` | a *single* one-way permutation `f n : (Fin n → Bool) ≃ (Fin n → Bool)`, PPT-computable, one-way (Def 27.3) — the text's "let `f` be a one-way permutation" in Thm 79.4 / Cor 81.7 / Thm 87.3 / ch. 4 Thm 126.4 | `Asymptotic/OneWay.lean` (ch. 2 inventory should define it; flagged here) |

### Proposed file split for chapter 3 (refines the plan's layout)

| File | Contents | Why it differs from the plan |
| --- | --- | --- |
| `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def 69.3, 69.4, the "distinguishes with probability" notations, Lem 71.5, Lem 71.6, Rem 72.7, Claim 72.a, Ex 72.b, Claim 73.a, Lem 73.8, quantifier bridge | as planned |
| `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean` | Def 74.1, 75.2 (+Rem 75.3), Def 77.1, Claim 67.a, next-bit soundness (Thm-75.4.conv), asymptotic Thm 75.4 | as planned, minus the concrete next-bit reduction |
| `TCSlib/Cryptography/Asymptotic/NextBit.lean` (**new**) | concrete next-bit reduction: hybrids `H^i`, flipped hybrid, mixing identity, Alg 76.5, exact bound `1/2 + ε/ℓ` | the Garg layer has no next-bit material; the frozen `Pseudorandom/` tree (and its facade) must not be edited, so the new concrete reduction lives in the campaign's tree |
| `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def 78.3 (single + collection), Thm 79.4, Claim 79.a, Lem 80.5, Cor 81.7, Shamir remarks, Thm 87.3 (a: padding, b: GL asymptotic, collection version) | as planned |
| `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean` (**new**) | Lem 84.1 and its sub-items (Alg 84.2, NT facts, majority test, range reduction) | Lemma 84.1 alone is 400+ lines of concrete reduction; keep `Candidates/DiscreteLog.lean` for Asm 52.2/Thm 52.3 |
| `TCSlib/Cryptography/Asymptotic/Encryption.lean` | Def 91.1 (on Def 24.7), Alg 92.1, Claim 92.a (OTP), Thm 92.2, Def 93.1, Thm 94.2 | as planned |
| `TCSlib/Cryptography/Asymptotic/PRF.lean` | random functions (Def 95.a, Claim 95.b), Def 96.1, Claim 96.a–c, Def 96.2, Cor 97.a (WLOG length-doubling), GGM evaluation is PPT, Thm 97.3 | as planned |
| `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (**new**) | Alg 99.1, Thm 99.2 (concrete: PRF reduction, collision bound, OTP) | Thm 99.2's concrete proof is new and long; separate from PRF.lean to respect the 600-line guideline |
| `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def 102.1, 102.2, Claims 103.a–b, Def 103.c, Thm 103.d, Def 103.e, Thm 103.f, Alg 104.3, Lem 104.a, Thm 104.4 | as planned |
| `TCSlib/Cryptography/Candidates/ElGamal.lean` (**new**) | Asm 105.1 (relative to a group generator), NT 105.a (safe primes, `G_q`), Claim 106.a (DDH ⇒ DL), Alg 106.2, Claim 107.a, Thm 107.3, Def 107.b (message encoding) | number theory + a concrete assumption belong with the candidates, not in PublicKey.lean |
| (appendix) | Thm 188.7, Lem 189.8, pairwise-independent sampling — all replaced by existing `chebyshev_pairwise` / `uprob_majority_fails_le`; Chernoff optional in `Asymptotic/Chernoff.lean` if ever needed | — |

## 1. Inventory table

Legend: scope C = core, O = optional, D = deferred. "Garg" = concrete layer already proved (namespace
`TCSlib.Cryptography`, source tag `[Gar26]`). Full statements, reuse notes and text issues are in §2.

| Id | Kind | § | Title | Scope | Diff | Proposed file | Existing Lean (concrete) | Depends on |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Claim-67.a | claim (show this) | 3.0 | no generator makes a perfectly random longer string | O | 2 | Asymptotic/Pseudorandom.lean | `statDist`, `distAdv_le_statDist` | — |
| Def-69.3 | definition | 3.1 | ensembles of distributions | C | 2 | Asymptotic/Ensembles.lean | samplers `σ → γ` (Experiments.lean) | Ensemble-D6 |
| Def-69.4 | definition | 3.1 | computational indistinguishability `≈`; "distinguishes with probability ε / μ(·)" | C | 2 | Asymptotic/Ensembles.lean | `distAdv`, `Negligible` | Def-69.3, Machine-NUPPT |
| Lem-71.5 | lemma | 3.1.1 | closure under efficient operations | C | 3 | Asymptotic/Ensembles.lean | `sunglassRed`, `distAdv_sunglassRed`, `pushSampler`, `distAdv_comp` | Def-69.4, Machine-Closure |
| Lem-71.6 | lemma | 3.1.1 | hybrid lemma | C | 1 | Asymptotic/Ensembles.lean | `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `mixDist`, `distAdv_mixDist_eq` | — |
| Rem-72.7 | remark | 3.1.1 | acceptance probability is a pseudometric; hybrid = triangle inequality | O | 1 | Asymptotic/Ensembles.lean | `abs_sub_le` | — |
| Claim-72.a | claim | 3.1.1 | a long chain of pairwise-indistinguishable distributions with distinguishable ends | O | 2 | Asymptotic/Ensembles.lean | `distAdv_le_statDist` | Def-69.4 |
| Ex-72.b | example | 3.1.1 | `{x⊕y}` ≈ `{z⊕y}` for pairwise-indistinguishable samplable `X,Y,Z` | O | 2 | Asymptotic/Ensembles.lean | `distAdv_sunglassRed` | Lem-71.5, Ensemble-D6 |
| Claim-73.a | claim (show this) | 3.1.1 | a predictor is a distinguisher (converse of 73.8; same identity) | C | 2 | Asymptotic/Ensembles.lean | `uprob_bool_prod` (GeneratorFromPermutation.lean) | Def-69.4 |
| Lem-73.8 | lemma | 3.1.1 | prediction lemma | C | 3 | Asymptotic/Ensembles.lean | `uprob_bool_prod`; pattern of `predProb_owpPredictor_false/true`, `exists_owpPredictor` | Def-69.4, Machine-Closure |
| Claim-73.b | implicit | 3.1 | "for infinitely many n with 1/p(n)" ⇔ non-negligible | C | 1 | Asymptotic/Ensembles.lean | `not_negligible_iff`, `Negligible.mono` | — |
| Def-74.1 | definition | 3.2.1 | pseudorandom ensembles | C | 1 | Asymptotic/Pseudorandom.lean | `prgAdv` (= `distAdv G id`) | Def-69.4 |
| Def-75.2 | definition | 3.2.2 | next-bit test | C | 2 | Asymptotic/Pseudorandom.lean | — | Def-69.3, Machine-NUPPT |
| Rem-75.3 | convention | 3.2.2 | predictor receives `1^n` | C | 1 | Asymptotic/Pseudorandom.lean | — | Def-75.2 |
| Thm-75.4 | theorem | 3.2.2 | completeness of the next-bit test (asymptotic) | C | 4 | Asymptotic/Pseudorandom.lean | — | Thm-75.4.c, Lem-71.6, Lem-73.8, Machine-Closure |
| Thm-75.4.c | theorem (concrete) | 3.2.2 | next-bit reduction: `∃ i < ℓ, ∃ flip`, predictor success `≥ 1/2 + ε/ℓ` | C | 4 | Asymptotic/NextBit.lean | `exists_hybrid_gap`, `acceptProb_update`, `uprob_bool_prod`, `prgHybrid` (pattern) | — |
| Thm-75.4.1 | hybrid def | 3.2.2 | hybrids `H^i_n = x_1…x_i u_{i+1}…u_ℓ` with `H^0 = U_ℓ`, `H^ℓ = X_n` | C | 2 | Asymptotic/NextBit.lean | pattern `prgHybrid`, `multicopyHybrid` | — |
| Thm-75.4.2 | claim | 3.2.2 | mixing identity `H^i = ½ H^{i+1} + ½ H̃^{i+1}` | C | 2 | Asymptotic/NextBit.lean | `acceptProb_id_owp` (same trick), `uprob_bool_prod` | Thm-75.4.1 |
| Alg-76.5 | algorithm | 3.2.2 | next-bit predictor `A'(1^n, t_1…t_i)` from a distinguisher | C | 2 | Asymptotic/NextBit.lean | pattern `owpPredictor` | Thm-75.4.2 |
| Thm-75.4.conv | claim (implicit) | 3.2.2 | soundness: pseudorandom ⇒ passes the next-bit test | O | 2 | Asymptotic/Pseudorandom.lean | `distAdv_comp` | Def-75.2, Claim-73.a |
| Def-77.1 | definition | 3.3.1 | pseudorandom generator | C | 2 | Asymptotic/Pseudorandom.lean | `prgAdv` | Def-74.1, Machine-PPT |
| Constr-77.a | construction | 3.3.2 | Shamir's generator `f^n(s)‖…‖f(s)‖s` | O | 1 | Asymptotic/HardCore.lean | — | OWP-single |
| Claim-78.a | claim | 3.3.2 | iterates of a permutation on a uniform seed are uniform | O | 1 | Asymptotic/HardCore.lean | `uprob_comp_equiv`, `acceptProb_comp_equiv` | — |
| Claim-78.b | claim | 3.3.2 | unpredictable *numbers* need not give unpredictable *bits* (a OWP may fix bits) | O | 2 | Asymptotic/HardCore.lean | `predProb_positionBit`, `predProb_fixedBitPredictor` (NoFixedBit.lean) | — |
| Def-78.3 | definition | 3.3.3 | hard-core predicate for a function `f` | C | 2 | Asymptotic/HardCore.lean | `predProb` | Machine-NUPPT, Machine-PPT |
| Def-78.3.coll | definition (unnumbered, needed) | 3.3.3 | hard-core predicate for a collection `{f_i}` | C | 2 | Asymptotic/HardCore.lean | `predProb` (indexed sampler) | Def-41.1, Def-78.3 |
| Claim-78.c | claim (stated, unproved) | 3.3.3 | LSB and `half_N` are hard-core for RSA | D | 5 | — | — | — |
| Thm-79.4 | theorem | 3.3.4 | `G(s) = f(s)‖h(s)` is a PRG for a OWP `f` with hard-core `h` | C | 3 | Asymptotic/HardCore.lean | `owpGen`, `owpPredictor`, `exists_owpPredictor`, `exists_owpPredictorBits`, `prgAdv_comp_equiv` | Def-77.1, Def-78.3, OWP-single, Machine-Closure |
| Claim-79.a | claim (in proof) | 3.3.4 | the first `n` bits of `G(s)` are uniform; next-bit predictors for positions `≤ n` succeed w.p. exactly `1/2` | O | 2 | Asymptotic/HardCore.lean | `uprob_comp_equiv` | Claim-78.a |
| Lem-80.5 | lemma | 3.3.5 | expansion of a one-bit-stretch PRG to `ℓ(n)` bits | C | 3 | Asymptotic/HardCore.lean | `prgExt`, `prgExtBits`, `prgExtRed`, `exists_prgExtRed_ge`, `exists_prgExtBitsRed_ge`, `prgExtAvgRed`, `prgAdv_prgExtAvgRed`, `distAdv_comp` | Def-77.1, Lem-71.5, Lem-71.6, Machine-Loop |
| Cor-81.7 | corollary | 3.3.5 | `G(x) = h(x)‖h(f(x))‖…‖h(f^{ℓ}(x))` is a PRG | C | 2 | Asymptotic/HardCore.lean | `prgExt` closed form `(G ((prgStep G)^[i] s)).1`, `prgExt_succ` | Thm-79.4, Lem-80.5 |
| Constr-82.a | construction (unproved) | 3.3.5 | PRG from a *collection* of OWPs, `G(r_1,r_2)` | D | 3 | Asymptotic/HardCore.lean | `prgExt` (needs a non-uniform-seed generalization) | Def-55.1, Def-78.3.coll |
| Constr-82.b | construction (unproved) | 3.3.6 | Blum–Micali PRG (modular exponentiation, `half_{p-1}`) | D | 3 | Candidates/DiscreteLogHardcore.lean | — | Lem-84.1, Constr-82.a |
| Constr-83.a | construction (unproved) | 3.3.6 | RSA PRG (`LSB`) | D | 5 | — | — | Claim-78.c |
| Constr-83.b | construction (unproved) | 3.3.6 | Blum–Blum–Shub (`LSB`, squaring mod `N`) | D | 5 | — | — | — |
| Claim-83.c | claim (unproved) | 3.3.6 | `log n` bits per iteration remain secure | D | 5 | — | — | — |
| Lem-84.1 | lemma | 3.4.1 | `half_{p-1}` is hard-core for `f_{p,g}(x) = g^x mod p` under DL | C | 5 | Candidates/DiscreteLogHardcore.lean | `uprob_majority_fails_le`, `chebyshev_pairwise`, `half_le_uprob_threshold`, `uprob_exists_le`, Mathlib `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.euler_criterion`, `IsCyclic (ZMod p)ˣ` | Asm-52.2, Thm-52.3, Thm-58.2, Thm-45.6, Machine-Repetition, Lem-84.1.1–.5 |
| Lem-84.1.0 | claim | 3.4.1 | `half_{p-1}` is PPT-computable from `x` | C | 1 | Candidates/DiscreteLogHardcore.lean | — | Machine-PPT |
| Lem-84.1.1 | number theory | 3.4.1 | for a generator `g` of `Z_p^*`: `g^{(p-1)/2} = -1`; `y = g^{2x}` has exactly the roots `g^x, g^{x+(p-1)/2}`; `y` is a square iff its DL is even | C | 2 | Candidates/DiscreteLogHardcore.lean | Mathlib `ZMod.pow_div_two_eq_neg_one_or_one`, `ZMod.euler_criterion`, `orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient` | — |
| Alg-84.2 | algorithm | 3.4.1 | bit-by-bit DL from a perfect `half` oracle; correctness | C | 3 | Candidates/DiscreteLogHardcore.lean | — | Lem-84.1.1 |
| Alg-85.a | algorithm | 3.4.1 | randomized majority test replacing line 8 (`z_i = y_{k-1} g^{r_i}`, count `lo`) | C | 3 | Candidates/DiscreteLogHardcore.lean | `majority`, `uprob_majority_fails_le`, `pairwiseUniform_eval` | Alg-84.2 |
| Lem-84.1.3 | claim | 3.4.1 | `Pr[noinc | low] ≤ 1/2 − ε/2` (re-randomization error `≤ ε/2`) for instances with DL in `[0, εp/4]` | C | 3 | Candidates/DiscreteLogHardcore.lean | `uprob_or_le`, `pushesUniform_add_right` | Alg-85.a |
| Lem-84.1.4 | claim (gap: "as we will show later") | 3.4.1 | range reduction: solving DL on `[0, εp/4]` solves DL w.p. `≥ ε/4 − negl` | C | 3 | Candidates/DiscreteLogHardcore.lean | `uprob_eq_one_div_card` | Alg-85.a |
| Lem-84.1.5 | claim (missing in text) | 3.4.1 | good-instance argument: success `1/2+ε` averaged over `(p,g,x)` gives `≥ ε/2` fraction of `(p,g)` with per-instance success `≥ 1/2+ε/2`; union bound over the `|p|` rounds | C | 3 | Candidates/DiscreteLogHardcore.lean | `half_le_uprob_threshold`, `uprob_exists_le` | — |
| Thm-87.3 | theorem | 3.4.2 | Goldreich–Levin: `g(x,r) = (f(x), r)` is a OWF (OWP) and `⟨x,r⟩` is hard-core for `g` | C | 4 | Asymptotic/HardCore.lean | see .a/.b | Thm-87.3.a, Thm-87.3.b |
| Thm-87.3.a | claim | 3.4.2 | `g` is one-way (and a permutation if `f` is) | C | 2 | Asymptotic/HardCore.lean | `OneWay.pad`, `OneWay.padInverter`, `OneWay.invProb_pad_le` (OutputLength.lean); `HardcoreBit.glPad` | Def-27.3, Machine-Closure |
| Thm-87.3.b | claim | 3.4.2 | `⟨x,r⟩` is hard-core for `g` (general case, asymptotic) | C | 4 | Asymptotic/HardCore.lean | `HardcoreBit.glBit`, `guessInverter`, `invProb_guessInverter`, `invProb_guessInverter_cubic` | Thm-87.3.c, Thm-87.3.1–.9, Machine-Repetition, Machine-Primitives |
| Thm-87.3.c | definition | 3.4.2 | the setting `g`, `h = ⟨·,·⟩`, inverters keeping `r`, per-`x` success `secProb` | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `ip`, `glPad`, `glBit`, `glInverter`, `secProb`, `predProb_glPad_eq` | — |
| Thm-87.3.1 | proof case | 3.4.3 | oversimplified case: perfect predictor ⇒ perfect inverter (queries `e_i`) | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `perfectRecover`, `perfectInverter`, `invProb_perfectInverter`, `ip_single` | — |
| Thm-87.3.2 | proof case | 3.4.3 | less simplified case `3/4 + ε`: pairs `(r, r ⊕ e_i)`, majority of `m` trials, success `≥ ε/4` | C | 1 | (exists) HardcoreBit/ThreeQuarters.lean | `trialBit`, `majorityRecover`, `majorityInverter`, `trialBit_correct`, `uprob_majorityRecover_ne_le`, `invProb_majorityInverter` | — |
| Thm-87.3.3 | claim | 3.4.3 | good set `S`: `Pr[x ∈ S] ≥ ε/2` (both thresholds `3/4`, `1/2`) | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `half_le_uprob_good`, `half_le_uprob_threshold` | — |
| Fact-88.4 | fact | 3.4.3 | `⟨a, b ⊕ c⟩ = ⟨a,b⟩ ⊕ ⟨a,c⟩` | C | 1 | (exists) HardcoreBit/InnerProduct.lean | `ip_add`, `ip_sum` | — |
| Alg-88.5 | algorithm | 3.4.3 | `B(y)` for the less simplified case | C | 1 | (exists) HardcoreBit/ThreeQuarters.lean | `majorityInverter` | — |
| Alg-89.6 | algorithm | 3.4.3 | `B(y)` for the general case with subroutine `C` producing `(⟨x,r_j⟩, r_j)` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `guessRecover`, `guessInverter`, `idealRecover`, `GuessCoins` | — |
| Thm-87.3.6 | claim | 3.4.3 | with pairwise-independent samples each `x_i` is wrong w.p. `≤ 1/(4mε'^2)`; union bound over `n` bits gives `< 1/2` when `m ≥ 2n/ε'^2` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `uprob_idealRecover_ne_le`, `one_sub_sum_le_uprob_eq` | — |
| Thm-87.3.7 | claim (show this!) | 3.4.3 | subset sums `r_I = ⊕_{j∈I} s_j` over nonempty `I ⊆ [log m]` are pairwise independent and uniform | C | 1 | (exists) HardcoreBit/PairwiseIndependence.lean | `subsetSum`, `pairwiseUniform_subsetSum`, `card_nonempty_finset` | — |
| Thm-87.3.8 | claim | 3.4.3 | all `log m` guesses `b'_j` are right w.p. `1/m`; then every `b_I` is right | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `uprob_guess_eq`, `guessRecover_correct_guess`, `uprob_guessRecover_ge` | — |
| Thm-87.3.9 | claim | 3.4.3 | final bound: `B` inverts w.p. `ε'/(2m) = (ε/2)^3/(4n)` | C | 1 | (exists) HardcoreBit/GoldreichLevin.lean | `invProb_guessInverter` (`ε/(4·2^k)`), `invProb_guessInverter_cubic` (`ε^3/(16n)`) | — |
| Thm-87.3.coll | theorem (needed by 104.4, ch.4) | 3.4.2 | GL for a collection: `g_i(x,r) = (f_i(x), r)`, `⟨x,r⟩` hard-core for the collection | C | 3 | Asymptotic/HardCore.lean | the per-`i` concrete theorems + `half_le_uprob_threshold` over `i` | Thm-87.3.b, Def-41.1, Def-78.3.coll |
| Def-91.1 | definition | 3.5 | single-message secure (private-key) encryption | C | 2 | Asymptotic/Encryption.lean | `distAdv` | Def-24.7, Machine-NUPPT |
| Alg-92.1 | algorithm | 3.6 | PRG-OTP scheme: `k ← U_{n/2}`, `Enc_k(m) = m ⊕ G(k)` | C | 2 | Asymptotic/Encryption.lean | — | Def-77.1, Def-24.7, Machine-Primitives |
| Claim-92.a | claim (OTP perfect secrecy, used) | 3.6 | `m ⊕ U` is uniform; `{m_0 ⊕ U}` and `{m_1 ⊕ U}` are identical | C | 1 | Asymptotic/Encryption.lean | `uprob_comp_equiv`, `pushesUniform_xor`, `acceptProb_comp_equiv` | — |
| Thm-92.2 | theorem | 3.6 | scheme 92.1 is single-message secure | C | 2 | Asymptotic/Encryption.lean | `distAdv_comp`, `prgAdv`, `abs_sub_le_sum_hybrids` | Alg-92.1, Claim-92.a, Lem-71.5, Lem-71.6 |
| Def-93.1 | definition | 3.7 | multi-message secure encryption | C | 2 | Asymptotic/Encryption.lean | `distAdv`, `copies`-style tuple samplers | Def-91.1 |
| Thm-94.2 | theorem | 3.7 | a multi-message secure scheme is not deterministic-and-stateless | C | 2 | Asymptotic/Encryption.lean | — | Def-93.1, Def-24.7 |
| Def-95.a | definition | 3.8.1 | random function `RF_n`, two descriptions (table / lazy machine) | C | 1 | (exists) Pseudorandom/Functions/Defs.lean | `randomFunction` | — |
| Claim-95.b | claim | 3.8.1 | the table and lazy descriptions give identical distributions | C | 1 | (exists) Pseudorandom/Functions/LazySampling.lean | `QueryTree.evalLazy`, `QueryTree.uprob_evalLazy`, `extendStream` | — |
| Def-96.1 | definition | 3.8.2 | oracle indistinguishability | C | 3 | Asymptotic/PRF.lean | `QueryTree`, `OracleAdversary`, `oracleDist`, `OracleAdversary.BoundedBy` | Oracle-D7 |
| Claim-96.a | claim ("easy to verify") | 3.8.2 | closure under efficient (oracle) operations for oracle ensembles | O | 3 | Asymptotic/PRF.lean | `QueryTree.simulate`, `QueryTree.eval_simulate`, `BoundedBy.simulate` (one-query-per-query case) | Def-96.1 |
| Claim-96.b | claim | 3.8.2 | hybrid lemma for oracle ensembles | C | 1 | Asymptotic/PRF.lean | `exists_hybrid_gap` | Def-96.1 |
| Claim-96.c | claim | 3.8.2 | prediction lemma for oracle ensembles | O | 2 | Asymptotic/PRF.lean | `uprob_bool_prod` | Def-96.1, Lem-73.8 |
| Def-96.2 | definition | 3.8.2 | pseudorandom function family | C | 2 | Asymptotic/PRF.lean | `prfAdv`, `prfAdv_eq`, `prfAdv_nonneg` | Def-96.1, Machine-PPT |
| Cor-97.a | claim (in proof) | 3.8.2 | any PRG yields a length-doubling PRG (truncate to `n+1` bits, then Lem 80.5) | C | 2 | Asymptotic/PRF.lean | `distAdv_comp`, `prgExtBits` | Def-77.1, Lem-80.5 |
| Constr-97.b | construction | 3.8.2 | GGM family `f_s(b_1…b_n) = g_{b_n}(⋯g_{b_1}(s)⋯)` | C | 1 | (exists) Pseudorandom/Functions/GGM.lean | `pairSel`, `ggmFrom`, `ggm`, `ggmBits`, `splitHalves` | — |
| Claim-97.c | claim (Def 96.2 clause 1) | 3.8.2 | `f_s(x)` is PPT-computable from `(s, x)` | C | 3 | Asymptotic/PRF.lean | — | Machine-Loop |
| Thm-97.3 | theorem | 3.8.2 | PRG ⇒ PRF (GGM is a PRF) | C | 4 | Asymptotic/PRF.lean | `ggm_prfAdv_le`, `exists_ggm_dist`, `ggmBits_prfAdv_le`, `exists_ggmBits_dist`, `ggmDist`, `ggmBitsDist` | Def-96.2, Cor-97.a, Thm-97.3.1–.3, Oracle-D7, Machine-Closure |
| Thm-97.3.1 | hybrids | 3.8.2 | level hybrids `HF^i` (levels `≤ i` random), `HF^1 = f_s`, `HF^n = RF_n` | C | 1 | (exists) GGM.lean | `hybridOracle`, `hybridProb`, `hybridProb_zero`, `hybridProb_top`, `levelAdv` | — |
| Thm-97.3.2 | sub-hybrids | 3.8.2 | query sub-hybrids `HHF^j`, `p(n)` many; gap `ε/(n p(n))` | C | 1 | (exists) SubHybrids.lean | `subHybridStream`, `subHybridProb`, `tableDist`, `table_hybrid`, `hybridProb_level` | — |
| Thm-97.3.3 | claim | 3.8.2 | `HHF^j` can be emulated in PPT (lazy sampling); closure gives a PRG distinguisher | C | 4 | Asymptotic/PRF.lean | `uprob_evalLazy`, `noteQuery`, `ggmDist` cost docstring | Oracle-D7, Machine-Closure, Machine-Loop |
| Alg-99.1 | algorithm | 3.9 | many-message scheme `Enc_k(m) = (r, m ⊕ f_k(r))` | C | 2 | Asymptotic/MultiMessage.lean | — | Def-96.2, Def-24.7, Machine-Primitives |
| Thm-99.2 | theorem | 3.9 | scheme 99.1 is multi-message secure | C | 4 | Asymptotic/MultiMessage.lean | `prfAdv`, `oracleDist`, `distAdv_le_statDist`, `uprob_exists_le`, `pushesUniform_eval_pair` | Alg-99.1, Thm-99.2.1–.3, Oracle-D7, Machine-Closure |
| Thm-99.2.1 | claim | 3.9 | `H1 ≈ H2` (and `H5 ≈ H6`): the oracle adversary with `q+1` queries built from `D` | C | 3 | Asymptotic/MultiMessage.lean | `QueryTree` (chain of `q+1` queries), `prfAdv` | — |
| Thm-99.2.2 | claim | 3.9 | `H2` vs `H3`: distinguishable only on a collision `r_i = r_j`, probability `≤ C(q+1,2)·2^{-n}` | C | 4 | Asymptotic/MultiMessage.lean | `uprob_exists_le`, `uprob_eq_one_div_card`, `uprob_update_absorb`, `PushesUniform` | — |
| Thm-99.2.3 | claim | 3.9 | `H3 = H4` by OTP perfect secrecy (vector version) | C | 1 | Asymptotic/MultiMessage.lean | `Claim-92.a`, `PushesUniform.prodMap` | Claim-92.a |
| Def-102.1 | definition | 3.10 | public-key encryption scheme (with message sampler clause 4) | C | 2 | Asymptotic/PublicKey.lean | — | Machine-PPT |
| Def-102.2 | definition | 3.10 | secure PKE | C | 2 | Asymptotic/PublicKey.lean | `distAdv` | Def-102.1, Machine-NUPPT |
| Claim-103.a | claim | 3.10 | perfect secrecy is impossible for PKE (unbounded adversary) | O | 2 | Asymptotic/PublicKey.lean | `statDist`, `distAdv_le_statDist` | Def-102.1 |
| Claim-103.b | claim | 3.10 | deterministic PKE is insecure | O | 2 | Asymptotic/PublicKey.lean | — | Def-102.2, Machine-Closure |
| Def-103.c | definition (unnumbered) | 3.10 | multi-message secure PKE | C | 2 | Asymptotic/PublicKey.lean | — | Def-102.2 |
| Thm-103.d | theorem (exercise) | 3.10 | for PKE, single-message security ⇒ multi-message security | C | 3 | Asymptotic/PublicKey.lean | `exists_hybrid_gap`, `multicopyRed` (pattern) | Def-103.c, Lem-71.5, Lem-71.6, Machine-Closure |
| Def-103.e | definition (unnumbered) | 3.10 | single-bit secure PKE | C | 1 | Asymptotic/PublicKey.lean | — | Def-102.1 |
| Thm-103.f | theorem (stated) | 3.10 | single-bit secure PKE ⇒ secure PKE by bitwise encryption | C | 3 | Asymptotic/PublicKey.lean | — | Thm-103.d, Def-103.e |
| Constr-104.a | remark | 3.10.1 | `Enc_i(m) = f_i(m)` (textbook RSA) is deterministic hence insecure | O | 1 | Asymptotic/PublicKey.lean | — | Claim-103.b |
| Alg-104.3 | algorithm | 3.10.1 | 1-bit PKE from a TDP with hard-core bit: `(f_i(r), b_i(r) ⊕ m)` | C | 2 | Asymptotic/PublicKey.lean | `owpGen` (pattern) | Def-56.1, Def-78.3.coll |
| Lem-104.a | lemma (concrete, in proof) | 3.10.1 | a distinguisher of `(pk, f_pk(r), b(r))` vs `(pk, f_pk(r), ¬b(r))` with advantage `ε` yields a predictor of `b` with success exactly `1/2 + ε/2` (indexed `owpPredictor`) | C | 3 | Asymptotic/PublicKey.lean | `owpPredictor`, `predProb_owpPredictor_false/true`, `acceptProb_id_owp`, `uprob_bool_prod` | — |
| Thm-104.4 | theorem | 3.10.1 | TDPs (with hard-core bit) ⇒ scheme 104.3 is a secure single-bit PKE | C | 3 | Asymptotic/PublicKey.lean | Lem-104.a | Alg-104.3, Lem-104.a, Lem-73.8, Thm-87.3.coll, Machine-Closure |
| Asm-105.1 | assumption | 3.11 | DDH in the order-`q` subgroup of `Z_p^*`, `p = 2q+1` safe prime | C | 2 | Candidates/ElGamal.lean | `distAdv` | Ensemble-D6, NT-105.a |
| NT-105.a | number theory | 3.11 | `p = 2q+1` prime: squares form the unique subgroup `G_q` of order `q`, cyclic, every `≠ 1` element generates; `a ↦ a^2` is 2-to-1 onto `G_q` | C | 3 | Candidates/ElGamal.lean | Mathlib `IsCyclic (ZMod p)ˣ`, `Subgroup.card_eq_card_quotient_mul_card_subgroup`, `ZMod.euler_criterion`, `IsCyclic.card_pow_eq_one_le`, `orderOf_eq_prime` | — |
| Claim-106.a | claim | 3.11 | DDH ⇒ DL (a DL solver breaks DDH) | O | 3 | Candidates/ElGamal.lean | — | Asm-105.1, Asm-52.2 |
| Claim-106.b | claim | 3.11 | in `Z_p^*` itself DDH is false: element orders (2, q, 2q) distinguish tuples | O | 3 | Candidates/ElGamal.lean | Mathlib `legendreSym`, `ZMod.euler_criterion` | NT-105.a |
| Alg-106.2 | algorithm | 3.11 | El Gamal `Gen/Enc/Dec` | C | 2 | Candidates/ElGamal.lean | — | NT-105.a, Machine-PPT, Thm-45.6 |
| Claim-107.a | claim (missing in text) | 3.11 | `h = g^2` for uniform `g ∈ Z_p^*` is uniform on `G_q`; it is a generator unless `h = 1` (probability `1/q`); statistical distance to "uniform generator" is `1/q` | C | 2 | Candidates/ElGamal.lean | `pushesUniform_of_surjective`, `statDist` | NT-105.a |
| Thm-107.3 | theorem (exercise) | 3.11 | DDH ⇒ El Gamal (message space `G_q`) is secure | C | 3 | Candidates/ElGamal.lean | `distAdv_comp`, `acceptProb_comp_equiv` (`Equiv.mulLeft`), `abs_sub_le_sum_hybrids` | Alg-106.2, Asm-105.1, Claim-107.a, Lem-71.5, Lem-71.6 |
| Def-107.b | definition (missing in text) | 3.11 | encoding of bit strings into `G_q` (`m ↦ ±m`, the square), so that Def 102.1's `{0,1}^n` message space is met | O | 3 | Candidates/ElGamal.lean | Mathlib `ZMod.exists_sq_eq_neg_one_iff` (`p ≡ 3 (4)`) | NT-105.a |
| Claim-107.c | claim (unproved) | 3.12 | one-way functions are minimal: PRG ⇒ OWF (also PRF/encryption ⇒ OWF) | O | 3 | Asymptotic/Pseudorandom.lean | `distAdv`, `invProb` | Def-77.1, Def-27.3 |
| Claim-107.d | claim (unproved, cited) | 3.12 | no black-box PKE from OWF | D | 5 | — | — | — |
| Thm-188.7 | appendix | A | Chernoff bound `Pr[∑X_i − μn ≥ ε] ≤ 2^{-ε²n}` | O | 3 | Asymptotic/Chernoff.lean (only if needed) | replaced by `chebyshev_pairwise` | — |
| Lem-189.8 | appendix | A | majority vote of `ℓ > p(n)^2` biased samples is right w.h.p. (statement garbled: "`1 − 2??`") | O | 1 | (exists) PairwiseIndependence.lean | `uprob_majority_fails_le` (bound `1/(4δ²ℓ)`) | — |
| Ineq-189.a | appendix | A | pairwise-independent sampling inequality `Pr[|∑X_i/n − μ| ≥ ε] ≤ (1−μ²)/(nε²)` | C | 1 | (exists) PairwiseIndependence.lean | `chebyshev_pairwise`, `chebyshev_pairwise_ident` (bits, bound `1/(4δ²m)`) | — |

## 2. Statements, reuse notes, text issues

### 2.1 §3.0–§3.1 Ensembles and computational indistinguishability

**Claim-67.a** (p. 67, "show this") — *No generator outputs a perfectly random longer string.*
Statement: for every `n < m` and every `G : (Fin n → Bool) → (Fin m → Bool)`, the pushforward of
`U_n` under `G` is not `U_m`; quantitatively `statDist (G_* U_n) U_m ≥ 1 − 2^{n−m} ≥ 1/2`, so an
unbounded distinguisher (membership in the image of `G`) has advantage `≥ 1/2`. Reuse: `statDist`,
`FinDist.map`, `distAdv_le_statDist` (the test "is `t` in the image" is a deterministic
distinguisher; `acceptProb` on `G` is `1`, on `U_m` is `|image|/2^m ≤ 2^{n−m}`). Optional,
difficulty 2. (The text argues via Shannon's theorem from ch. 1; the pigeonhole form is simpler.)

**Def-69.3** — *Ensemble.* A sequence `{X_n}` with `X_n` a distribution over `{0,1}^*`. D6 reading:
`structure Ensemble` with `seedLen outLen : ℕ → ℕ` (explicit `C(n+1)^c` formulas, or at least
`PolyBound`) and `sample n : (Fin (seedLen n) → Bool) → (Fin (outLen n) → Bool)`; the distribution
`X_n` is the pushforward of uniform seeds (dyadic). `Samplable X` := the sampler family is computed
by one PPT on input `1^n` (coins = seed). Deviation: every distribution is dyadic (the text allows
arbitrary distributions over `{0,1}^*`; the text's own ensembles are all of this form, except the
DDH/El Gamal ones that sample primes and `Z_q` — see Asm-105.1).
Reuse: samplers `σ → γ` of `Foundations/Experiments.lean` are the one-`n` slices.

**Def-69.4** — *Computational indistinguishability.* `X ≈ Y` iff for every nuPPT `D` there is a
negligible `ε` with `|Pr[t ← X_n : D(t)=1] − Pr[t ← Y_n : D(t)=1]| < ε(n)` for all `n`. Formal:
`CompIndist X Y := ∀ D : NUPPT, Negligible (fun n => distAdv (X.sample n) (Y.sample n) (D.dist n))`
where `D.dist n : (Fin (outLen n) → Bool) → (Fin (coins n) → Bool) → Bool` runs the machine on
`pairEncode (pairEncode (List.ofFn t) (α n)) (List.ofFn r)` and reads `[true]`. Note: the text's
`∃ ε negligible, ∀ n, gap(n) < ε(n)` is equivalent to `Negligible gap` because `gap ∈ [0,1]`
(`Negligible.mono` one way; take `ε = gap + 2^{-n}` with `Negligible.add` the other way).
Also define the notations: `Distinguishes D X_n Y_n ε := ε < distAdv …` ("with probability `ε`")
and the ensemble version "for all `n`". The text does **not** give `D` the input `1^n` in Def 69.4
(it does in Def 75.2 and 96.1); with `outLen n ≥ 1` polynomial and the advice string of length
depending on `n`, the machine can recover `n` from `|α|` or `|t|` — record as a convention
(adversaries always receive `1^n`, D5), no mathematical difference.
Text issue: strict `<` here, `≤` in Defs 91.1/93.1/102.2 — immaterial.

**Lem-71.5** — *Closure under efficient operations.* If `X ≈ Y` then for every nuPPT `M`,
`{M(X_n)} ≈ {M(Y_n)}`. Here `M(X_n)` is the ensemble with sampler `pushSampler (M.run n) (X.sample n)`
(seed = seed of `X` ++ coins of `M`); its seed length is polynomial, so it is an ensemble in the D6
sense. Concrete: `distAdv_sunglassRed : distAdv X Y (sunglassRed P D) = distAdv (pushSampler P X) (pushSampler P Y) D`
(exact equality, randomized `P`), `distAdv_comp` (deterministic `P`). Bridge: `D' = D ∘ M` is an
nuPPT (Machine-Closure: post-composition, advice concatenation `pairEncode (α_M n) (α_D n)`, coin
splitting `r = r_M ++ r_D` with explicit lengths), then `Negligible.mono` with the equality.
Difficulty 3 (all in the machine closure).

**Lem-71.6** — *Hybrid lemma.* If `D` distinguishes `X^1` and `X^m` with probability `ε` then some
`i ∈ [1, m−1]` has `D` distinguishing `X^i, X^{i+1}` with probability `ε/m`. Concrete:
`exists_hybrid_gap (P : ℕ → ℝ) (ht : 0 < t) : ∃ k < t, |P 0 − P t| / t ≤ |P k − P (k+1)|` with
`P i = acceptProb (X^{i+1}) D` and `t = m − 1` (the proof's own bound is `ε/(m−1) > ε/m`; the
text's `ε/m` is weaker but correct — note the off-by-one in text_issues). Also
`abs_sub_le_sum_hybrids` (telescoping form) and the uniform variant `distAdv_mixDist_eq`
(random index, exact `|P 0 − P t|/t`), which removes the non-uniform choice of `i`. Nothing to
add; difficulty 1. Statement in Lean should be the concrete one (no machines involved).

**Rem-72.7** — `D ↦ Pr[D(·)=1]` induces a pseudometric; the hybrid lemma is the triangle
inequality. Formal: `distAdv X Z D ≤ distAdv X Y D + distAdv Y Z D` (`abs_sub_le`). Optional,
difficulty 1 (one-liner, useful as API).

**Claim-72.a** — "it is easy to construct a long sequence in which adjacent pairs are
indistinguishable but the extremes are distinguishable": e.g. `2^n + 1` single-bit distributions
`B_i = Bernoulli(i/2^n)` (sampler from `n` coins: output `1` iff the seed, read as a number, is
`< i`): `statDist B_i B_{i+1} = 2^{-n}`, hence `distAdv ≤ 2^{-n}` for every `D`
(`distAdv_le_statDist`) — adjacent pairs are even *statistically* indistinguishable, while
`B_0 = 0` and `B_{2^n} = 1` are told apart by the identity with advantage `1`. Optional,
difficulty 2.

**Ex-72.b** — For pairwise `≈` ensembles `X, Y, Z` over `{0,1}^n` with PPT samplers,
`{x ← X_n; y ← Y_n : x ⊕ y} ≈ {y ← Y_n; z ← Z_n : z ⊕ y}`: instance of Lem-71.5 with
`M(t) = t ⊕ y`, `y ← Y_{|t|}` (needs `Samplable Y`), applied to `X ≈ Z`. Concrete:
`distAdv_sunglassRed` with `P t c = t + Y.sample n c`. Optional, difficulty 2.

**Claim-73.a** (p. 73, "show this!") — *Predicting implies distinguishing.* If `A` satisfies
`Pr[b ← {0,1}; t ← X^b_n : A(t) = b] ≥ 1/2 + δ`, then `A` itself (as a distinguisher) has
`|Pr[A(X^1)=1] − Pr[A(X^0)=1]| ≥ 2δ`. Concrete identity (to be proved once, used by 73.8, 75.4,
104.4): for samplers `X⁰, X¹` and `A : γ → ρ → Bool`,
`uprob (fun (b, s, r) => A (X^b s) r = b) = 1/2 + (acceptProb X¹ A − acceptProb X⁰ A)/2`
(`uprob_bool_prod` splits on `b`; `uprob_not` for the `b = 0` half). Both directions of the
prediction lemma are this identity. Core, difficulty 2.

**Lem-73.8** — *Prediction lemma.* If a nuPPT `D` distinguishes `{X⁰_n}, {X¹_n}` with probability
`μ(n)` for infinitely many `n`, there is a nuPPT `A` with
`Pr[b ← {0,1}; t ← X^b_n : A(t) = b] ≥ 1/2 + μ(n)/2` for infinitely many `n`. Proof: `A = D` or
`A = 1 − D` according to the sign of `Pr[D(X¹)=1] − Pr[D(X⁰)=1]` (the sign is a per-`n`
non-uniform choice = one advice bit; the text's "one of these works for infinitely many `n`"
avoids advice by pigeonhole on an infinite set — both routes are available; the advice route gives
the stronger "for every `n`" statement). Concrete: from Claim-73.a's identity,
`∃ flip : Bool, predProb₂ X⁰ X¹ (flipPred D flip) = 1/2 + distAdv X⁰ X¹ D / 2` (the pattern of
`exists_owpPredictor`/`predProb_owpPredictor_true`). Asymptotic: `¬Negligible (distAdv …)` ⇒
`¬Negligible (predAdv …)` for the nuPPT `A` with advice bit `flip n`. Difficulty 3 (advice bit
hard-wiring + output negation: Machine-Closure).
Text issue: the hypothesis quantifies "for infinitely many `n`" — this is the `not_negligible_iff`
form; also the conclusion's `A` depends on `D` only, as it should.

**Claim-73.b** — The ubiquitous "assume for contradiction there is a polynomial `p` such that for
infinitely many `n` the advantage exceeds `1/p(n)`" is exactly `not_negligible_iff`
(`¬Negligible μ ↔ ∃ c, ∀ n₀, ∃ n ≥ n₀, 1/n^c ≤ |μ n|`); with `1/p(n)` for a general polynomial
`p` replaced by `1/n^c` (fine: `p(n) ≤ n^c` eventually). Exists; difficulty 1. Planners: every
asymptotic theorem is stated positively (`Negligible …`) and proved by contraposition through this
lemma.

### 2.2 §3.2 Pseudorandomness and the next-bit test

**Def-74.1** — *Pseudorandom ensemble.* `X` (over `{0,1}^{ℓ(n)}`) is pseudorandom iff
`X ≈ {U_{ℓ(n)}}`. Formal: `Pseudorandom X := CompIndist X (uniformEnsemble X.outLen)`; at one `n`
the advantage is `prgAdv (X.sample n) D = distAdv (X.sample n) id D`. Difficulty 1.

**Def-75.2** — *Next-bit test.* `X` over `{0,1}^{ℓ(n)}` passes the next-bit test iff for every
nuPPT `A` there is a negligible `ε` with, for all `n` and all `i`,
`Pr[t ← X_n : A(1^n, t_1 … t_i) = t_{i+1}] < 1/2 + ε(n)`. Intended index range: `0 ≤ i < ℓ(n)`
(prefix of length `i`, predicted bit `t_{i+1}`, bits 1-indexed); the text writes
`i ∈ [0, …, ℓ(n)]`, which includes a nonexistent bit `t_{ℓ(n)+1}`. Formal (one `n`):
`nextBitProb (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) := uprob fun (s, r) => A (Fin.init-prefix (X s) i) r = X s i`
(0-indexed: prefix of length `i.val`, predict bit `i`). Asymptotic: `∀ A nuPPT, Negligible (fun n => sup_i (nextBitProb … − 1/2))`
— the `∀ i` inside a single negligible `ε` is important (the text's quantifier order is
`∃ ε ∀ n ∀ i`); formalize as `∀ A, ∃ ε, Negligible ε ∧ ∀ n i, nextBitProb … ≤ 1/2 + ε n`, or
equivalently `Negligible (fun n => ⨆ i, …)` over the finite `i`. The machine `A` gets `1^n` and
the prefix (as `pairEncode (1^n) prefix`); `i` is the prefix length. **Rem-75.3** is the
convention that `A` gets `1^n` (so its time is polynomial in `n`, not in the prefix length) — D5.

**Thm-75.4** — *Completeness of the next-bit test.* If `X` passes the next-bit test then `X` is
pseudorandom. Contrapositive proof in the text; the formal route: concrete reduction
`Thm-75.4.c` + `Claim-73.b` + machine closure.

**Thm-75.4.c** (concrete, new) — for every sampler `X : σ → Fin ℓ → Bool` (`0 < ℓ`) and every
distinguisher `D : (Fin ℓ → Bool) → ρ → Bool`, there exist `i : Fin ℓ` and `flip : Bool` such that
`nextBitProb X i (nextBitPred D i flip) ≥ 1/2 + prgAdv X D / ℓ`, where `nextBitPred D i flip`
(= **Alg-76.5**) on a prefix `t_1…t_i` draws `ℓ − i` uniform bits `u_{i+1}…u_ℓ` and coins for
`D`, runs `g ← D(t_1…t_i u_{i+1}…u_ℓ)`, outputs `u_{i+1}` if `g = 1` and `¬u_{i+1}` otherwise
(negated if `flip`). Proof plan (the text's, made exact):
* **Thm-75.4.1** hybrids `H^i : σ × (Fin ℓ → Bool) → Fin ℓ → Bool`, `H^i (s,u) j = if j < i then X s j else u j`;
  `acceptProb (H^0) D = acceptProb id D` (`acceptProb_snd`), `acceptProb (H^ℓ) D = acceptProb X D`
  (`acceptProb_fst`). Hybrid lemma: `∃ i < ℓ, prgAdv X D / ℓ ≤ |P(H^i) − P(H^{i+1})|`.
* flipped hybrid `H̃^{i+1} (s,u) j = if j < i then X s j else if j = i then ¬X s i else u j`.
* **Thm-75.4.2** mixing identity: `P(H^i) = (P(H^{i+1}) + P(H̃^{i+1}))/2` — the bit `u_i` of `H^i`
  equals `X s i` or `¬X s i` each with probability `1/2` independently of everything else
  (`uprob_bool_prod` after the bijection `(b, s, u) ↦ (s, update u i (xor b (X s i)))`, as in
  `acceptProb_id_owp`). Hence `|P(H^{i+1}) − P(H̃^{i+1})| ≥ 2 prgAdv/ℓ`.
* predictor analysis: `nextBitProb X i (nextBitPred D i false) = 1/2 + (P(H^{i+1}) − P(H̃^{i+1}))/2`
  — the completed string is a sample of `H^{i+1}` when `u_{i+1} = t_{i+1}` and of `H̃^{i+1}`
  otherwise (Claim-73.a's identity with `X¹ = H^{i+1}`, `X⁰ = H̃^{i+1}`); `flip = true` gives
  `1/2 − (…)/2`. Choose `flip` by the sign.
Reusable patterns: `prgHybrid`/`acceptProb_prgExtRed_right` (planting a uniform bit via
`acceptProb_update`), `owpPredictor`/`predProb_owpPredictor_false` (predictor from a
distinguisher plus one random bit). Difficulty 4 (new 250-line concrete file).
Asymptotic bridge: `i(n)` and `flip(n)` are advice; `nextBitPred` = draw `ℓ(n) − i` coins,
concatenate, one call of `D`, compare/negate (Machine-Closure + Machine-Primitives). Then
`not_negligible_iff` on `prgAdv` gives `c` with `prgAdv ≥ n^{-c}` i.o., so the predictor has
advantage `≥ n^{-c}/ℓ(n)` i.o., contradicting Def 75.2 (`Negligible.mul_pow`-style arithmetic).

Text issues (Thm 75.4 proof): (a) Alg 76.5 draws "`ℓ(n) − i` bits `← U_{ℓ(n)−1}`" — should be
`U_{ℓ(n)−i}`; (b) `H̃^i_n` is defined with `x̄_i` and a stray `u_{l(m)}`, while the argument uses
`H̃^{i+1}` flipping bit `i+1`; (c) the proof's hybrids are 0-indexed `x_0 x_1 …` while Def 75.2 is
1-indexed `t_1 t_2 …`; (d) the final displayed probability has `A(t) = 1` where `A(t) = b` is meant,
and the prediction-lemma display writes `D` for `A`; (e) the text applies the hybrid lemma with
`ℓ(n)+1` hybrids and claims gap `1/(p(n)ℓ(n))` (fine, `ℓ` gaps).

**Thm-75.4.conv** (implicit converse: pseudorandom ⇒ passes next-bit test) — concrete: for a
next-bit predictor `A` at position `i` with success `1/2 + δ` on `X`, the distinguisher
`D(t) := [A(t_1…t_i) = t_{i+1}]` has `acceptProb X D = 1/2 + δ` and `acceptProb id D = 1/2`
exactly (the uniform bit `t_{i+1}` is independent of the prefix and of `A`'s coins), hence
`prgAdv X D = δ`. Optional, difficulty 2; it is the honest statement behind "a pseudorandom
distribution passes all efficient tests".

### 2.3 §3.3 Pseudorandom generators and hard-core bits

**Def-77.1** — *PRG.* `G : {0,1}^* → {0,1}^*` is a PRG iff (1) `G` is computable by a PPT
(Def 24.6: same output for every coin string, so effectively deterministic polynomial time:
`Complexity.PolyTimeComputable` on `List Bool`), (2) `|G(x)| > |x|`, (3) `{x ← U_n : G(x)}` is
pseudorandom. Formal: `structure PRG` with `stretch : ℕ → ℕ` (explicit polynomial `ℓ`, `n < ℓ n`),
`G : ∀ n, (Fin n → Bool) → (Fin (ℓ n) → Bool)`, `computable : PolyTimeComputable (bridge of G)`,
`secure : ∀ D nuPPT, Negligible (fun n => prgAdv (G n) (D.dist n))`. Deviation: length-regular
(`|G(x)|` depends only on `|x|`), as the concrete layer assumes; the text's `G : {0,1}^* → {0,1}^*`
with `|G(x)| > |x|` admits irregular lengths, which no construction in the book uses.

**Constr-77.a / Claim-78.a / Claim-78.b** (Shamir's generator, p. 77–78). `G(s) = f^n(s)‖…‖f(s)‖s`.
Claim-78.a: if `f` is a permutation of `{0,1}^n` and `x` uniform then `f^k(x)` is uniform
(`uprob_comp_equiv` with `(Equiv.iterate f k)`; also `acceptProb_comp_equiv`). Claim-78.b: the
blocks are unpredictable (inverting `f`) but individual bits may be predictable — a OWP may leave
the first two bits of its input unchanged; the concrete witness is Garg's Claim 2.3
(`predProb_fixedBitPredictor`, `predProb_positionBit` in `HardcoreBit/NoFixedBit.lean`: a fixed
input bit of `f(x_{-y})‖x_y‖y` is predicted with probability `1`). Both optional (difficulty 1–2);
record as remarks in `HardCore.lean`'s module docstring if not formalized.

**Def-78.3** — *Hard-core predicate.* `h : {0,1}^* → {0,1}` is hard-core for `f` iff `h` is
PPT-computable and for every nuPPT `A` there is a negligible `ε` with, for all `n`,
`Pr[x ← {0,1}^n : A(1^n, f(x)) = h(x)] ≤ 1/2 + ε(n)`. Formal:
`HardCore (f : ∀ n, (Fin n → Bool) → (Fin (m n) → Bool)) (h : ∀ n, (Fin n → Bool) → Bool) :=
PolyTimeComputable h ∧ ∀ A nuPPT, Negligible (fun n => predProb (f n) (h n) (A.pred n) − 1/2)`
(`predProb f B A = uprob fun (x, r) => A (f x) r = B x` is the exact one-`n` slice; the
`− 1/2` may be negative, which `Negligible` (absolute values) tolerates, or state
`∃ ε, Negligible ε ∧ ∀ n, predProb … ≤ 1/2 + ε n`). Text issue: the definition mixes `k` and `n`
(`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); intended `k = n`. Note the text says hard-core "for
`f(x)`" with `f` a single function (not a collection), and later uses it for collections:

**Def-78.3.coll** (unnumbered, needed by Lem 84.1, Alg 104.3/Thm 104.4 and ch. 4 Thm 126.4) —
`{h_i}` is hard-core for the collection `{f_i : D_i → R_i}_{i ∈ I}` with index sampler `Gen` iff
`h_i(x)` is PPT-computable from `(i, x)` and for every nuPPT `A` there is a negligible `ε` with
`Pr[i ← Gen(1^n); x ← D_i : A(1^n, i, f_i(x)) = h_i(x)] ≤ 1/2 + ε(n)`. Concretely this is
`predProb` for the sampler `(c, x) ↦ (i(c), x)` on the typed domain `Σ i, D_i` or, in the D5/D6
style, for `f n : (Fin (s n) → Bool) × (Fin n → Bool) → …` with the index drawn from the first
component (`pairEncode i (f_i x)` on tapes). Difficulty 2.

**Claim-78.c** — LSB and `half_N` are hard-core for RSA "under the RSA assumption" (stated as
known, no proof; Alexi–Chor–Goldreich–Schnorr). Deferred (difficulty 5; nothing downstream needs
it; the RSA PRG of §3.3.6 is illustrative).

**Thm-79.4** — Let `f` be a one-way permutation (single function, `f n : (Fin n → Bool) ≃ (Fin n → Bool)`,
PPT-computable, one-way) and `h` hard-core for `f`. Then `G(s) = f(s)‖h(s)` (output length `n+1`)
is a PRG. Concrete (exists, with `β := Unit`): `owpGen f B : α × β → α × β × Bool`,
`exists_owpPredictor : ∃ flip, predProb (owpPair f) B (owpPredictor D flip) = 1/2 + prgAdv (owpGen f B) D`;
with `β = Unit`, `owpPair f ≃ f` and `owpGen f B ≃ (f s, B s)`; the bit-string form needs the
re-encoding `(Fin n → Bool) × Bool ≃ (Fin (n+1) → Bool)` (`Fin.snocEquiv`-style; `owpBitsEquiv`
is the `n+n+1` version) and `prgAdv_comp_equiv`. Deviation (proof route): the text proves 79.4
through Thm 75.4 ("the first `n` bits are uniform so the predictor must be for bit `n+1`",
Claim-79.a); the formal proof uses Garg's direct reduction (one call of `D` on `f(s)‖σ` with a
random bit `σ`, output `σ` or `¬σ`), which gives the exact bound `1/2 + ε` without the `1/ℓ` loss.
Record in the docstring. Text issues: the proof says "`A` predicts the `i`th bit with probability
`1/p(n)`" (meaning advantage) and "contradicts that `b` is hard-core" (`b` should be `h`).
Bridge: the predictor is nuPPT (one extra coin, one call, advice bit `flip`: Machine-Closure);
`not_negligible_iff`. Difficulty 3.
Downstream: ch. 4 Thm 126.4 uses the same `f, h` with `Com(b, r) = (f(r), b ⊕ h(r))` — see Lem-104.a.

**Claim-79.a** (in the proof of 79.4) — for a permutation `f`, `{s ← U_n : f(s)}` is `U_n`, so a
next-bit predictor for any position `i ≤ n` of `G(s) = f(s)‖h(s)` succeeds with probability
exactly `1/2`. Optional, difficulty 2 (not needed on the formal route).

**Lem-80.5** — *Expansion.* Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG and `ℓ` a polynomial;
`G'(s) = b_1 … b_{ℓ(n)}` where `X_0 = s`, `X_{i+1}‖b_{i+1} = G(X_i)`. Then `G'` is a PRG.
Concrete (exists): `prgExtBits G l : (Fin n → Bool) → Fin (l + n) → Bool` (bits *and* final seed),
`exists_prgExtBitsRed_ge : ∃ k < l, prgAdv (prgExtBits G l) D / l ≤ prgAdv G (prgExtBitsRed G l k D)`;
the text's `G'` is the projection of `prgExtBits G l` onto its first `l` bits, and the projection
is a deterministic post-processing (`distAdv_comp`: a distinguisher of the projected output is a
distinguisher of the full output with the same advantage). Also the uniform version
`prgAdv_prgExtAvgRed` (exact `ε/l`, random `k`). Encoding deviations: Garg's `G : S → Bool × S`
puts the bit first and reads `G(s)` as `(bit, next seed)` via `Fin.consEquiv`; the text's
`X_{i+1}‖b_{i+1}` puts the seed first — a fixed re-encoding (`prgAdv_comp_equiv`). The text's
proof (hybrids `H^i = U_{m−i}‖G_i(U_n)`, reduction `M(y)` that knows `i`) is Garg's up to indexing.
Bridge: the reduction at hybrid `k` makes `l − k − 1` calls to `G` (Machine-Loop) and one call to
`D`, draws `l` coins, and has `k` as advice; `G'` itself is PPT-computable by iterating `G` `ℓ(n)`
times (Machine-Loop); `Negligible.mul_pow` for the factor `ℓ(n)`. Difficulty 3.
Text issues: `m(n)` and `ℓ(n)` used interchangeably; hybrids "for `i = 1, …, m(n)`" should start
at `0`; in `M(y)` the input `y` is read as `y_1` = bit, `y_2…y_{n+1}` = seed, contradicting the
construction's `X_{i+1}‖b_{i+1}` order; `G'` drops the final seed while the hybrids keep it
implicitly.

**Cor-81.7** — For a OWP `f` with hard-core bit `h`, `G(x) = h(x)‖h(f(x))‖h(f^{(2)}(x))‖…‖h(f^{ℓ(n)}(x))`
is a PRG. Proof: apply Lem 80.5 to `G'(x) = f(x)‖h(x)` (Thm 79.4). Formal: with
`G₁ s := (h s, f s) : Bool × S`, the closed form of `prgExt` gives output bit `i` equal to
`(G₁ ((prgStep G₁)^[i] s)).1 = h (f^[i] s)` and `prgStep G₁ = f`, so the corollary's formula is
`prgExt G₁ l` projected to bits (with `l = ℓ(n) + 1` bits `i = 0 … ℓ(n)`). Text issue: the formula
lists `ℓ(n)+1` bits (`i = 0 … ℓ(n)`) whereas Lem 80.5 produces `ℓ(n)`; harmless. Expansion needs
`ℓ(n) + 1 > n`. Difficulty 2 (composition + the closed-form identity). PPT-computability of `G`:
Machine-Loop over `f` and `h`.

**Constr-82.a** — PRG from a collection of OWPs `{f_i}` with hard-core bits `{h_i}`:
`G(r_1, r_2) = h_i(f_i(x))‖h_i(f_i^{(2)}(x))‖…` where `r_1` samples `i` and `r_2` samples `x ∈ D_i`
("can be easily adapted"; no proof). Deferred: `prgExt` assumes a *uniform* seed type `S` and
`prgAdv` against uniform `Bool × S`; here the seed `(i, x)` is not uniform on a product type and
the one-bit generator `(i, x) ↦ (h_i(x), (i, f_i(x)))` must keep `i` in its state. The needed
generalization: stretch extension for `G : S → Bool × S` relative to a seed *sampler* `μ : σ → S`
with `G_*μ ≈ (U_1, μ)` ("`μ`-pseudorandom one-bit generator"); the hybrids and the reduction go
through verbatim with `μ` in place of `id` (`acceptProb_update` is unchanged). Then `i` must be
dropped from the output (`distAdv_comp`). Difficulty 3; nothing downstream needs it (ch. 4 uses a
single OWP). The three instantiations **Constr-82.b** (Blum–Micali: Lem 84.1 + Constr-82.a),
**Constr-83.a** (RSA PRG: Claim-78.c), **Constr-83.b** (BBS: hard-core LSB for squaring, not in the
text) and **Claim-83.c** (`log n` bits per iteration, "provably secure", unproved) are deferred.

### 2.4 §3.4 Hard-core bits from any one-way function

**Lem-84.1** — *DL hard-core bit.* Under the DL assumption, `half_{p−1}(x) := [0 ≤ x ≤ (p−1)/2]`
is a hard-core predicate for `f_{p,g}(x) = g^x mod p` of the collection `DL` (index `(p, g)` with
`p` an `n`-bit prime and `g` a generator of `Z_p^*`, domain `Z_{p−1}`; Thm 52.3 writes the index
as `(q, g)` with `D_i = Z_q`, `R_i = G_p` — garbled). Precise intended statement: for every nuPPT
`A` there is a negligible `ε` with
`Pr[(p,g) ← Gen_DL(1^n); x ← Z_{p−1} : A(1^n, p, g, g^x) = half_{p−1}(x)] ≤ 1/2 + ε(n)`,
provided `Pr[(p,g) ← Gen_DL(1^n); x ← Z_{p−1} : B(1^n, p, g, g^x) = x]` is negligible for every
nuPPT `B` (DL in `Z_p^*`). **Text error:** Assumption 52.2 is stated for *prime-order* groups
`G_q`, but the lemma, Alg 84.2 and the proof use `Z_p^*` (even order `p−1`, `g^{(p−1)/2} = −1`,
square roots split the exponent's parity); the lemma needs DL in `Z_p^*` for a uniform generator
`g` (as in Thm 52.3's collection), which is a different assumption from 52.2. Formalize the DL
assumption for the `Z_p^*` collection explicitly (ch. 2 inventory: Thm 52.3's `DL` collection) and
cite 52.2 as the stated form. Also "`x ← Z_p`" in the proof should be `x ← Z_{p−1}`.
Scope core (the task lists it), difficulty 5 — the hardest item of the chapter; the text's proof
is a sketch with four gaps (Lem-84.1.3–.5 and the square-root algorithm). Recommended split:

* **Lem-84.1.0** `half_{p−1}` is PPT-computable (a comparison; trivial, Machine-PPT).
* **Lem-84.1.1** number theory (concrete, Mathlib): for `p` an odd prime and `g` a generator of
  `(ZMod p)ˣ`: `g^{(p−1)/2} = −1` (`ZMod.pow_div_two_eq_neg_one_or_one` plus `orderOf g = p − 1`
  via `orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient`, `Nat.totient_prime`);
  `g^e` is a square iff `e` is even (`ZMod.euler_criterion`); the square roots of `g^{2x}` are
  exactly `g^x` and `g^{x + (p−1)/2} = −g^x`. Difficulty 2.
* **Alg-84.2** bit-by-bit DL with a *perfect* oracle `A(y) = half_{p−1}(DL(y))`: for `k = |p|`
  down to `1`: if `y_k` is a square set `x_k = 0` else `x_k = 1, y_k ← y_k/g`; `y_{k−1} ← √y_k`
  (one of the two roots); if `A(y_{k−1}) = 0` then `y_{k−1} ← −y_{k−1}`; output the bits `x`.
  Correctness: with `y = g^e`, each round halves `e` (after removing the parity bit) and the oracle
  selects the root with the *smaller* exponent `⌊e/2⌋ < (p−1)/2`; after `|p|` rounds the bits are
  the binary expansion of `e`. Text issues: the loop writes `k = |p|` and decrements. (Run-3
  audit P8-3: the root selection "IF `b = 0` THEN `y_{k−1} ← −y_{k−1}`" is *consistent* with
  `half`'s convention — `half = 1` iff the exponent is in the lower half, and the root with
  `A = 1` is kept; the boundary exponent `(p−1)/2` only arises as the second root `−1` of
  `y = 1`, whose canonical root `y^{(p+1)/4} = 1` is kept under either convention, so the strict
  `half_{p−1}(x) := [2x < p−1]` of the formalization is a harmless variant, not a necessity.)
  Difficulty 3 (concrete, deterministic correctness).
  The square root itself is **Thm 58.2** (ch. 2, `p ≡ 3 (mod 4)`; the general case is "an
  exercise" in the text and not in Mathlib as an algorithm). For the *concrete* lemma the root
  may be `Classical.choose`; for the *asymptotic* lemma the inverter must be PPT, so either
  (i) take "modular square roots are PPT-computable" as an explicit hypothesis of the asymptotic
  statement, or (ii) restrict `Gen_DL` to primes `p ≡ 3 (mod 4)` (Thm 58.2 is one modular
  exponentiation, Thm 45.6). Planners must choose; (ii) is recommended (Deviation).
* **Alg-85.a** the randomized majority test replacing line 8: `ℓ` times draw `r_i ← Z_{p−1}`,
  set `z_i = y_{k−1} g^{r_i}`, `b_i ← A(z_i)`, increment `lo` when `(b_i = 0 ∧ r_i < (p−1)/2) ∨ (b_i = 1 ∧ r_i ≥ (p−1)/2)`;
  decide by majority. Concrete analysis: the trials are independent (fresh `r_i`, fresh coins), so
  `uprob_majority_fails_le` (pairwise independence suffices; `pairwiseUniform_eval`) gives failure
  `≤ 1/(4 δ² ℓ)` with `δ = ε/2`, i.e. the text's "Chernoff, `ℓ = (1/ε)²`" becomes an explicit `ℓ`
  with `1/(ε² ℓ) ≤ 1/(4|p|)` so that the union bound over `|p|` rounds leaves failure `≤ 1/4`.
  Difficulty 3.
* **Lem-84.1.3** `Pr[noinc | low(y_{k−1})] ≤ 1/2 − ε/2` for instances whose exponent lies in
  `[0, s]`, `s = εp/4`: conditioned on a fixed instance with exponent `e ≤ s`, the exponent of
  `z_i` is `e + r_i mod (p−1)`, and `half(e + r_i) ≠ half(r_i)` only when `r_i` is within `s` of
  a boundary (`[(p−1)/2 − s, (p−1)/2)` or `[p−1−s, p−1)`), probability `≤ 2s/(p−1) ≤ ε/2`; union
  bound with `A`'s error `1/2 − ε` (per-instance success `≥ 1/2 + ε` — see .5). Needs
  `pushesUniform_add_right` (`r ↦ e + r` is a bijection of `Z_{p−1}`) and `uprob_or_le`.
  Difficulty 3. Text issue: the text's success probability is `1/2 + ε` with "`ε = s(n)`" (should
  be `1/s(n)`), and the arithmetic `1/2 − ε + 2(ε/4)` treats `s` as `εp/4` with two intervals of
  length `s` (total `2s/p = ε/2`) — consistent but sloppy.
* **Lem-84.1.4** range reduction ("as we will show later" — never shown): a solver `B₀` for
  instances with exponent in `[0, s]` yields a solver for all instances: pick `t ← [0, ⌈(p−1)/s⌉)`
  uniformly, run `B₀` on `y · g^{−ts}` and output `x₀ + ts`; the shifted exponent lies in `[0, s]`
  with probability `≥ s/(p−1) − 1/(p−1) ≈ ε/4` (`uprob_eq_one_div_card`-style counting). So the
  DL inverter succeeds with probability `≥ (ε/4)(3/4)` on the good `(p, g)`. Difficulty 3.
* **Lem-84.1.5** (missing in the text) the predictor's success `1/2 + ε` is averaged over
  `(p, g, x)`; the reduction fixes `(p, g)` from its input. Good-set argument over `(p, g)`:
  `half_le_uprob_threshold` gives a set of `(p, g)` of probability `≥ ε/2` on which the success
  over uniform `x` is `≥ 1/2 + ε/2` (rename `ε` accordingly in .3); the final inversion probability
  is `≥ (ε/2) · (ε/8) · (3/4)` up to the constants chosen. Union bound over the `|p|` rounds
  (`uprob_exists_le`). Difficulty 3.
Asymptotic bridge: the inverter makes `|p| · ℓ(n)` calls to `A` with fresh coins
(Machine-Repetition), modular exponentiations (Thm 45.6), square roots (Thm 58.2), majority
(Machine-Primitives), and samples `Z_{p−1}` from coins — exact uniform sampling of `Z_{p−1}` by a
worst-case-time PPT is impossible; sample `|p| + n` bits and reduce mod `p−1` (statistical distance
`≤ 2^{−n}`), recorded as a Deviation (the same device is needed for Asm 105.1 / Alg 106.2). Everything
else is `Negligible` arithmetic. Total difficulty 5; recommend the concrete statement as the core
deliverable and the asymptotic wrapper with (ii) above.

**Thm-87.3** — *Goldreich–Levin.* Let `f` be a OWF (resp. OWP) and `g(x, r) = (f(x), r)` with
`|x| = |r|`. Then `g` is a OWF (resp. OWP) and `h(x, r) = ⟨x, r⟩` is a hard-core predicate for `g`.
**Text error:** the statement says "hard-core predicate for `f`"; it is for `g` (the proof and all
uses are for `g`). Two parts:

* **Thm-87.3.a** `g` one-way: concrete `OneWay.invProb_pad_le : invProb (pad f) A ≤ invProb f (padInverter A)`
  with `pad f (x, y) = (f x, y)` — exactly `g`; `padInverter A v (y, r) = (A (v, y) r).1` draws the
  padding and calls `A` once (Machine-Closure). `g` is a permutation iff `f` is (`Equiv.prodCongr f (Equiv.refl _)`).
  Note `HardcoreBit.glPad f` is the same map on bit strings (`glPad f z = (f z.1, z.2)`); the two
  developments should be glued by `rfl`/`Prod.ext`. Difficulty 2.
* **Thm-87.3.b** `⟨x,r⟩` hard-core for `g`, asymptotic: for every nuPPT `A`, `Negligible (fun n => predProb (glPad (f n)) glBit (A.pred n) − 1/2)`.
  Proof: if not, `not_negligible_iff` gives `c` with `predProb ≥ 1/2 + n^{−c}` for infinitely many
  `n`; set `ε = n^{−c}` and `k(n) = ⌈log₂(2 n^{2c+1} + 1)⌉` (depends only on `n, c`), so that
  `2n ≤ ε² (2^k − 1)`; `invProb_guessInverter` gives `invProb (glPad f) (guessInverter A k) ≥ ε/(4·2^k) ≥ n^{−c}/(16 n^{2c+1} + 8)`
  — inverse polynomial infinitely often, contradicting one-wayness of `g` (87.3.a). Use
  `invProb_guessInverter` (hypothesis `hk` only), **not** `invProb_guessInverter_cubic` (its second
  hypothesis `ε² 2^k ≤ 4n` cannot be guaranteed uniformly when `ε` is unknown to the reduction).
  The inverter `guessInverter A k` makes `n(2^k − 1) = O(n^{2c+2})` calls to `A` with fresh coins,
  draws `k` strings and `k` bits, computes subset XORs, inner products and `n` majorities
  (Machine-Repetition + Machine-Primitives); `k(n)` and `c` are hard-wired (advice or computed from
  `n`). Difficulty 4.
Concrete sub-items all exist (`HardcoreBit/*`): the setting **Thm-87.3.c** (`ip`, `glPad`, `glBit`,
`glInverter`, `secProb`, `predProb_glPad_eq`); the **oversimplified case** Thm-87.3.1
(`invProb_perfectInverter`: `predProb = 1 ⇒ invProb = 1`, queries `e_i`, `ip_single`); the
**less simplified case** Thm-87.3.2 (`invProb_majorityInverter`: `3/4 + ε ≤ predProb`, `n ≤ 2ε²T`
⇒ `ε/4 ≤ invProb`; the text's `m = poly(1/ε)` with Chernoff is `T` with Chebyshev); the good set
Thm-87.3.3 (`half_le_uprob_good`, for both thresholds; the text's displayed inequality chain
`< ε/2 + (1 − ε/2)(3/4 + ε/2) < 3/4 + ε` is this lemma); **Fact-88.4** (`ip_add`, `ip_sum`);
**Alg-88.5** (`majorityInverter`), **Alg-89.6** (`guessInverter` with the "subroutine `C`"
implemented by guessing `b'_1 … b'_{log m}` and forming subset sums); Thm-87.3.6
(`uprob_idealRecover_ne_le`: each bit wrong w.p. `≤ 1/(ε²(2^k − 1))`, then `one_sub_sum_le_uprob_eq`
for the union bound; the text's "`n/(mε'^2) < 1/2` when `m ≥ 2n/ε'^2`" is the hypothesis `hk`);
Thm-87.3.7 (the "show this!": `pairwiseUniform_subsetSum` — note the text takes
`r_1, …, r_{m−1}` as sums over subsets of `log m` strings, i.e. `2^{log m} − 1` *nonempty*
subsets, which matches the formalization exactly; Garg's text included `L = ∅`); Thm-87.3.8
(`uprob_guess_eq`: all `log m` guesses right w.p. `1/m`; `guessRecover_correct_guess`);
Thm-87.3.9 (final bound). **Constants:** in the text's own notation the predictor has success
`1/2 + ε`, the good set uses `ε' = ε/2`, `m = 2n/ε'^2`, and the final bound is
`ε'/(2m) = ε'^3/(4n) = (ε/2)^3/(4n) = ε^3/(32n)`; the concrete layer proves `ε^3/(16n)`
(`invProb_guessInverter_cubic`), which is *stronger*. The plan's seeded note ("`ε^3/(4n)` becomes
`ε^3/(16n)`") compares `ε'` with `ε`; correct it to: PS10 `ε^3/(32n)` ≤ Garg `ε^3/(16n)`.

**Thm-87.3.coll** (unnumbered; required so that "if trapdoor permutations exist" in Thm 104.4 and
"OWP with a hard-core predicate" in ch. 4 Thm 126.4 are meaningful): for a collection `{f_i}`
(OWF/OWP/TDP) with index sampler `Gen`, `g_i(x, r) = (f_i(x), r)` is a collection of the same kind
and `h(x, r) = ⟨x, r⟩` is hard-core for it (Def-78.3.coll). Proof: the concrete GL theorem is per
fixed `f_i`; average over `i`: if the predictor succeeds w.p. `≥ 1/2 + ε` over `(i, x, r)`, then
`half_le_uprob_threshold` gives a set of `i` of probability `≥ ε/2` on which it succeeds w.p.
`≥ 1/2 + ε/2`, and `invProb_guessInverter` applies to each such `f_i` (the inverter receives `i`
as part of its input `(i, f_i(x), r)`); inversion probability `≥ (ε/2) · (ε/2)/(4·2^k)`. Difficulty 3.

### 2.5 §3.5–§3.7 Secure private-key encryption

**Def-91.1** — *Single-message security.* An efficient private-key scheme `(Gen, Enc, Dec)`
(Def 24.7: `Gen(1^n)` PPT, `Enc_k(m)` PPT for `m ∈ {0,1}^n`, `Dec_k(c)` PPT with output in
`{0,1}^n ∪ {⊥}`, `Pr[Dec_k(Enc_k(m)) = m] = 1`) is single-message secure iff for every nuPPT `D`
there is a negligible `ε` with, for all `n` and all `m_0, m_1 ∈ {0,1}^n`,
`distAdv {k ← Gen(1^n) : Enc_k(m_0)} {k ← Gen(1^n) : Enc_k(m_1)} D ≤ ε(n)`. Formal: the scheme is
a structure with `keyLen, ctLen : ℕ → ℕ` (explicit polynomials), `gen n : coins → key`,
`enc n : key → msg → coins → ct`, `dec n : key → ct → Option msg`, PPT fields and correctness;
`SingleMessageSecure S := ∀ D nuPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (encDist S n m₀) (encDist S n m₁) (D.dist n) ≤ ε n`
with `encDist S n m : (keyCoins × encCoins) → ct`. The quantifier order (`ε` before `m_0, m_1`) is
the text's; equivalently `Negligible (fun n => ⨆ m₀ m₁, distAdv …)` over the finite message space.
Deviation: message length is a fixed polynomial of `n` (the text's `n`; Alg 92.1 uses `2n`-bit
messages below). Downstream: ch. 4 Thm 112.2 (zero-knowledge encryption ⇔ security) needs exactly
this definition plus a PPT message sampler.

**Alg-92.1** — `Gen(1^n): k ← U_{n/2}`; `Enc_k(m) = m ⊕ G(k)`; `Dec_k(c) = c ⊕ G(k)` with `G`
length-doubling. Text issue: `n/2` needs `n` even. Formal (Deviation): key length `n`, message and
ciphertext length `2n`, `G : {0,1}^n → {0,1}^{2n}` (or any `ℓ(n)`-bit message with a PRG of
stretch `ℓ`). Enc/Dec are PPT: one evaluation of `G` and a bitwise XOR (Machine-Primitives: XOR of
two equal-length strings given as `pairEncode`). Correctness: `(m ⊕ G k) ⊕ G k = m` (`add_add_cancel`
in the Boolean ring). Difficulty 2.

**Claim-92.a** — *OTP perfect secrecy (used in Thm 92.2 and 99.2).* For every `m : Fin ℓ → Bool`,
the map `u ↦ m + u` is a bijection, so `{u ← U_ℓ : m ⊕ u}` is `U_ℓ`; hence
`acceptProb (fun u => m₀ + u) D = acceptProb (fun u => m₁ + u) D` for every `D`.
Exists as `pushesUniform_xor`/`uprob_comp_equiv (Equiv.addLeft m)`; one-liner. Vector version
(Thm-99.2.3): `(u_j) ↦ (m_j + u_j)` is a bijection of `Fin q → Fin ℓ → Bool`.

**Thm-92.2** — Scheme 92.1 is single-message secure. Concrete: for all `D`, `m_0, m_1`,
`distAdv (Enc(m₀)) (Enc(m₁)) D ≤ prgAdv G (fun z r => D (m₀ + z) r) + prgAdv G (fun z r => D (m₁ + z) r)`.
Proof: hybrids `H¹ = m₀ ⊕ G(U_n)`, `H² = m₀ ⊕ U_{2n}`, `H³ = m₁ ⊕ U_{2n}`, `H⁴ = m₁ ⊕ G(U_n)`;
`|P(H¹) − P(H²)| = prgAdv G (D ∘ (m₀ ⊕ ·))` by `distAdv_comp`; `P(H²) = P(H³)` by Claim-92.a;
`|P(H³) − P(H⁴)|` likewise; triangle inequality (`abs_sub_le_sum_hybrids` with `t = 3` or two
`abs_sub_le`). Bridge: `D ∘ (m_i ⊕ ·)` is nuPPT with `m_i^n` hard-wired as advice (the text's
footnote: "`M_i` is non-uniform as it has the message hard-coded") — Machine-Closure; the message
family `n ↦ (m₀^n, m₁^n)` extracted from the negation of the definition (choice of a witness pair
per `n`: `Classical.choose`, fine). Difficulty 2. Text issues: hybrid labels "`H²_n` (OTP with
`m_1`)" should read `m_0`; "distinguishes two consecutive hybrids with probability `1/4p(n)`" is
`1/(3p(n))` (three gaps).

**Def-93.1** — *Multi-message security.* For every nuPPT `D` and every polynomial `q` there is a
negligible `ε` with, for all `n` and all `m_0, …, m_{q(n)}, m'_0, …, m'_{q(n)} ∈ {0,1}^n`,
`distAdv {k ← Gen : (Enc_k(m_0), …, Enc_k(m_{q(n)}))} {k ← Gen : (Enc_k(m'_0), …)} D ≤ ε(n)`;
the `q(n) + 1` encryptions use one key and independent encryption coins. Formal: sampler
`multiEncDist S n q (m : Fin (q+1) → msg) : keyCoins × (Fin (q+1) → encCoins) → Fin (q+1) → ct`.
Note the count is `q(n) + 1` messages (indices `0 … q(n)`). Difficulty 2.

**Thm-94.2** — A multi-message secure scheme cannot be deterministic and stateless. Precise: if
`Enc` is deterministic (`enc n k m c` does not depend on `c`) and stateless (the model is
stateless anyway), the scheme is correct, `n ≥ 1` and `q(n) ≥ 1`, then the PPT distinguisher
`D((c_0, c_1, …)) = [c_0 = c_1]` has advantage exactly `1` between the encryptions of
`(m_0, m_0, …)` and `(m_0, m_1, …)` with `m_0 ≠ m_1`: in the first `c_0 = c_1`; in the second
`c_0 ≠ c_1` because `Dec_k` is a function and recovers `m_0 ≠ m_1` (correctness with probability
`1`, `forall_of_uprob_eq_one`). Hence Def 93.1 fails (a negligible `ε` is eventually `< 1`).
Difficulty 2 (string equality: Machine-Primitives/`polyTimeComputable_lenEq`-style test).
Text issue: the proof needs correctness to get `c'_0 ≠ c'_1` (not stated) and `m_0 ≠ m_1`.

The discussion after Thm 94.2 (`r ‖ m ⊕ f(r)`, "no PRG produces exponentially many bits",
birthday collisions for `|r| = O(log n)`) is motivation, not claims to formalize.

### 2.6 §3.8–§3.9 Pseudorandom functions and multi-message encryption

**Def-95.a / Claim-95.b** — `RF_n` is the uniform distribution on functions `{0,1}^n → {0,1}^n`
(`randomFunction I O = id` on the seed type `I → O`, `Fintype.card_fun` gives `2^{n 2^n}`). The
"computational description" (answer a new query with a fresh uniform value, repeat recorded
answers) gives the same distribution: `QueryTree.uprob_evalLazy` (lazy sampling with `q` fresh
values equals the uniform table, for trees making `≤ q` queries). Both exist; difficulty 1.

**Def-96.1** — *Oracle indistinguishability.* For ensembles `{O_n}, {O'_n}` of distributions over
functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, `{O_n} ≈ {O'_n}` iff for every nuPPT oracle machine `D`
there is a negligible `ε` with `|Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]| < ε(n)`
for all `n`. Typo: the text writes `{O'_n} ≈ {O'_n}`. D7 reading: an oracle ensemble is a family
of samplers `O n : seeds → (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)` (for `RF_n` the seed *is* the table
— exponentially long, fine at the concrete level; for a keyed family the seed is the key); an
nuPPT oracle adversary is an nuPPT `M` that, on `(1^n, α_n, coins, transcript)`, outputs the next
query or a final bit, with an explicit polynomial query bound `q(n)`; it determines a
`OracleAdversary ρ I O` (a `QueryTree` per coin string) with `BoundedBy (q n)`, and the advantage
is `distAdv (O n) (O' n) (oracleDist A)`. Deviation (D7): no machine-level oracle tape; the
`Turing.OracleTM` of `TuringMachine/Oracle.lean` is a *decision*-oracle model (yes/no answers),
not usable for string-valued oracles without new infrastructure. Difficulty 3 (the unfolding of
the driver machine into a `QueryTree` with the bound is the only real work).
**Claim-96.a** (closure under efficient oracle operations): if `{O_n} ≈ {O'_n}` and `M` is an nuPPT
oracle machine computing a function with oracle access, then `{M^{O_n}} ≈ {M^{O'_n}}` as oracle
ensembles. Concrete: a "query-tree-valued simulation" `QueryTree.bind`: each query `x` of the
outer tree is answered by running an inner tree (`M` on `x`) against the oracle; `eval` and the
query bound multiply. Only the one-query-per-query case exists (`QueryTree.simulate`,
`eval_simulate`, `BoundedBy.simulate`). Optional, difficulty 3.
**Claim-96.b** (hybrid lemma for oracles) is `exists_hybrid_gap` on `acceptProb (O^i) (oracleDist A)`;
exists. **Claim-96.c** (prediction lemma for oracles) is Claim-73.a's identity with the oracle
distinguisher; optional, difficulty 2.

**Def-96.2** — *PRF.* A family `{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` is pseudorandom iff (1)
`f_s(x)` is computable by a PPT given `(s, x)` and (2) `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle
ensembles. Formal: `F n : (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`,
`PolyTimeComputable (bridge of (s, x) ↦ F n s x)`, and `∀ A nuPPT-oracle with bound q, Negligible (fun n => prfAdv (F n) (A n))`
where `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)` (exists, `Defs.lean`).
Difficulty 2. Remark (p. 96, "critical that `s` is not revealed") is not a claim in the model.

**Cor-97.a** (first sentence of the proof of Thm 97.3: "any PRG `g` is sufficient to construct a
PRG `g'` with polynomial expansion … WLOG `g` is length-doubling") — from a PRG `G : n → ℓ(n) > n`
bits: truncation `G₁ = G` restricted to its first `n + 1` bits is a PRG (post-processing by a
projection: `distAdv_comp`), and Lem 80.5 applied to `G₁` with `ℓ' = n` gives output `2n` bits
(`prgExtBits G₁ n : Fin (n + n) → Bool`). Needed so that Thm 97.3 can be stated literally ("if a
PRG exists then PRFs exist"). Difficulty 2 (plus Machine-Loop for computability).

**Constr-97.b** — GGM: `f_s(b_1 … b_n) = g_{b_n}(⋯ g_{b_1}(s) ⋯)` with `g(x) = g_0(x)‖g_1(x)`.
Exists: `ggmBits G : (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool` (`ggm (splitHalves ∘ G)`),
`ggmFrom`, `pairSel`. **Claim-97.c** (clause (1) of Def 96.2 for GGM): `(s, x) ↦ f_s(x)` is
PPT-computable: `n` evaluations of `G` with a selected half — Machine-Loop over the bits of `x`
(`exists_loopTM`-based) plus `splitHalves` on tapes (prefix/suffix extraction). Difficulty 3.

**Thm-97.3** — If a PRG exists then a PRF exists; precisely: if `G : {0,1}^n → {0,1}^{2n}` is a
PRG then `ggmBits G` is a PRF. Concrete (exists): `ggmBits_prfAdv_le : A.BoundedBy q → prfAdv (ggmBits G) A ≤ ∑_{i<n} ∑_{j<q} distAdv G id (ggmBitsDist G A q i j)`
and `exists_ggmBits_dist : 0 < n → 0 < q → ∃ i j, prfAdv (ggmBits G) A / (n q) ≤ distAdv G id (ggmBitsDist G A q i j)`.
Hybrids: **Thm-97.3.1** level hybrids `HF^i` (`hybridOracle G i`: levels `≤ i` random, below
pseudorandom; `hybridProb_zero`: `H_0 = f_s`, `hybridProb_top`: `H_n = RF_n`; the text's indexing
`HF^1 = f_s`, `HF^n = RF_n` has `n − 1` gaps and bound `ε/n`; the formal one has `n` gaps);
**Thm-97.3.2** query sub-hybrids `HHF^j` (`subHybridProb`, `tableDist`, `table_hybrid`,
`hybridProb_level`; Deviation documented in `SubHybrids.lean`: sub-hybrids indexed by *distinct*
prefixes in order of first appearance, the challenge answers every query with that prefix);
**Thm-97.3.3** "queries to `HHF^j` can be emulated in PPT (lazy sampling)": the distinguisher
`ggmBitsDist G A q i j` (cost documented in its docstring: one run of `A`, `≤ n` evaluations of
`G` per query, `q` fresh seeds and `q` fresh pairs as coins, a list of `≤ q` prefixes) must be
exhibited as an nuPPT oracle-free distinguisher: Oracle-D7 (driving `A`'s query tree inside the
reduction), Machine-Loop (`G` iterations), Machine-Closure (advice `i, j`), lazy-sampling list
maintenance (`noteQuery`) — difficulty 4. Then `Negligible.mul_pow` for the factor `n q(n)`.
Bridge total difficulty 4.

**Alg-99.1** — `Gen(1^n): k ← U_n`; `Enc_k(m): r ← U_n, output (r, m ⊕ f_k(r))`; `Dec_k(r, c) = c ⊕ f_k(r)`
for a PRF `{f_k}` and `m ∈ {0,1}^n`. Ciphertext length `2n`; Enc PPT (Claim-97.c + XOR). Difficulty 2.

**Thm-99.2** — Scheme 99.1 is multi-message secure. Concrete statement (new): for every `D` and
message vectors `m, m' : Fin (q+1) → Fin n → Bool`,
`distAdv (multiEnc m) (multiEnc m') D ≤ prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) · 2^{−n}`
where **Thm-99.2.1** `A_m D : OracleAdversary` draws `r_0 … r_q`, queries the oracle at each `r_j`
(a chain of `q + 1` `query` nodes, `BoundedBy (q+1)`), and runs `D` on `((r_j, m_j ⊕ F(r_j)))_j`
— `H¹ → H²` is `prfAdv F (A_m D)` by definition of `oracleDist` (and `acceptProb` unfolding);
**Thm-99.2.2** `|P(H²) − P(H³)| ≤ C(q+1,2) 2^{−n}`: `H²` uses a uniform table `R` at the points
`r_j`, `H³` uses fresh uniform pads `p_j`; on the event `Inj := ∀ i ≠ j, r_i ≠ r_j` the tuple
`(R(r_j))_j` is uniform (evaluation of a uniform table at distinct points pushes uniform to
uniform: a generalization of `pushesUniform_eval_pair` to injective index tuples, provable via
`Equiv.funSplitAt`/`uprob_update_absorb` by induction, or by `uprob_pi_forall` counting), so the two
hybrids agree conditioned on `Inj`; `Pr[¬Inj] ≤ ∑_{i<j} Pr[r_i = r_j] = C(q+1,2) 2^{−n}`
(`uprob_exists_le`, `uprob_eq_one_div_card`); a coupling lemma "two experiments that agree on an
event `E` have advantage `≤ Pr[¬E]`" (new, generic, difficulty 2; `distAdv_le_statDist` is an
alternative route via `FinDist`); **Thm-99.2.3** `P(H³) = P(H⁴)` by the vector OTP (Claim-92.a);
`H⁴ → H⁵ → H⁶` symmetric. Difficulty 4 (new 300–400-line concrete file). Bridge: `A_m D` is an
nuPPT oracle adversary with `q(n) + 1` queries and the messages as advice (Oracle-D7,
Machine-Closure); `Negligible` arithmetic with `C(q(n)+1, 2) 2^{−n}` (`negligible_two_pow_neg`,
`Negligible.mul_pow`). Text issue: the collision bound is written `C(q(n), 2) 2^{−n}` for
`q(n) + 1` values; should be `C(q(n)+1, 2)`.

### 2.7 §3.10–§3.12 Public-key encryption, DDH, El Gamal, closing remarks

**Def-102.1** — *PKE scheme.* `(Gen, Enc, Dec)` with (1) `(pk, sk) ← Gen(1^n)` PPT; (2)
`c ← Enc_pk(m)` PPT for `m ∈ {0,1}^n`; (3) `Dec_sk(c)` deterministic with output in `{0,1}^n ∪ {⊥}`;
(4) a polynomial-time `M` with `M(1^n, i)` = the `i`-th `n`-bit message in some order (if it
exists); (5) `Pr[(pk,sk) ← Gen(1^n) : Dec_sk(Enc_pk(m)) = m] = 1` for all `n`, `m`. Formal: structure
with explicit polynomial lengths for `pk, sk, ct`, PPT fields, `dec` a plain function (PolyTime),
correctness, and a `PolyTimeComputable` message enumerator (clause (4) is odd — for `{0,1}^n`
messages the `i`-th message is the binary expansion of `i`; keep it as a field so that ch. 4
Thm 112.2's analogue for PKE can use it, or drop it with a Deviation note; the plan's seeded issue
list already flags Thm 112.2's sampler). Difficulty 2.

**Def-102.2** — *Secure PKE.* For every nuPPT `D` there is a negligible `ε` with, for all `n` and
`m_0, m_1 ∈ {0,1}^n`, `distAdv {(pk,sk) ← Gen : (pk, Enc_pk(m_0))} {… (pk, Enc_pk(m_1))} D ≤ ε(n)`
(the public key is part of the distinguisher's input). Difficulty 2.

**Claim-103.a** — perfect secrecy is impossible for PKE: for a correct scheme and `m_0 ≠ m_1`, the
supports of `Enc_pk(m_0)` and `Enc_pk(m_1)` are disjoint for each `(pk, sk)` (a common ciphertext
would decrypt to both), so `statDist ((pk, Enc_pk(m_0))) ((pk, Enc_pk(m_1))) = 1` and the
(unbounded) test "is `c` in the support of `Enc_pk(m_0)`" has advantage `1`. Optional, difficulty 2.
**Claim-103.b** — deterministic PKE is insecure: if `Enc_pk(m)` ignores its coins, the nuPPT
`D(pk, c) = [c = Enc_pk(m_0)]` has advantage `1` (needs `Enc` PPT so that `D` is efficient, and
correctness for `Enc_pk(m_0) ≠ Enc_pk(m_1)`). Optional, difficulty 2. **Constr-104.a**
(`Enc_i(m) = f_i(m)`, "the RSA cryptosystem", p. 104) is an instance.

**Def-103.c** (unnumbered) — multi-message PKE security: as Def 93.1 with `(pk, Enc_pk(m_0), …, Enc_pk(m_{q(n)}))`,
fresh coins per encryption, one key pair. **Thm-103.d** (exercise, p. 103) — for PKE,
single-message security implies multi-message security. Concrete: for every `D`, `q`, `m, m'`:
`distAdv (multiEnc m) (multiEnc m') D ≤ ∑_{j ≤ q} distAdv (singleEnc m_j) (singleEnc m'_j) (D_j)`
where `D_j(pk, c)` encrypts `m'_0 … m'_{j−1}` and `m_{j+1} … m_q` itself under `pk` (fresh coins),
places `c` at position `j` and runs `D` — the key point being that encryption needs only `pk`
(impossible for private-key schemes). This is `exists_multicopyRed_ge`'s hybrid with a shared
`pk` and position-dependent samplers; reuse the proof pattern (`multicopyHybrid`, planting via
`acceptProb_update`), not the lemma itself (it assumes identical copies and no shared parameter).
Bridge: `D_j` is nuPPT (runs `Enc` `q` times: Machine-Repetition; advice `j`, messages). Difficulty 3.
Downstream: ch. 4 Def 126.3/Thm 126.4 "multi-value hiding follows by a simple hybrid argument
(show this!)" is the same lemma with `Com(v, r)` in place of `Enc_pk`; design the concrete lemma
generically (a family of samplers `X_j(pk; m)` with `pk` sampled once) so both uses share it.

**Def-103.e** (unnumbered) — single-bit secure PKE: Def 102.2 with message space `{0,1}`
(`m_0 = 0`, `m_1 = 1` only). **Thm-103.f** (stated, p. 103) — encrypting an `n`-bit message bit by
bit under a single-bit secure PKE gives a secure PKE for `{0,1}^n` (and the resulting scheme meets
Def 102.1 with `Dec` returning `⊥` if any bit decrypts to `⊥`). Proof: Thm-103.d for the
single-bit scheme with `q = n − 1` gives `distAdv ≤ ∑_{i<n} (single-bit advantage of D_i) ≤ n · ε(n)`;
`Negligible.mul_pow`. Difficulty 3 (mostly bookkeeping of the bitwise scheme as a PKE).

**Alg-104.3** — 1-bit PKE from a TDP collection with hard-core bits: `Gen(1^n): (f_i, f_i^{−1}) ← Gen_T(1^n)`,
`pk = (f_i, b_i)` (the index `i`), `sk = f_i^{−1}` (the trapdoor `t`); `Enc_pk(m): r ← {0,1}^n, (f_i(r), b_i(r) ⊕ m)`;
`Dec_sk(c_1, c_2) = b_i(f_i^{−1}(c_1)) ⊕ c_2`. Correctness is `f_i^{−1}(f_i(r)) = r`. Domain
Deviation: the text samples `r ← {0,1}^n` while Def 56.1 has domains `D_i` with a sampler; take
`D_i = {0,1}^n` or sample `r ← D_i` with the collection's sampler (the proof is the same). The
hard-core bits `b_i` come from Thm-87.3.coll applied to the TDP (`g_i(x, r) = (f_i(x), r)`, which
is again a TDP). Difficulty 2.

**Lem-104.a** (the concrete content of the proof of Thm 104.4; also the hiding proof of ch. 4
Thm 126.4) — for a family of permutations `f_i` with bits `b_i` and an index sampler, and any
distinguisher `D` of `X⁰ = (i, f_i(r), b_i(r))` versus `X¹ = (i, f_i(r), ¬b_i(r))` (these are the
encryptions of `0` and `1`), the predictor `A'(i, y)`: draw `c ← {0,1}`, `m ← D(i, (y, c))`, output
`c ⊕ m` (negated if `flip`), satisfies, for one `flip`,
`predProb (fun (i, r) => (i, f_i r)) (fun (i, r) => b_i r) (A' flip) = 1/2 + distAdv X⁰ X¹ D / 2`.
This is `predProb_owpPredictor_false/true`, `acceptProb_id_owp`, `exists_owpPredictor` with an
index carried along (`owpGen f B` has a fixed `f : α ≃ α`; the indexed version replaces `α` by
`Σ i, D_i` or threads `i` through `β`). The text's proof first applies the prediction lemma to the
ciphertext distinguisher and then converts the predictor `A` of `m` into a predictor of `b`: the
composite is exactly `owpPredictor`. Difficulty 3.

**Thm-104.4** — If trapdoor permutations exist then scheme 104.3 is a secure single-bit PKE.
Precise: for a TDP collection with a hard-core bit family (Thm-87.3.coll supplies one), scheme
104.3 satisfies Def-103.e. Proof: Lem-104.a + `not_negligible_iff`; bridge: `A'` is nuPPT (one
coin, one call, advice bit). Text issues: the hypothesis omits the hard-core bit (needs 87.3 for
collections); "By the prediction lemma, there exist a machine `A` such that
`Pr[… D(pk, Enc_pk(m)) = m]`" writes `D` for `A`. Difficulty 3.

**Asm-105.1** — *DDH.* `{p ← Π̃_n; y ← Gen_q; a, b ← Z_q : (p, y, y^a, y^b, y^{ab})} ≈ {…; a, b, z ← Z_q : (p, y, y^a, y^b, y^z)}`,
where `Π̃_n = {p ∈ Π_n : p = 2q + 1, q ∈ Π_{n−1}}` (safe primes), `Gen_q` = generators of the
order-`q` subgroup `G_q ⊆ Z_p^*` (every element `≠ 1` of `G_q`). Formalization issues: (i) no
PPT is known to sample safe primes (the text says so in §2.8), and exact uniform sampling of
`Z_q` by a worst-case-time PPT is impossible — so the assumption should be stated **relative to a
group-instance generator** `GenG : PPT` outputting `(p, q, y)` with `p = 2q + 1` prime and `y` a
generator of `G_q`, and with exponents sampled as `(|q| + n)`-bit numbers reduced mod `q`
(statistical distance `≤ 2^{−n}` from uniform), as Deviations; alternatively state the assumption
with the uniform (non-efficient) samplers at the concrete level and only require efficiency of the
reduction (which is all Thm 107.3 uses) — but then Alg 106.2's `Gen` is not PPT, violating
Def 102.1(1). Recommended: `GenG` abstraction (standard), `DDH GenG := CompIndist (ddhReal GenG) (ddhRandom GenG)`.
(ii) The tuple is encoded as a bit string (`pairEncode` chain) — D6. Difficulty 2 given NT-105.a.

**NT-105.a** — for `p = 2q + 1` with `p, q` prime (`q` odd): `Z_p^* ≅ (ZMod p)ˣ` is cyclic of order
`2q` (Mathlib instance `IsCyclic Rˣ` for finite integral domains, `ZMod.card_units_eq_totient`,
`Nat.totient_prime`); the squares form a subgroup of order `q` (image of `x ↦ x^2`, kernel `{±1}`,
`Subgroup.card_eq_card_quotient_mul_card_subgroup`), which is the unique subgroup of order `q`
(`IsCyclic.card_pow_eq_one_le`); it is cyclic of prime order so every element `≠ 1` generates
(`orderOf_eq_prime`/`orderOf_dvd_card`); `x ∈ G_q ↔ x^q = 1 ↔ IsSquare x` (`ZMod.euler_criterion`).
Difficulty 3 (Mathlib glue; nothing exists in TCSlib; `SchnorrProtocol.lean` works in an abstract
group `G` with `ZMod q` exponents and may be a model for the El Gamal file).

**Claim-106.a** — DDH ⇒ DL (p. 106): if DL in `G_q` is solvable w.p. `δ` (non-negligible), the
distinguisher that computes `a` from `y^a` and tests `(y^b)^a = z` has advantage `≥ δ(1 − 1/q)`
(on a DDH tuple it accepts whenever the DL succeeds; on a random tuple it accepts only if the DL
succeeds *and* `z = y^{ab}`, probability `δ/q`). Optional, difficulty 3 (needs the DL assumption in
`G_q`, Asm 52.2's actual form).
**Claim-106.b** — in a non-prime-order group such as `Z_p^*` the DDH assumption is false (element
orders `2, q, 2q`, i.e. the Legendre symbol, distinguish `y^{ab}` from `y^z`). Optional, difficulty 3
(Mathlib `legendreSym`, `quadraticChar`); the Garg plan deferred the same attack.

**Alg-106.2** — El Gamal: `Gen(1^n)`: safe prime `p = 2q + 1` of length `n`; random `g ∈ Z_p`,
`h = g^2 mod p`; `a ← Z_q`; `pk = (p, h, h^a)`, `sk = (p, h, a)`. `Enc_pk(m)`: `b ← Z_q`,
`(h^b, h^{ab} · m)`. `Dec_sk(c_1, c_2) = c_2 / c_1^a`. Correctness: `h^{ab} m / (h^b)^a = m` for
`m ∈ Z_p^*` (`c_1 ≠ 0`). Text issues: `g` "random in `Z_p`" may be `0` or `±1`, giving `h ∈ {0, 1}`
(then `pk` is degenerate; probability `3/p`); `Gen` should draw `g ∈ Z_p^* ∖ {±1}` or resample;
`q` is omitted from `pk` (recoverable as `(p−1)/2`). **Message space (text error, see Thm 107.3):**
`m` must lie in `G_q`. Formal: `Gen = GenG` plus `a`; `pk = (p, q, h, h^a)`. Modular exponentiation
is Thm 45.6; sampling as in Asm-105.1. Difficulty 2.

**Claim-107.a** (missing in the text) — for uniform `g ∈ Z_p^*`, `h = g^2` is uniform on `G_q`
(`x ↦ x^2` is a surjective homomorphism `Z_p^* → G_q` with fibres of size `2`:
`pushesUniform_of_surjective`); `h` is a generator of `G_q` unless `h = 1` (probability `1/q`), so
the distribution of `h` is within statistical distance `1/q ≤ 2^{−(n−2)}` of the uniform generator
`y ← Gen_q` used in Asm 105.1 (`statDist`, `distAdv_le_statDist`); this term is negligible and
must be added to the bound in Thm 107.3. Difficulty 2.

**Thm-107.3** — If DDH holds then El Gamal is secure. Precise (with message space `G_q`): for every
nuPPT `D` there is a negligible `ε` with, for all `n` and `m_0, m_1 ∈ G_q`,
`distAdv {(pk, Enc_pk(m_0))} {(pk, Enc_pk(m_1))} D ≤ ε(n)`. Concrete: with `T_real = (p, h, h^a, h^b, h^{ab})`
and `T_rand = (p, h, h^a, h^b, h^z)`,
`distAdv (Enc(m₀)) (Enc(m₁)) D ≤ ddhAdv (D ∘ mult m₀) + ddhAdv (D ∘ mult m₁) + 2/q`
where `mult m (p, h, A, B, Z) = ((p, h, A), (B, Z · m))` (`distAdv_comp`), the middle hybrids
`(pk, h^b, h^z m_0)` and `(pk, h^b, h^z m_1)` coincide because `z ↦ h^z m` is a bijection of `G_q`
for `m ∈ G_q` (`Equiv.mulLeft`, `acceptProb_comp_equiv`), and `2/q` accounts for Claim-107.a
(generator vs square sampling). **Text error:** with `m ∈ Z_p^*` arbitrary (as the scheme is
written), `h^z · m` ranges over the coset `m G_q`, so encryptions of a quadratic residue and a
non-residue are distinguishable by the Legendre symbol of `c_2` (Claim-106.b); the "exercise" is
false as stated and true for `m ∈ G_q` (or with **Def-107.b**: encode `m ∈ [1, q]` as `m` if
`IsSquare m` else `p − m` — exactly one is a square since `−1` is a non-residue for `p ≡ 3 (4)`,
`ZMod.exists_sq_eq_neg_one_iff`, and `p = 2q + 1` with `q` odd is `≡ 3 (4)`; decoding compares
with `q`; this meets Def 102.1's bit-string message space up to length bookkeeping — optional,
difficulty 3). Bridge: `D ∘ mult m_i` is nuPPT with `m_i` as advice and one modular
multiplication (Thm 45.6-level arithmetic; Machine-Closure). Difficulty 3.

**Claim-107.c** (§3.12, "one-way functions are a minimal assumption, because the existence of any
of these primitives implies the existence of one-way functions") — the PRG case is formalizable:
a PRG `G` with stretch `ℓ(n) ≥ n + 1` is a OWF: an inverter `B` with `invProb G B = δ` gives the
distinguisher `D(t) = [G(B(t)) = t]`, accepting `G(U_n)` w.p. `δ` and `U_ℓ` w.p. `≤ 2^{n−ℓ} ≤ 1/2`
(only image points can be accepted), so `prgAdv ≥ δ − 1/2` — this needs `δ > 1/2`; the standard
proof first amplifies or uses `ℓ ≥ 2n` (then `2^{−n}`) — for a general PRG compose with Lem 80.5
first. Optional, difficulty 3. The PRF/encryption ⇒ OWF cases and **Claim-107.d** (Impagliazzo–Rudich,
no black-box PKE from OWF) are deferred (the latter is not formalizable in this framework).

### 2.8 Appendix facts cited by chapter-3 proofs

**Thm-188.7** (Chernoff, `Pr[|∑X_i − μn| ≥ ε] ≤ 2^{−ε²n}`), **Lem-189.8** (majority vote; the
statement is garbled, "`> 1 − 2??`", proof unfinished "we have that …") and the unnumbered
**pairwise-independent sampling inequality** (`Pr[|∑X_i/n − μ| ≥ ε] ≤ (1 − μ²)/(nε²)`, "a corollary of
Chebyshev") are used in Lem 84.1 (majority test), Thm 87.3 (both cases) and the remark after
Def 24.6. The concrete layer replaces all of them by Chebyshev for pairwise independent bits:
`chebyshev_pairwise`, `chebyshev_pairwise_ident` (`Pr[|∑X_i − pm| ≥ δm] ≤ 1/(4δ²m)`) and
`uprob_majority_fails_le` (majority of `m` pairwise independent trials each right w.p. `≥ 1/2 + δ`
fails w.p. `≤ 1/(4δ²m)`), which give polynomially many trials instead of `O(ε^{−2} log)` — enough
for every asymptotic statement. Chernoff (not in Mathlib in this form; Mathlib has
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` for measures) is optional, difficulty 3, and only
worth doing if an exponentially small failure probability is ever needed (ch. 4's GI simulator
truncation uses `(1/2)^n`, not Chernoff).

## 3. Errors and gaps in the source text (chapter 3)

Outright errors (`text_errors`):

1. **Theorem 87.3** states that `⟨x, r⟩` is a hard-core predicate "for `f`"; it is for
   `g(x, r) = (f(x), r)` (the proof and every use are for `g`).
2. **Lemma 84.1 vs Assumption 52.2**: the DL assumption is stated for prime-order groups `G_q`,
   while Lemma 84.1, Algorithm 84.2 and the proof use the full group `Z_p^*` of even order
   (`g^{(p−1)/2} = −1`, parity of the exponent via quadratic residuosity). The lemma needs DL in
   `Z_p^*` for a uniform generator (Theorem 52.3's collection, itself garbled: index `(q, g)`,
   domain `Z_q`, range `G_p`). Also `x ← Z_p` should be `x ← Z_{p−1}`, and "`ε = s(n)`" should be
   `ε = 1/s(n)`.
3. **Theorem 107.3 / Algorithm 106.2**: El Gamal is written for arbitrary `m ∈ Z_p` while DDH is
   over the order-`q` subgroup `G_q`; for messages in different cosets of `G_q` (a residue and a
   non-residue) the ciphertext's second component reveals the coset (Legendre symbol), so the
   scheme is not secure as stated. Correct with message space `G_q` (or an encoding into `G_q`).
   Also `Gen` draws `g ∈ Z_p` (may be `0, ±1`, giving a degenerate `h`).
4. **Definition 75.2** quantifies `i ∈ [0, …, ℓ(n)]` and predicts `t_{i+1}`, which does not exist
   for `i = ℓ(n)`; intended `0 ≤ i < ℓ(n)`.
5. **Definition 78.3** mixes `k` and `n` (`x ← {0,1}^k`, `A(1^n, ·)`, `ε(n)`, `∀ k`); intended `k = n`.
6. **Definition 96.1** has the typo `{O'_n} ≈ {O'_n}`.
7. **Theorem 104.4** omits the hard-core bit from its hypothesis ("if trapdoor permutations
   exist") — it needs Theorem 87.3 for collections; its proof writes `D` where `A` (the
   predictor from the prediction lemma) is meant.
8. **Algorithm 76.5** draws "`ℓ(n) − i` random bits `← U_{ℓ(n)−1}`" (should be `U_{ℓ(n)−i}`); the
   proof of Theorem 75.4 defines `H̃^i` with `x̄_i` and a stray `u_{l(m)}` but uses `H̃^{i+1}`,
   mixes 0- and 1-indexed bits, and its last display has `A(t) = 1` for `A(t) = b`.
9. **Lemma 80.5's proof**: `m(n)` and `ℓ(n)` are used interchangeably; the hybrids "for
   `i = 1, …, m(n)`" must start at `0`; the reduction `M(y)` reads `y` as bit-then-seed while the
   construction writes `X_{i+1}‖b_{i+1}` (seed-then-bit).
10. **Theorem 99.2's proof**: the collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`
    (`q(n) + 1` values `r_0 … r_{q(n)}`).
11. **Algorithm 84.2 / p. 86**: the analysis bounds `Pr[noinc | low(y_{k−1})]` by `1/2 − ε/2`,
    but with the increment rule as printed (`lo` counts disagreements `b_i ≠ half(r_i)`) this is
    the complementary event; the majority test itself and line 11's root selection ("IF `b = 0`
    THEN `y_{k−1} ← −y_{k−1}`": keep the root iff `A` answers `1` = lower half) are consistent
    with `half`'s convention. (Run-3 audit P8-3 corrects the run-1 reading, which called line 11
    inverted and a strict `half` necessary; the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant — the boundary exponent `(p−1)/2` only arises as the
    second root `−1` of `y = 1`, whose canonical root is `1`.)
12. **Theorem 92.2's proof**: hybrid `H²_n` is labelled "OTP with `m_1`" but is `m_0 ⊕ r`; with
    four hybrids the gap is `1/(3p(n))`, not `1/(4p(n))` (harmless).

Gaps the formalization must fill (not errors): the range reduction "as we will show later" in
Lemma 84.1 (never shown); the good-instance averaging over `(p, g)` in Lemma 84.1; the square-root
algorithm for `p ≡ 1 (mod 4)` ("exercise", not in Mathlib); the PKE single ⇒ multi message
theorem and the bitwise single-bit ⇒ full-message theorem (p. 103, "exercise"/"follows directly");
Theorem 107.3 ("exercise") including the generator-vs-square sampling term `1/q`; Lemma 189.8's
garbled statement; Corollary 81.7's extra bit; Lemma 71.6's `ε/m` where the proof gives `ε/(m−1)`.

## 4. Guidance for the planners

### 4.1 What the machine layer must provide for chapter 3 (ordered by how many items need it)

1. `Machine-NUPPT` + `Machine-Closure` (post-composition with a PPT, hard-wired per-`n` constants
   as advice, extra coins, pairing of inputs): every asymptotic item.
2. `Machine-Primitives`: XOR of two equal-length strings (Alg 92.1, 99.1, 104.3, GL), string
   equality (Thm 94.2, Claim 103.b), inner product mod 2 and majority (GL inverter, DL majority
   test), prefix/suffix/`cons`/`append` on tapes (next-bit predictor, `prgExtBits`, `splitHalves`).
3. `Machine-Loop`: iterate a PPT map `poly(n)` times (Lem 80.5's `G'`, Cor 81.7's `G`, GGM
   evaluation, the reductions of Lem 80.5 and Thm 97.3).
4. `Machine-Repetition`: polynomially many calls with fresh coins + aggregation (GL inverter
   `n(2^k − 1)` calls, DL inverter `|p| ℓ(n)` calls, PKE single ⇒ multi reduction `q(n)` encryptions,
   Thm 99.2's oracle adversary).
5. `Oracle-D7`: nuPPT-driven query trees with an explicit query bound; a reduction that *hosts* an
   oracle adversary and answers its queries itself (GGM distinguisher, Thm 99.2) — this is where
   the design panel's decision matters most for chapter 3.
6. Number-theoretic PPT algorithms from chapter 2: modular exponentiation (Thm 45.6), square
   roots mod `p ≡ 3 (4)` (Thm 58.2), a group-instance generator for safe primes (abstracted), and
   near-uniform sampling of `Z_q` from coins (statistical error `2^{−n}`, Deviation).

### 4.2 Risk ranking (chapter 3)

| Item | Risk | Mitigation |
| --- | --- | --- |
| Lem-84.1 (DL hard-core bit) | highest: four proof gaps, square-root algorithm, `Z_p^*` vs prime-order mismatch, `~500` lines | concrete statement with `p ≡ 3 (4)` and `Classical.choose` roots as core; asymptotic wrapper with the sqrt restriction; keep in its own file; accept a sorry under a full sketch if the fill stalls |
| Thm-99.2 (multi-message) | high: new concrete proof with a coupling/collision argument | prove a generic "agree on an event `E` ⇒ advantage `≤ Pr[¬E]`" lemma and "uniform table at distinct points is uniform" first |
| Thm-97.3 bridge (GGM distinguisher as nuPPT) | high: depends on Oracle-D7 and Loop | state the asymptotic theorem with the concrete `exists_ggmBits_dist` and a single admitted closure lemma "`ggmBitsDist` is nuPPT" if needed |
| Thm-75.4.c (next-bit reduction) | medium: new 250-line concrete file but all tools exist | copy the structure of `Generators.lean` (`prgHybrid`, `acceptProb_prgExtRed_right`) |
| Thm-87.3.b bridge (GL inverter as nuPPT) | medium: `n 2^k` calls, subset XOR table | Machine-Repetition with a `Fin n × NESubset k` index; `k(n) = ⌈log₂(2n^{2c+1}+1)⌉` |
| Thm-107.3 / Asm-105.1 | medium: number theory glue + sampling deviations | `GenG` abstraction; message space `G_q` |

### 4.3 Items of chapter 3 that chapter 4 consumes

Def 91.1 and Def 24.7 (Thm 112.2: security ⇔ zero-knowledge, needs a PPT message sampler);
Def 102.1/102.2 (ZK for PKE, remark only); Lem 71.6 (every ch. 4 hybrid proof); Lem 71.5
(Thm 128.8's closure step); Thm 79.4's `f, h` and Lem-104.a (Thm 126.4: `Com(b, r) = (f(r), b ⊕ h(r))`,
"hiding follows using identically the same proof as Theorem 104.4"); Thm-103.d's generic
shared-parameter hybrid (Def 126.3's multi-value hiding, "show this!"); Thm-87.3 for a single OWP
(so that "OWP with a hard-core predicate" in Thm 126.4 is available from "OWP exists").

### 4.4 Statement-shape recommendations

* Keep every concrete lemma free of machines (exact inequalities on `distAdv`/`predProb`/`invProb`
  for arbitrary function adversaries), in the style of the Garg layer; put *all* machine content in
  the asymptotic wrappers, each of which has the fixed three-step shape (instantiate, closure,
  negligible arithmetic).
* Prefer the *advice* route for per-`n` choices (`i`, `flip`, `m_n`, `k(n)`); the averaged
  uniform reductions (`mixDist`, `prgExtAvgRed`, `multicopyAvgRed`, `distAdv_multicopyAvgRed`)
  are available when a uniform reduction is wanted, but the text's proofs are non-uniform.
* State security definitions positively with `Negligible` and prove theorems by contraposition
  through `not_negligible_iff`; never quantify over abstract polynomials (use `n^c`, `Negligible.mul_pow`).
* Lengths: every ensemble/scheme carries explicit `C (n+1)^c` length formulas (plan convention);
  the PRG stretch `ℓ` must satisfy `n < ℓ n`; GGM and Alg 99.1 use `2n`; Alg 92.1 uses key `n`,
  message `2n` (Deviation from `n/2`).

### 4.5 Alignment with the parallel run-1 documents (checked 2026-10-27 22:00)

* `inventory-ch2.md` uses the ids `Def-24.7`, `Def-27.3`, `Def-41.1`, `Asm-52.2`, `Thm-52.3`,
  `Def-55.1`, `Def-56.1`, `Thm-58.2`, `Thm-45.6`, `Rem-52.2` (safe primes / squares subgroup),
  `Thm-188.7`, `Lem-189.8` — the labels used above refer to those items. Its `Asm-52.2` is
  already "relative to a group family" (`DLGroupFamily`, sampler `GenDL`), which is the shape
  Lem-84.1 needs **except** that Lem-84.1 works in `Z_p^*` (even order); the DL hard-core file
  must instantiate the family with `G = (ZMod p)ˣ`, `|G| = p − 1` (not prime) — coordinate with
  the ch. 2 owner (the family structure should not force prime order). The `OWP-single` label is
  ch. 2's `FunFamily` (design doc §3.1) with a bijectivity field.
* `design-faithful-tapes.md` names the machine layer `Poly` (`C (n+1)^c`), `PPT` (`runWith`,
  `sampleAt`, `sample`, `Computes`, `Coins`), `NUPPT` (advice form; `NUPPTSeq` verbatim form with
  an equivalence theorem), `ones n = 1^n`, `decodeBits n : List Bool → Option (Fin n → Bool)`,
  `FunFamily`, `StrongOneWay`/`WeakOneWay` over `NUPPT` with `Negligible (invSucc F A)`. The
  chapter-3 definitions should follow the same pattern: `CompIndist X Y := ∀ A : NUPPT, Negligible (distAdvAt X Y A)`,
  with `distAdvAt` built from `A.sampleAt`, `decodeBits`, and `distAdv`.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/i/replay.log =====

# closure of pack 03i's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 339 modules, extracted from g03-replay.log
TCSlib/Complexity/CircuitComplexity/Advice rc=0 10s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Basic rc=0 20s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEval rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect rc=0 10s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine rc=0 22s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalRun rc=0 18s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalSpec rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuit rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSat rc=0 10s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGFanin rc=0 10s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGTransform rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/HardWire rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredCircuit rc=0 9s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredDAG rc=0 12s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredPPoly rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PPoly rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PSubsetPPoly rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PairEncode rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/SizeClasses rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/TreeDAG rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UHalt rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UHaltMachine rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UnaryCode rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UnaryLanguages rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Uniform rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Universal rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CoNP rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CounterProgPolyTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/EXP rc=0 40s errors=0 sorry=0
TCSlib/Complexity/ClassNP/ExpPoly rc=0 6s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NTIME rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Nondeterminism rc=0 43s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 8s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Reductions rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT rc=0 70s errors=0 sorry=0
TCSlib/Complexity/ClassNP/TMSAT rc=0 19s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Transducer rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith rc=0 6s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/AddSub rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Basic rc=0 6s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/DetMod rc=0 2539s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/DetModMath rc=0 6s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Div rc=0 7s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Iterate rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Jacobi rc=0 39s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Loops rc=0 12s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/ModPow rc=0 7s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Mul rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/PrimeFind rc=0 9s errors=0 sorry=0
TCSlib/Complexity/ClassP/BinaryArith/Words rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 6s errors=0 sorry=2
TCSlib/Complexity/CookLevin/Hardness rc=0 565s errors=0 sorry=0
TCSlib/Complexity/CookLevin/Snapshot rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Formulas/CNF rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Formulas/CNFEncoding rc=0 4s errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Collapse rc=0 4s errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Defs rc=0 4s errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Levels rc=0 6s errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Normalize rc=0 5s errors=0 sorry=0
TCSlib/Complexity/PolyHierarchy/Padding rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/Adleman rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/AlgCircuit rc=0 14s errors=0 sorry=0
TCSlib/Complexity/Randomized/AlgCircuitExample rc=0 7s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInP rc=0 14s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInPCount rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPLInPWords rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPEqP rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPHard rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting rc=0 38s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 11s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Classes rc=0 30s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Coins rc=0 16s errors=0 sorry=0
TCSlib/Complexity/Randomized/DirectedWalk rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/ErrorReduction rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/ExpectedTime rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/Fingerprint rc=0 15s errors=0 sorry=0
TCSlib/Complexity/Randomized/Inclusions rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching rc=0 20s errors=0 sorry=0
TCSlib/Complexity/Randomized/MatchingMath rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Median rc=0 21s errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly rc=0 15s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 3s errors=0 sorry=1
TCSlib/Complexity/Randomized/PPT rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTM rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyTimeModel rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality rc=0 11s errors=0 sorry=0
TCSlib/Complexity/Randomized/PrimalityMath rc=0 15s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/QuasiPolyHierarchy rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected rc=0 7s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomBits rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalk rc=0 7s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalkCover rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalkHitting rc=0 17s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalkMixing rc=0 18s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalkMixingPad rc=0 18s errors=0 sorry=0
TCSlib/Complexity/Randomized/RandomWalkPad rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/SchwartzZippel rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/SipserGacs rc=0 15s errors=0 sorry=0
TCSlib/Complexity/Randomized/Space rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplify rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPoly rc=0 32s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine rc=0 43s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun rc=0 12s errors=0 sorry=0
TCSlib/Complexity/Randomized/SpaceAmplifyRun rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPath rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathLoops rc=0 20s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathMachine rc=0 56s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathParse rc=0 26s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathRL rc=0 22s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathSearch rc=0 17s errors=0 sorry=0
TCSlib/Complexity/Randomized/UPathWalk rc=0 42s errors=0 sorry=0
TCSlib/Complexity/Randomized/UniformSample rc=0 22s errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap rc=0 15s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts rc=0 7s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses rc=0 77s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPEval rc=0 14s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT rc=0 7s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPRun rc=0 43s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Basic rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Bridge rc=0 4s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Checks rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Deciders rc=0 20s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Engine rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Langs rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Layout rc=0 37s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Layout2 rc=0 35s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Machine rc=0 191s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Parse rc=0 20s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Regs rc=0 22s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Run rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Scan rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Step rc=0 9s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/StepDecider rc=0 29s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Valid rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Codec/Word rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ConfigCount rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ConfigGraph rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Constructible rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine rc=0 29s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main rc=0 56s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax rc=0 27s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run rc=0 28s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpBFS/Search rc=0 11s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ExpTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/ImplicitPoly rc=0 13s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess rc=0 42s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/Path rc=0 4s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard rc=0 15s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide rc=0 24s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine rc=0 75s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs rc=0 17s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun rc=0 27s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk rc=0 22s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine rc=0 40s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof rc=0 26s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost rc=0 16s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape rc=0 154s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions rc=0 3s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARM rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMKit rc=0 4s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops rc=0 29s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMSim rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Bank rc=0 4s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Bin rc=0 5s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Call rc=0 11s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn rc=0 9s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Clean rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep rc=0 12s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Compile rc=0 5s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/DblLang rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Frag rc=0 10s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/FragDec rc=0 9s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Layout rc=0 14s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Lib rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARM rc=0 5s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile rc=0 20s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/MARMTime rc=0 14s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARM rc=0 7s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile rc=0 15s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMKit rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMProb rc=0 369s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof rc=0 8s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/NARMRun rc=0 5s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Parse rc=0 11s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Parse2 rc=0 28s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp rc=0 16s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain rc=0 13s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Program rc=0 6s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/Sim rc=0 20s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Machines/VWord rc=0 3s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/NSPACE rc=0 3s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/SpaceClasses rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/ClockLoop rc=0 7s errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/ClockMachine rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/CodePrefix rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TimeHierarchy/Diagonal rc=0 16s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Catalog rc=0 364s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/CfgRecord rc=0 237s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Basic rc=0 10s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Catalog rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Counter rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Embed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Lift rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Contract/Seam rc=0 8s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/CounterLoop rc=0 39s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 23s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputCall rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/InputLength rc=0 13s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 102s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/NDClockHost rc=0 10s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/NDClockHostRun rc=0 10s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/NDCombinators rc=0 7s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 103s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/RecordTable rc=0 197s errors=0 sorry=4
TCSlib/Complexity/TuringMachine/Build/Scan rc=0 21s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Seam rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/VirtualInput rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/WordTests rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 8s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/ChoiceWords rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CodeFormat rc=0 7s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CodeParser rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Composition rc=0 6s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProg rc=0 12s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgRun rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 5s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/MathlibBridge rc=0 8s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Nondeterministic rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/NondeterministicSpace rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/Oblivious rc=0 17s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate rc=0 13s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule rc=0 18s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup rc=0 20s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 28s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 10s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/SymbolLift rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UnaryTape rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Universal rc=0 53s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalBlock rc=0 18s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalInterpreter rc=0 17s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalStartup rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Computable rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Diagonalization rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Uncomputability/Halting rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 19s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 18s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 33s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 16s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 15s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 19s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 14s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 138s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 26s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Experiments rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/GoldreichLevin rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/InnerProduct rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/ThreeQuarters rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/OutputLength rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Generators rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0
TCSlib/Programs/Compat rc=0 3s errors=0 sorry=0
TCSlib/Programs/Util/List rc=0 9s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/i/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03i's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.PermFamily.glHalf_f_even: propext, Quot.sound
TCSlib.Cryptography.PermFamily.glHalf_f_odd: propext, Quot.sound
TCSlib.Cryptography.glHalfBit_even: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.glHalfBit_odd: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.predProb_glHalf_even: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.predProb_glHalf_odd: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProb_glHalf_even: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProb_glHalf_odd_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.comp_div_two: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.OneWayPermutation.glHalf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_owp_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_securePRG_of_owp: propext, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/i/admissions.txt =====

# declarations with `sorry` in pack 03i's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/i/lint.log =====

# scripts/style_lint.py on pack 03i's files, at a3c5fa8b72e50939822f22364647dc844a3914a0









0 findings in 8 files

## ===== TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.NextBit
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine infrastructure for the hard-core predicate theorems

Proof infrastructure for `TCSlib.Cryptography.Asymptotic.HardCore` and
`TCSlib.Cryptography.Asymptotic.HardCorePermutation` ([PS10, Theorems 79.4 and 87.3,
Lemma 80.5]): the reductions of those theorems as `Complexity.NUPPT`s, built by the closure
calculus of `TCSlib.Complexity.Randomized` (foundation decision D2 of
`PassShelatChapter2-4Plan.md`), together with the bit-string identities and the probability
bookkeeping that identify each machine with the concrete reduction of the Garg layer.

* `Complexity.NUPPT.wrap` — the **one-call wrapper**: for a machine `A`, polynomial-time
  `pre`/`post`, an advice family `β` and a coin polynomial `p`, the machine that reads its
  first `p(n)` coins as data, pre-processes `⟨⟨⟨1^n, y⟩, coins⟩, β n⟩`, calls `A` once with
  the remaining coins and post-processes the answer. It packages every single-call reduction
  of the hard-core chapter (the predictor of Theorem 79.4, the hybrid distinguisher of
  Lemma 80.5, the padding inverters of Theorem 87.3, the pass-through-bit reductions of the
  balanced permutation).
* `TCSlib.Cryptography.prgIterFun` — the iterated evaluation of a one-bit-stretch generator
  (`Complexity.polyTimeComputable_iterateEmit`), for the expansion of Lemma 80.5.
* The small `List.ofFn` identities (`ofFn_snoc_eq`, `ofFn_appendEquiv`) and coin-split
  bijections used by all of them.

## Main definitions

* `Complexity.NUPPT.wrap`, `Complexity.NUPPT.wrapFun` — the one-call wrapper machine and
  its raw function.
* `TCSlib.Cryptography.prgIterStep`, `TCSlib.Cryptography.prgIterFun` — the iterated
  generator evaluation.

## Main results

* `Complexity.NUPPT.runAt_wrap` — the activation of the one-call wrapper on split coins.
* `TCSlib.Cryptography.prgIterFun_poly`, `TCSlib.Cryptography.prgIterFun_ofFn` — the
  iterated evaluation is polynomial-time and computes the output bits of the expansion.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4: Theorem 79.4; §3.3.5: Lemma 80.5; §3.4.2–3.4.3: Theorem 87.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3), §3.3 (Theorems 3.1, 3.2).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- `List.ofFn (Fin.snoc v b) = List.ofFn v ++ [b]`. -/
theorem ofFn_snoc_eq {n : ℕ} (v : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc v b : Fin (n + 1) → Bool) = List.ofFn v ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- `List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)]`. -/
theorem ofFn_eq_init_append {n : ℕ} (v : Fin (n + 1) → Bool) :
    List.ofFn v = List.ofFn (Fin.init v) ++ [v (Fin.last n)] := by
  have h := ofFn_snoc_eq (Fin.init v) (v (Fin.last n))
  rwa [Fin.snoc_init_self] at h

/-- `List.ofFn` of an appended pair is the concatenation of the encodings. -/
theorem ofFn_appendEquiv {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    List.ofFn (Fin.appendEquiv a b (x, y)) = List.ofFn x ++ List.ofFn y :=
  List.ofFn_fin_append x y

/-- The first `a` bits of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem take_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).take a = List.ofFn x :=
  List.take_left' (List.length_ofFn)

/-- The bits after the first `a` of `List.ofFn x ++ List.ofFn y` with `|x| = a`. -/
theorem drop_ofFn_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (List.ofFn x ++ List.ofFn y).drop a = List.ofFn y :=
  List.drop_left' (List.length_ofFn)

/-- Transport of bit strings along an equality of lengths (`Fin.cast` on the index). -/
def finCastEquiv {a b : ℕ} (h : a = b) : (Fin a → Bool) ≃ (Fin b → Bool) where
  toFun f j := f (Fin.cast h.symm j)
  invFun f i := f (Fin.cast h i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport along an equality of lengths does not change the encoding. -/
theorem ofFn_finCastEquiv {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
    List.ofFn (finCastEquiv h f) = List.ofFn f :=
  (List.ofFn_congr h f).symm

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## The one-call wrapper -/

/-- The raw function of the one-call wrapper on the layout `⟨⟨⟨1^n, y⟩, ⟨β, α⟩⟩, r⟩`: cut the
coins at `p(n)`, form the view `w := ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β⟩`, run `A` on `pre w` with
advice `α` and the remaining coins, and return `post ⟨w, answer⟩`. -/
def wrapFun (A : NUPPT) (pre post : List Bool → List Bool) (p : PolyExpr) (z : List Bool) :
    List Bool :=
  post (pairEncode
    (layout (inParam z) (inArg z)
      ((pairSndD (pairEncode (inParam z) (inCoins z))).take
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
      (pairFstD (inAdvice z)))
    (A.output (layout (inParam z)
      (pre (layout (inParam z) (inArg z)
        ((pairSndD (pairEncode (inParam z) (inCoins z))).take
          (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length))
        (pairFstD (inAdvice z))))
      (pairSndD (inAdvice z))
      ((pairSndD (pairEncode (inParam z) (inCoins z))).drop
        (p.eval (pairFstD (pairEncode (inParam z) (inCoins z))).length)))))

/-- The raw function of the one-call wrapper is polynomial-time (the pairing calculus, the
typed coin cuts `polyTimeComputable_pairTakePoly`/`pairDropPoly`, and `A.output`). -/
theorem wrapFun_poly (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (p : PolyExpr) :
    PolyTimeComputable (A.wrapFun pre post p) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have htake := (polyTimeComputable_pairTakePoly p).comp hcut
  have hdrop := (polyTimeComputable_pairDropPoly p).comp hcut
  have hw := polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg htake
    (polyTimeComputable_pairFstD.comp polyTimeComputable_inAdvice)
  have hA := A.polyTimeComputable_output.comp
    (polyTimeComputable_layout polyTimeComputable_inParam (hpre.comp hw)
      (polyTimeComputable_pairSndD.comp polyTimeComputable_inAdvice) hdrop)
  exact hpost.comp (hw.pairEncode hA)

/-- **The one-call wrapper** [PS10, §2.1, the closure properties used implicitly]: the
machine with coins `p + A.coins` and advice `⟨β n, A.advice n⟩` that, on `⟨1^n, y⟩` with coins
`r`, forms the view `w = ⟨⟨⟨1^n, y⟩, r.take (p n)⟩, β n⟩`, calls `A(1^n, pre w)` once with the
remaining coins and returns `post ⟨w, answer⟩`. Every single-call reduction of the hard-core
chapter is an instance (`runAtL_wrap`, `runAt_wrap`). -/
noncomputable def wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) : NUPPT :=
  ofPolyTime (A.wrapFun_poly hpre hpost p) (.add p A.coins)
    (.add (.add (.mul (.const 2) b) (.const 2)) A.adv)
    (fun n => pairEncode (β n) (A.advice n)) (fun n => by
      rw [length_pairEncode]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have h₁ := hβ n
      have h₂ := A.advice_length n
      omega)

/-- The coin polynomial of the one-call wrapper is `p + A.coins`. -/
@[simp] theorem coins_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) :
    (A.wrap hpre hpost β b hβ p).coins = .add p A.coins := rfl

/-- The untyped activation of the one-call wrapper. -/
theorem runAtL_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.wrap hpre hpost β b hβ p).runAtL n y r =
      post (pairEncode (layout (List.replicate n true) y (r.take (p.eval n)) (β n))
        (A.runAtL n (pre (layout (List.replicate n true) y (r.take (p.eval n)) (β n)))
          (r.drop (p.eval n)))) := by
  unfold wrap
  rw [runAtL_ofPolyTime]
  simp [wrapFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- The typed activation of the one-call wrapper on coins `r` that split as `a ++ c`: the
data coins `a` (`p(n)` bits) and the coins `c` of `A`. (Stated for any coin string `r` whose
encoding is `List.ofFn a ++ List.ofFn c`, so that any coin bijection can be used.) -/
theorem runAt_wrap (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) (p : PolyExpr) (n : ℕ) (y : List Bool)
    {m : ℕ} (hm : m = p.eval n) (a : Fin m → Bool) (c : A.Coins n)
    (r : (A.wrap hpre hpost β b hβ p).Coins n) (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (A.wrap hpre hpost β b hβ p).runAt n y r =
      post (pairEncode (layout (List.replicate n true) y (List.ofFn a) (β n))
        (A.runAt n (pre (layout (List.replicate n true) y (List.ofFn a) (β n))) c)) := by
  rw [runAt_eq, runAtL_wrap, hr, List.take_left' (by simp [hm]), List.drop_left' (by simp [hm]),
    runAt_eq]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Reindexing the coins of an adversary -/

/-- Reindexing the coins of a distinguisher by a bijection does not change acceptance
probabilities. -/
theorem acceptProb_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype ρ] [Fintype ρ']
    (X : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : acceptProb X D = acceptProb X D' := by
  unfold acceptProb
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-- Reindexing the coins of a distinguisher by a bijection does not change PRG advantages. -/
theorem prgAdv_coins_equiv {σ γ ρ ρ' : Type*} [Fintype σ] [Fintype γ] [Fintype ρ] [Fintype ρ']
    (G : σ → γ) (D : γ → ρ → Bool) (D' : γ → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ x c, D x (e c) = D' x c) : prgAdv G D = prgAdv G D' := by
  unfold prgAdv distAdv
  rw [acceptProb_coins_equiv G D D' e h, acceptProb_coins_equiv id D D' e h]

/-- Reindexing the coins of a predictor by a bijection does not change prediction
probabilities. -/
theorem predProb_coins_equiv {α β ρ ρ' : Type*} [Fintype α] [Fintype ρ] [Fintype ρ']
    (f : α → β) (B : α → Bool) (A : β → ρ → Bool) (A' : β → ρ' → Bool) (e : ρ' ≃ ρ)
    (h : ∀ y c, A y (e c) = A' y c) : predProb f B A = predProb f B A' := by
  unfold predProb
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr e)]
  exact OneWay.uprob_congr fun z => by simp [h]

/-! ## Theorem 79.4: the generator `f(s) ‖ h(s)` and its predictor -/

/-- **The evaluator of `f(s) ‖ h(s)`** from evaluators `F` of `f` and `H` of `h` on `⟨1^n, s⟩`:
`s ↦ F ⟨1^{|s|}, s⟩ ++ H ⟨1^{|s|}, s⟩` is polynomial-time and computes
`List.ofFn (Fin.snoc (f s) (h s))` (the efficiency clause of [PS10, Theorem 79.4]). -/
theorem exists_owpGenEvaluator (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    {F H : List Bool → List Bool} (hF : PolyTimeComputable F) (hH : PolyTimeComputable H)
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x))
    (hHx : ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
      ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (Fin.snoc (P.f n s) (h n s) : Fin (n + 1) → Bool) := by
  have hpre : PolyTimeComputable fun w : List Bool => pairEncode (List.replicate w.length true) w :=
    polyTimeComputable_unary.pairEncode polyTimeComputable_id
  refine ⟨fun w => F (pairEncode (List.replicate w.length true) w) ++
    H (pairEncode (List.replicate w.length true) w), (hF.comp hpre).append (hH.comp hpre),
    fun n s => ?_⟩
  have h1 := hFx n s
  have h2 := hHx n s
  simp only [NUPPT.advInput, List.length_ofFn] at h1 h2 ⊢
  rw [h1, h2, ofFn_snoc_eq]

/-- The pre-processing of the predictor of [PS10, Theorem 79.4]: on the view
`⟨⟨⟨1^n, y⟩, [σ]⟩, [flip]⟩` form the distinguisher's input `y ++ [σ]`. -/
def owpPredPre (w : List Bool) : List Bool := NUPPT.inArg w ++ NUPPT.inAdvice w

/-- The post-processing of the predictor of [PS10, Theorem 79.4]: on `⟨view, answer⟩` output
`[xor (if answer = [true] then σ else !σ) flip]`. -/
def owpPredPost (v : List Bool) : List Bool :=
  [xor (if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
    else !(NUPPT.inAdvice (pairFstD v)).headD false) ((NUPPT.inCoins (pairFstD v)).headD false)]

/-- The pre-processing of the predictor is polynomial-time. -/
theorem owpPredPre_poly : PolyTimeComputable owpPredPre :=
  NUPPT.polyTimeComputable_inArg.append NUPPT.polyTimeComputable_inAdvice

/-- The post-processing of the predictor is polynomial-time (`polyTimeComputable_pairEq` for
the verdict test, `StateLoop.headBit_poly` for the two bits, `polyTimeComputable_ite`,
`StateLoop.xor_poly`). -/
theorem owpPredPost_poly : PolyTimeComputable owpPredPost := by
  have htest : PolyTimeComputable fun v : List Bool => [decide (pairSndD v = [true])] := by
    convert polyTimeComputable_pairEq.comp
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [true])) using 1
    funext v
    simp
  have hσ : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inAdvice (pairFstD v)).headD false] :=
    StateLoop.headBit_poly.comp (NUPPT.polyTimeComputable_inAdvice.comp polyTimeComputable_pairFstD)
  have hflip : PolyTimeComputable fun v : List Bool =>
      [(NUPPT.inCoins (pairFstD v)).headD false] :=
    StateLoop.headBit_poly.comp (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairFstD)
  have hite : PolyTimeComputable fun v : List Bool =>
      [if pairSndD v = [true] then (NUPPT.inAdvice (pairFstD v)).headD false
        else !(NUPPT.inAdvice (pairFstD v)).headD false] := by
    convert polyTimeComputable_ite htest hσ (StateLoop.not_poly hσ) using 1
    funext v
    by_cases hv : pairSndD v = [true] <;> simp [hv]
  exact StateLoop.xor_poly hite hflip

/-- **The predictor machine of [PS10, Theorem 79.4]** for a distinguisher `D` and a sign
family `flip`: advice `⟨[flip n], D.advice n⟩`, coins `1 + D.coins`; on `⟨1^n, y⟩` it reads the
first coin `σ`, calls `D(1^n, y ++ [σ])` with the remaining coins and outputs
`[xor (if D accepts then σ else !σ) (flip n)]` (`Complexity.NUPPT.wrap`). -/
noncomputable def owpPredMachine (D : NUPPT) (flip : ℕ → Bool) : NUPPT :=
  D.wrap owpPredPre_poly owpPredPost_poly (fun n => [flip n]) (.const 1)
    (fun _ => by simp) (.const 1)

/-- The predictor machine on coins `r = [σ] ++ c` computes the concrete predictor
`owpPredictor` of [Gar26, Theorem 3.2]: `xor (if D(y ‖ σ) then σ else !σ) flip`. -/
theorem owpPredMachine_predictor (D : NUPPT) (flip : ℕ → Bool) (n : ℕ) (y : Fin n → Bool)
    (σ : Bool) (c : D.Coins n) (r : (owpPredMachine D flip).Coins n)
    (hr : List.ofFn r = [σ] ++ List.ofFn c) :
    (owpPredMachine D flip).predictor n n y r =
      xor (if D.distinguisher n (n + 1) (Fin.snoc y σ) c then σ else !σ) (flip n) := by
  unfold owpPredMachine NUPPT.predictor NUPPT.distinguisher
  rw [NUPPT.runAt_wrap D owpPredPre_poly owpPredPost_poly (fun n => [flip n]) (.const 1)
    (fun _ => by simp) (.const 1) n (List.ofFn y) (m := 1) rfl (fun _ => σ) c r
    (by rw [hr]; rfl)]
  have h1 : List.ofFn (fun _ : Fin 1 => σ) = [σ] := by simp [List.ofFn_succ]
  simp only [owpPredPost, owpPredPre, pairSndD_pairEncode, pairFstD_pairEncode,
    NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, h1, List.headD_cons]
  rw [← ofFn_snoc_eq, NUPPT.runAt_eq]
  by_cases hD : D.runAtL n (List.ofFn (Fin.snoc y σ)) (List.ofFn c) = [true]
  · simp only [hD, if_true, decide_true]
    cases σ <;> cases flip n <;> rfl
  · simp only [hD, if_false, decide_false]
    cases σ <;> cases flip n <;> rfl

/-- **The prediction probability of the predictor machine** equals that of the concrete
predictor `owpPredictor` [Gar26, Theorem 3.2] run against `D(1^n, ·)` with the sign `flip n`,
for any `f` and `B` on `{0,1}^n`. -/
theorem owpPredMachine_predProb (D : NUPPT) (flip : ℕ → Bool) {n : ℕ}
    (f : (Fin n → Bool) → (Fin n → Bool)) (B : (Fin n → Bool) → Bool) :
    predProb f B ((owpPredMachine D flip).predictor n n) =
      predProb f B (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := by
  refine predProb_coins_equiv f B _ _
    (((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      (Fin.appendEquiv 1 (D.coinLen n))) fun y c => ?_
  obtain ⟨σ, c⟩ := c
  refine owpPredMachine_predictor D flip n y σ c _ ?_
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id]
  exact (ofFn_appendEquiv ((Equiv.funUnique (Fin 1) Bool).symm σ) c).trans
    (congrArg (· ++ List.ofFn c) (by simp [List.ofFn_succ]))

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Lemma 80.5: the iterated evaluation of a one-bit-stretch generator -/

/-- The seed update of the iterated evaluation: `w ↦ (F w).take |w|` (the first `|w|` bits of
the generator's output, the next seed `X_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterStep (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).take w.length

/-- The emitted bit of the iterated evaluation: `w ↦ (F w).drop |w|` (the last bit of the
generator's output, the bit `b_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterEmit (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).drop w.length

/-- The iterated evaluation: the output bits of `ℓ(|s|) + 1` rounds of the generator from the
seed `s`, concatenated (`Complexity.polyTimeComputable_iterateEmit`). -/
def prgIterFun (F : List Bool → List Bool) (ℓ : PolyExpr) (s : List Bool) : List Bool :=
  (List.range (ℓ.eval s.length + 1)).flatMap fun i => prgIterEmit F ((prgIterStep F)^[i] s)

/-- The seed update is polynomial-time (`polyTimeComputable_pairTakePoly var` on `⟨w, F w⟩`). -/
theorem prgIterStep_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterStep F) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterStep]

/-- The emitted bit is polynomial-time (`polyTimeComputable_pairDropPoly var` on `⟨w, F w⟩`). -/
theorem prgIterEmit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterEmit F) := by
  convert (polyTimeComputable_pairDropPoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterEmit]

/-- The seed update never lengthens a word, so its orbit stays within the input length. -/
theorem length_prgIterStep_iterate_le (F : List Bool → List Bool) (w : List Bool) (i : ℕ) :
    ((prgIterStep F)^[i] w).length ≤ w.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (List.length_take_le _ _).trans ih

/-- **The iterated evaluation is polynomial-time** (instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := ℓ` and orbit bound `P := var`). -/
theorem prgIterFun_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (prgIterFun F ℓ) :=
  polyTimeComputable_iterateEmit (prgIterStep_poly hF) (prgIterEmit_poly hF) ℓ .var
    (fun x i _ => length_prgIterStep_iterate_le F x i)

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- On an encoded seed the seed update computes the first `n` bits of `G(s)`. -/
theorem prgIterStep_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterStep F (List.ofFn s) = List.ofFn (Fin.init (G n s)) := by
  unfold prgIterStep
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.take_left' List.length_ofFn]

/-- On an encoded seed the emitted bit is the last bit of `G(s)`. -/
theorem prgIterEmit_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterEmit F (List.ofFn s) = [G n s (Fin.last n)] := by
  unfold prgIterEmit
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.drop_left' List.length_ofFn]

/-- The iterates of the seed update on an encoded seed are the encoded iterates of
`s ↦ init (G s)`. -/
theorem prgIterStep_iterate_ofFn (n : ℕ) (s : Fin n → Bool) (i : ℕ) :
    (prgIterStep F)^[i] (List.ofFn s) = List.ofFn ((fun x => Fin.init (G n x))^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, prgIterStep_ofFn G hFs, Function.iterate_succ_apply']

/-- **The iterated evaluation on an encoded seed** is the string of the `ℓ(n) + 1` output bits
`G(X_i)_{last}`, `X_i` the `i`-th iterate of `s ↦ init (G s)`. -/
theorem prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    prgIterFun F ℓ (List.ofFn s) =
      List.ofFn fun i : Fin (ℓ.eval n + 1) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  unfold prgIterFun
  rw [List.length_ofFn]
  refine List.ext_getElem (by simp [List.length_flatMap, prgIterStep_iterate_ofFn G hFs,
    prgIterEmit_ofFn G hFs]) fun j hj₁ hj₂ => ?_
  have hmap : ((List.range (ℓ.eval n + 1)).flatMap fun i =>
      prgIterEmit F ((prgIterStep F)^[i] (List.ofFn s))) =
      (List.range (ℓ.eval n + 1)).map fun i => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
    rw [List.map_eq_flatMap]
    congr 1
    funext i
    rw [prgIterStep_iterate_ofFn G hFs, prgIterEmit_ofFn G hFs]
  simp only [hmap, List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- The first `ℓ(n)` bits of the iterated evaluation: the output of the expansion `G'` of
[PS10, Lemma 80.5]. -/
theorem take_prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    (prgIterFun F ℓ (List.ofFn s)).take (ℓ.eval n) =
      List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  rw [prgIterFun_ofFn G hFs, List.ofFn_succ', List.concat_eq_append,
    List.take_left' List.length_ofFn]
  rfl

/-- **The evaluator of the expansion `G'`** [PS10, Lemma 80.5, "`G'` is efficiently
computable"]: `s ↦ (prgIterFun F ℓ s).take (ℓ |s|)` is polynomial-time and computes the
`ℓ(n)` output bits. -/
theorem exists_expandEvaluator (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧ ∀ n (s : Fin n → Bool),
      E (List.ofFn s) =
        List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  refine ⟨fun w => (prgIterFun F ℓ w).take (ℓ.eval w.length), ?_, fun n s => ?_⟩
  · convert (polyTimeComputable_pairTakePoly ℓ).comp
      (polyTimeComputable_id.pairEncode (prgIterFun_poly hF ℓ)) using 1
    funext w
    simp
  · dsimp only
    rw [List.length_ofFn, take_prgIterFun_ofFn G hFs]

end Generator

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## FP glue: cutting a string at the length of another -/

/-- `w ↦ (b w).take |a w|` is polynomial-time (`polyTimeComputable_pairTakePoly var` on
`⟨a w, b w⟩`). -/
theorem takeLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).take (a w).length := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-- `w ↦ (b w).drop |a w|` is polynomial-time (`polyTimeComputable_pairDropPoly var` on
`⟨a w, b w⟩`). -/
theorem dropLen_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => (b w).drop (a w).length := by
  convert (polyTimeComputable_pairDropPoly .var).comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Negligible functions times polynomials -/

/-- A syntactic polynomial times a negligible function is negligible
([Gar26, §1.2]; `Negligible.mul_pow` and `Negligible.const_mul` through the normal-form
majorant `C (n+1)^c ≤ C 2^c n^c` of `PolyExpr.eval_le`). -/
theorem Negligible.polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, c, hC⟩ := p.eval_le
  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
  have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  have hp : (p.eval n : ℝ) ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c :=
    calc (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := h1
      _ ≤ C * (2 * (n : ℝ)) ^ c := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (C : ℝ) * 2 ^ c * (n : ℝ) ^ c := by rw [_root_.mul_pow, mul_assoc]
  calc |(p.eval n : ℝ) * μ n| = (p.eval n : ℝ) * |μ n| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ (C : ℝ) * 2 ^ c * (n : ℝ) ^ c * |μ n| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = |(C : ℝ) * 2 ^ c * ((n : ℝ) ^ c * μ n)| := by
        rw [abs_mul ((C : ℝ) * 2 ^ c) ((n : ℝ) ^ c * μ n), abs_mul ((n : ℝ) ^ c) (μ n),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) * 2 ^ c),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), mul_assoc]

/-! ## Lemma 80.5: the hybrid distinguisher -/

/-- The pre-processing of the hybrid-`k` reduction of [PS10, Lemma 80.5] on the view
`⟨⟨⟨1^n, T⟩, c⟩, ⟨1^k, 1^{ℓ−k−1}⟩⟩`: the `ℓ`-bit string
`c.take k ++ T.drop n ++ (prgIterFun F ℓ (T.take n)).take (ℓ − k − 1)` — `k` uniform bits,
the given bit `T_{n+1}`, and `ℓ − k − 1` bits generated from the given seed `T_1 ⋯ T_n`. -/
def expandRedPre (F : List Bool → List Bool) (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (NUPPT.inAdvice w).take (pairFstD (NUPPT.inCoins w)).length ++
    (NUPPT.inArg w).drop (NUPPT.inParam w).length ++
    (prgIterFun F ℓ ((NUPPT.inArg w).take (NUPPT.inParam w).length)).take
      (pairSndD (NUPPT.inCoins w)).length

/-- The pre-processing of the hybrid reduction is polynomial-time. -/
theorem expandRedPre_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (expandRedPre F ℓ) :=
  ((takeLen_poly (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inCoins)
    NUPPT.polyTimeComputable_inAdvice).append
      (dropLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)).append
    (takeLen_poly (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inCoins)
      ((prgIterFun_poly hF ℓ).comp
        (takeLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)))

/-- **The hybrid-`k` distinguisher machine of [PS10, Lemma 80.5]** for a distinguisher `D` of
the expansion, a hybrid index family `k n < ℓ(n)` and the evaluator `F` of the generator:
advice `⟨⟨1^{k n}, 1^{ℓ(n) − k n − 1}⟩, D.advice n⟩`, coins `ℓ + D.coins`; on `⟨1^n, T⟩` it forms
the `ℓ(n)`-bit hybrid string (`expandRedPre`) and returns `D`'s verdict on it
(`Complexity.NUPPT.wrap`). -/
noncomputable def expandRedMachine (D : NUPPT) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F) (ℓ : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) : NUPPT :=
  D.wrap (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD
    (fun n => pairEncode (List.replicate (k n) true) (List.replicate (ℓ.eval n - k n - 1) true))
    (.add (.mul (.const 3) ℓ) (.const 2)) (fun n => by
      rw [length_pairEncode, List.length_replicate, List.length_replicate]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := hk n
      omega) ℓ

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- **The hybrid string** formed by `expandRedPre` on the view of `⟨1^n, T⟩` with data coins
`a` and advice `⟨1^k, 1^{ℓ−k−1}⟩` is the input of the concrete hybrid distinguisher
[Gar26, Theorem 3.1]: bit `i` is `a_i` for `i < k`, the given bit `T_{last}` at `i = k`, and
`G(X_{i−k−1})_{last}` beyond, with `X_j` the `j`-th iterate of `s ↦ init (G s)` on `init T`. 

**Proof sketch.** Unfold the projections of the view; `T` splits as `init T ‖ [T_last]` (`ofFn_eq_init_append`) and the iterated evaluation is `prgIterFun_ofFn`; then `List.ext_getElem` with the three index ranges `i < k`, `i = k`, `i > k` (`List.getElem_append_left/right`, `List.getElem_take`, `List.getElem_ofFn`). -/
theorem expandRedPre_layout (ℓ : PolyExpr) (n k : ℕ) (hk : k < ℓ.eval n) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) :
    expandRedPre F ℓ (NUPPT.layout (List.replicate n true) (List.ofFn T) (List.ofFn a)
      (pairEncode (List.replicate k true) (List.replicate (ℓ.eval n - k - 1) true))) =
    List.ofFn fun i : Fin (ℓ.eval n) => if (i : ℕ) < k then a i else if (i : ℕ) = k then T (Fin.last n)
      else G n ((fun x => Fin.init (G n x))^[i - k - 1] (Fin.init T)) (Fin.last n) := by
  simp only [expandRedPre, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, NUPPT.inArg_layout,
    NUPPT.inParam_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  rw [ofFn_eq_init_append T, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    prgIterFun_ofFn G hFs]
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_append, List.length_take, List.length_ofFn, List.length_singleton]
    omega
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_ofFn]
    by_cases h1 : j < k
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_take, List.getElem_ofFn]
      simp [h1]
    · by_cases h2 : j = k
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp [h2]
      · rw [List.getElem_append_right (by simp; omega), List.getElem_take, List.getElem_ofFn]
        simp only [h1, h2, if_false, List.length_append, List.length_take, List.length_ofFn,
          List.length_singleton]
        rw [show j - (min k (ℓ.eval n) + 1) = j - k - 1 by omega]

/-- **The hybrid distinguisher machine computes the concrete hybrid reduction**: on coins
`r = a ++ c` its verdict on `T` is `D`'s verdict on the hybrid string with uniform bits `a`
and coins `c`. -/
theorem expandRedMachine_distinguisher (D : NUPPT) (hF : PolyTimeComputable F) (ℓ : PolyExpr)
    (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) (n : ℕ) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) (c : D.Coins n) (r : (expandRedMachine D hF ℓ k hk).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (expandRedMachine D hF ℓ k hk).distinguisher n (n + 1) T r =
      D.distinguisher n (ℓ.eval n) (fun i => if (i : ℕ) < k n then a i
        else if (i : ℕ) = k n then T (Fin.last n)
        else G n ((fun x => Fin.init (G n x))^[i - k n - 1] (Fin.init T)) (Fin.last n)) c := by
  unfold expandRedMachine NUPPT.distinguisher
  rw [NUPPT.runAt_wrap D (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD _ _ _ ℓ n
    (List.ofFn T) rfl a c r hr, pairSndD_pairEncode, expandRedPre_layout G hFs ℓ n (k n) (hk n) T a]

end Generator

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Theorem 87.3, first clause: the padded family `g(x, r) = (f(x), r)` is one-way -/

/-- **The evaluator of `g(x, r) = (f(x), r)`** [PS10, Theorem 87.3, "`g` is easy to compute"]
from an evaluator `F` of `f` on `⟨1^n, x⟩`: on `⟨1^n, x ‖ r⟩` output
`F ⟨1^n, (x ‖ r).take (inLen n)⟩ ++ (x ‖ r).drop (inLen n)`. -/
theorem exists_glPadEvaluator (𝓕 : FunFamily) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (hFx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
      F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
      ∀ n (x r : Fin (𝓕.inLen.eval n) → Bool),
        E (NUPPT.advInput n (List.ofFn x ++ List.ofFn r)) = List.ofFn (𝓕.f n x) ++ List.ofFn r := by
  refine ⟨fun w => F (pairEncode (pairFstD w)
      ((pairSndD w).take (𝓕.inLen.eval (pairFstD w).length))) ++
      (pairSndD w).drop (𝓕.inLen.eval (pairFstD w).length),
    (hF.comp (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly 𝓕.inLen))).append
      (polyTimeComputable_pairDropPoly 𝓕.inLen), fun n x r => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append]
  rw [← NUPPT.advInput, hFx]

/-- The post-processing of the padding inverter of [PS10, Theorem 87.3]: on `⟨view, answer⟩`
keep the first `|r|` bits of the answer, `r` the coin head of the view (the string `x'` of the
answer `x' ‖ r'`). -/
def glPadInvPost (v : List Bool) : List Bool :=
  (pairSndD v).take (NUPPT.inAdvice (pairFstD v)).length

/-- The post-processing of the padding inverter is polynomial-time. -/
theorem glPadInvPost_poly : PolyTimeComputable glPadInvPost :=
  takeLen_poly (NUPPT.polyTimeComputable_inAdvice.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairSndD

/-- **The padding inverter machine of [PS10, Theorem 87.3]** (`OneWay.padInverter` of
[Gar26, Lemma 2.3] at the machine level): for an inverter `A` of `g(x, r) = (f(x), r)` and the
padding length `p`, the machine with coins `p + A.coins` and `A`'s advice that, on `⟨1^n, y⟩`,
reads its first `p(n)` coins as the padding `r`, calls `A(1^n, y ++ r)` with the remaining coins
and returns the first `p(n)` bits of the answer (`Complexity.NUPPT.wrap`; the pre-processing
`y ++ r` is `owpPredPre`). -/
noncomputable def glPadInvMachine (A : NUPPT) (p : PolyExpr) : NUPPT :=
  A.wrap owpPredPre_poly glPadInvPost_poly (fun _ => []) (.const 0) (fun _ => by simp) p

/-- The padding inverter on coins `r = a ++ c` returns the first `p(n)` bits of
`A(1^n, y ++ a; c)`. -/
theorem glPadInvMachine_runAt (A : NUPPT) (p : PolyExpr) (n : ℕ) (y : List Bool)
    (a : Fin (p.eval n) → Bool) (c : A.Coins n) (r : (glPadInvMachine A p).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (glPadInvMachine A p).runAt n y r = (A.runAt n (y ++ List.ofFn a) c).take (p.eval n) := by
  unfold glPadInvMachine
  rw [NUPPT.runAt_wrap A owpPredPre_poly glPadInvPost_poly _ _ _ p n y rfl a c r hr]
  simp [glPadInvPost, owpPredPre]

/-- **The padding inverter inverts `f` at least as often as `A` inverts `g`**
([PS10, Theorem 87.3], first clause; [Gar26, Lemma 2.3]): at every `n`, the inversion
probability of `A` against `g_n = appendEquiv ∘ HardcoreBit.glPad (f n) ∘ appendEquiv⁻¹` on
`{0,1}^{2·inLen n}` is at most that of `glPadInvMachine A inLen` against `f n`.

**Proof sketch.** Reindex the inputs by `appendEquiv` and the coins of the padding inverter by
`appendEquiv`, regroup by `Equiv.prodAssoc` and compare pointwise (`uprob_mono`): if `A`'s
answer `x' ‖ r'` satisfies `f(x') ‖ r' = f(x) ‖ r` then `f(x') = f(x)` (`Fin.appendEquiv` is
injective) and the padding inverter returns exactly `x'`. -/
theorem invProbOpt_glPad_le (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    invProbOpt (fun z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool =>
        Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
          (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)))
      (A.inverter n (𝓕.inLen.eval n + 𝓕.inLen.eval n) (𝓕.outLen.eval n + 𝓕.inLen.eval n)) ≤
    invProbOpt (𝓕.f n)
      ((glPadInvMachine A 𝓕.inLen).inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n)) := by
  unfold invProbOpt
  refine le_of_eq_of_le (uprob_comp_equiv
    ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.inLen.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (Fin (𝓕.inLen.eval n) → Bool)).prodCongr
      (Fin.appendEquiv (𝓕.inLen.eval n) (A.coinLen n))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, r⟩, c⟩ := w
  obtain ⟨x', hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, Equiv.symm_apply_apply,
    Equiv.prodAssoc_apply, NUPPT.inverter_eq_some_iff] at hx' hfx' ⊢
  obtain ⟨⟨x'', r''⟩, rfl⟩ := (Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).surjective x'
  simp only [Equiv.symm_apply_apply] at hfx' hx'
  have hpair := (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective
    (show Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x'', r'')) =
      Fin.appendEquiv _ _ (HardcoreBit.glPad (𝓕.f n) (x, r)) from hfx')
  simp only [HardcoreBit.glPad, Prod.mk.injEq] at hpair
  refine ⟨x'', ?_, hpair.1⟩
  rw [glPadInvMachine_runAt A 𝓕.inLen n _ r c _ (ofFn_appendEquiv r c)]
  simp only [HardcoreBit.glPad] at hx'
  rw [ofFn_appendEquiv, ofFn_appendEquiv] at hx'
  rw [hx', take_ofFn_append]

end TCSlib.Cryptography

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Theorem 87.3 for collections, first clause: the padded collection is one-way -/

/-- The decoder of the padded collection `g_i(x, r) = ⟨f_i(x), r⟩` (the `decD` of
`Collection.glPad`): split the string as a pair, decode the first component with `decD i` and
the second as an `L`-bit string. -/
def glPadDecode (F : Collection) (i : List Bool) (L : ℕ) (w : List Bool) :
    Option (F.D i × (Fin L → Bool)) :=
  match pairDecode w with
  | some (a, b) => match F.decD i a, decodeFin L b with
    | some x, some r => some (x, r)
    | _, _ => none
  | none => none

/-- Decoding `⟨a, ofFn s⟩`: the first component decoded by `decD i`, paired with `s`. -/
theorem glPadDecode_pairEncode_ofFn (F : Collection) (i : List Bool) {L : ℕ} (a : List Bool)
    (s : Fin L → Bool) :
    glPadDecode F i L (pairEncode a (List.ofFn s)) = (F.decD i a).map fun x => (x, s) := by
  cases h : F.decD i a <;> simp [glPadDecode, pairDecode_pairEncode, decodeFin_ofFn, h]

/-- A successful decoding `glPadDecode F i L w = some (x, s)` means `w = ⟨a, b⟩` with
`decD i a = some x` (and `b` the encoding of `s`). -/
theorem glPadDecode_eq_some (F : Collection) (i : List Bool) {L : ℕ} (w : List Bool)
    {x : F.D i} {s : Fin L → Bool} (h : glPadDecode F i L w = some (x, s)) :
    ∃ a b, w = pairEncode a b ∧ F.decD i a = some x ∧ decodeFin L b = some s := by
  unfold glPadDecode at h
  cases hw : pairDecode w with
  | none => simp [hw] at h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    refine ⟨a, b, eq_pairEncode_of_pairDecode w a b hw, ?_⟩
    simp only [hw] at h
    cases ha : F.decD i a <;> cases hb : decodeFin L b <;> simp [ha, hb] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-- **The sampler of the padded collection is close to uniform** ([PS10, Theorem 87.3],
collection form, clause (2)): if a sampler `S` with coins `Sample.coins + m` runs `Sample` on
its first coins and appends the remaining `m(n)` coins, and `Sample` is `δ`-close to uniform on
`D_i`, then the decoded output of `S` is `δ`-close to uniform on `D_i × {0,1}^L` (`L = m(n)`).

**Proof sketch.** `StatClose.prod` of the closeness of `Sample` with the exact uniformity of the
padding, mapped through `(o, s) ↦ o.map (·, s)` (`StatClose.map`) and transported along the coin
split `appendEquiv` (`StatClose.comp_equiv_left`); the decoder on `⟨a, ofFn s⟩` is
`glPadDecode_pairEncode_ofFn`. -/
theorem statClose_glPadSampler (F : Collection) (m : PolyExpr) (S : NUPPT)
    (hS : S.coins = .add F.sample.coins m)
    (hrun : ∀ n i r, S.runAtL n i r =
      pairEncode (F.sample.runAtL n i (r.take (F.sample.coinLen n))) (r.drop (F.sample.coinLen n)))
    {δ : ℕ → ℝ} (hclose : F.SampleClose δ) (n : ℕ) (r : F.gen.Coins n) (L : ℕ) (hL : L = m.eval n) :
    StatClose (fun s : S.Coins n => glPadDecode F (F.index n r) L (S.runAt n (F.index n r) s))
      (fun x : F.D (F.index n r) × (Fin L → Bool) => some x) (δ n) := by
  have hlen : F.sample.coinLen n + L = S.coinLen n := by
    show F.sample.coinLen n + L = S.coins.eval n
    rw [hS, PolyExpr.eval_add, hL]; rfl
  let e : F.sample.Coins n × (Fin L → Bool) ≃ S.Coins n :=
    (Fin.appendEquiv _ _).trans (finCastEquiv hlen)
  have h0 : StatClose (fun s : Fin L → Bool => s) (fun s : Fin L → Bool => s) 0 := StatClose.refl _
  have h1 := ((hclose n r).prod h0).map
    (fun z : Option (F.D (F.index n r)) × (Fin L → Bool) => z.1.map fun x => (x, z.2))
  rw [add_zero] at h1
  have h2 := h1.comp_equiv_left e.symm
  convert h2 using 1
  · funext s
    obtain ⟨⟨s₁, s₂⟩, rfl⟩ := e.surjective s
    have hofn : List.ofFn (e (s₁, s₂)) = List.ofFn s₁ ++ List.ofFn s₂ := by
      simp only [e, Equiv.trans_apply]
      rw [ofFn_finCastEquiv, ofFn_appendEquiv]
    simp only [NUPPT.runAt_eq, hrun, hofn, take_ofFn_append, drop_ofFn_append,
      glPadDecode_pairEncode_ofFn, Equiv.symm_apply_apply]

/-- The pre-processing of the inverter of the padded collection: on the view
`⟨⟨⟨1^n, ⟨i, y⟩⟩, r⟩, []⟩` form `A`'s input `⟨i, ⟨y, r⟩⟩`. -/
def glPadCollPre (w : List Bool) : List Bool :=
  pairEncode (pairFstD (NUPPT.inArg w)) (pairEncode (pairSndD (NUPPT.inArg w)) (NUPPT.inAdvice w))

/-- The pre-processing of the collection inverter is polynomial-time. -/
theorem glPadCollPre_poly : PolyTimeComputable glPadCollPre :=
  (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      NUPPT.polyTimeComputable_inAdvice)

/-- The post-processing of the collection inverter: the first component of `A`'s answer. -/
def glPadCollPost (v : List Bool) : List Bool := pairFstD (pairSndD v)

/-- The post-processing of the collection inverter is polynomial-time. -/
theorem glPadCollPost_poly : PolyTimeComputable glPadCollPost :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The inverter of the padded collection** ([PS10, Theorem 87.3], collection form): for an
inverter `A` of `g_i(x, r) = ⟨f_i(x), r⟩` and the padding length `m`, the machine with coins
`m + A.coins` and `A`'s advice that, on `⟨1^n, ⟨i, y⟩⟩`, reads its first `m(n)` coins as the
padding `r`, calls `A(1^n, ⟨i, ⟨y, r⟩⟩)` with the remaining coins and returns the first component
of the answer (`Complexity.NUPPT.wrap`). -/
noncomputable def glPadCollInvMachine (A : NUPPT) (m : PolyExpr) : NUPPT :=
  A.wrap glPadCollPre_poly glPadCollPost_poly (fun _ => []) (.const 0) (fun _ => by simp) m

/-- The collection inverter on coins `r = a ++ c` returns the first component of
`A(1^n, ⟨i, ⟨y, a⟩⟩; c)`. -/
theorem glPadCollInvMachine_runAt (A : NUPPT) (m : PolyExpr) (n : ℕ) (i y : List Bool)
    (a : Fin (m.eval n) → Bool) (c : A.Coins n) (r : (glPadCollInvMachine A m).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (glPadCollInvMachine A m).runAt n (pairEncode i y) r =
      pairFstD (A.runAt n (pairEncode i (pairEncode y (List.ofFn a))) c) := by
  unfold glPadCollInvMachine
  rw [NUPPT.runAt_wrap A glPadCollPre_poly glPadCollPost_poly _ _ _ m n (pairEncode i y) rfl a c r hr]
  simp [glPadCollPost, glPadCollPre]

/-- **The collection inverter inverts `F` at least as often as `A` inverts the padded
collection** ([PS10, Theorem 87.3], collection form, first clause): the inversion experiment of
`A` against `g_i(x, r) = ⟨f_i(x), r⟩` (with the padding of length `L r = m(n)` and the decoder
`glPadDecode`) is at most `F.invProbAt (glPadCollInvMachine A m) n`.

**Proof sketch.** Pointwise in the generator's coins (`OneWay.uexp_mono`); for a fixed index
reindex the padding by `L r = m(n)` and the coins of the collection inverter by `appendEquiv`,
regroup by `Equiv.prodAssoc` and compare pointwise (`uprob_mono`): a decoded answer `(x', r')`
with `⟨f_i(x'), r'⟩ = ⟨f_i(x), r⟩` has `f_i(x') = f_i(x)` (`pairDecode_pairEncode`), and the
collection inverter returns the first component `a` of `A`'s answer `⟨a, b⟩`, which decodes to
`x'` (`glPadDecode_eq_some`). -/
theorem glPad_invProbAt_le (F : Collection) (m : PolyExpr) (A : NUPPT) (n : ℕ)
    (L : F.gen.Coins n → ℕ) (hL : ∀ r, L r = m.eval n) :
    uexp (fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L r) → Bool)) × A.Coins n =>
        ∃ x', glPadDecode F (F.index n r) (L r)
            (A.runAt n (pairEncode (F.index n r)
              (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
          pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
            pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2)) ≤
    F.invProbAt (glPadCollInvMachine A m) n := by
  unfold Collection.invProbAt
  refine OneWay.uexp_mono fun r => ?_
  refine le_of_eq_of_le (uprob_comp_equiv
    (((Equiv.refl (F.D (F.index n r))).prodCongr (finCastEquiv (hL r).symm)).prodCongr
        (Equiv.refl (A.Coins n))) _).symm ?_
  refine le_of_le_of_eq ?_ ((uprob_comp_equiv
    (Equiv.prodAssoc (F.D (F.index n r)) (Fin (m.eval n) → Bool) (A.Coins n)) _).trans
    (uprob_comp_equiv ((Equiv.refl (F.D (F.index n r))).prodCongr
      (Fin.appendEquiv (m.eval n) (A.coinLen n))) _))
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨x, ρ⟩, c⟩ := w
  obtain ⟨⟨x', ρ'⟩, hx', hfx'⟩ := hw
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, Equiv.prodAssoc_apply,
    ofFn_finCastEquiv] at hx' hfx' ⊢
  have hf : F.f (F.index n r) x' = F.f (F.index n r) x := by
    have := congrArg pairDecode hfx'
    simp only [pairDecode_pairEncode, Option.some.injEq, Prod.mk.injEq] at this
    exact this.1
  obtain ⟨a, b, hab, ha, -⟩ := glPadDecode_eq_some F (F.index n r) _ hx'
  refine ⟨x', ?_, hf⟩
  rw [glPadCollInvMachine_runAt A m n _ _ ρ c _ (ofFn_appendEquiv ρ c), hab, pairFstD_pairEncode, ha]

end TCSlib.Cryptography

namespace Complexity.NUPPT

open Turing

/-! ## The parameter-change machine as a definition -/

/-- **The parameter-change machine `n ↦ p(n)`** (the witness of `exists_reparam`, as a
definition so that its coins and activation are available by `rfl`): advice `A.advice (p n)`,
coins `A.coins.subst p`; on `⟨1^n, y⟩` it replaces the unary parameter by `1^{p(n)}`
(`polyTimeComputable_unaryPoly p`) and runs `A`. -/
noncomputable def reparam (A : NUPPT) (p : PolyExpr) : NUPPT :=
  ofPolyTime (A.polyTimeComputable_output.comp
    (polyTimeComputable_layout ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_inParam)
      polyTimeComputable_inArg polyTimeComputable_inAdvice polyTimeComputable_inCoins))
    (A.coins.subst p) (A.adv.subst p) (fun n => A.advice (p.eval n)) (fun n => by
      rw [PolyExpr.eval_subst]
      exact A.advice_length _)

/-- The coin polynomial of the parameter-change machine is `A.coins.subst p`. -/
@[simp] theorem coins_reparam (A : NUPPT) (p : PolyExpr) : (A.reparam p).coins = A.coins.subst p :=
  rfl

/-- The parameter-change machine at `n` behaves as `A` at `p(n)`. -/
theorem runAtL_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) (y r : List Bool) :
    (A.reparam p).runAtL n y r = A.runAtL (p.eval n) y r := by
  unfold reparam
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- The number of coins of the parameter-change machine at `n` is that of `A` at `p(n)`. -/
theorem coinLen_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) :
    (A.reparam p).coinLen n = A.coinLen (p.eval n) := by
  simp [coinLen, PolyExpr.eval_subst]

/-- The coins of `A` at `p(n)` as the coins of the parameter-change machine at `n`. -/
noncomputable def reparamCoins (A : NUPPT) (p : PolyExpr) (n : ℕ) :
    A.Coins (p.eval n) ≃ (A.reparam p).Coins n :=
  TCSlib.Cryptography.finCastEquiv (coinLen_reparam A p n).symm

/-- The typed activation of the parameter-change machine. -/
theorem runAt_reparam (A : NUPPT) (p : PolyExpr) (n : ℕ) (y : List Bool) (c : A.Coins (p.eval n)) :
    (A.reparam p).runAt n y (reparamCoins A p n c) = A.runAt (p.eval n) y c := by
  rw [runAt_eq, runAtL_reparam, reparamCoins, TCSlib.Cryptography.ofFn_finCastEquiv, runAt_eq]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Helpers of the padded families and collections (`Asymptotic/HardCore.lean`) -/

/-- The re-encoding `(x ‖ r, c) ↦ ((x, r), c)` of the experiments. -/
def splitPair (a b : ℕ) (ρ : Type*) :
    (Fin (a + b) → Bool) × ρ ≃ ((Fin a → Bool) × (Fin b → Bool)) × ρ where
  toFun z := ((Fin.appendEquiv a b).symm z.1, z.2)
  invFun z := (Fin.appendEquiv a b z.1, z.2)
  left_inv z := Prod.ext ((Fin.appendEquiv a b).apply_symm_apply z.1) rfl
  right_inv z := Prod.ext ((Fin.appendEquiv a b).symm_apply_apply z.1) rfl

namespace Collection

variable (F : Collection)

/-- The raw sampler of the padded collection on the layout `⟨⟨⟨1^n, i⟩, []⟩, r⟩`: run the
domain sampler of `F` on the first `|Sample's coins|` coins and append the remaining coins
as the padding `r`. -/
def glPadSampleFun (z : List Bool) : List Bool :=
  pairEncode
    (F.sample.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) []
      ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).take
        (F.sample.coins.eval (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))))
    ((pairSndD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).drop
      (F.sample.coins.eval (pairFstD (pairEncode (NUPPT.inParam z) (NUPPT.inCoins z))).length))

/-- The raw sampler of the padded collection is polynomial-time (pairing calculus,
`polyTimeComputable_pairTakePoly`/`pairDropPoly`, the sampler's own output function). -/
theorem glPadSampleFun_poly : PolyTimeComputable (glPadSampleFun F) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have htake := (polyTimeComputable_pairTakePoly F.sample.coins).comp hcut
  have hdrop := (polyTimeComputable_pairDropPoly F.sample.coins).comp hcut
  exact (F.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      NUPPT.polyTimeComputable_inArg (polyTimeComputable_const []) htake)).pairEncode hdrop

/-- The activation of the padded sampler on the index `i` with coins `s`, stated on the
machine (so that `glPad` can discharge `sample_spec`): `Sample(1^n, i)` on the first
`|Sample's coins|` coins paired with the remaining coins. -/
theorem glPadSample_runAt (m : PolyExpr) (n : ℕ) (i : List Bool)
    (s : (NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)).Coins n) :
    (NUPPT.ofPolyTimeUniform (glPadSampleFun_poly F) (.add F.sample.coins m)).runAt n i s =
      pairEncode (F.sample.runAtL n i ((List.ofFn s).take (F.sample.coinLen n)))
        ((List.ofFn s).drop (F.sample.coinLen n)) := by
  simp only [NUPPT.runAt, NUPPT.ofPolyTimeUniform, NUPPT.output_ofPolyTime,
    glPadSampleFun, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, F.sample_uniform n,
    NUPPT.coinLen, NUPPT.runAtL]

end Collection

/-- The raw trapdoor inverter of the padded collection on the layout
`⟨⟨⟨1^n, ⟨t, ⟨y, r⟩⟩⟩, []⟩, s⟩`: run `Inv(1^n, ⟨t, y⟩; s)` and append `r`. -/
def glPadInvFun (T : TrapdoorCollection) (z : List Bool) : List Bool :=
  pairEncode
    (T.inv.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))) []
      (NUPPT.inCoins z)))
    (pairSndD (pairSndD (NUPPT.inArg z)))

/-- The raw trapdoor inverter of the padded collection is polynomial-time. -/
theorem glPadInvFun_poly (T : TrapdoorCollection) : PolyTimeComputable (glPadInvFun T) :=
  (T.inv.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
        NUPPT.polyTimeComputable_inArg)))
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).pairEncode
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      NUPPT.polyTimeComputable_inArg))

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State loops for the hard-core predicate theorems

The loop machines behind the Goldreich–Levin theorem [PS10, Theorem 87.3]: the guarded state
iteration `polyTimeComputable_stateIterate` (an instance of
`Complexity.polyTimeComputable_iterate` on the length-guarded step
`Complexity.StateLoop.gstep`), the block encoding `blocksStr` of a tuple of equal-length bit
strings, the **selective block XOR** `selXorFun` computing `⊕_{t : β_t = 1} s_t` on
`⟨⟨1^m, β⟩, s⟩` — the subset XOR `S_L` of [PS10, Algorithm 89.6] and, with one-bit blocks, the
inner product `⟨x, r⟩` of [PS10, Fact 88.4] (`ipFun`) — and unary halving `1^n ↦ 1^{⌊n/2⌋}`
(`unaryHalf`, for the balanced permutation of `Asymptotic/HardCorePermutation.lean`).

Each loop is specified by the closed form of its orbit on well-formed inputs
(`SelXor.orbit_eq`), its stabilisation (`SelXor.orbit_stable`) and the length bound that
keeps the guard of `gstep` from firing (`SelXor.orbit_length_le`).

## Main definitions

* `TCSlib.Cryptography.blocksEquiv`, `TCSlib.Cryptography.blocksStr` — tuples of blocks as
  one bit string.
* `TCSlib.Cryptography.selXorFun`, `TCSlib.Cryptography.SelXor.partialSum` — the selective
  block XOR and its partial sums.
* `TCSlib.Cryptography.ipFun`, `TCSlib.Cryptography.unaryHalf` — the inner-product evaluator
  and unary halving.

## Main results

* `TCSlib.Cryptography.polyTimeComputable_stateIterate` — guarded state iteration is
  polynomial-time.
* `TCSlib.Cryptography.selXorFun_poly`, `TCSlib.Cryptography.selXorFun_input` — the selective
  block XOR is polynomial-time and computes the subset XOR.
* `TCSlib.Cryptography.ipFun_poly`, `TCSlib.Cryptography.ipFun_ofFn` — the inner-product
  evaluator is polynomial-time and computes `⟨x, r⟩`.
* `TCSlib.Cryptography.unaryHalf_poly` — unary halving is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

/-! ## State loops run for a fixed number of rounds -/

/-- **Guarded state iteration.** A state word `⟨x, s⟩` retains the input `x` and evolves its
state from `start x` by the length-guarded step `Complexity.StateLoop.gstep step B`; running it
for `|⟨x, start x⟩|` rounds and reading `out` is polynomial-time (instance of
`Complexity.polyTimeComputable_iterate`, the orbit bound being `StateLoop.length_gstep_iterate_le`).
On inputs whose genuine orbit stays within `B|x|` the guard never fires
(`StateLoop.gstep_iterate_eq`), which is how each loop below is identified with its closed
form. (The pattern of `Complexity.polyTimeComputable_stateFind`, `Randomized/Repetition.lean`,
with a fixed round count instead of an acceptance test.) -/
theorem polyTimeComputable_stateIterate {start step out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hout : PolyTimeComputable out) (B : PolyExpr) :
    PolyTimeComputable fun x =>
      out ((gstep step B)^[(pairEncode x (start x)).length] (pairEncode x (start x))) := by
  have hF := polyTimeComputable_iterate (gstep_poly hstep B) .var (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  exact hout.comp (hF.comp hpre)

/-- Bitwise XOR of two polynomial-time maps is polynomial-time
(`Complexity.polyTimeComputable_pairXor` on the pair). -/
theorem zipXor_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => List.zipWith xor (a w) (b w) := by
  convert polyTimeComputable_pairXor.comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Blocks of bit strings -/

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (private copy of
`FunFamily.blocks`, `Asymptotic/OneWay.lean`). -/
def blocksEquiv (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The inverse of `blocksEquiv` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquiv_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (p : Fin (q * ℓ)) :
    (blocksEquiv q ℓ).symm t p = t p.divNat p.modNat := rfl

/-- The encoding of a tuple of `k` blocks of `m` bits as one string of `k · m` bits. -/
def blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) : List Bool :=
  List.ofFn ((blocksEquiv k m).symm s)

/-- The length of the block encoding. -/
@[simp] theorem length_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) :
    (blocksStr s).length = k * m := List.length_ofFn

/-- Block `i` of the block encoding: the `m` bits after the first `i · m`. 

**Proof sketch.** `List.ext_getElem`: the length is `min m (k·m − i·m) = m`; position `j` of the block is position `i·m + j` of the encoding, whose block index is `i` and offset `j` (`Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right`). -/
theorem take_drop_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) (i : Fin k) :
    ((blocksStr s).drop (i * m)).take m = List.ofFn (s i) := by
  have hm : 0 < m ∨ m = 0 := by omega
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_take, List.length_drop, length_blocksStr, List.length_ofFn]
    have := i.isLt
    rcases hm with hm | hm
    · refine min_eq_left ?_
      rw [← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left m (by omega)
    · simp [hm]
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_take, List.getElem_drop, blocksStr, List.getElem_ofFn,
      blocksEquiv_symm_apply]
    have hmpos : 0 < m := by omega
    congr 1
    · refine Fin.ext ?_
      simp only [Fin.coe_divNat]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hmpos, Nat.div_eq_of_lt hj₂, zero_add]
    · refine Fin.ext ?_
      simp only [Fin.coe_modNat]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj₂]

/-- The block encoding of a tuple of one-bit blocks is the string of the bits. -/
theorem blocksStr_one {k : ℕ} (r : Fin k → Bool) :
    blocksStr (fun t (_ : Fin 1) => r t) = List.ofFn r := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [blocksStr, List.getElem_ofFn, blocksEquiv_symm_apply]
  congr 1
  exact Fin.ext (by simp [Fin.coe_divNat])

/-- Bitwise XOR of two encoded strings is the encoding of the pointwise sum (`Bool` as a
Boolean ring, `+` is XOR). -/
theorem zipWith_xor_ofFn_add {m : ℕ} (a b : Fin m → Bool) :
    List.zipWith xor (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_zipWith, List.getElem_ofFn, Pi.add_apply]
  rfl

/-! ## The selective block XOR `⊕_{t : β_t = 1} s_t` -/

namespace SelXor

/-- The partial subset sum `∑_{t < i, β_t = 1} s_t` of the blocks `s_t`, by recursion on `i`. -/
def partialSum {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : ℕ → (Fin m → Bool)
  | 0 => 0
  | i + 1 => partialSum β s i + if h : i < k then (if β ⟨i, h⟩ then s ⟨i, h⟩ else 0) else 0

/-- The partial sum is the subset sum over the indices `t < i` with `β_t = 1`. 

**Proof sketch.** Induction on `i`; the filter at `i + 1` splits the term `t = i` off the filter at `i` (`Finset.sum_filter`, `Finset.sum_add_distrib`, `Finset.sum_eq_single`). -/
theorem partialSum_eq {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    partialSum β s i = ∑ t ∈ univ.filter (fun t : Fin k => (t : ℕ) < i ∧ β t = true), s t := by
  induction i with
  | zero => simp [partialSum]
  | succ i ih =>
    rw [partialSum, ih, Finset.sum_filter, Finset.sum_filter]
    by_cases hi : i < k
    · rw [dif_pos hi]
      have hsplit : ∀ t : Fin k,
          (if (t : ℕ) < i + 1 ∧ β t = true then s t else 0) =
            (if (t : ℕ) < i ∧ β t = true then s t else 0) +
              (if t = ⟨i, hi⟩ ∧ β t = true then s t else 0) := by
        intro t
        by_cases ht : t = ⟨i, hi⟩
        · subst ht
          simp
        · have ht' : (t : ℕ) ≠ i := fun h => ht (Fin.ext h)
          by_cases hb : β t = true
          · by_cases hlt : (t : ℕ) < i
            · simp [hlt, hb, ht, Nat.lt_succ_of_lt hlt]
            · have : ¬ (t : ℕ) < i + 1 := by omega
              simp [hlt, hb, ht, this]
          · simp [hb]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single ⟨i, hi⟩ (fun t _ ht => by simp [ht]) (fun h => absurd (mem_univ _) h)]
      simp
    · rw [dif_neg hi, add_zero]
      refine Finset.sum_congr rfl fun t _ => ?_
      have : ((t : ℕ) < i + 1 ↔ (t : ℕ) < i) := by have := t.isLt; omega
      simp [this]


/-- The initial state on the input `⟨⟨1^m, β⟩, s⟩`: `⟨β, ⟨s, 1^m ⊕ 1^m⟩⟩` (the accumulator starts
at `0^m`). -/
def start (x : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD x))
    (pairEncode (pairSndD x) (List.zipWith xor (pairFstD (pairFstD x)) (pairFstD (pairFstD x))))

/-- The step on the state word `⟨⟨⟨1^m, β⟩, s⟩, ⟨β', ⟨s', acc⟩⟩⟩`: if `β'` is empty, stay;
otherwise consume its first bit `b`, drop one block of `m` bits from `s'`, and XOR that block
into `acc` when `b = 1`. -/
def step (w : List Bool) : List Bool :=
  if pairFstD (pairSndD w) = [] then pairSndD w else
    pairEncode (pairFstD (pairSndD w)).tail
      (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
        (if (pairFstD (pairSndD w)).headD false then
          List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
            ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
        else pairSndD (pairSndD (pairSndD w))))

/-- The output: the accumulator of the final state word. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The length bound on the states of the loop. -/
def bound : PolyExpr := .mul (.const 2) .var

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_pairSndD.pairEncode
      (zipXor_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- The step is polynomial-time (`polyTimeComputable_ite` on the emptiness test, the FP
toolkit of `Complexity.StateLoop`, `takeLen_poly`/`dropLen_poly` and `zipXor_poly`). 

**Proof sketch.** The branch on `β' = []` is `polyTimeComputable_ite` with `isNil_poly`; the body pairs `tail_poly` with the dropped block (`dropLen_poly`) and the conditional XOR (`polyTimeComputable_ite` on `headBit_poly`, `zipXor_poly` with `takeLen_poly`). -/
theorem step_poly : PolyTimeComputable step := by
  have hβ : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have htest : PolyTimeComputable fun w => [decide (pairFstD (pairSndD w) = [])] := isNil_poly.comp hβ
  have hhead : PolyTimeComputable fun w => [(pairFstD (pairSndD w)).headD false] :=
    headBit_poly.comp hβ
  have hbody : PolyTimeComputable fun w =>
      pairEncode (pairFstD (pairSndD w)).tail
        (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
          (if (pairFstD (pairSndD w)).headD false then
            List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
              ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
          else pairSndD (pairSndD (pairSndD w)))) :=
    (tail_poly.comp hβ).pairEncode ((dropLen_poly hu hs).pairEncode
      (polyTimeComputable_ite hhead (zipXor_poly hacc (takeLen_poly hu hs)) hacc))
  convert polyTimeComputable_ite htest polyTimeComputable_pairSndD hbody using 1
  funext w
  simp only [step, decide_eq_true_eq]

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The well-formed input `⟨⟨1^m, β⟩, s⟩` for `β ∈ {0,1}^k` and `k` blocks `s_t ∈ {0,1}^m`. -/
def input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)

/-- The closed form of the orbit on a well-formed input, for `i ≤ k` rounds:
`⟨β.drop i, ⟨s.drop (i·m), partialSum β s i⟩⟩`. 

**Proof sketch.** Induction on `i`: the initial accumulator `1^m ⊕ 1^m` is `0^m` (`List.zipWith_replicate`, `List.ofFn_const`); at round `i < k` the head of `β.drop i` is `β_i` (`List.drop_eq_getElem_cons`), the block is `take_drop_blocksStr`, and the accumulator update is `zipWith_xor_ofFn_add` against the recursion of `partialSum`. -/
theorem orbit_eq (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) (hi : i ≤ k) :
    orbit start step (input m β s) i =
      pairEncode ((List.ofFn β).drop i)
        (pairEncode ((blocksStr s).drop (i * m)) (List.ofFn (partialSum β s i))) := by
  induction i with
  | zero =>
    simp only [orbit_zero, start, input, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_zero,
      Nat.zero_mul, partialSum, List.zipWith_replicate, Nat.min_self]
    congr 2
    rw [Bool.xor_self]
    exact (List.ofFn_const m false).symm
  | succ i ih =>
    have hi' : i < k := hi
    rw [orbit_succ, ih (Nat.le_of_succ_le hi)]
    unfold step
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, input, List.length_replicate]
    have hne : (List.ofFn β).drop i ≠ [] := by
      rw [Ne, List.drop_eq_nil_iff, List.length_ofFn]; omega
    rw [if_neg hne, List.tail_drop, List.drop_drop,
      List.drop_eq_getElem_cons (i := i) (l := List.ofFn β) (by rw [List.length_ofFn]; exact hi'),
      List.headD_cons, List.getElem_ofFn, take_drop_blocksStr s ⟨i, hi'⟩]
    congr 2
    · rw [Nat.succ_mul]
    · rw [partialSum, dif_pos hi']
      by_cases hb : β ⟨i, hi'⟩ = true
      · rw [if_pos hb, if_pos hb, zipWith_xor_ofFn_add]
      · rw [if_neg hb, if_neg hb, add_zero]

/-- After `k` rounds the loop is stationary (`β'` is exhausted). -/
theorem orbit_stable (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (j : ℕ) :
    orbit start step (input m β s) (k + j) = orbit start step (input m β s) k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, orbit_succ, ih, orbit_eq m β s k le_rfl]
    unfold step
    simp [List.drop_eq_nil_of_le]

/-- Every state of the loop on a well-formed input has length at most `2|input|`. -/
theorem orbit_length_le (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
  have key : ∀ i ≤ k, (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
    intro i hi
    rw [orbit_eq m β s i hi]
    simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, input,
      length_pairEncode, List.length_drop, List.length_ofFn, List.length_replicate, length_blocksStr]
    omega
  rcases le_or_gt i k with hi | hi
  · exact key i hi
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [orbit_stable]
    exact key k le_rfl

end SelXor

/-- **The selective block XOR**: on `⟨⟨1^m, β⟩, s⟩` with `β ∈ {0,1}^k` and `s` a string of `k`
blocks of `m` bits, output `⊕_{t : β_t = 1} s_t` (the subset XOR `S_L` of [PS10, Algorithm 89.6]
for `L = {t | β_t = 1}`, and the inner product `⟨x, r⟩` for `m = 1`). Realised as the guarded
state loop `SelXor.step` run for `|⟨x, start x⟩|` rounds. -/
def selXorFun (x : List Bool) : List Bool :=
  SelXor.out ((gstep SelXor.step SelXor.bound)^[(pairEncode x (SelXor.start x)).length]
    (pairEncode x (SelXor.start x)))

/-- The selective block XOR is polynomial-time. -/
theorem selXorFun_poly : PolyTimeComputable selXorFun :=
  polyTimeComputable_stateIterate SelXor.start_poly SelXor.step_poly SelXor.out_poly SelXor.bound

/-- **The selective block XOR computes the subset XOR**: on the well-formed input
`⟨⟨1^m, β⟩, s⟩` it outputs the encoding of `∑_{t : β_t = 1} s_t` (`Bool` as a Boolean ring).

**Proof sketch.** The genuine orbit is bounded (`SelXor.orbit_length_le`), so the guard never
fires (`StateLoop.gstep_iterate_eq`); the loop runs for `R ≥ k` rounds, is stationary after `k`
(`SelXor.orbit_stable`), and its state after `k` rounds is `SelXor.orbit_eq` with
`SelXor.partialSum_eq`. -/
theorem selXorFun_input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) :
    selXorFun (SelXor.input m β s) =
      List.ofFn (∑ t ∈ univ.filter (fun t : Fin k => β t = true), s t) := by
  unfold selXorFun
  set R := (pairEncode (SelXor.input m β s) (SelXor.start (SelXor.input m β s))).length with hR
  have hRk : k ≤ R := by
    rw [hR, length_pairEncode, SelXor.input, length_pairEncode, length_pairEncode, List.length_ofFn]
    omega
  rw [gstep_iterate_eq SelXor.start SelXor.step SelXor.bound _ R
    (fun i _ => SelXor.orbit_length_le m β s i) R le_rfl]
  obtain ⟨j, hj⟩ : ∃ j, R = k + j := ⟨R - k, by omega⟩
  rw [hj, SelXor.orbit_stable, SelXor.orbit_eq m β s k le_rfl, SelXor.out, pairSndD_pairEncode,
    pairSndD_pairEncode, pairSndD_pairEncode, SelXor.partialSum_eq]
  congr 2
  refine Finset.filter_congr fun t _ => ?_
  simp [t.isLt]

/-! ## The inner product `⟨x, r⟩` and unary halving -/

/-- The inner-product evaluator on `⟨x, r⟩`: the selective block XOR with one-bit blocks. -/
def ipFun (z : List Bool) : List Bool :=
  selXorFun (pairEncode (pairEncode [true] (pairFstD z)) (pairSndD z))

/-- Composition of polynomial-time functions, in applied form (so that the unifier never
unfolds the outer function; private copy of `ptc_comp` in `Randomized/Closure.lean`). -/
theorem ptcComp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The inner-product evaluator is polynomial-time. -/
theorem ipFun_poly : PolyTimeComputable ipFun := by
  have h := ptcComp (g := selXorFun) selXorFun_poly
    (((polyTimeComputable_const [true]).pairEncode polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  exact h

/-- `⟨x, r⟩ = ∑_{t : x_t = 1} r_t` in the Boolean ring `Bool`. -/
theorem ip_eq_sum_filter {k : ℕ} (x r : Fin k → Bool) :
    HardcoreBit.ip x r = ∑ t ∈ univ.filter (fun t : Fin k => x t = true), r t := by
  rw [HardcoreBit.ip, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases x t <;> cases r t <;> rfl

/-- **The inner-product evaluator computes `⟨x, r⟩`** on encoded strings of equal length. -/
theorem ipFun_ofFn {k : ℕ} (x r : Fin k → Bool) :
    ipFun (pairEncode (List.ofFn x) (List.ofFn r)) = [HardcoreBit.ip x r] := by
  unfold ipFun
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  have hin : pairEncode (pairEncode [true] (List.ofFn x)) (List.ofFn r) =
      SelXor.input 1 x (fun t (_ : Fin 1) => r t) := by
    rw [SelXor.input, blocksStr_one]
    rfl
  rw [hin, selXorFun_input, ip_eq_sum_filter, List.ofFn_succ, List.ofFn_zero, Finset.sum_apply]

/-- Unary halving `1^n ↦ 1^{⌊n/2⌋}`. -/
def unaryHalf (u : List Bool) : List Bool := List.replicate (u.length / 2) true

/-- Unary halving is polynomial-time: the block map with blocks of two symbols and the constant
emission `[true]` (`Complexity.polyTimeComputable_blockMap`) emits one `true` per full block. -/
theorem unaryHalf_poly : PolyTimeComputable unaryHalf := by
  convert (polyTimeComputable_blockMap (.const 2) (polyTimeComputable_const [true])).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) using 1
  funext u
  simp only [Function.comp_apply, pairSndD_pairEncode, PolyExpr.eval_const, unaryHalf, id]
  rw [← List.map_eq_flatMap, List.map_const', List.length_range]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreGL.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter as a machine

The recovery procedure of [PS10, Algorithm 89.6] (`HardcoreBit.guessRecover`,
[Gar26, Figure 2.5]) as a polynomial-time string function: for each bit position `i < m` and
each nonempty `L ⊆ [k]` it queries the predictor `A` on `⟨1^n, Y ‖ (S_L ⊕ e_i)⟩` with fresh
coins and votes `B_L ⊕ A(…)`; bit `i` is the majority of its `2^k − 1` votes. The
`m (2^k − 1)` rounds are one guarded state loop (`GLLoop`, run through
`polyTimeComputable_stateIterate`) whose rounds are driven by a **table** hard-wired as
advice: the list of all pairs `⟨e_i, β_L⟩` (`β_L` the indicator string of `L`) in a fixed
order (`glTable`), so that no counter arithmetic is needed; the subset XORs `S_L`, `B_L` are
`selXorFun`/`ipFun`, the majorities `Complexity.polyTimeComputable_blockMap` with
`Complexity.polyTimeComputable_majority`.

The nonempty subsets are enumerated by `nesubsetEquiv : NESubset k ≃ Fin (2^k − 1)`
(`Fintype.equivFin` and `HardcoreBit.card_nonempty_finset`); the coins of the machine split
as the `GuessCoins` of the concrete inverter followed by unread coins (`glCoinsEquiv`).

## Main definitions

* `TCSlib.Cryptography.nesubsetEquiv`, `TCSlib.Cryptography.betaOf` — the enumeration of the
  nonempty subsets of `[k]` and their indicator strings.
* `TCSlib.Cryptography.GLLoop.start`, `GLLoop.step`, `GLLoop.out` — the voting loop.
* `TCSlib.Cryptography.glVotesFun`, `TCSlib.Cryptography.glRecoverFun` — the votes of all
  rounds and the recovered string (majorities of the votes).

## Main results

* `TCSlib.Cryptography.GLLoop.orbit_eq` — the closed form of the voting loop.
* `TCSlib.Cryptography.glRecoverFun_input` — the recovered string is
  `List.ofFn (guessRecover A' k Y c)` on the well-formed input.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

/-! ## Enumerating the nonempty subsets -/

/-- The nonempty subsets of `[k]` enumerated by `Fin (2^k − 1)` (noncomputable; it only
indexes the advice table and the coin blocks). -/
noncomputable def nesubsetEquiv (k : ℕ) : HardcoreBit.NESubset k ≃ Fin (2 ^ k - 1) :=
  (Fintype.equivFin _).trans (finCongr (by rw [HardcoreBit.card_nonempty_finset, Fintype.card_fin]))

/-- The indicator string of the `j`-th nonempty subset. -/
noncomputable def betaOf {k : ℕ} (j : Fin (2 ^ k - 1)) : Fin k → Bool :=
  fun t => decide (t ∈ ((nesubsetEquiv k).symm j).1)

/-- The subset with indicator string `betaOf j` is the `j`-th nonempty subset. -/
theorem filter_betaOf {k : ℕ} (j : Fin (2 ^ k - 1)) :
    univ.filter (fun t : Fin k => betaOf j t = true) = ((nesubsetEquiv k).symm j).1 := by
  ext t
  simp [betaOf]

/-- The number of `true`s of an encoded string is the cardinality of its support. -/
theorem count_true_ofFn {M : ℕ} (v : Fin M → Bool) :
    (List.ofFn v).count true = #(univ.filter fun j : Fin M => v j = true) := by
  rw [Finset.card_filter]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun j => v j.succ), Fin.sum_univ_succ]
    cases v 0 <;> simp [add_comm]

/-! ## The voting loop -/

namespace GLLoop

/-- The fixed data of the loop: `⟨⟨⟨1^n, Y⟩, α⟩, ⟨⟨1^m, 1^k⟩, ⟨1^{|ρ|}, ⟨s, b⟩⟩⟩⟩` (the layout of
`A`'s input slots, then the unary lengths, the coins of `A` in unary and the `GuessCoins`
strings `s`, `b`). -/
def fixed (u Y α um uk ur s b : List Bool) : List Bool :=
  NUPPT.layout u Y α (pairEncode (pairEncode um uk) (pairEncode ur (pairEncode s b)))

/-- The input of the loop: the fixed data, the table and the coin blocks. -/
def input (fx tbl cs : List Bool) : List Bool := pairEncode fx (pairEncode tbl cs)

/-- The initial state `⟨tbl, ⟨cs, []⟩⟩`: the whole table, all coin blocks, no votes. -/
def start (x : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD x)) (pairEncode (pairSndD (pairSndD x)) [])

/-- The projections of the fixed data out of a state word `⟨⟨fx, ⟨tbl, cs⟩⟩, ⟨tbl', ⟨cs', votes⟩⟩⟩`. -/
def fx (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- The unary parameter `1^n`. -/
def pu (w : List Bool) : List Bool := NUPPT.inParam (fx w)

/-- The string `Y` passed to `A`. -/
def pY (w : List Bool) : List Bool := NUPPT.inArg (fx w)

/-- The advice of `A`. -/
def pα (w : List Bool) : List Bool := NUPPT.inAdvice (fx w)

/-- The unary block length `1^m`. -/
def pum (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inCoins (fx w)))

/-- The unary number of guessed bits `1^k`. -/
def puk (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inCoins (fx w)))

/-- The unary coin length `1^{|ρ|}` of `A`. -/
def pur (w : List Bool) : List Bool := pairFstD (pairSndD (NUPPT.inCoins (fx w)))

/-- The strings `s_1 ⋯ s_k`. -/
def ps (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (NUPPT.inCoins (fx w))))

/-- The guessed bits `b_1 ⋯ b_k`. -/
def pb (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (NUPPT.inCoins (fx w))))

/-- The remaining table. -/
def ptbl (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining coin blocks. -/
def pcs (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- The votes so far. -/
def pvotes (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The current table entry `⟨e_i, β_L⟩`: the first `|⟨1^m, 1^k⟩|` bits of the remaining table. -/
def entry (w : List Bool) : List Bool := (ptbl w).take (pairEncode (pum w) (puk w)).length

/-- The vote of the current round: `B_L ⊕ [A(1^n, Y ‖ (S_L ⊕ e_i); c) = 1]`. -/
def vote (A : NUPPT) (w : List Bool) : Bool :=
  xor ((ipFun (pairEncode (pairSndD (entry w)) (pb w))).headD false)
    (decide (A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) = [true]))

/-- The step: if the table is exhausted, stay; otherwise consume one entry and one coin block
and append the round's vote. -/
def step (A : NUPPT) (w : List Bool) : List Bool :=
  if ptbl w = [] then pairSndD w else
    pairEncode ((ptbl w).drop (pairEncode (pum w) (puk w)).length)
      (pairEncode ((pcs w).drop (pur w).length) (pvotes w ++ [vote A w]))

/-- The output: the votes of the final state. -/
def out (w : List Bool) : List Bool := pvotes w

/-- The length bound on the states. -/
def bound : PolyExpr := .add (.mul (.const 2) .var) (.const 2)

/-- When the table is exhausted the step is stationary. -/
theorem step_of_table_nil (A : NUPPT) (w : List Bool) (h : ptbl w = []) : step A w = pairSndD w := by
  unfold step
  rw [if_pos h]

/-- The projection `fx` is polynomial-time. -/
theorem fx_poly : PolyTimeComputable fx := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
/-- The projection `pu` is polynomial-time. -/
theorem pu_poly : PolyTimeComputable pu := NUPPT.polyTimeComputable_inParam.comp fx_poly
/-- The projection `pY` is polynomial-time. -/
theorem pY_poly : PolyTimeComputable pY := NUPPT.polyTimeComputable_inArg.comp fx_poly
/-- The projection `pα` is polynomial-time. -/
theorem pα_poly : PolyTimeComputable pα := NUPPT.polyTimeComputable_inAdvice.comp fx_poly
/-- The projection `pum` is polynomial-time. -/
theorem pum_poly : PolyTimeComputable pum :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `puk` is polynomial-time. -/
theorem puk_poly : PolyTimeComputable puk :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `pur` is polynomial-time. -/
theorem pur_poly : PolyTimeComputable pur :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `ps` is polynomial-time. -/
theorem ps_poly : PolyTimeComputable ps :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly)))
/-- The projection `pb` is polynomial-time. -/
theorem pb_poly : PolyTimeComputable pb :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly)))
/-- The projection `ptbl` is polynomial-time. -/
theorem ptbl_poly : PolyTimeComputable ptbl := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
/-- The projection `pcs` is polynomial-time. -/
theorem pcs_poly : PolyTimeComputable pcs :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
/-- The projection `pvotes` is polynomial-time. -/
theorem pvotes_poly : PolyTimeComputable pvotes :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
/-- The projection `entry` is polynomial-time. -/
theorem entry_poly : PolyTimeComputable entry :=
  takeLen_poly (pum_poly.pairEncode puk_poly) ptbl_poly


/-- The vote of a round is polynomial-time (`ipFun`, `selXorFun`, `A.output` on the layout,
the verdict test `polyTimeComputable_pairEq`). 

**Proof sketch.** The bit `B_L` is `headBit_poly` after `ipFun_poly`; the query is the pairing of `pY` with the XOR (`zipXor_poly`) of `selXorFun` and the unit vector; `A.output` on the layout is `A.polyTimeComputable_output` after `polyTimeComputable_layout`; the verdict test is `polyTimeComputable_pairEq`; the two bits are combined by `xor_poly`. -/
theorem vote_poly (A : NUPPT) : PolyTimeComputable fun w => [vote A w] := by
  have hβ : PolyTimeComputable fun w => pairSndD (entry w) :=
    polyTimeComputable_pairSndD.comp entry_poly
  have hB : PolyTimeComputable fun w => [(ipFun (pairEncode (pairSndD (entry w)) (pb w))).headD false] :=
    ptcComp headBit_poly (ptcComp ipFun_poly (hβ.pairEncode pb_poly))
  have hq : PolyTimeComputable fun w => pairEncode (pY w) (List.zipWith xor
      (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))) :=
    pY_poly.pairEncode (zipXor_poly (ptcComp selXorFun_poly ((pum_poly.pairEncode hβ).pairEncode ps_poly))
      (polyTimeComputable_pairFstD.comp entry_poly))
  have hans : PolyTimeComputable fun w => A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) :=
    ptcComp A.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout pu_poly hq pα_poly (takeLen_poly pur_poly pcs_poly))
  have htest : PolyTimeComputable fun w => [decide (A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hans.pairEncode (polyTimeComputable_const [true])) using 1
    funext w
    simp
  exact xor_poly hB htest

/-- The step is polynomial-time. -/
theorem step_poly (A : NUPPT) : PolyTimeComputable (step A) := by
  have hbody : PolyTimeComputable fun w =>
      pairEncode ((ptbl w).drop (pairEncode (pum w) (puk w)).length)
        (pairEncode ((pcs w).drop (pur w).length) (pvotes w ++ [vote A w])) :=
    (dropLen_poly (pum_poly.pairEncode puk_poly) ptbl_poly).pairEncode
      ((dropLen_poly pur_poly pcs_poly).pairEncode (pvotes_poly.append (vote_poly A)))
  have htest : PolyTimeComputable fun w => [decide (ptbl w = [])] := isNil_poly.comp ptbl_poly
  convert polyTimeComputable_ite htest polyTimeComputable_pairSndD hbody using 1
  funext w
  simp only [step, decide_eq_true_eq]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_const []))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := pvotes_poly


/-! ### The well-formed input and the closed form of the orbit -/

/-- The table entry for the round `p = (i, j)`: `⟨e_i, β_j⟩` with `e_i` the unit vector and `β_j`
the indicator string of the `j`-th nonempty subset. -/
noncomputable def glEntry (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) : List Bool :=
  pairEncode (List.ofFn (Pi.single p.divNat true : Fin m → Bool)) (List.ofFn (betaOf p.modNat))

/-- Every table entry has length `2m + 2 + k`. -/
theorem length_glEntry (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) :
    (glEntry m k p).length = 2 * m + 2 + k := by
  simp [glEntry, length_pairEncode]

/-- The table entry as a block of `2m + 2 + k` bits. -/
noncomputable def glEntryFn (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) : Fin (2 * m + 2 + k) → Bool :=
  fun v => (glEntry m k p).getD v false

/-- The block of an entry encodes the entry. -/
theorem ofFn_glEntryFn (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) :
    List.ofFn (glEntryFn m k p) = glEntry m k p := by
  refine List.ext_getElem (by simp [length_glEntry]) fun v hv₁ hv₂ => ?_
  simp [glEntryFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv₂]

/-- **The advice table** of all rounds: the entries `⟨e_i, β_j⟩` in the order of
`Fin (m · (2^k − 1))`. -/
noncomputable def glTable (m k : ℕ) : List Bool := blocksStr (glEntryFn m k)

/-- The well-formed loop input: the fixed data with `s`, `b`, the table, and the coin blocks
followed by unread coins `ex`. -/
noncomputable def wfInput (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool) :
    List Bool :=
  input (fixed (List.replicate n true) Y (A.advice n) (List.replicate m true)
    (List.replicate k true) (List.replicate (A.coinLen n) true) (blocksStr s) (List.ofFn b))
    (glTable m k) (blocksStr cs ++ ex)

/-- The vote of the round `p = (i, j)` on the well-formed input:
`B_{L_j} ⊕ [A(1^n, Y ‖ (S_{L_j} ⊕ e_i); c_p) = 1]`. -/
noncomputable def wfVote (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool)
    (p : Fin (m * (2 ^ k - 1))) : Bool :=
  xor (HardcoreBit.ip (betaOf p.modNat) b)
    (decide (A.runAtL n (pairEncode Y (List.ofFn
      (∑ t ∈ univ.filter (fun t : Fin k => betaOf p.modNat t = true), s t + Pi.single p.divNat true)))
      (List.ofFn (cs p)) = [true]))

section Spec

variable (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool) (b : Fin k → Bool)
  (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool)

/-- The fixed data of a well-formed state word. -/
theorem fx_wf (st : List Bool) : fx (pairEncode (wfInput A n m k Y s b cs ex) st) =
    fixed (List.replicate n true) Y (A.advice n) (List.replicate m true) (List.replicate k true)
      (List.replicate (A.coinLen n) true) (blocksStr s) (List.ofFn b) := by
  simp [fx, wfInput, input]

/-- The block `t` of the coin blocks followed by unread coins. -/
theorem take_drop_coins (t : ℕ) (ht : t < m * (2 ^ k - 1)) :
    (((blocksStr cs ++ ex).drop (t * A.coinLen n)).take (A.coinLen n)) = List.ofFn (cs ⟨t, ht⟩) := by
  have h1 : t * A.coinLen n ≤ (blocksStr cs).length := by
    rw [length_blocksStr]; exact Nat.mul_le_mul_right _ ht.le
  rw [List.drop_append_of_le_length h1, List.take_append_of_le_length, take_drop_blocksStr cs ⟨t, ht⟩]
  rw [List.length_drop, length_blocksStr]
  have : (t + 1) * A.coinLen n ≤ m * (2 ^ k - 1) * A.coinLen n := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at this
  omega

/-- Dropping one more block of the coin blocks followed by unread coins. -/
theorem drop_drop_coins (t : ℕ) :
    ((blocksStr cs ++ ex).drop (t * A.coinLen n)).drop (A.coinLen n) =
      (blocksStr cs ++ ex).drop ((t + 1) * A.coinLen n) := by
  rw [List.drop_drop, Nat.succ_mul]

/-- The closed form of the orbit on the well-formed input, for `t ≤ m (2^k − 1)` rounds:
`⟨table.drop (t · entry), ⟨coins.drop (t · |ρ|), votes of the first t rounds⟩⟩`. 

**Proof sketch.** Induction on `t`. The table is not exhausted before round `m(2^k − 1)` (`List.drop_eq_nil_iff`, `length_blocksStr`), so the step consumes the entry `t` (`take_drop_blocksStr`, `ofFn_glEntryFn`), whose components are `e_i` and `β_j`; the vote is `wfVote` by `ipFun_ofFn`, `selXorFun_input`, `zipWith_xor_ofFn_add`, `take_drop_coins` and `NUPPT.runAtL_eq_output_layout`; the table and coin components advance by `List.drop_drop` (`drop_drop_coins`) and the votes by `List.ofFn_succ'`. -/
theorem orbit_eq (t : ℕ) (ht : t ≤ m * (2 ^ k - 1)) :
    orbit start (step A) (wfInput A n m k Y s b cs ex) t =
      pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
        (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
          (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)) := by
  induction t with
  | zero =>
    simp [orbit_zero, start, wfInput, input]
  | succ t ih =>
    have ht' : t < m * (2 ^ k - 1) := ht
    rw [orbit_succ, ih (Nat.le_of_succ_le ht)]
    have hne : (glTable m k).drop (t * (2 * m + 2 + k)) ≠ [] := by
      rw [Ne, List.drop_eq_nil_iff, glTable, length_blocksStr]
      intro h
      have : (t + 1) * (2 * m + 2 + k) ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
        Nat.mul_le_mul_right _ ht'
      rw [Nat.succ_mul] at this
      omega
    have hentry : entry (pairEncode (wfInput A n m k Y s b cs ex)
        (pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
          (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
            (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)))) =
        glEntry m k ⟨t, ht'⟩ := by
      simp only [entry, ptbl, pairFstD_pairEncode, pairSndD_pairEncode, pum, puk, fx_wf, fixed,
        NUPPT.inCoins_layout, length_pairEncode, List.length_replicate, glTable]
      rw [take_drop_blocksStr (glEntryFn m k) ⟨t, ht'⟩, ofFn_glEntryFn]
    have hvote : vote A (pairEncode (wfInput A n m k Y s b cs ex)
        (pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
          (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
            (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)))) =
        wfVote A n m k Y s b cs ⟨t, ht'⟩ := by
      unfold vote
      rw [hentry]
      simp only [glEntry, pairFstD_pairEncode, pairSndD_pairEncode, pu, pY, pα, pum, pb, ps, pur,
        pcs, fx_wf, fixed, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
        NUPPT.inCoins_layout, List.length_replicate, ipFun_ofFn, List.headD_cons,
        take_drop_coins A n m k cs ex t ht']
      have hin : pairEncode (pairEncode (List.replicate m true)
          (List.ofFn (betaOf (Fin.modNat ⟨t, ht'⟩)))) (blocksStr s) =
          SelXor.input m (betaOf (Fin.modNat ⟨t, ht'⟩)) s := rfl
      rw [hin, selXorFun_input, zipWith_xor_ofFn_add, ← NUPPT.runAtL_eq_output_layout]
      rfl
    unfold step
    rw [if_neg (by simpa [ptbl] using hne), hvote]
    simp only [ptbl, pairFstD_pairEncode, pairSndD_pairEncode, pum, puk, pur, pcs, pvotes, fx_wf,
      fixed, NUPPT.inCoins_layout, length_pairEncode, List.length_replicate]
    refine congrArg₂ pairEncode ?_ (congrArg₂ pairEncode ?_ ?_)
    · rw [List.drop_drop, show t * (2 * m + 2 + k) + (2 * m + 2 + k) = (t + 1) * (2 * m + 2 + k) by ring]
    · exact drop_drop_coins A n m k cs ex t
    · rw [List.ofFn_succ', List.concat_eq_append]
      rfl

/-- After `m (2^k − 1)` rounds the loop is stationary (the table is exhausted). -/
theorem orbit_stable (j : ℕ) :
    orbit start (step A) (wfInput A n m k Y s b cs ex) (m * (2 ^ k - 1) + j) =
      orbit start (step A) (wfInput A n m k Y s b cs ex) (m * (2 ^ k - 1)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, orbit_succ, ih, orbit_eq A n m k Y s b cs ex _ le_rfl]
    have h0 : (glTable m k).drop (m * (2 ^ k - 1) * (2 * m + 2 + k)) = [] :=
      List.drop_eq_nil_of_le (by rw [glTable, length_blocksStr])
    rw [step_of_table_nil, pairSndD_pairEncode]
    simp only [ptbl, pairFstD_pairEncode, pairSndD_pairEncode]
    exact h0

/-- Every state of the loop on the well-formed input has length at most `2|input| + 2`. -/
theorem orbit_length_le (t : ℕ) :
    (orbit start (step A) (wfInput A n m k Y s b cs ex) t).length ≤
      bound.eval (wfInput A n m k Y s b cs ex).length := by
  have key : ∀ t ≤ m * (2 ^ k - 1), (orbit start (step A) (wfInput A n m k Y s b cs ex) t).length ≤
      bound.eval (wfInput A n m k Y s b cs ex).length := by
    intro t ht
    rw [orbit_eq A n m k Y s b cs ex t ht]
    simp only [bound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
      wfInput, input, length_pairEncode, List.length_drop, List.length_ofFn, glTable,
      length_blocksStr, List.length_append]
    have : t ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
      ht.trans (Nat.le_mul_of_pos_right _ (by omega))
    omega
  rcases le_or_gt t (m * (2 ^ k - 1)) with ht | ht
  · exact key t ht
  · obtain ⟨j, rfl⟩ : ∃ j, t = m * (2 ^ k - 1) + j := ⟨t - m * (2 ^ k - 1), by omega⟩
    rw [orbit_stable]
    exact key _ le_rfl

end Spec

end GLLoop

/-! ## The votes and the recovered string -/

/-- **The votes of all rounds**: the voting loop run for `|⟨x, start x⟩|` rounds. -/
def glVotesFun (A : NUPPT) (x : List Bool) : List Bool :=
  GLLoop.out ((gstep (GLLoop.step A) GLLoop.bound)^[(pairEncode x (GLLoop.start x)).length]
    (pairEncode x (GLLoop.start x)))

/-- The votes are polynomial-time. -/
theorem glVotesFun_poly (A : NUPPT) : PolyTimeComputable (glVotesFun A) :=
  polyTimeComputable_stateIterate GLLoop.start_poly (GLLoop.step_poly A) GLLoop.out_poly GLLoop.bound

/-- **The votes on the well-formed input** are the `m (2^k − 1)` round votes `wfVote`. -/
theorem glVotesFun_wfInput (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool) :
    glVotesFun A (GLLoop.wfInput A n m k Y s b cs ex) =
      List.ofFn (GLLoop.wfVote A n m k Y s b cs) := by
  unfold glVotesFun
  set R := (pairEncode (GLLoop.wfInput A n m k Y s b cs ex)
    (GLLoop.start (GLLoop.wfInput A n m k Y s b cs ex))).length with hR
  have hRk : m * (2 ^ k - 1) ≤ R := by
    rw [hR, length_pairEncode, GLLoop.wfInput, GLLoop.input, length_pairEncode, length_pairEncode,
      GLLoop.glTable, length_blocksStr]
    have : m * (2 ^ k - 1) ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [gstep_iterate_eq GLLoop.start (GLLoop.step A) GLLoop.bound _ R
    (fun i _ => GLLoop.orbit_length_le A n m k Y s b cs ex i) R le_rfl]
  obtain ⟨j, hj⟩ : ∃ j, R = m * (2 ^ k - 1) + j := ⟨R - m * (2 ^ k - 1), by omega⟩
  rw [hj, GLLoop.orbit_stable, GLLoop.orbit_eq A n m k Y s b cs ex _ le_rfl, GLLoop.out,
    GLLoop.pvotes, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- The majority of each block of `|fst z|` bits of `snd z` (the function of
`Complexity.polyTimeComputable_blockMap` with `Complexity.polyTimeComputable_majority`). -/
def glMajFun (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / (pairFstD z).length)).flatMap fun i =>
    [decide ((((pairSndD z).drop (i * (pairFstD z).length)).take (pairFstD z).length).length <
      2 * (((pairSndD z).drop (i * (pairFstD z).length)).take (pairFstD z).length).count true)]

/-- The blockwise majority is polynomial-time. -/
theorem glMajFun_poly : PolyTimeComputable glMajFun :=
  polyTimeComputable_blockMap .var polyTimeComputable_majority

/-- **The blockwise majority of the votes** `W : Fin m → Fin M → Bool`, with block length `M`
(given in unary), is the string of the majorities `majority (W i)`, provided `M > 0` or `m = 0`. -/
theorem glMajFun_blocksStr {m M : ℕ} (hM : 0 < M ∨ m = 0) (W : Fin m → Fin M → Bool) :
    glMajFun (pairEncode (List.replicate M true) (blocksStr W)) =
      List.ofFn fun i : Fin m => HardcoreBit.majority (W i) := by
  unfold glMajFun
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, length_blocksStr]
  have hdiv : m * M / M = m := by
    rcases hM with hM | rfl
    · exact Nat.mul_div_cancel m hM
    · simp
  rw [hdiv, ← List.map_eq_flatMap]
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [take_drop_blocksStr W ⟨j, by simpa using hj₂⟩, List.length_ofFn, count_true_ofFn,
    HardcoreBit.majority, Fintype.card_fin]

/-- Unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{ab}` as a string function
(`Turing.FinTM.computesFunInTime_unaryMul`). -/
def unaryMulFun (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, v) => List.replicate (u.length * v.length) true
  | none => []

/-- Unary multiplication is polynomial-time. -/
theorem unaryMulFun_poly : PolyTimeComputable unaryMulFun := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  exact ⟨M, c, 2, hM⟩

/-- Unary multiplication on a pair of unary strings. -/
theorem unaryMulFun_pairEncode (a b : ℕ) :
    unaryMulFun (pairEncode (List.replicate a true) (List.replicate b true)) =
      List.replicate (a * b) true := by
  simp [unaryMulFun, pairDecode_pairEncode]


end TCSlib.Cryptography

/-! ## The Goldreich–Levin recovery machine -/

namespace Complexity.NUPPT

/-- **Pre-processing as a definition** (the witness of `exists_comp` with `post = id`): the
machine with `A`'s coins and advice that runs `A(1^n, pre y)`. -/
noncomputable def precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    NUPPT :=
  ofPolyTime (A.polyTimeComputable_output.comp
    (polyTimeComputable_layout polyTimeComputable_inParam (hpre.comp polyTimeComputable_inArg)
      polyTimeComputable_inAdvice polyTimeComputable_inCoins)) A.coins A.adv A.advice A.advice_length

/-- The pre-processed machine has the coins of `A`. -/
@[simp] theorem coins_precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    (A.precomp hpre).coins = A.coins := rfl

/-- The activation of the pre-processed machine. -/
theorem runAtL_precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) : (A.precomp hpre).runAtL n y r = A.runAtL n (pre y) r := by
  unfold precomp
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

namespace GLRaw

/-- The Goldreich–Levin advice `⟨1^k, ⟨1^M, table⟩⟩` slot of the raw input. -/
def adv (z : List Bool) : List Bool := pairFstD (NUPPT.inAdvice z)

/-- The advice of `A`. -/
def α (z : List Bool) : List Bool := pairSndD (NUPPT.inAdvice z)

/-- The unary `1^k`. -/
def uk (z : List Bool) : List Bool := pairFstD (adv z)

/-- The unary `1^M`, `M = 2^k − 1`. -/
def uM (z : List Bool) : List Bool := pairFstD (pairSndD (adv z))

/-- The table. -/
def tbl (z : List Bool) : List Bool := pairSndD (pairSndD (adv z))

/-- The unary block length `1^{m(n)}`. -/
def um (mP : PolyExpr) (z : List Bool) : List Bool :=
  List.replicate (mP.eval (NUPPT.inParam z).length) true

/-- The unary coin length `1^{|ρ|}` of `A`. -/
def ur (A : NUPPT) (z : List Bool) : List Bool :=
  List.replicate (A.coins.eval (NUPPT.inParam z).length) true

/-- The unary `1^{k·m}`. -/
def ukm (mP : PolyExpr) (z : List Bool) : List Bool := unaryMulFun (pairEncode (uk z) (um mP z))

/-- The strings `s_1 ⋯ s_k`: the first `k·m` coins. -/
def cs₁ (mP : PolyExpr) (z : List Bool) : List Bool := (NUPPT.inCoins z).take (ukm mP z).length

/-- The coins after the first `k·m`. -/
def r₁ (mP : PolyExpr) (z : List Bool) : List Bool := (NUPPT.inCoins z).drop (ukm mP z).length

/-- The guessed bits `b_1 ⋯ b_k`: the next `k` coins. -/
def cb (mP : PolyExpr) (z : List Bool) : List Bool := (r₁ mP z).take (uk z).length

/-- The remaining coins: the blocks for the calls of `A`. -/
def cs₂ (mP : PolyExpr) (z : List Bool) : List Bool := (r₁ mP z).drop (uk z).length

/-- The projection `adv` is polynomial-time. -/
theorem adv_poly : PolyTimeComputable adv := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice
/-- The projection `α` is polynomial-time. -/
theorem α_poly : PolyTimeComputable α := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
/-- The projection `uk` is polynomial-time. -/
theorem uk_poly : PolyTimeComputable uk := polyTimeComputable_pairFstD.comp adv_poly
/-- The projection `uM` is polynomial-time. -/
theorem uM_poly : PolyTimeComputable uM :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp adv_poly)
/-- The projection `tbl` is polynomial-time. -/
theorem tbl_poly : PolyTimeComputable tbl :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp adv_poly)
/-- The projection `um` is polynomial-time. -/
theorem um_poly (mP : PolyExpr) : PolyTimeComputable (um mP) := by
  unfold um
  exact ptcComp (g := fun x => List.replicate (mP.eval x.length) true)
    (polyTimeComputable_unaryPoly mP) NUPPT.polyTimeComputable_inParam
/-- The projection `ur` is polynomial-time. -/
theorem ur_poly (A : NUPPT) : PolyTimeComputable (ur A) := by
  unfold ur
  exact ptcComp (g := fun x => List.replicate (A.coins.eval x.length) true)
    (polyTimeComputable_unaryPoly A.coins) NUPPT.polyTimeComputable_inParam
/-- The projection `ukm` is polynomial-time. -/
theorem ukm_poly (mP : PolyExpr) : PolyTimeComputable (ukm mP) := by
  unfold ukm
  exact ptcComp (g := unaryMulFun) unaryMulFun_poly (uk_poly.pairEncode (um_poly mP))
/-- The projection `cs₁` is polynomial-time. -/
theorem cs₁_poly (mP : PolyExpr) : PolyTimeComputable (cs₁ mP) :=
  takeLen_poly (ukm_poly mP) NUPPT.polyTimeComputable_inCoins
/-- The projection `r₁` is polynomial-time. -/
theorem r₁_poly (mP : PolyExpr) : PolyTimeComputable (r₁ mP) :=
  dropLen_poly (ukm_poly mP) NUPPT.polyTimeComputable_inCoins
/-- The projection `cb` is polynomial-time. -/
theorem cb_poly (mP : PolyExpr) : PolyTimeComputable (cb mP) := takeLen_poly uk_poly (r₁_poly mP)
/-- The projection `cs₂` is polynomial-time. -/
theorem cs₂_poly (mP : PolyExpr) : PolyTimeComputable (cs₂ mP) := dropLen_poly uk_poly (r₁_poly mP)

end GLRaw

/-- **The raw recovery function** on the layout `⟨⟨⟨1^n, Y⟩, ⟨⟨1^k, ⟨1^M, table⟩⟩, α⟩⟩, r⟩`:
split the coins into `s` (`k·m` bits), `b` (`k` bits) and the call blocks, run the voting loop
on the fixed data `⟨⟨⟨1^n, Y⟩, α⟩, ⟨⟨1^m, 1^k⟩, ⟨1^{|ρ|}, ⟨s, b⟩⟩⟩⟩`, the table and the blocks,
and take the blockwise majority with block length `M`. -/
def glRawFun (A : NUPPT) (mP : PolyExpr) (z : List Bool) : List Bool :=
  glMajFun (pairEncode (GLRaw.uM z) (glVotesFun A (GLLoop.input
    (GLLoop.fixed (NUPPT.inParam z) (NUPPT.inArg z) (GLRaw.α z) (GLRaw.um mP z) (GLRaw.uk z)
      (GLRaw.ur A z) (GLRaw.cs₁ mP z) (GLRaw.cb mP z))
    (GLRaw.tbl z) (GLRaw.cs₂ mP z))))

/-- The raw recovery function is polynomial-time. -/
theorem glRawFun_poly (A : NUPPT) (mP : PolyExpr) : PolyTimeComputable (glRawFun A mP) := by
  unfold glRawFun
  exact ptcComp (g := glMajFun) glMajFun_poly (GLRaw.uM_poly.pairEncode
    (ptcComp (g := glVotesFun A) (glVotesFun_poly A)
      ((NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
        NUPPT.polyTimeComputable_inArg GLRaw.α_poly
        (((GLRaw.um_poly mP).pairEncode GLRaw.uk_poly).pairEncode
          ((GLRaw.ur_poly A).pairEncode ((GLRaw.cs₁_poly mP).pairEncode (GLRaw.cb_poly mP))))).pairEncode
        (GLRaw.tbl_poly.pairEncode (GLRaw.cs₂_poly mP)))))

/-- The Goldreich–Levin advice at `n`: `⟨1^{k(n)}, ⟨1^{2^{k(n)} − 1}, table⟩⟩`. -/
noncomputable def glAdvice (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (List.replicate (k n) true)
    (pairEncode (List.replicate (2 ^ k n - 1) true) (GLLoop.glTable (mP.eval n) (k n)))

/-- The coin polynomial of the recovery machine: `K·m + K + m·K·ρ`, a majorant of
`k·m + k + m(2^k − 1)·|ρ|` when `2^k ≤ K`. -/
def glCoins (mP K : PolyExpr) (A : NUPPT) : PolyExpr :=
  .add (.mul K mP) (.add K (.mul mP (.mul K A.coins)))

/-- The advice polynomial of the recovery machine. -/
def glAdvPoly (mP K : PolyExpr) (A : NUPPT) : PolyExpr :=
  .add (.mul (.const 2) (.add (.add (.mul (.const 4) K) (.const 4))
    (.mul (.mul mP K) (.add (.add (.mul (.const 2) mP) (.const 2)) K)))) (.add (.const 2) A.adv)

/-- `k ≤ 2^k`. -/
theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le

/-- The advice of the recovery machine is polynomially bounded. -/
theorem length_glAdvice_le (mP K : PolyExpr) (A : NUPPT) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) : (pairEncode (glAdvice mP k n) (A.advice n)).length ≤ (glAdvPoly mP K A).eval n := by
  have hK := hk n
  have hkK : k n ≤ K.eval n := (le_two_pow (k n)).trans hK
  have hMK : 2 ^ k n - 1 ≤ K.eval n := (Nat.sub_le _ _).trans hK
  have hA := A.advice_length n
  simp only [glAdvice, glAdvPoly, length_pairEncode, List.length_replicate, GLLoop.glTable,
    length_blocksStr, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have htbl : mP.eval n * (2 ^ k n - 1) * (2 * mP.eval n + 2 + k n) ≤
      mP.eval n * K.eval n * (2 * mP.eval n + 2 + K.eval n) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hMK) (by omega)
  omega

/-- **The Goldreich–Levin recovery machine** [PS10, Algorithm 89.6] for a predictor `A`, the
block length `mP`, the guess count `k` with `2^{k(n)} ≤ K(n)`: advice `⟨glAdvice, A.advice n⟩`,
coins `glCoins`, output function `glRawFun`. -/
noncomputable def glMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  NUPPT.ofPolyTime (glRawFun_poly A mP) (glCoins mP K A) (glAdvPoly mP K A)
    (fun n => pairEncode (glAdvice mP k n) (A.advice n)) (length_glAdvice_le mP K A k hk)

/-- The coins of the recovery machine. -/
@[simp] theorem coins_glMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : (glMachine A mP K k hk).coins = glCoins mP K A := rfl

/-- The number of coins actually read by the recovery machine at `n`. -/
def glNeed (A : NUPPT) (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  k n * mP.eval n + (k n + mP.eval n * (2 ^ k n - 1) * A.coinLen n)

/-- The coins read are at most the coins available. -/
theorem glNeed_le (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) :
    glNeed A mP k n ≤ (glCoins mP K A).eval n := by
  have hK := hk n
  have hkK : k n ≤ K.eval n := (le_two_pow (k n)).trans hK
  have hMK : 2 ^ k n - 1 ≤ K.eval n := (Nat.sub_le _ _).trans hK
  simp only [glNeed, glCoins, PolyExpr.eval_add, PolyExpr.eval_mul, NUPPT.coinLen]
  have h1 : k n * mP.eval n ≤ K.eval n * mP.eval n := Nat.mul_le_mul_right _ hkK
  have h2 : mP.eval n * (2 ^ k n - 1) * A.coins.eval n ≤ mP.eval n * (K.eval n * A.coins.eval n) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hMK)
  omega

/-- **The recovery machine on well-formed coins** `s ‖ b ‖ blocks ‖ extra` computes the
blockwise majorities of the round votes: bit `i` is the majority over `j` of
`wfVote (i, j)`. 

**Proof sketch.** Unfold `runAtL_ofPolyTime` and the projections of the raw layout; the coin cuts at `k·m` (`unaryMulFun_pairEncode`) and `k` are `List.take_left'`/`drop_left'` on the concatenation `hr`; the loop input is `GLLoop.wfInput`, so the votes are `glVotesFun_wfInput`, which is `blocksStr` of the votes indexed by `finProdFinEquiv`; conclude with `glMajFun_blocksStr`. -/
theorem glMachine_runAt (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) (Y : List Bool) (s : Fin (k n) → Fin (mP.eval n) → Bool) (b : Fin (k n) → Bool)
    (cs : Fin (mP.eval n * (2 ^ k n - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool)
    (r : (glMachine A mP K k hk).Coins n)
    (hr : List.ofFn r = blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex)
    (hM : 0 < 2 ^ k n - 1 ∨ mP.eval n = 0) :
    (glMachine A mP K k hk).runAt n Y r =
      List.ofFn fun i : Fin (mP.eval n) => HardcoreBit.majority fun j : Fin (2 ^ k n - 1) =>
        GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs (finProdFinEquiv (i, j)) := by
  rw [NUPPT.runAt_eq]
  unfold glMachine
  rw [NUPPT.runAtL_ofPolyTime]
  unfold glRawFun
  simp only [GLRaw.uM, GLRaw.adv, GLRaw.α, GLRaw.uk, GLRaw.tbl, GLRaw.um, GLRaw.ur, GLRaw.ukm,
    GLRaw.cs₁, GLRaw.r₁, GLRaw.cb, GLRaw.cs₂, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, glAdvice,
    List.length_replicate, unaryMulFun_pairEncode, hr]
  have h1 : (blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex).take (k n * mP.eval n) = blocksStr s := by
    simp only [List.append_assoc]
    exact List.take_left' (length_blocksStr s)
  have h2 : (blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex).drop (k n * mP.eval n) =
      List.ofFn b ++ (blocksStr cs ++ ex) := by
    simp only [List.append_assoc]
    exact List.drop_left' (length_blocksStr s)
  rw [h1, h2, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  have hin : GLLoop.input (GLLoop.fixed (List.replicate n true) Y (A.advice n)
      (List.replicate (mP.eval n) true) (List.replicate (k n) true)
      (List.replicate (A.coins.eval n) true) (blocksStr s) (List.ofFn b))
      (GLLoop.glTable (mP.eval n) (k n)) (blocksStr cs ++ ex) =
      GLLoop.wfInput A n (mP.eval n) (k n) Y s b cs ex := rfl
  rw [hin, glVotesFun_wfInput]
  have hW : List.ofFn (GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs) =
      blocksStr fun i j => GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs (finProdFinEquiv (i, j)) := by
    unfold blocksStr
    congr 1
    funext p
    rw [blocksEquiv_symm_apply]
    congr 1
    exact (finProdFinEquiv.apply_symm_apply p).symm
  rw [hW, glMajFun_blocksStr hM]


/-! ## A bound on powers of two -/

/-- `2^{size x} ≤ 2x + 1`. -/
theorem two_pow_size_le (x : ℕ) : 2 ^ Nat.size x ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hpos : 0 < Nat.size x := Nat.size_pos.mpr hx
    have h := Nat.lt_size.mp (Nat.sub_lt hpos Nat.one_pos)
    calc 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ ≤ 2 * x + 1 := by omega


/-! ## Majorities under reindexing -/

/-- The majority is invariant under a bijective reindexing of the votes. -/
theorem majority_comp_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ'] (σ : κ' ≃ κ) (v : κ → Bool) :
    HardcoreBit.majority (fun x => v (σ x)) = HardcoreBit.majority v := by
  classical
  unfold HardcoreBit.majority
  have hcard : #(univ.filter fun x => v (σ x) = true) = #(univ.filter fun y => v y = true) := by
    rw [← Finset.card_map σ.toEmbedding]
    congr 1
    ext y
    simp [Finset.mem_map_equiv]
  rw [Fintype.card_congr σ, hcard]

/-! ## The coins of the recovery machine as `GuessCoins` -/

/-- A tuple of blocks with values in an arbitrary type as a function of the flattened index
(`blocksEquiv` for an arbitrary codomain). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- The coins of the concrete inverter (`GuessCoins`) together with unread coins, as the coin
string of the recovery machine: `s` as `k` blocks of `m` bits, then `b`, then the call blocks
indexed by `(i, j)` with `j` the enumeration of the subsets, then the unread coins. -/
noncomputable def glCoinsEquiv (A : NUPPT) (n m k Q : ℕ)
    (hQ : k * m + (k + m * (2 ^ k - 1) * A.coinLen n) ≤ Q) :
    HardcoreBit.GuessCoins m k (A.Coins n) × (Fin (Q - (k * m + (k + m * (2 ^ k - 1) * A.coinLen n))) → Bool) ≃
      (Fin Q → Bool) :=
  ((((blocksEquiv k m).symm.prodCongr ((Equiv.refl (Fin k → Bool)).prodCongr
      (((Equiv.refl (Fin m)).arrowCongr ((nesubsetEquiv k).arrowCongr (Equiv.refl (A.Coins n)))).trans
        ((blocksEquivX m (2 ^ k - 1) (A.Coins n)).symm.trans
          (blocksEquiv (m * (2 ^ k - 1)) (A.coinLen n)).symm)))).trans
    ((Equiv.refl _).prodCongr (Fin.appendEquiv k (m * (2 ^ k - 1) * A.coinLen n)))).trans
      (Fin.appendEquiv (k * m) (k + m * (2 ^ k - 1) * A.coinLen n))).prodCongr (Equiv.refl _) |>.trans
    ((Fin.appendEquiv _ _).trans (finCastEquiv (Nat.add_sub_cancel' hQ)))

/-- The call blocks `(i, L) ↦ c i L` as a function of the flattened round index `p = (i, j)`,
`L` the `j`-th nonempty subset (the transport of `c` along `glCoinsEquiv`). -/
noncomputable def glBlocks (A : NUPPT) (n m k : ℕ) (c : Fin m → HardcoreBit.NESubset k → A.Coins n) :
    Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool :=
  (blocksEquivX m (2 ^ k - 1) (A.Coins n)).symm
    (((Equiv.refl (Fin m)).arrowCongr ((nesubsetEquiv k).arrowCongr (Equiv.refl (A.Coins n)))) c)

/-- The call block of the round `p` is `c p.divNat L_{p.modNat}`. -/
@[simp] theorem glBlocks_apply (A : NUPPT) (n m k : ℕ) (c : Fin m → HardcoreBit.NESubset k → A.Coins n)
    (p : Fin (m * (2 ^ k - 1))) :
    glBlocks A n m k c p = c p.divNat ((nesubsetEquiv k).symm p.modNat) := rfl

/-- The encoding of the coins `(s, b, c)` with unread coins `ex`:
`s ‖ b ‖ blocks ‖ ex`. -/
theorem ofFn_glCoinsEquiv (A : NUPPT) (n m k Q : ℕ)
    (hQ : k * m + (k + m * (2 ^ k - 1) * A.coinLen n) ≤ Q)
    (g : HardcoreBit.GuessCoins m k (A.Coins n))
    (ex : Fin (Q - (k * m + (k + m * (2 ^ k - 1) * A.coinLen n))) → Bool) :
    List.ofFn (glCoinsEquiv A n m k Q hQ (g, ex)) =
      blocksStr g.1 ++ List.ofFn g.2.1 ++ blocksStr (glBlocks A n m k g.2.2) ++ List.ofFn ex := by
  obtain ⟨s, b, c⟩ := g
  simp only [glCoinsEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl,
    id]
  rw [ofFn_finCastEquiv, ofFn_appendEquiv, ofFn_appendEquiv, ofFn_appendEquiv]
  simp only [List.append_assoc]
  rfl


/-! ## The inversion probability of the family inverter -/

/-- The concrete predictor `A'` of [PS10, Algorithm 89.6] induced by a machine `A₁` at parameter
`n` and an encoding `enc` of the first argument: `A'(y, q) = [A₁(1^n, ⟨enc y, q⟩) = 1]`. -/
def glPredictorOf (A₁ : NUPPT) (n m : ℕ) {β : Type*} (enc : β → List Bool) :
    β × (Fin m → Bool) → A₁.Coins n → Bool :=
  fun p c => decide (A₁.runAtL n (pairEncode (enc p.1) (List.ofFn p.2)) (List.ofFn c) = [true])

/-- **The recovery machine computes `guessRecover`** on well-formed coins: for coins
`(s, b, c)` and unread coins `ex`, the answer on `y` is the encoding of
`guessRecover (glPredictor A n o m) k y (s, b, c)`.

**Proof sketch.** `glMachine_runAt` gives the blockwise majorities of the round votes; the
vote of the round `(i, L)` is `subsetSum L b ⊕ A'(y, subsetSum L s ⊕ e_i; c i L)` by
`filter_betaOf`, `ip_eq_sum_filter` and the projections of `finProdFinEquiv`; the majority over
`j : Fin (2^k − 1)` is the majority over `L : NESubset k` by `majority_comp_equiv`. -/
theorem glMachine_runAt_guessRecover (A₁ : NUPPT) (iP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ iP.eval n = 0)
    {β : Type*} (enc : β → List Bool) (y : β)
    (g : HardcoreBit.GuessCoins (iP.eval n) (k n) (A₁.Coins n))
    (ex : Fin ((glCoins iP K A₁).eval n - glNeed A₁ iP k n) → Bool) :
    (glMachine A₁ iP K k hk).runAt n (enc y)
        (glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (g, ex)) =
      List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (iP.eval n) enc) (k n) y g) := by
  obtain ⟨s, b, c⟩ := g
  rw [glMachine_runAt A₁ iP K k hk n (enc y) s b (glBlocks A₁ n (iP.eval n) (k n) c) (List.ofFn ex) _
    (ofFn_glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (s, b, c) ex) hM]
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [← majority_comp_equiv (nesubsetEquiv (k n))]
  unfold HardcoreBit.guessRecover
  refine congrArg HardcoreBit.majority (funext fun L => ?_)
  simp only [GLLoop.wfVote, glBlocks_apply, glPredictorOf, HardcoreBit.subsetSum]
  have hdiv : (finProdFinEquiv (i, nesubsetEquiv (k n) L)).divNat = i :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, nesubsetEquiv (k n) L))
  have hmod : (finProdFinEquiv (i, nesubsetEquiv (k n) L)).modNat = nesubsetEquiv (k n) L :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, nesubsetEquiv (k n) L))
  simp only [hdiv, hmod, filter_betaOf, Equiv.symm_apply_apply, ip_eq_sum_filter]
  rfl

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreGLColl.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGL
import TCSlib.Cryptography.Asymptotic.Collections

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter for collections

The collection form of [PS10, Theorem 87.3] (needed by [PS10, Theorem 104.4] and Chapter 4):
if `F` is a collection of one-way functions whose elements have encoding length `m(n)` at
generated indices, then `⟨encD_i x, r⟩` is hard-core for the padded collection
`g_i(x, r) = ⟨f_i(x), r⟩`. This file supplies the machine side for
`Collection.OneWay.glPad_hardCore` (`Asymptotic/HardCore.lean`):

* the evaluator of the bit `⟨padFin(encD_i x), r⟩` on `⟨i, ⟨encD_i x, r⟩⟩` (`padToLen`, `ipFun`);
* the recovery machine `glMachine` of `Asymptotic/HardCoreGL.lean` applied to the predictor
  pre-processed to query `⟨i, ⟨y, q⟩⟩` (`collPre`), wrapped into an inverter of the padded
  collection (`glCollMachine`);
* the per-index transfer `glColl_uprob_le` from the encoded-domain Goldreich–Levin bound
  `HardcoreBit.invProb_guessInverter_enc_pad` (`Asymptotic/GoldreichLevinDomain.lean`) to the
  inversion event of `glCollMachine`;
* the final negligibility argument `glColl_negligible`: the good set of indices
  (`HardcoreBit.half_le_uprob_threshold`), the averaging `HardcoreBit.uprob_mul_le_uexp`, and
  the polynomial arithmetic with the guess count `glKc` for a predictor of advantage
  `n^{−c}/2`.

## Main definitions

* `TCSlib.Cryptography.glKc`, `TCSlib.Cryptography.glKcBound` — the guess count for advantage
  `n^{−c}/2` and its polynomial majorant.
* `TCSlib.Cryptography.padToLen` — padding a string to the length of another.
* `TCSlib.Cryptography.glCollMachine` — the inverter of the padded collection.

## Main results

* `TCSlib.Cryptography.exists_glBitCollEvaluator` — the hard-core bit of the padded collection
  is polynomial-time computable.
* `TCSlib.Cryptography.glColl_uprob_le` — the recovery event implies the inversion event.
* `TCSlib.Cryptography.glColl_negligible` — the hardness clause of the collection form.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5: Definition 41.1; §3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6; §3.6: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The guess count for a predictor of advantage `n^{−c}/2` -/

/-- The guess count `k(n) := size (8 m(n) n^{2c})`: `2 m ≤ (n^{−c}/2)² (2^k − 1)`. -/
def glKc (mP : PolyExpr) (c n : ℕ) : ℕ := Nat.size (8 * mP.eval n * n ^ (2 * c))

/-- The polynomial majorant `16 m n^{2c} + 1` of `2^{k(n)}`. -/
def glKcBound (mP : PolyExpr) (c : ℕ) : PolyExpr :=
  .add (.mul (.const 16) (.mul mP (.pow .var (2 * c)))) (.const 1)

/-- `8 m n^{2c} < 2^{k(n)}`. -/
theorem lt_two_pow_glKc (mP : PolyExpr) (c n : ℕ) :
    8 * mP.eval n * n ^ (2 * c) < 2 ^ glKc mP c n :=
  Nat.lt_size_self _

/-- `2^{k(n)} ≤ 16 m n^{2c} + 1`. -/
theorem two_pow_glKc_le (mP : PolyExpr) (c : ℕ) (n : ℕ) :
    2 ^ glKc mP c n ≤ (glKcBound mP c).eval n := by
  simp only [glKcBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var]
  unfold glKc
  calc 2 ^ Nat.size (8 * mP.eval n * n ^ (2 * c)) ≤ 2 * (8 * mP.eval n * n ^ (2 * c)) + 1 :=
        two_pow_size_le _
    _ = 16 * (mP.eval n * n ^ (2 * c)) + 1 := by ring

/-- The real form of the guess-count inequality for `ε = n^{−c}/2`, `n ≥ 1`. -/
theorem glKc_real (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    2 * (mP.eval n : ℝ) ≤ (1 / (n : ℝ) ^ c / 2) ^ 2 * ((2 : ℝ) ^ glKc mP c n - 1) := by
  have h := lt_two_pow_glKc mP c n
  have hcast : (8 * (mP.eval n : ℝ) * (n : ℝ) ^ (2 * c)) + 1 ≤ (2 : ℝ) ^ glKc mP c n := by
    exact_mod_cast h
  have hnR : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast hn) c
  have hsq : (1 / (n : ℝ) ^ c / 2) ^ 2 = 1 / (4 * (n : ℝ) ^ (2 * c)) := by
    rw [pow_mul]; field_simp; ring
  rw [hsq, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- The guess count is positive when the block length is (`n ≥ 1`). -/
theorem glKc_pos_or (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    0 < 2 ^ glKc mP c n - 1 ∨ mP.eval n = 0 := by
  rcases Nat.eq_zero_or_pos (mP.eval n) with hm | hm
  · exact Or.inr hm
  · left
    have h := lt_two_pow_glKc mP c n
    have : 0 < 8 * mP.eval n * n ^ (2 * c) := by positivity
    omega

/-! ## Padding and the bit evaluator -/

/-- Padding or truncating the first component of a pair to the length of the second:
`⟨a, b⟩ ↦ (a ++ 0^{|b|}).take |b|`, the string `ofFn (padFin |b| a)`. -/
def padToLen (z : List Bool) : List Bool :=
  (pairFstD z ++ List.zipWith xor (pairSndD z) (pairSndD z)).take (pairSndD z).length

/-- Padding is polynomial-time. -/
theorem padToLen_poly : PolyTimeComputable padToLen :=
  takeLen_poly polyTimeComputable_pairSndD
    (polyTimeComputable_pairFstD.append (zipXor_poly polyTimeComputable_pairSndD polyTimeComputable_pairSndD))

/-- Padding `a` to the length of an encoded `L`-bit string encodes `padFin L a`. -/
theorem padToLen_pairEncode_ofFn (a : List Bool) {L : ℕ} (ρ : Fin L → Bool) :
    padToLen (pairEncode a (List.ofFn ρ)) = List.ofFn (padFin L a) := by
  simp only [padToLen, pairFstD_pairEncode, pairSndD_pairEncode, List.length_ofFn]
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.length_ofFn] at hj₂
  simp only [List.getElem_take, List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD]
  by_cases h : j < a.length
  · rw [List.getElem_append_left h, List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega), List.getElem_zipWith,
      Bool.xor_self]
    rfl

/-- The encoding of `padFin L w` is `w` when `|w| = L`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-- **The evaluator of the hard-core bit of the padded collection** `⟨padFin(encD_i x), r⟩` on
`⟨i, ⟨encD_i x, r⟩⟩` [PS10, Theorem 87.3, collection form, efficiency clause]. -/
theorem exists_glBitCollEvaluator (F : Collection) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ i (x : F.D i) {L : ℕ} (ρ : Fin L → Bool),
        H (pairEncode i (pairEncode (F.encD i x) (List.ofFn ρ))) =
          [HardcoreBit.ip (padFin L (F.encD i x)) ρ] := by
  refine ⟨fun w => ipFun (pairEncode (padToLen (pairSndD w)) (pairSndD (pairSndD w))),
    ptcComp (g := ipFun) ipFun_poly ((ptcComp (g := padToLen) padToLen_poly polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)), fun i x L ρ => ?_⟩
  simp only [pairSndD_pairEncode, padToLen_pairEncode_ofFn, ipFun_ofFn]

/-- The inner product is invariant under transport along an equality of lengths (private copy
of `HardcoreBit.ip_cast`, `Asymptotic/HardCorePermutation.lean`). -/
private theorem ip_cast' {k m : ℕ} (h : k = m) (x r : Fin k → Bool) :
    HardcoreBit.ip x r =
      HardcoreBit.ip (fun j => x (Fin.cast h.symm j)) (fun j => r (Fin.cast h.symm j)) := by
  subst h; rfl

/-! ## The predictor pre-processing and the inverter -/

/-- The pre-processing of the collection predictor: `⟨⟨i, y⟩, q⟩ ↦ ⟨i, ⟨y, q⟩⟩`. -/
def collPre (z : List Bool) : List Bool :=
  pairEncode (pairFstD (pairFstD z)) (pairEncode (pairSndD (pairFstD z)) (pairSndD z))

/-- The pre-processing is polynomial-time. -/
theorem collPre_poly : PolyTimeComputable collPre :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)

/-- The predictor queried by the recovery machine on `⟨⟨i, y⟩, q⟩` is the collection
distinguisher `A(1^n, ⟨i, ⟨y, q⟩⟩)`. -/
theorem glPredictorOf_precomp_coll (A : NUPPT) (n m : ℕ) (i y : List Bool) (q : Fin m → Bool)
    (c : A.Coins n) :
    glPredictorOf (A.precomp collPre_poly) n m (fun y : List Bool => pairEncode i y) (y, q) c =
      A.distinguisherL n (pairEncode i (pairEncode y (List.ofFn q))) c := by
  simp only [glPredictorOf, NUPPT.runAtL_precomp, collPre, pairFstD_pairEncode, pairSndD_pairEncode,
    NUPPT.distinguisherL, NUPPT.runAt_eq]

/-- The pre-processing of the collection inverter: on the view of `⟨1^n, ⟨i, ⟨y, r⟩⟩⟩`, the
string `⟨i, y⟩`. -/
def glCollPre (v : List Bool) : List Bool :=
  pairEncode (pairFstD (NUPPT.inArg v)) (pairFstD (pairSndD (NUPPT.inArg v)))

/-- The pre-processing is polynomial-time. -/
theorem glCollPre_poly : PolyTimeComputable glCollPre :=
  (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))

/-- The post-processing of the collection inverter: `⟨answer, r⟩`. -/
def glCollPost (v : List Bool) : List Bool :=
  pairEncode (pairSndD v) (pairSndD (pairSndD (NUPPT.inArg (pairFstD v))))

/-- The post-processing is polynomial-time. -/
theorem glCollPost_poly : PolyTimeComputable glCollPost :=
  polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)))

/-- **The inverter of the padded collection** [PS10, Algorithm 89.6, collection form]: the
recovery machine for the pre-processed predictor, run on `⟨i, y⟩`, its answer paired with `r`. -/
noncomputable def glCollMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  (glMachine (A.precomp collPre_poly) mP K k hk).wrap glCollPre_poly glCollPost_poly (fun _ => [])
    (.const 0) (fun _ => by simp) (.const 0)

/-- The collection inverter on `⟨i, ⟨y, r⟩⟩` with coins `c` returns `⟨recovery(⟨i, y⟩), r⟩`. -/
theorem glCollMachine_runAt (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) (i y rs : List Bool) (c : (glMachine (A.precomp collPre_poly) mP K k hk).Coins n)
    (r' : (glCollMachine A mP K k hk).Coins n) (hr' : List.ofFn r' = List.ofFn c) :
    (glCollMachine A mP K k hk).runAt n (pairEncode i (pairEncode y rs)) r' =
      pairEncode ((glMachine (A.precomp collPre_poly) mP K k hk).runAt n (pairEncode i y) c) rs := by
  unfold glCollMachine
  rw [NUPPT.runAt_wrap (glMachine (A.precomp collPre_poly) mP K k hk) glCollPre_poly glCollPost_poly
    _ _ _ (.const 0) n _ rfl (fun _ : Fin 0 => false) c r' (by rw [hr']; rfl)]
  simp [glCollPre, glCollPost]

/-! ## The per-index transfer -/

/-- **The recovery event implies the inversion event**: at an index `i` whose elements have
encoding length `m(n)`, if the recovery procedure (with the collection predictor) outputs
`padFin(encD_i x)` on `f_i(x)`, the collection inverter inverts `g_i(x, r) = ⟨f_i(x), r⟩`.

**Proof sketch.** Reindex the padding by `L = m(n)` and the coins of the inverter by
`glCoinsEquiv` (the unread coins dropped by `uprob_fst`); pointwise, `glCollMachine_runAt`,
`glMachine_runAt_guessRecover` and `glPredictorOf_precomp_coll` identify the inverter's answer
with `⟨ofFn (guessRecover …), r⟩`, which is `⟨encD_i x, r⟩` (`ofFn_padFin_of_length`) and decodes
to `(x, r)` (`glPadDecode_pairEncode_ofFn`, `decD_encD`). -/
theorem glColl_uprob_le (F : Collection) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (A : NUPPT) (n : ℕ) (i : List Bool) (L : ℕ)
    (hL : L = mP.eval n) (hM : 0 < 2 ^ k n - 1 ∨ mP.eval n = 0)
    (henc : ∀ x : F.D i, (F.encD i x).length = mP.eval n) :
    uprob (fun z : (F.D i × (Fin (mP.eval n) → Bool)) ×
        HardcoreBit.GuessCoins (mP.eval n) (k n) (A.Coins n) =>
      HardcoreBit.guessRecover
        (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (c : A.Coins n) =>
          A.distinguisherL n (pairEncode i (pairEncode p.1 (List.ofFn p.2))) c) (k n)
        (F.f i z.1.1) z.2 = padFin (mP.eval n) (F.encD i z.1.1)) ≤
    uprob (fun z : (F.D i × (Fin L → Bool)) × (glCollMachine A mP K k hk).Coins n =>
      ∃ x', glPadDecode F i L ((glCollMachine A mP K k hk).runAt n
          (pairEncode i (pairEncode (F.f i z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
        pairEncode (F.f i x'.1) (List.ofFn x'.2) = pairEncode (F.f i z.1.1) (List.ofFn z.1.2)) := by
  have hpred : (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (c : A.Coins n) =>
      A.distinguisherL n (pairEncode i (pairEncode p.1 (List.ofFn p.2))) c) =
      glPredictorOf (A.precomp collPre_poly) n (mP.eval n) (fun y : List Bool => pairEncode i y) := by
    funext p c
    obtain ⟨y, q⟩ := p
    exact (glPredictorOf_precomp_coll A n (mP.eval n) i y q c).symm
  rw [hpred]
  have hcoins : (glCollMachine A mP K k hk).coinLen n = (glCoins mP K (A.precomp collPre_poly)).eval n := by
    simp [glCollMachine, NUPPT.coinLen]
  let eC : HardcoreBit.GuessCoins (mP.eval n) (k n) ((A.precomp collPre_poly).Coins n) ×
      (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool) ≃
      (glCollMachine A mP K k hk).Coins n :=
    (glCoinsEquiv (A.precomp collPre_poly) n (mP.eval n) (k n) _ (glNeed_le (A.precomp collPre_poly) mP K k hk n)).trans (finCastEquiv hcoins.symm)
  haveI : Nonempty (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool) := ⟨fun _ => false⟩
  refine le_of_eq_of_le (uprob_fst (β := Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool)
    _).symm ?_
  refine le_of_le_of_eq ?_ (uprob_comp_equiv ((Equiv.prodAssoc (F.D i × (Fin (mP.eval n) → Bool))
    (HardcoreBit.GuessCoins (mP.eval n) (k n) ((A.precomp collPre_poly).Coins n))
    (Fin ((glCoins mP K (A.precomp collPre_poly)).eval n - glNeed (A.precomp collPre_poly) mP k n) → Bool)).trans
    (((Equiv.refl (F.D i)).prodCongr (finCastEquiv hL.symm)).prodCongr eC)) _)
  refine uprob_mono fun w hw => ?_
  obtain ⟨⟨⟨x, ρ⟩, g⟩, ex⟩ := w
  simp only [Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.coe_refl, id] at hw ⊢
  rw [glCollMachine_runAt A mP K k hk n i (F.f i x) (List.ofFn (finCastEquiv hL.symm ρ))
      (glCoinsEquiv (A.precomp collPre_poly) n (mP.eval n) (k n) _ (glNeed_le (A.precomp collPre_poly) mP K k hk n) (g, ex)) _
      (by simp only [eC, Equiv.trans_apply]; exact ofFn_finCastEquiv _ _),
    glMachine_runAt_guessRecover (A.precomp collPre_poly) mP K k hk n hM (fun y : List Bool => pairEncode i y) (F.f i x) g ex,
    hw, ofFn_padFin_of_length (henc x), glPadDecode_pairEncode_ofFn, F.decD_encD]
  exact ⟨(x, finCastEquiv hL.symm ρ), rfl, rfl⟩


/-! ## The hardness clause -/

/-- **The hardness clause of the collection form of Goldreich–Levin** [PS10, Theorem 87.3,
collection form]: if every inverter `B` of the padded collection `g_i(x, r) = ⟨f_i(x), r⟩` (with
padding length `L n r = m(n)` and decoder `glPadDecode`) has negligible success, then the
advantage `max 0 (Pr[A predicts ⟨padFin(encD_i x), r⟩] − 1/2)` of any predictor `A` is
negligible.

**Proof sketch.** By contradiction: `not_negligible_iff` gives `c` with `1/2 + n^{−c} ≤ uexp q`
for infinitely many `n`, `q r` the per-index success. The good indices
`{r | 1/2 + n^{−c}/2 ≤ q r}` have probability `≥ n^{−c}/2`
(`HardcoreBit.half_le_uprob_threshold`). At a good index the prediction hypothesis, transported
to padding length `m(n)` (`finCastEquiv`, `ip_cast'`), feeds
`HardcoreBit.invProb_guessInverter_enc_pad` with the guess count `glKc` (`glKc_real`), so the
recovery procedure outputs `padFin(encD_i x)` with probability `≥ ε/(4·2^k)`, `ε = n^{−c}/2`;
`glColl_uprob_le` turns this into the inversion event of `glCollMachine`. Averaging over the
good indices (`HardcoreBit.uprob_mul_le_uexp`) gives inversion probability
`≥ ε²/(4·2^k) ≥ n^{−(2c+d+1)}` (`two_pow_glKc_le`, `PolyExpr.eval_le`) infinitely often,
contradicting `hhard (glCollMachine …)`. -/
theorem glColl_negligible (F : Collection) (mP : PolyExpr) (L : ∀ n, F.gen.Coins n → ℕ)
    (hL : ∀ n r, L n r = mP.eval n)
    (henc : ∀ n (r : F.gen.Coins n) (x : F.D (F.index n r)),
      (F.encD (F.index n r) x).length = mP.eval n)
    (A : NUPPT)
    (hhard : ∀ B : NUPPT, Negligible fun n => uexp fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × B.Coins n =>
        ∃ x', glPadDecode F (F.index n r) (L n r) (B.runAt n (pairEncode (F.index n r)
            (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
          pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
            pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2)) :
    Negligible fun n => max 0 (uexp (fun r : F.gen.Coins n =>
      uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × A.Coins n =>
        A.distinguisherL n (pairEncode (F.index n r)
          (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2 =
          HardcoreBit.ip (padFin (L n r) (F.encD (F.index n r) z.1.1)) z.1.2) - 1 / 2) := by
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.mp hneg
  set K := glKcBound mP c with hK
  set B := glCollMachine A mP K (glKc mP c) (two_pow_glKc_le mP c) with hB
  obtain ⟨C, d, hCd⟩ := K.eval_le
  obtain ⟨n₀, hn₀⟩ := hhard B (2 * c + d + 1)
  obtain ⟨n, hn, hgap⟩ := hc (max n₀ (max 1 (16 * C * 2 ^ d)))
  have hn1 : 1 ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnC : 16 * C * 2 ^ d ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  haveI : Nonempty (F.gen.Coins n) := ⟨fun _ => false⟩
  set q : F.gen.Coins n → ℝ := fun r =>
    uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × A.Coins n =>
      A.distinguisherL n (pairEncode (F.index n r)
        (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2 =
        HardcoreBit.ip (padFin (L n r) (F.encD (F.index n r) z.1.1)) z.1.2 with hq
  have hε0 : (0 : ℝ) < 1 / (n : ℝ) ^ c := by positivity
  have hpred : 1 / 2 + 1 / (n : ℝ) ^ c ≤ uexp q := by
    rw [abs_of_nonneg (le_max_left _ _)] at hgap
    rcases le_or_gt (uexp q - 1 / 2) 0 with hle | hlt
    · rw [max_eq_left hle] at hgap; linarith
    · rw [max_eq_right hlt.le] at hgap; linarith
  have hgood := HardcoreBit.half_le_uprob_threshold q (fun r => uprob_le_one _) (by norm_num)
    hε0.le hpred
  set ε : ℝ := 1 / (n : ℝ) ^ c / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hkR := glKc_real mP c n hn1
  have hM := glKc_pos_or mP c n hn1
  set inner : F.gen.Coins n → ℝ := fun r =>
    uprob fun z : (F.D (F.index n r) × (Fin (L n r) → Bool)) × B.Coins n =>
      ∃ x', glPadDecode F (F.index n r) (L n r) (B.runAt n (pairEncode (F.index n r)
          (pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2))) z.2) = some x' ∧
        pairEncode (F.f (F.index n r) x'.1) (List.ofFn x'.2) =
          pairEncode (F.f (F.index n r) z.1.1) (List.ofFn z.1.2) with hinnerdef
  have hinner : ∀ r : F.gen.Coins n, 1 / 2 + ε ≤ q r →
      ε / (4 * 2 ^ glKc mP c n) ≤ inner r := by
    intro r hr
    have hq' : 1 / 2 + ε ≤ uprob fun z : (F.D (F.index n r) × (Fin (mP.eval n) → Bool)) × A.Coins n =>
        (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (cc : A.Coins n) =>
          A.distinguisherL n (pairEncode (F.index n r) (pairEncode p.1 (List.ofFn p.2))) cc)
          (F.f (F.index n r) z.1.1, z.1.2) z.2 =
        HardcoreBit.ip (padFin (mP.eval n) (F.encD (F.index n r) z.1.1)) z.1.2 := by
      refine hr.trans (le_of_eq ?_)
      rw [hq]
      refine (OneWay.uprob_congr fun z => ?_).trans (uprob_comp_equiv
        (((Equiv.refl (F.D (F.index n r))).prodCongr (finCastEquiv (hL n r))).prodCongr
          (Equiv.refl (A.Coins n))) _)
      obtain ⟨⟨x, ρ⟩, cc⟩ := z
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, ofFn_finCastEquiv]
      rw [ip_cast' (hL n r) (padFin (L n r) (F.encD (F.index n r) x)) ρ]
      exact Iff.rfl
    have hGL := HardcoreBit.invProb_guessInverter_enc_pad
      (fun x : F.D (F.index n r) => padFin (mP.eval n) (F.encD (F.index n r) x)) (F.f (F.index n r))
      (fun (p : List Bool × (Fin (mP.eval n) → Bool)) (cc : A.Coins n) =>
        A.distinguisherL n (pairEncode (F.index n r) (pairEncode p.1 (List.ofFn p.2))) cc)
      (k := glKc mP c n) (ε := ε) hεpos hkR hq'
    have htr := glColl_uprob_le F mP K (glKc mP c) (two_pow_glKc_le mP c) A n (F.index n r)
      (L n r) (hL n r) hM (henc n r)
    exact hGL.trans htr
  have hbound := HardcoreBit.uprob_mul_le_uexp (G := fun r => 1 / 2 + ε ≤ q r) (q := inner)
    (fun r => uprob_nonneg _) hinner
  have hsmall := hn₀ n (le_of_max_le_left hn)
  have hnn : 0 ≤ uexp inner := by
    unfold uexp
    exact div_nonneg (Finset.sum_nonneg fun r _ => uprob_nonneg _) (Nat.cast_nonneg _)
  rw [abs_of_nonneg hnn] at hsmall
  have hprod : ε * (ε / (4 * 2 ^ glKc mP c n)) ≤ uexp inner :=
    (mul_le_mul_of_nonneg_right hgood (by positivity)).trans hbound
  have h2k : ((2 : ℝ) ^ glKc mP c n) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ d := by
    exact_mod_cast (two_pow_glKc_le mP c n).trans (hCd n)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnCR : (16 : ℝ) * C * 2 ^ d ≤ n := by exact_mod_cast hnC
  have hpow : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have hεsq : ε * (ε / (4 * 2 ^ glKc mP c n)) = 1 / (16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n) := by
    rw [hε, pow_mul]
    field_simp
    ring
  have hlow : 1 / (n : ℝ) ^ (2 * c + d + 1) ≤ 1 / (16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    calc 16 * (n : ℝ) ^ (2 * c) * 2 ^ glKc mP c n ≤ 16 * (n : ℝ) ^ (2 * c) * (C * (2 * (n : ℝ)) ^ d) := by
          gcongr
          exact h2k.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
      _ = (n : ℝ) ^ (2 * c) * (n : ℝ) ^ d * (16 * C * 2 ^ d) := by ring
      _ ≤ (n : ℝ) ^ (2 * c) * (n : ℝ) ^ d * n := by gcongr
      _ = (n : ℝ) ^ (2 * c + d + 1) := by ring
  linarith

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/HardCoreGLFamily.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGL

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter for function families

The family side of [PS10, Theorem 87.3] (`FunFamily.StrongOneWay.glPad_hardCore` in
`Asymptotic/HardCore.lean`): the guess count `glK` for a predictor of advantage `n^{−c}` and its
polynomial majorant, the evaluator of the bit `⟨x, r⟩` on `⟨1^n, x ‖ r⟩`, the inverter
`glFamMachine` of `g(x, r) = (f(x), r)` obtained by wrapping the recovery machine `glMachine`
of `Asymptotic/HardCoreGL.lean` (applied to the predictor pre-processed to query `y ‖ q`), and
the identity `invProbOpt_glFam_eq` between its inversion probability and that of the concrete
inverter `HardcoreBit.guessInverter` [PS10, Algorithm 89.6; Gar26, Figure 2.5].

## Main definitions

* `TCSlib.Cryptography.glK`, `TCSlib.Cryptography.glKBound` — the guess count and its
  polynomial majorant.
* `TCSlib.Cryptography.glFamMachine` — the inverter of `g(x, r) = (f(x), r)`.

## Main results

* `TCSlib.Cryptography.glK_real`, `TCSlib.Cryptography.two_pow_glK_le` — the guess-count
  inequalities.
* `TCSlib.Cryptography.exists_glBitEvaluator` — the bit `⟨x, r⟩` is polynomial-time computable.
* `TCSlib.Cryptography.invProbOpt_glFam_eq` — the family inverter inverts exactly as often as
  `guessInverter`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The guess count and its bounds -/

/-- The guess count `k(n) := size (2 m(n) n^{2c})` of the reduction for a predictor of advantage
`n^{−c}`: `2 m n^{2c} < 2^k`, i.e. `2 m ≤ ε²(2^k − 1)` for `ε = n^{−c}`. -/
def glK (mP : PolyExpr) (c n : ℕ) : ℕ := Nat.size (2 * mP.eval n * n ^ (2 * c))

/-- The polynomial majorant `4 m n^{2c} + 1` of `2^{k(n)}`. -/
def glKBound (mP : PolyExpr) (c : ℕ) : PolyExpr :=
  .add (.mul (.const 4) (.mul mP (.pow .var (2 * c)))) (.const 1)

/-- `2 m n^{2c} < 2^{k(n)}`. -/
theorem lt_two_pow_glK (mP : PolyExpr) (c n : ℕ) : 2 * mP.eval n * n ^ (2 * c) < 2 ^ glK mP c n :=
  Nat.lt_size_self _

/-- `2^{k(n)} ≤ 4 m n^{2c} + 1`. -/
theorem two_pow_glK_le (mP : PolyExpr) (c : ℕ) (n : ℕ) :
    2 ^ glK mP c n ≤ (glKBound mP c).eval n := by
  simp only [glKBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var]
  unfold glK
  calc 2 ^ Nat.size (2 * mP.eval n * n ^ (2 * c)) ≤ 2 * (2 * mP.eval n * n ^ (2 * c)) + 1 :=
        two_pow_size_le _
    _ = 4 * (mP.eval n * n ^ (2 * c)) + 1 := by ring

/-- The real form of the guess-count inequality: `2 m ≤ ε² (2^k − 1)` for `ε = 1/n^c`, `n ≥ 1`. -/
theorem glK_real (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    2 * (mP.eval n : ℝ) ≤ (1 / (n : ℝ) ^ c) ^ 2 * ((2 : ℝ) ^ glK mP c n - 1) := by
  have h := lt_two_pow_glK mP c n
  have hnR : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast hn) c
  have hcast : (2 * (mP.eval n : ℝ) * (n : ℝ) ^ (2 * c)) + 1 ≤ (2 : ℝ) ^ glK mP c n := by
    exact_mod_cast h
  rw [one_div, inv_pow, ← pow_mul, mul_comm c 2]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- The guess count is positive when the block length is (`n ≥ 1`). -/
theorem glK_pos_or (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    0 < 2 ^ glK mP c n - 1 ∨ mP.eval n = 0 := by
  rcases Nat.eq_zero_or_pos (mP.eval n) with hm | hm
  · exact Or.inr hm
  · left
    have h := lt_two_pow_glK mP c n
    have : 0 < 2 * mP.eval n * n ^ (2 * c) := by positivity
    omega

/-! ## The inverter of `g(x, r) = (f(x), r)` from the recovery machine -/

/-- Pre-processing of the family inverter: on the view of `⟨1^n, y ‖ r⟩`, the string
`y = (y ‖ r).take (outLen n)`. -/
def glFamPre (oP : PolyExpr) (v : List Bool) : List Bool :=
  (NUPPT.inArg v).take (oP.eval (NUPPT.inParam v).length)

/-- The pre-processing is polynomial-time. -/
theorem glFamPre_poly (oP : PolyExpr) : PolyTimeComputable (glFamPre oP) := by
  convert (polyTimeComputable_pairTakePoly oP).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg) using 1
  funext v
  simp [glFamPre]

/-- Post-processing of the family inverter: `answer ++ (y ‖ r).drop (outLen n)`. -/
def glFamPost (oP : PolyExpr) (v : List Bool) : List Bool :=
  pairSndD v ++ (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length)

/-- The post-processing is polynomial-time. -/
theorem glFamPost_poly (oP : PolyExpr) : PolyTimeComputable (glFamPost oP) := by
  have h : PolyTimeComputable fun v =>
      (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length) := by
    convert (polyTimeComputable_pairDropPoly oP).comp
      ((NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairFstD).pairEncode
        (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)) using 1
    funext v
    simp
  exact polyTimeComputable_pairSndD.append h

/-- **The inverter of `g(x, r) = (f(x), r)`** [PS10, Algorithm 89.6]: the recovery machine on
`y = (y ‖ r).take (outLen n)`, its answer `x'` followed by `r`. -/
noncomputable def glFamMachine (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  (glMachine A iP K k hk).wrap (glFamPre_poly oP) (glFamPost_poly oP) (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 0)

/-- The family inverter on `y ‖ r` with coins `c` (as a string) returns the recovery machine's
answer on `y` followed by `r`. -/
theorem glFamMachine_runAt (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (y : Fin (oP.eval n) → Bool) (r : Fin (iP.eval n) → Bool)
    (c : (glMachine A iP K k hk).Coins n) (r' : (glFamMachine A iP oP K k hk).Coins n)
    (hr' : List.ofFn r' = List.ofFn c) :
    (glFamMachine A iP oP K k hk).runAt n (List.ofFn y ++ List.ofFn r) r' =
      (glMachine A iP K k hk).runAt n (List.ofFn y) c ++ List.ofFn r := by
  unfold glFamMachine
  rw [NUPPT.runAt_wrap (glMachine A iP K k hk) (glFamPre_poly oP) (glFamPost_poly oP) _ _ _
    (.const 0) n _ rfl (fun _ : Fin 0 => false) c r' (by rw [hr']; rfl)]
  simp [glFamPre, glFamPost]

/-! ## The evaluator of `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` -/

/-- **The evaluator of the Goldreich–Levin bit** `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` (the efficiency clause
of [PS10, Theorem 87.3], Fact 88.4): cut after `inLen n` bits and apply `ipFun`. -/
theorem exists_glBitEvaluator (iP : PolyExpr) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x r : Fin (iP.eval n) → Bool),
        H (NUPPT.advInput n (List.ofFn x ++ List.ofFn r)) = [HardcoreBit.ip x r] := by
  refine ⟨fun w => ipFun (pairEncode ((pairSndD w).take (iP.eval (pairFstD w).length))
      ((pairSndD w).drop (iP.eval (pairFstD w).length))),
    ptcComp ipFun_poly ((polyTimeComputable_pairTakePoly iP).pairEncode
      (polyTimeComputable_pairDropPoly iP)), fun n x r => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append, ipFun_ofFn]

/-! ## The inversion probability of the family inverter -/

/-- The pre-processing `⟨Y, q⟩ ↦ Y ++ q` of the family predictor. -/
def concatPre (z : List Bool) : List Bool := pairFstD z ++ pairSndD z

/-- The pre-processing is polynomial-time. -/
theorem concatPre_poly : PolyTimeComputable concatPre := polyTimeComputable_pairConcat

/-- The predictor of the family, called by the recovery machine on the pair `⟨y, q⟩`, computes
the concrete predictor `A(1^n, y ‖ q)` of [PS10, Algorithm 89.6]. -/
theorem glPredictorOf_precomp_concat (A : NUPPT) (n o m : ℕ) (y : Fin o → Bool) (q : Fin m → Bool)
    (c : A.Coins n) :
    glPredictorOf (A.precomp concatPre_poly) n m (fun y : Fin o → Bool => List.ofFn y) (y, q) c =
      A.predictor n (o + m) (Fin.appendEquiv o m (y, q)) c := by
  simp only [glPredictorOf, NUPPT.runAtL_precomp, concatPre, pairFstD_pairEncode, pairSndD_pairEncode,
    NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_eq, ofFn_appendEquiv]


/-- **The inversion probability of the family inverter is that of the concrete inverter**
`guessInverter` of [PS10, Algorithm 89.6; Gar26, Figure 2.5] against `HardcoreBit.glPad (f n)`,
for the predictor `A'(y, q) = A(1^n, y ‖ q)`.

**Proof sketch.** Reindex the input by `appendEquiv` and the coins by `glCoinsEquiv` (the unread
coins are dropped by `uprob_fst`); on `(x, r)` with coins `(s, b, c)` the family inverter
returns `guessRecover … ‖ r` (`glFamMachine_runAt`, `glMachine_runAt_guessRecover`), which
inverts `g(x, r) = (f(x), r)` exactly when `guessInverter` does. -/
theorem invProbOpt_glFam_eq (𝓕 : FunFamily) (A : NUPPT) (K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ 𝓕.inLen.eval n = 0) :
    invProbOpt (fun z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool =>
        Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
          (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)))
      ((glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen K k hk).inverter n
        (𝓕.inLen.eval n + 𝓕.inLen.eval n) (𝓕.outLen.eval n + 𝓕.inLen.eval n)) =
    invProb (HardcoreBit.glPad (𝓕.f n))
      (HardcoreBit.guessInverter
        (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) (k n)) := by
  set A₁ := A.precomp concatPre_poly with hA₁
  have hpred : (fun (y : (Fin (𝓕.outLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) (c : A.Coins n) =>
      A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n) (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) =
      glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) := by
    funext y c
    obtain ⟨y, q⟩ := y
    exact (glPredictorOf_precomp_concat A n (𝓕.outLen.eval n) (𝓕.inLen.eval n) y q c).symm
  rw [hpred]
  unfold invProbOpt invProb
  have hcoins : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).coinLen n = (glCoins 𝓕.inLen K A₁).eval n := by
    simp [glFamMachine, NUPPT.coinLen]
  let eC : HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) ×
      (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool) ≃
      (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).Coins n :=
    (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n)).trans (finCastEquiv hcoins.symm)
  rw [← uprob_comp_equiv ((Equiv.prodAssoc ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool))
    (HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n))
    (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool)).trans
    ((Fin.appendEquiv (α := Bool) (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr eC))]
  refine (OneWay.uprob_congr fun w => ?_).trans (uprob_fst fun v : ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) ×
    HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) =>
      HardcoreBit.glPad (𝓕.f n) (HardcoreBit.guessInverter
        (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n)
        (HardcoreBit.glPad (𝓕.f n) v.1) v.2) = HardcoreBit.glPad (𝓕.f n) v.1)
  obtain ⟨⟨⟨x, r⟩, g⟩, ex⟩ := w
  simp only [Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_apply_apply, NUPPT.inverter_eq_some_iff]
  have hrun : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n
      (List.ofFn (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.glPad (𝓕.f n) (x, r)))) (eC (g, ex)) =
      List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y))
        (k n) (𝓕.f n x) g) ++ List.ofFn r := by
    rw [ofFn_appendEquiv]
    show (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n (List.ofFn (𝓕.f n x) ++ List.ofFn r) _ = _
    rw [glFamMachine_runAt A₁ 𝓕.inLen 𝓕.outLen K k hk n (𝓕.f n x) r
      (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n) (g, ex)) _
      (by simp only [eC, Equiv.trans_apply]; exact ofFn_finCastEquiv _ _),
      glMachine_runAt_guessRecover A₁ 𝓕.inLen K k hk n hM (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y)
        (𝓕.f n x) g ex]
  rw [hrun]
  constructor
  · rintro ⟨x', hx', hfx'⟩
    rw [← ofFn_appendEquiv, List.ofFn_inj] at hx'
    subst hx'
    rw [Equiv.symm_apply_apply] at hfx'
    exact (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective hfx'
  · intro hinv
    refine ⟨Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.guessRecover
      (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n) (𝓕.f n x) g, r),
      (ofFn_appendEquiv _ _).symm, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact congrArg _ hinv

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin on an encoded finite domain

The concrete Goldreich–Levin theorem `HardcoreBit.invProb_guessInverter` [Gar26, Theorem 2.3]
draws `x` uniformly from the cube `{0,1}^n`. The collection form of [PS10, Theorem 87.3]
(needed by [PS10, Theorem 104.4] and by Chapter 4) draws `x` uniformly from a finite domain
`D_i` [PS10, Definition 41.1] that is only *encoded* into `{0,1}^m` by an injective `encD_i`:
the image is in general a strict subset of the cube (`Z_N^*`, `QR_N`, a subgroup `G_q`), the
predictor's behaviour off the image is uncontrolled, and the uniform element of `D_i` is not a
uniform element of the cube. So the cube theorem cannot be transferred to collections, and the
run-2 sketch of `Collection.OneWay.glPad_hardCore`, which "identified `D_i` with `{0,1}^m`
through the injective encoding", was invalid (run-3 audit, finding P4-2).

This file proves the statement that is actually needed. For any finite type `α`, any map
`enc : α → {0,1}^m` (injectivity is not needed to *recover* `enc x`; it is needed downstream
to decode `x` from it), any `f : α → β` and any predictor `A` of `⟨enc x, r⟩` from `(f x, r)`
with success `1/2 + ε` over uniform `x : α`, `r ∈ {0,1}^m` and coins, the recovery procedure
of [PS10, Algorithm 89.6] (`HardcoreBit.guessRecover`) outputs `enc x` with probability at
least `ε/(4·2^k)` whenever `2m ≤ ε²(2^k − 1)`. The proof is the proof of
`invProb_guessInverter`: the good set is `half_le_uprob_threshold` over `α` (already general),
and the per-`x` analysis (`uprob_idealRecover_ne_le`, `one_sub_sum_le_uprob_eq`,
`uprob_guessRecover_ge`) is applied, for each fixed `x`, to the *constant* function
`fun _ => f x` at the point `enc x` — those lemmas only ever evaluate `f` at the point under
analysis, so no uniformity of the point on the cube is used.

## Main definitions

None: the file proves lemmas about the existing `HardcoreBit.guessRecover`.

## Main results

* `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc` — the encoded-domain
  Goldreich–Levin bound.
* `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad` — the same bound on the
  sample space `(α × {0,1}^m) × coins` of the padded collection (the padding `r` is carried
  along unused), the form consumed by `Collection.OneWay.glPad_hardCore`
  (`Asymptotic/HardCore.lean`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4.3: Definition 41.1; §3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

/-- **Goldreich–Levin on an encoded finite domain** [PS10, Theorem 87.3, collection form;
Gar26, Theorem 2.3, real case]: let `x` be uniform on a finite type `α`, `enc : α → {0,1}^m`,
`f : α → β`, and let the predictor `A` output `⟨enc x, r⟩` on `(f x, r)` with probability at
least `1/2 + ε` (`ε > 0`) over uniform `x`, `r ∈ {0,1}^m` and its coins. If the number `k` of
guessed bits satisfies `2m ≤ ε²(2^k − 1)`, then the recovery procedure of
[PS10, Algorithm 89.6] (`guessRecover A k`, run on `f x` with fresh coins) outputs the string
`enc x` with probability at least `ε/(4·2^k)` over uniform `x` and its coins. This is the
cube theorem `invProb_guessInverter` with the uniform cube element replaced by an arbitrary
uniformly distributed encoded element; in particular `x` uniform on a collection domain `D_i`
encoded by `encD_i` (run-3 audit P4-2).

**Deviation:** none beyond those of `invProb_guessInverter` (explicit `k`, nonempty subsets,
bound `ε/(4·2^k)` instead of the text's `ε³/(32n)`, source error 37).

**Proof sketch.** Let `q x := Pr_{r, c}[A(f x, r; c) = ⟨enc x, r⟩]`, which is the per-point
success `secProb (fun _ => f x) A (enc x)` of the concrete layer; by Fubini
(`uprob_comp_equiv` with `Equiv.prodAssoc`, `uprob_prod`) the hypothesis says
`1/2 + ε ≤ uexp q` (in particular `α` is nonempty). The good set
`{x | 1/2 + ε/2 ≤ q x}` has probability at least `ε/2` (`half_le_uprob_threshold`). For a good
`x`, every bit of the ideal procedure for the constant function `fun _ => f x` at the point
`enc x` is wrong with probability at most `1/(ε²(2^k − 1)) ≤ 1/(2m)`
(`uprob_idealRecover_ne_le`), so by the union bound (`one_sub_sum_le_uprob_eq`) the ideal
procedure outputs `enc x` with probability at least `1/2`, and the guessing procedure does so
with probability at least `2^{-k} · 1/2` (`uprob_guessRecover_ge`), its output on
`(fun _ => f x) (enc x) = f x` being `guessRecover A k (f x)`. Averaging over `x`
(`uprob_prod`, `uprob_mul_le_uexp`) gives `(ε/2)(2^{-k}/2) = ε/(4·2^k)`. -/
theorem invProb_guessInverter_enc {α β ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty ρ] {m : ℕ}
    (enc : α → Fin m → Bool) (f : α → β) (A : β × (Fin m → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hk : 2 * (m : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ uprob fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) :
    ε / (4 * 2 ^ k) ≤ uprob fun z : α × GuessCoins m k ρ =>
      guessRecover A k (f z.1) z.2 = enc z.1 := by
  classical
  set q : α → ℝ := fun x => secProb (fun _ : Fin m → Bool => f x) A (enc x) with hq
  have hexp : uprob (fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) = uexp q := by
    rw [← uprob_comp_equiv (Equiv.prodAssoc α (Fin m → Bool) ρ).symm, uprob_prod]
    rfl
  haveI : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : uexp q = 0 := by simp [uexp]
    rw [hexp, h0] at h
    linarith
  have hG := half_le_uprob_threshold q (fun x => uprob_le_one _) (by norm_num) hε.le (hexp ▸ h)
  have hgood : ∀ x, 1 / 2 + ε / 2 ≤ q x →
      1 / 2 ^ k * (1 / 2) ≤ uprob fun c : GuessCoins m k ρ =>
        guessRecover A k (f x) c = enc x := by
    intro x hx
    refine le_trans ?_ (uprob_guessRecover_ge (fun _ => f x) A (enc x))
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (one_sub_sum_le_uprob_eq
      (fun ω : (Fin k → Fin m → Bool) × (Fin m → NESubset k → ρ) =>
        idealRecover (fun _ => f x) A (enc x) ω.1 ω.2) (enc x))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [sq_nonneg ε]
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; norm_num at hpos
      · exact h0
    have hsum : ∑ i : Fin m, uprob (fun ω : (Fin k → Fin m → Bool) ×
        (Fin m → NESubset k → ρ) =>
          idealRecover (fun _ => f x) A (enc x) ω.1 ω.2 i ≠ enc x i) ≤
        ∑ _i : Fin m, 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
      sum_le_sum fun i _ => uprob_idealRecover_ne_le (fun _ => f x) A hk0 (enc x) i hε hx
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have : (m : ℝ) * (1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  rw [uprob_prod]
  have hcomb := uprob_mul_le_uexp (G := fun x => 1 / 2 + ε / 2 ≤ q x)
    (q := fun x => uprob fun c : GuessCoins m k ρ => guessRecover A k (f x) c = enc x)
    (fun x => uprob_nonneg _) hgood
  calc ε / (4 * 2 ^ k) = ε / 2 * (1 / 2 ^ k * (1 / 2)) := by field_simp; ring
    _ ≤ uprob (fun x => 1 / 2 + ε / 2 ≤ q x) * (1 / 2 ^ k * (1 / 2)) := by gcongr
    _ ≤ _ := hcomb

/-- **Goldreich–Levin on an encoded domain, with the padding carried along**: the bound of
`invProb_guessInverter_enc` on the sample space `(α × {0,1}^m) × coins` of the padded
collection `g_i(x, r) = (f_i(x), r)` of [PS10, Theorem 87.3] — the element `(x, r)` of the
padded domain together with the recovery coins, the padding `r` being unused by the recovery
procedure. This is the shape of the inner probability of `Collection.invProbAt` for
`Collection.glPad` and the form consumed by `Collection.OneWay.glPad_hardCore`
(run-3 audit P4-2). The proof is `invProb_guessInverter_enc` and the reshuffling of an
independent unused component (`uprob_fst`, `uprob_comp_equiv`). -/
theorem invProb_guessInverter_enc_pad {α β ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty ρ]
    {m : ℕ} (enc : α → Fin m → Bool) (f : α → β) (A : β × (Fin m → Bool) → ρ → Bool) {k : ℕ}
    {ε : ℝ} (hε : 0 < ε) (hk : 2 * (m : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ uprob fun z : (α × (Fin m → Bool)) × ρ =>
      A (f z.1.1, z.1.2) z.2 = ip (enc z.1.1) z.1.2) :
    ε / (4 * 2 ^ k) ≤ uprob fun z : (α × (Fin m → Bool)) × GuessCoins m k ρ =>
      guessRecover A k (f z.1.1) z.2 = enc z.1.1 := by
  refine le_trans (invProb_guessInverter_enc enc f A hε hk h) (le_of_eq ?_)
  let e : (α × GuessCoins m k ρ) × (Fin m → Bool) ≃ (α × (Fin m → Bool)) × GuessCoins m k ρ :=
    { toFun := fun w => ((w.1.1, w.2), w.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc uprob (fun z : α × GuessCoins m k ρ => guessRecover A k (f z.1) z.2 = enc z.1)
      = uprob (fun w : (α × GuessCoins m k ρ) × (Fin m → Bool) =>
          guessRecover A k (f w.1.1) w.1.2 = enc w.1.1) :=
        (uprob_fst (fun z : α × GuessCoins m k ρ => guessRecover A k (f z.1) z.2 = enc z.1)).symm
    _ = _ := uprob_comp_equiv e fun z : (α × (Fin m → Bool)) × GuessCoins m k ρ =>
          guessRecover A k (f z.1.1) z.2 = enc z.1.1

end TCSlib.Cryptography.HardcoreBit

## ===== TCSlib/Cryptography/Asymptotic/HardCorePermutation.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreClaims

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core bits for one-way permutations: the balanced Goldreich–Levin permutation

[PS10, §3.4] states its purpose as "the existence of OWPs implies the existence of OWPs with a
hard-core bit" (p. 86), from which [PS10, Theorem 79.4] builds a pseudorandom generator from
any one-way permutation (p. 84) and Chapter 4 builds commitment schemes
[PS10, Theorem 126.4]. Goldreich–Levin [PS10, Theorem 87.3] (`goldreich_levin`) provides
`g(x, r) = (f(x), r)` with `|x| = |r|`: a permutation of `{0,1}^{2n}` — a family defined at
*even* lengths only, with the typed input length `var + var` (`FunFamily.glPad`), which can
never be packaged as the `PermFamily` (one permutation of `{0,1}^n` for *every* `n`) that
`OneWayPermutation` and the consumers `owp_hardcore_prg`, `cor_81_7`, `owp_commitment`,
`exists_commitment_of_owp_hardCore` and `zk_proof_of_owp_levinReduction` take (run-3 audit,
finding P4-1: `glPad`'s input length is the syntactic polynomial `var + var ≠ var`).

This file closes the gap with the **balanced** Goldreich–Levin permutation
`PermFamily.glHalf`: at length `n` write `m := ⌊n/2⌋` and
`g_n(x ‖ w) := f_m(x) ‖ w` for `x ∈ {0,1}^m`, `w ∈ {0,1}^{n − m}` — the first `m` bits go
through `f_m`, the remaining `n − m` bits (`r`, plus one pass-through bit when `n` is odd) are
copied; the hard-core bit is `glHalfBit n (x ‖ w) := ⟨x, w|_m⟩`, the inner product of the
first two blocks of `m` bits. At even `n = m + m` this is literally `FunFamily.glPad` of `f`
at parameter `m` (`PermFamily.glHalf_f_even`, `glHalfBit_even`); at odd `n = m + m + 1` it is
`glPad` at `m` followed by an untouched bit (`PermFamily.glHalf_f_odd`, `glHalfBit_odd`), and
the prediction and inversion experiments at `n` are those of `glPad` at `m` with the extra
bit turned into a coin of the adversary (`predProb_glHalf_even`, `predProb_glHalf_odd`,
`invProb_glHalf_even`, `invProb_glHalf_odd_le`). The theorem `OneWayPermutation.glHalf` —
`f` a one-way permutation ⇒ `glHalf f` a one-way permutation with hard-core bit `glHalfBit` —
is the "(OWP)" clause of [PS10, Theorem 87.3] in the form every consumer needs;
`exists_owp_hardCore` and `exists_securePRG_of_owp` are the textbook consequences.

**Deviation:** the text's `g` is defined on `{0,1}^{2n}` only ("`|x| = |r|`"); `glHalf` is its
extension to every length by one pass-through bit at odd lengths, so that it is a
`PermFamily` (domain exactly `{0,1}^n` at every `n`, the frozen shape of DESIGN §2.9). The
pass-through bit is uniform and independent of `x`, so it costs nothing: one-wayness and the
hard-core property at `2m + 1` reduce to those of `glPad` at `m`.

## Main definitions

* `TCSlib.Cryptography.PermFamily.glHalf` — the balanced Goldreich–Levin permutation
  `x ‖ w ↦ f_{⌊n/2⌋}(x) ‖ w` (with `PermFamily.glHalfFun`, `PermFamily.glHalfInv`).
* `TCSlib.Cryptography.glHalfBit` — its hard-core bit `⟨x, w|_{⌊n/2⌋}⟩`.

## Main results

* `TCSlib.Cryptography.OneWayPermutation.glHalf` [PS10, Theorem 87.3, "(OWP)" clause]: a
  one-way permutation yields a one-way permutation with a hard-core bit (sorried under its
  sketch; the fill routes through `FunFamily.StrongOneWay.glPad` and
  `FunFamily.StrongOneWay.glPad_hardCore` at parameter `⌊n/2⌋`).
* `TCSlib.Cryptography.exists_owp_hardCore`, `TCSlib.Cryptography.exists_securePRG_of_owp`
  [PS10, §3.4, pp. 84 and 86]: the hypothesis of Theorems 79.4, 81.7 and 126.4 from one-way
  permutations alone; pseudorandom generators from one-way permutations.
* The proved bridges `PermFamily.glHalf_f_even`, `PermFamily.glHalf_f_odd`, `glHalfBit_even`,
  `glHalfBit_odd`, `predProb_glHalf_even`, `predProb_glHalf_odd`, `invProb_glHalf_even`,
  `invProb_glHalf_odd_le`, and `Negligible.comp_div_two` (negligible in `⌊n/2⌋` is negligible
  in `n`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4: Theorem 79.4; §3.3.5: Corollary 81.7; §3.4: pp. 84, 86; §3.4.2: Theorem 87.3;
  §4.7: Theorem 126.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3), §3.3 (Theorem 3.2).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The balanced permutation -/

/-- Transport of a permutation family along an equality of parameters: `P.f k` and `P.f m`
agree under the casts `Fin.cast` when `k = m` (used to pass between `⌊(m + m)/2⌋` and `m`). -/
theorem PermFamily.f_congr (P : PermFamily) {k m : ℕ} (h : k = m) (x : Fin k → Bool)
    (i : Fin k) :
    P.f k x i = P.f m (fun j => x (Fin.cast h.symm j)) (Fin.cast h i) := by
  subst h; rfl

/-- The forward map of the balanced Goldreich–Levin permutation at length `n`: position
`i < ⌊n/2⌋` carries bit `i` of `f_{⌊n/2⌋}` applied to the first `⌊n/2⌋` bits of the input, every
other position is copied. -/
def PermFamily.glHalfFun (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) : Bool :=
  if h : (i : ℕ) < n / 2 then
    P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩
  else z i

/-- The inverse map of the balanced Goldreich–Levin permutation: `f_{⌊n/2⌋}⁻¹` on the first
`⌊n/2⌋` bits, the identity elsewhere. -/
def PermFamily.glHalfInv (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) : Bool :=
  if h : (i : ℕ) < n / 2 then
    (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩
  else z i

/-- Unfolding of the forward map on the first block: position `j < ⌊n/2⌋` carries bit `j` of
`f_{⌊n/2⌋}(x)` where `x` is the first block of the input. -/
theorem PermFamily.glHalfFun_castLE (P : PermFamily) (n : ℕ) (z : Fin n → Bool)
    (j : Fin (n / 2)) :
    P.glHalfFun n z (Fin.castLE (Nat.div_le_self n 2) j) =
      P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) j := by
  simp only [PermFamily.glHalfFun, Fin.coe_castLE, j.isLt, dite_true]

/-- Unfolding of the inverse map on the first block. -/
theorem PermFamily.glHalfInv_castLE (P : PermFamily) (n : ℕ) (z : Fin n → Bool)
    (j : Fin (n / 2)) :
    P.glHalfInv n z (Fin.castLE (Nat.div_le_self n 2) j) =
      (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) j := by
  simp only [PermFamily.glHalfInv, Fin.coe_castLE, j.isLt, dite_true]

/-- The **balanced Goldreich–Levin permutation** of a permutation family `f`
[PS10, Theorem 87.3, "(OWP)" clause, parametrised by the output length]: at length `n`, with
`m := ⌊n/2⌋`, `g_n(x ‖ w) = f_m(x) ‖ w` for `x ∈ {0,1}^m` and `w ∈ {0,1}^{n − m}` — the text's
`g(x, r) = (f(x), r)` with `|x| = |r| = m` at even `n`, followed by one pass-through bit at
odd `n`. A permutation of `{0,1}^n` at every `n`, hence a `PermFamily` (which
`FunFamily.glPad`, of input length `var + var`, is not; run-3 audit P4-1).

**Deviation:** the text defines `g` on `{0,1}^{2n}` only; the odd lengths are filled by a
pass-through bit so that the family has the frozen `PermFamily` shape. -/
def PermFamily.glHalf (P : PermFamily) : PermFamily where
  f n :=
    { toFun := P.glHalfFun n
      invFun := P.glHalfInv n
      left_inv := fun z => by
        funext i
        by_cases h : (i : ℕ) < n / 2
        · have hfun : (fun j => P.glHalfFun n z (Fin.castLE (Nat.div_le_self n 2) j)) =
              P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) :=
            funext fun j => P.glHalfFun_castLE n z j
          have : i = Fin.castLE (Nat.div_le_self n 2) ⟨i, h⟩ := Fin.ext rfl
          rw [this, PermFamily.glHalfInv_castLE, hfun, Equiv.symm_apply_apply]
        · simp only [PermFamily.glHalfInv, PermFamily.glHalfFun, h, dite_false]
      right_inv := fun z => by
        funext i
        by_cases h : (i : ℕ) < n / 2
        · have hfun : (fun j => P.glHalfInv n z (Fin.castLE (Nat.div_le_self n 2) j)) =
              (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) :=
            funext fun j => P.glHalfInv_castLE n z j
          have : i = Fin.castLE (Nat.div_le_self n 2) ⟨i, h⟩ := Fin.ext rfl
          rw [this, PermFamily.glHalfFun_castLE, hfun, Equiv.apply_symm_apply]
        · simp only [PermFamily.glHalfInv, PermFamily.glHalfFun, h, dite_false] }

/-- Unfolding: `g_n(z)_i = f_{⌊n/2⌋}(z|_{⌊n/2⌋})_i` for `i < ⌊n/2⌋` and `z_i` otherwise. -/
theorem PermFamily.glHalf_f_apply (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) :
    P.glHalf.f n z i = if h : (i : ℕ) < n / 2 then
      P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩ else z i := rfl

/-- The inner product is invariant under transport along an equality of lengths. -/
theorem HardcoreBit.ip_cast {k m : ℕ} (h : k = m) (x r : Fin k → Bool) :
    HardcoreBit.ip x r =
      HardcoreBit.ip (fun j => x (Fin.cast h.symm j)) (fun j => r (Fin.cast h.symm j)) := by
  subst h; rfl

/-- The **hard-core bit of the balanced permutation**: `⟨x, w|_m⟩` with `m = ⌊n/2⌋`, the inner
product of the first block `x` of `m` bits with the following block of `m` bits
(the `r` of [PS10, Theorem 87.3]; the pass-through bit of odd `n` is ignored). It does not
depend on the permutation family. -/
def glHalfBit (n : ℕ) (z : Fin n → Bool) : Bool :=
  HardcoreBit.ip (fun j : Fin (n / 2) => z (Fin.castLE (Nat.div_le_self n 2) j))
    (fun j : Fin (n / 2) => z ⟨n / 2 + j, by omega⟩)

/-! ## Even lengths: the balanced permutation is `glPad` -/

/-- **At even length `m + m` the balanced permutation is the padded family**
`g(x, r) = (f(x), r)` of Goldreich–Levin at parameter `m`: `P.glHalf.f (m + m) = P.toFunFamily.glPad.f m`
as functions on `{0,1}^{m+m}` (`FunFamily.glPad`'s input length `var + var` evaluates to
`m + m`). -/
theorem PermFamily.glHalf_f_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z := by
  have hm : (m + m) / 2 = m := by omega
  funext i
  change P.glHalfFun (m + m) z i =
    Fin.append (P.f m fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j)) i
  by_cases h : (i : ℕ) < m
  · have hi : i = Fin.castAdd m ⟨i, h⟩ := Fin.ext rfl
    rw [hi, Fin.append_left]
    simp only [PermFamily.glHalfFun, Fin.coe_castAdd, hm, h, dite_true]
    rw [PermFamily.f_congr P hm]
    rfl
  · have hi : i = Fin.natAdd m ⟨i - m, by omega⟩ := Fin.ext (by simp; omega)
    rw [hi, Fin.append_right]
    simp only [PermFamily.glHalfFun, Fin.coe_natAdd, hm]
    rw [dif_neg (by omega)]

/-- **At even length the hard-core bit is Goldreich–Levin's `⟨x, r⟩`**:
`glHalfBit (m + m) = P.toFunFamily.glBit m` (`FunFamily.glBit`, the inner product of the two
halves). -/
theorem glHalfBit_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    glHalfBit (m + m) z = P.toFunFamily.glBit m z := by
  have hm : (m + m) / 2 = m := by omega
  change _ = HardcoreBit.ip (fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))
  unfold glHalfBit
  rw [HardcoreBit.ip_cast hm]
  congr 1
  funext j
  congr 1
  exact Fin.ext (by simp only [Fin.coe_cast, Fin.coe_natAdd]; omega)

/-- **Prediction experiments at even length**: predicting `glHalfBit` from `g_{m+m}` is
predicting `⟨x, r⟩` from `glPad f` at parameter `m` (the concrete `predProb` of
[Gar26, Definition 2.3]). -/
theorem predProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m) → Bool) → ρ → Bool) :
    predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) A =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) A := by
  unfold predProb
  congr 1
  funext z
  rw [PermFamily.glHalf_f_even, glHalfBit_even]

/-- **Inversion experiments at even length**: inverting `g_{m+m}` is inverting `glPad f` at
parameter `m`. -/
theorem invProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m) → Bool) → ρ → (Fin (m + m) → Bool)) :
    invProb (P.glHalf.f (m + m)) A = invProb (P.toFunFamily.glPad.f m) A := by
  unfold invProb
  congr 1
  funext z
  rw [PermFamily.glHalf_f_even, PermFamily.glHalf_f_even]

/-! ## Odd lengths: `glPad` followed by a pass-through bit -/

/-- **At odd length `m + m + 1` the balanced permutation is `glPad` at `m` followed by an
untouched bit**: `g(x ‖ r ‖ e) = (f(x) ‖ r) ‖ e`.

**Proof sketch.** Pointwise, with `⌊(m + m + 1)/2⌋ = m`. A position `i` is either the last
one (both sides give `e`: `Fin.snoc_last`, and the `dite` of `glHalfFun` takes its `else`
branch) or `castSucc j` with `j < m + m` (`Fin.eq_castSucc_or_eq_last`). For `j < m` both sides
are bit `j` of `f_m(x)` (`Fin.append_left`; the first block of `x ‖ r ‖ e` is `x` by
`Fin.snoc_castSucc`, transported along `⌊(m + m + 1)/2⌋ = m` by `PermFamily.f_congr`); for
`m ≤ j` both sides are the copied bit `r_{j − m}` (`Fin.append_right`, `Fin.snoc_castSucc`). -/
theorem PermFamily.glHalf_f_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) :
    P.glHalf.f (m + m + 1) (Fin.snoc z e) = Fin.snoc (P.toFunFamily.glPad.f m z) e := by
  have hm : (m + m + 1) / 2 = m := by omega
  funext i
  change P.glHalfFun (m + m + 1) (Fin.snoc z e) i =
    (Fin.snoc (Fin.append (P.f m fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))) e :
      Fin (m + m + 1) → Bool) i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    by_cases h : (j : ℕ) < m
    · have hj : j = Fin.castAdd m ⟨j, h⟩ := Fin.ext rfl
      rw [hj, Fin.append_left]
      simp only [PermFamily.glHalfFun, Fin.coe_castSucc, Fin.coe_castAdd, hm, h, dite_true]
      rw [PermFamily.f_congr P hm]
      have hx : (fun j' => (Fin.snoc z e : Fin (m + m + 1) → Bool)
          (Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j')) : Fin m → Bool) =
          fun j' => z (Fin.castAdd m j') := by
        funext j'
        have : Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j') =
            Fin.castSucc (Fin.castAdd m j') := Fin.ext (by simp)
        rw [this, Fin.snoc_castSucc]
      rw [hx]
      rfl
    · have hj : j = Fin.natAdd m ⟨j - m, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj, Fin.append_right]
      simp only [PermFamily.glHalfFun, Fin.coe_castSucc, Fin.coe_natAdd, hm]
      rw [dif_neg (by omega), Fin.snoc_castSucc]
  · rw [Fin.snoc_last]
    simp only [PermFamily.glHalfFun, Fin.val_last, hm]
    rw [dif_neg (by omega), Fin.snoc_last]

/-- **At odd length the hard-core bit ignores the pass-through bit**:
`glHalfBit (m + m + 1) (z ‖ e) = ⟨x, r⟩` for `z = x ‖ r`. -/
theorem glHalfBit_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) :
    glHalfBit (m + m + 1) (Fin.snoc z e) = P.toFunFamily.glBit m z := by
  have hm : (m + m + 1) / 2 = m := by omega
  change _ = HardcoreBit.ip (fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))
  unfold glHalfBit
  rw [HardcoreBit.ip_cast hm]
  congr 1
  · funext j
    have : Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j) =
        Fin.castSucc (Fin.castAdd m j) := Fin.ext (by simp)
    rw [this, Fin.snoc_castSucc]
  · funext j
    have : (⟨(m + m + 1) / 2 + ↑(Fin.cast hm.symm j), by omega⟩ : Fin (m + m + 1)) =
        Fin.castSucc (Fin.natAdd m j) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc, Fin.coe_natAdd]; omega)
    rw [this, Fin.snoc_castSucc]

/-- The re-encoding `(z, (e, c)) ↦ (z ‖ e, c)` of the sample spaces of the odd-length
experiments: the pass-through bit `e` of the input becomes a coin of the adversary. -/
private def snocCoins (m : ℕ) (ρ : Type*) :
    (Fin (m + m) → Bool) × (Bool × ρ) ≃ (Fin (m + m + 1) → Bool) × ρ where
  toFun w := (Fin.snoc w.1 w.2.1, w.2.2)
  invFun w := (Fin.init w.1, (w.1 (Fin.last _), w.2))
  left_inv w := by
    obtain ⟨z, e, c⟩ := w
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv w := by
    obtain ⟨z, c⟩ := w
    simp only [Fin.snoc_init_self]

/-- **Prediction experiments at odd length**: predicting `glHalfBit` from `g_{m+m+1}` with a
predictor `A` is predicting `⟨x, r⟩` from `glPad f` at parameter `m` with the predictor that
draws the pass-through bit `e` as an extra coin and calls `A` on `(f(x) ‖ r) ‖ e`. -/
theorem predProb_glHalf_odd {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m + 1) → Bool) → ρ → Bool) :
    predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) A =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => A (Fin.snoc y c.1) c.2) := by
  unfold predProb
  refine (uprob_eq_of_equiv (snocCoins m ρ) fun w => ?_).symm
  obtain ⟨z, e, c⟩ := w
  show (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c = P.toFunFamily.glBit m z) ↔
    (A (P.glHalf.f (m + m + 1) (Fin.snoc z e)) c = glHalfBit (m + m + 1) (Fin.snoc z e))
  rw [PermFamily.glHalf_f_odd, glHalfBit_odd P]

/-- **Inversion experiments at odd length**: an inverter `A` of `g_{m+m+1}` gives the inverter
of `glPad f` at parameter `m` that draws the pass-through bit `e`, calls `A` on `(f(x) ‖ r) ‖ e`
and drops the last bit of the answer; it inverts at least as often (a correct answer of `A`
has the right last bit and a correct `glPad`-preimage in front). -/
theorem invProb_glHalf_odd_le {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m + 1) → Bool) → ρ → (Fin (m + m + 1) → Bool)) :
    invProb (P.glHalf.f (m + m + 1)) A ≤
      invProb (P.toFunFamily.glPad.f m)
        (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => Fin.init (A (Fin.snoc y c.1) c.2)) := by
  unfold invProb
  rw [← uprob_comp_equiv (snocCoins m ρ)]
  refine uprob_mono fun w hw => ?_
  obtain ⟨z, e, c⟩ := w
  simp only [snocCoins, Equiv.coe_fn_mk, PermFamily.glHalf_f_odd] at hw ⊢
  have hw' : P.glHalf.f (m + m + 1)
      (Fin.snoc (Fin.init (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c))
        (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c (Fin.last _))) =
      Fin.snoc (P.toFunFamily.glPad.f m z) e := by
    rwa [Fin.snoc_init_self]
  rw [PermFamily.glHalf_f_odd] at hw'
  have := congrArg Fin.init hw'
  simpa only [Fin.init_snoc] using this

/-! ## Negligible functions of `⌊n/2⌋` -/

/-- **Negligible in `⌊n/2⌋` is negligible in `n`**: if `ν` is negligible then so is
`n ↦ ν(⌊n/2⌋)` (the reductions of `OneWayPermutation.glHalf` run the Goldreich–Levin adversaries
at parameter `⌊n/2⌋`).

**Proof sketch.** Given `c`, take `n₀` with `|ν m| < 1/m^{c+1}` for `m ≥ n₀`. For
`n ≥ 2(n₀ + 3^c + 1)` the value `m := ⌊n/2⌋` satisfies `m ≥ n₀`, `m ≥ 3^c` and `n ≤ 3m`, so
`n^c ≤ 3^c m^c ≤ m^{c+1}` and `|ν m| < 1/m^{c+1} ≤ 1/n^c`. -/
theorem Negligible.comp_div_two {ν : ℕ → ℝ} (hν : Negligible ν) :
    Negligible fun n => ν (n / 2) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := hν (c + 1)
  refine ⟨2 * (n₀ + 3 ^ c + 1), fun n hn => ?_⟩
  have hd : 0 < 3 ^ c := by positivity
  obtain ⟨hm, h3, hpos⟩ : n₀ ≤ n / 2 ∧ 3 ^ c ≤ n / 2 ∧ 0 < n / 2 := by
    generalize 3 ^ c = d at hd hn ⊢
    omega
  refine lt_of_lt_of_le (hn₀ (n / 2) hm) ?_
  have hmR : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  have hle : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 3 * (n / 2) := by omega
    exact_mod_cast this
  calc (n : ℝ) ^ c ≤ (3 * ((n / 2 : ℕ) : ℝ)) ^ c := by gcongr
    _ = (3 : ℝ) ^ c * ((n / 2 : ℕ) : ℝ) ^ c := by rw [_root_.mul_pow]
    _ ≤ ((n / 2 : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) ^ c := by
        gcongr
        exact_mod_cast h3
    _ = ((n / 2 : ℕ) : ℝ) ^ (c + 1) := by ring

/-! ## Encodings and machines for the balanced permutation -/

/-- The first `k` bits of an encoded string are the encoding of its restriction. -/
private theorem take_ofFn_castLE {n k : ℕ} (h : k ≤ n) (z : Fin n → Bool) :
    (List.ofFn z).take k = List.ofFn fun j : Fin k => z (Fin.castLE h j) := by
  refine List.ext_getElem (by simp [h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

/-- The `k` bits after the first `a` of an encoded string. -/
private theorem take_drop_ofFn {n a k : ℕ} (h : a + k ≤ n) (z : Fin n → Bool) :
    ((List.ofFn z).drop a).take k = List.ofFn fun j : Fin k => z ⟨a + j, by omega⟩ := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- **The encoding of `g_n(z)`**: `f_{⌊n/2⌋}` of the first block followed by the remaining bits
of `z`. -/
theorem PermFamily.ofFn_glHalf_f (P : PermFamily) (n : ℕ) (z : Fin n → Bool) :
    List.ofFn (P.glHalf.f n z) =
      List.ofFn (P.f (n / 2) fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ++
        (List.ofFn z).drop (n / 2) := by
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_ofFn, List.length_append, List.length_drop]
    omega
  simp only [List.length_ofFn] at hj₁
  rw [List.getElem_ofFn, PermFamily.glHalf_f_apply]
  by_cases h : j < n / 2
  · rw [dif_pos h, List.getElem_append_left (by simp [h]), List.getElem_ofFn]
  · rw [dif_neg h, List.getElem_append_right (by simp; omega), List.getElem_drop, List.getElem_ofFn]
    congr 1
    exact Fin.ext (by simp; omega)

/-- **The balanced permutation is easy to compute** from an evaluator `F` of `f` on `⟨1^n, x⟩`:
on `⟨1^n, z⟩` halve the parameter (`unaryHalf`), cut `z` after `⌊n/2⌋` bits, apply `F` to the
first block at parameter `⌊n/2⌋` and copy the rest. -/
theorem PermFamily.glHalf_easy (P : PermFamily) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x)) :
    P.glHalf.toFunFamily.Easy := by
  have huh : PolyTimeComputable fun w => unaryHalf (pairFstD w) :=
    ptcComp unaryHalf_poly polyTimeComputable_pairFstD
  refine ⟨fun w => F (pairEncode (unaryHalf (pairFstD w))
      ((pairSndD w).take (unaryHalf (pairFstD w)).length)) ++
      (pairSndD w).drop (unaryHalf (pairFstD w)).length,
    (ptcComp hF (huh.pairEncode (takeLen_poly huh polyTimeComputable_pairSndD))).append
      (dropLen_poly huh polyTimeComputable_pairSndD), fun n z => ?_⟩
  have hFx' : ∀ n (x : Fin n → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (P.f n x) := hFx
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, unaryHalf,
    List.length_replicate]
  rw [take_ofFn_castLE (Nat.div_le_self n 2), hFx', PermFamily.toFunFamily_f]
  exact (P.ofFn_glHalf_f n z).symm

/-- **The hard-core bit of the balanced permutation is easy to compute**: on `⟨1^n, z⟩` halve
the parameter, cut the two blocks of `⌊n/2⌋` bits and apply the inner-product evaluator
`ipFun`. -/
theorem glHalfBit_easy : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
    ∀ n (z : Fin n → Bool), H (NUPPT.advInput n (List.ofFn z)) = [glHalfBit n z] := by
  have huh : PolyTimeComputable fun w => unaryHalf (pairFstD w) :=
    ptcComp unaryHalf_poly polyTimeComputable_pairFstD
  refine ⟨fun w => ipFun (pairEncode ((pairSndD w).take (unaryHalf (pairFstD w)).length)
      (((pairSndD w).drop (unaryHalf (pairFstD w)).length).take (unaryHalf (pairFstD w)).length)),
    ptcComp ipFun_poly ((takeLen_poly huh polyTimeComputable_pairSndD).pairEncode
      (takeLen_poly huh (dropLen_poly huh polyTimeComputable_pairSndD))), fun n z => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, unaryHalf,
    List.length_replicate]
  rw [take_ofFn_castLE (Nat.div_le_self n 2), take_drop_ofFn (by omega), ipFun_ofFn]
  rfl

/-- The post-processing of the odd-length inverter: the answer truncated to the length of the
argument `y` (dropping the pass-through bit). -/
private def glHalfInvPost (v : List Bool) : List Bool :=
  (pairSndD v).take (NUPPT.inArg (pairFstD v)).length

/-- The post-processing of the odd-length inverter is polynomial-time. -/
private theorem glHalfInvPost_poly : PolyTimeComputable glHalfInvPost :=
  takeLen_poly (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairSndD

/-- The parameter `2m + 1` as a syntactic polynomial. -/
private def oddParam : PolyExpr := .add (.add .var .var) (.const 1)

/-- **The odd-length inverter**: for an inverter `A` of `glHalf` and the parameter `m`, the
machine at parameter `m` that draws one coin `e`, runs `A` at parameter `2m + 1` on `y ++ [e]`
and drops the last bit of the answer (`Complexity.NUPPT.reparam` and `NUPPT.wrap`). -/
noncomputable def glHalfOddInv (A : NUPPT) : NUPPT :=
  (A.reparam oddParam).wrap owpPredPre_poly glHalfInvPost_poly (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 1)

/-- **The odd-length predictor**: for a predictor `A` of `glHalfBit` and the parameter `m`, the
machine at parameter `m` that draws one coin `e`, runs `A` at parameter `2m + 1` on `y ++ [e]`
and returns its verdict. -/
noncomputable def glHalfOddPred (A : NUPPT) : NUPPT :=
  (A.reparam oddParam).wrap owpPredPre_poly polyTimeComputable_pairSndD (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 1)

/-- The coins `(e, c)` of the odd-length machines (for any post-processing `post`): the
pass-through bit and the coins of `A` at `2m + 1`. -/
private noncomputable def oddCoins (A : NUPPT) (m : ℕ) {post : List Bool → List Bool}
    (hpost : PolyTimeComputable post) :
    Bool × A.Coins (m + m + 1) ≃ (NUPPT.wrap (A.reparam oddParam) owpPredPre_poly hpost
      (fun _ => []) (.const 0) (fun _ => by simp) (.const 1)).Coins m :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (NUPPT.reparamCoins A oddParam m)).trans
    (Fin.appendEquiv 1 ((A.reparam oddParam).coinLen m))

/-- The encoding of the coins `(e, c)` is `[e] ++ c`. -/
private theorem ofFn_oddCoins (A : NUPPT) (m : ℕ) {post : List Bool → List Bool}
    (hpost : PolyTimeComputable post) (e : Bool) (c : A.Coins (m + m + 1)) :
    List.ofFn (oddCoins A m hpost (e, c)) =
      List.ofFn (fun _ : Fin 1 => e) ++ List.ofFn (NUPPT.reparamCoins A oddParam m c) := by
  simp only [oddCoins, Equiv.trans_apply]
  exact (ofFn_appendEquiv ((Equiv.funUnique (Fin 1) Bool).symm e) _).trans
    (congrArg (· ++ _) (by simp [List.ofFn_succ]))

/-- The odd-length inverter on `(e, c)` returns the first `|y|` bits of `A(1^{2m+1}, y ++ [e]; c)`. -/
private theorem glHalfOddInv_runAt (A : NUPPT) (m : ℕ) (y : List Bool) (e : Bool)
    (c : A.Coins (m + m + 1)) :
    (glHalfOddInv A).runAt m y (oddCoins A m glHalfInvPost_poly (e, c)) =
      (A.runAt (m + m + 1) (y ++ [e]) c).take y.length := by
  unfold glHalfOddInv
  rw [NUPPT.runAt_wrap (A.reparam oddParam) owpPredPre_poly glHalfInvPost_poly (fun _ => [])
    (.const 0) (fun _ => by simp) (.const 1) m y rfl (fun _ => e)
    (NUPPT.reparamCoins A oddParam m c) (oddCoins A m glHalfInvPost_poly (e, c))
    (ofFn_oddCoins A m glHalfInvPost_poly e c)]
  simp only [glHalfInvPost, owpPredPre, pairSndD_pairEncode, pairFstD_pairEncode,
    NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.runAt_reparam]
  rfl

/-- The odd-length predictor on `(e, c)` returns the verdict of `A(1^{2m+1}, y ++ [e]; c)`. -/
private theorem glHalfOddPred_runAt (A : NUPPT) (m : ℕ) (y : List Bool) (e : Bool)
    (c : A.Coins (m + m + 1)) :
    (glHalfOddPred A).runAt m y (oddCoins A m polyTimeComputable_pairSndD (e, c)) =
      A.runAt (m + m + 1) (y ++ [e]) c := by
  unfold glHalfOddPred
  rw [NUPPT.runAt_wrap (A.reparam oddParam) owpPredPre_poly polyTimeComputable_pairSndD
    (fun _ => []) (.const 0) (fun _ => by simp) (.const 1) m y rfl (fun _ => e)
    (NUPPT.reparamCoins A oddParam m c) (oddCoins A m polyTimeComputable_pairSndD (e, c))
    (ofFn_oddCoins A m polyTimeComputable_pairSndD e c)]
  simp only [owpPredPre, pairSndD_pairEncode, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.runAt_reparam]
  rfl

/-- **Inversion at even length**: inverting `glHalf` at `2m` with `A` is inverting `glPad` at
`m` with the parameter-change machine `A.reparam (var + var)`. -/
theorem glHalf_invProbAt_even (P : PermFamily) (A : NUPPT) (m : ℕ) :
    P.glHalf.toFunFamily.invProbAt A (m + m) =
      P.toFunFamily.glPad.invProbAt (A.reparam (.add .var .var)) m := by
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob]
  refine (OneWay.uprob_congr fun z => ?_).trans (uprob_comp_equiv
    ((Equiv.refl (Fin (m + m) → Bool)).prodCongr (NUPPT.reparamCoins A (.add .var .var) m)) _)
  obtain ⟨x, c⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, NUPPT.runAt_reparam,
    PermFamily.toFunFamily_f, PermFamily.glHalf_f_even]
  exact Iff.rfl

/-- **Inversion at odd length**: inverting `glHalf` at `2m + 1` with `A` is at most inverting
`glPad` at `m` with the odd-length inverter. -/
theorem glHalf_invProbAt_odd_le (P : PermFamily) (A : NUPPT) (m : ℕ) :
    P.glHalf.toFunFamily.invProbAt A (m + m + 1) ≤
      P.toFunFamily.glPad.invProbAt (glHalfOddInv A) m := by
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob]
  refine le_of_eq_of_le (uprob_comp_equiv (snocCoins m (A.Coins (m + m + 1))) _).symm ?_
  refine le_of_le_of_eq ?_ (uprob_comp_equiv
    ((Equiv.refl (Fin (m + m) → Bool)).prodCongr (oddCoins A m glHalfInvPost_poly)) _)
  refine uprob_mono fun w hw => ?_
  obtain ⟨z, e, c⟩ := w
  obtain ⟨x', hx', hfx'⟩ := hw
  simp only [snocCoins, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl,
    id, PermFamily.toFunFamily_f, PermFamily.glHalf_f_odd] at hx' hfx' ⊢
  rw [← Fin.snoc_init_self x', PermFamily.glHalf_f_odd] at hfx'
  have hinit := congrArg Fin.init hfx'
  simp only [Fin.init_snoc] at hinit
  refine ⟨Fin.init x', ?_, hinit⟩
  rw [glHalfOddInv_runAt, ← ofFn_snoc_eq, hx', List.length_ofFn, ofFn_eq_init_append,
    List.take_left' List.length_ofFn]

/-- **Prediction at even length**: predicting `glHalfBit` from `glHalf` at `2m` with `A` is
predicting `⟨x, r⟩` from `glPad` at `m` with `A.reparam (var + var)`. -/
theorem glHalf_predProb_even (P : PermFamily) (A : NUPPT) (m : ℕ) :
    predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        ((A.reparam (.add .var .var)).predictor m (m + m)) := by
  rw [predProb_glHalf_even]
  refine (predProb_coins_equiv _ _ _ _ (NUPPT.reparamCoins A (.add .var .var) m) fun y c => ?_).symm
  simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_reparam]
  rfl

/-- **Prediction at odd length**: predicting `glHalfBit` from `glHalf` at `2m + 1` with `A` is
predicting `⟨x, r⟩` from `glPad` at `m` with the odd-length predictor. -/
theorem glHalf_predProb_odd (P : PermFamily) (A : NUPPT) (m : ℕ) :
    predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) (A.predictor (m + m + 1) (m + m + 1)) =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        ((glHalfOddPred A).predictor m (m + m)) := by
  rw [predProb_glHalf_odd]
  refine (predProb_coins_equiv _ _ _ _ (oddCoins A m polyTimeComputable_pairSndD) fun y c => ?_).symm
  obtain ⟨e, c⟩ := c
  simp only [NUPPT.predictor, NUPPT.distinguisher]
  rw [glHalfOddPred_runAt, ← ofFn_snoc_eq]

/-- The absolute value of a negligible function is negligible. -/
private theorem negligible_abs {μ : ℕ → ℝ} (hμ : Negligible μ) : Negligible fun n => |μ n| :=
  hμ.mono ⟨0, fun n _ => by rw [abs_abs]⟩

/-! ## One-way permutations have a hard-core bit [PS10, Theorem 87.3, "(OWP)"] -/

/-- **One-way permutations have a hard-core bit** ([PS10, Theorem 87.3], the "(OWP)" clause,
and the stated purpose of [PS10, §3.4], p. 86: "the existence of OWPs implies the existence of
OWPs with a hard-core bit"): if `f` is a one-way permutation then the balanced Goldreich–Levin
permutation `g = glHalf f`, `g_n(x ‖ w) = f_{⌊n/2⌋}(x) ‖ w`, is a one-way permutation and
`glHalfBit`, `(x ‖ w) ↦ ⟨x, w|_{⌊n/2⌋}⟩`, is a hard-core predicate for it. This is the form of
Theorem 87.3 consumed by `owp_hardcore_prg` (Theorem 79.4), `cor_81_7`, `owp_commitment`
(Theorem 126.4) and the Chapter 4 headlines; `goldreich_levin` (the `FunFamily` form at even
lengths) cannot feed them (run-3 audit P4-1).

**Deviation:** the text's `g` lives on `{0,1}^{2n}`; odd lengths carry one pass-through bit
(see the module docstring). The text says hard-core "for `f`" (source error 26).

**Proof sketch.** Write `m := ⌊n/2⌋`, so that `n = m + m` or `n = m + m + 1`, and let
`𝓖 := P.toFunFamily.glPad` with `hG := hP.glPad : 𝓖.StrongOneWay` and
`hB := hP.glPad_hardCore : HardCore 𝓖 P.toFunFamily.glBit` (`goldreich_levin hP`).
*Easy (one-wayness clause):* from `hP.easy = ⟨F, hF, hFx⟩` the evaluator on `⟨1^n, z⟩`
computes `1^m` from `1^n` (unary halving: `polyTimeComputable_iterate` with state
`⟨1^k, 1^j⟩ ↦ ⟨1^{k−2}, 1^{j+1}⟩` for `R := var` rounds, reading the second component, or a
`Build/`-style primitive), cuts `z` after `m` bits (`polyTimeComputable_pairTakePoly`/
`pairDropPoly` on `⟨1^m, z⟩`) and outputs `F ⟨1^m, z.take m⟩ ++ z.drop m`
(`PolyTimeComputable.pairEncode`, `.comp`, `.append`); the identity with
`List.ofFn (P.glHalf.f n z)` is `PermFamily.glHalf_f_apply` (`List.ofFn` of the two blocks).
*One-wayness, even `n = m + m`:* for an inverter `A : NUPPT` of `glHalf`,
`NUPPT.exists_reparam A (mul (const 2) var)` gives `A'` with `A'.runAtL m y r = A.runAtL (2m) y r`
and coins `A.coins.subst (2·var)`, so `A'.Coins m ≃ A.Coins (m + m)` (`PolyExpr.eval_subst`,
`finCongr`); by `invProbAt_eq_uprob`, `uprob_comp_equiv` and `invProb_glHalf_even`,
`P.glHalf.toFunFamily.invProbAt A (m + m) = 𝓖.invProbAt A' m`, which is `≤ ν₁ m` with
`ν₁ := fun m => 𝓖.invProbAt A' m` negligible by `hG.hard A'`.
*One-wayness, odd `n = m + m + 1`:* `NUPPT.exists_split (const 1)` then `exists_reparam`
(`2·var + 1`) and `exists_comp` (post-processing `stripLast`) give `A''` at parameter `m` that
reads one coin `e`, calls `A` at `2m + 1` on `y ++ [e]` and drops the last bit of the answer;
`invProb_glHalf_odd_le` (with `invProbOpt_le_invProb`, a wrong-length answer of `A` failing on
both sides) bounds `P.glHalf.toFunFamily.invProbAt A (m + m + 1) ≤ 𝓖.invProbAt A'' m =: ν₂ m`,
negligible by `hG.hard A''`. *Combination:* `invProbAt A n ≤ ν₁ (n/2) + ν₂ (n/2)` for every
`n` (both terms nonnegative, `invProbAt_nonneg`), negligible by `Negligible.comp_div_two`,
`Negligible.add` and `Negligible.mono`.
*Hard-core, easy clause:* `⟨x, r⟩` on `⟨1^n, z⟩`: halve `1^n` as above, cut `z` into
`x := z.take m` and `r := (z.drop m).take m` (`pairTakePoly`/`pairDropPoly` on `⟨1^m, ·⟩`),
bitwise AND (`polyTimeComputable_pairXor`-style) and parity (a `polyTimeComputable_majority`-style
count modulo 2 by `polyTimeComputable_iterate`); the identity with `[glHalfBit n z]` unfolds
`glHalfBit` and `HardcoreBit.ip`.
*Hard-core, hardness:* for a predictor `A : NUPPT`, even `n = m + m`: `predProb_glHalf_even`
and the reparametrised `A'` (as above, with `NUPPT.predictor` in place of `inverter`) identify
`predProb (P.glHalf.f n) (glHalfBit n) (A.predictor n n)` with
`predProb (𝓖.f m) (P.toFunFamily.glBit m) (A'.predictor m (m + m))`, bounded by
`1/2 + ε₁ m` with `ε₁` negligible by `hB.hard A'`; odd `n = m + m + 1`: `predProb_glHalf_odd`
identifies it with the `glPad` experiment at `m` against `A''` built by
`NUPPT.exists_split (const 1)` (the pass-through bit is the first coin, passed as data and
appended to the input) and `exists_reparam`, bounded by `1/2 + ε₂ m` by `hB.hard A''`
(`uprob_comp_equiv` on the coin split `A''.Coins m ≃ Bool × A.Coins (m + m + 1)`). The single
negligible function of Definition 78.3 is `ε n := ε₁ (n/2) + ε₂ (n/2)` (`Negligible.comp_div_two`,
`Negligible.add`). -/
theorem OneWayPermutation.glHalf {P : PermFamily} (hP : OneWayPermutation P) :
    OneWayPermutation P.glHalf ∧ HardCore P.glHalf.toFunFamily glHalfBit := by
  have hG : P.toFunFamily.glPad.StrongOneWay := hP.glPad
  have hB : HardCore P.toFunFamily.glPad P.toFunFamily.glBit := hP.glPad_hardCore
  obtain ⟨F, hF, hFx⟩ := hP.easy
  refine ⟨⟨P.glHalf_easy hF hFx, fun A => ?_⟩, ⟨glHalfBit_easy, fun A => ?_⟩⟩
  · have h₁ := hG.hard (A.reparam (.add .var .var))
    have h₂ := hG.hard (glHalfOddInv A)
    refine (h₁.comp_div_two.add h₂.comp_div_two).mono ⟨0, fun n _ => ?_⟩
    have hn₁ := FunFamily.invProbAt_nonneg P.toFunFamily.glPad (A.reparam (.add .var .var)) (n / 2)
    have hn₂ := FunFamily.invProbAt_nonneg P.toFunFamily.glPad (glHalfOddInv A) (n / 2)
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (add_nonneg hn₁ hn₂)]
    obtain ⟨m, hm | hm⟩ : ∃ m, n = m + m ∨ n = m + m + 1 := ⟨n / 2, by omega⟩
    · subst hm
      rw [show (m + m) / 2 = m by omega] at hn₁ hn₂ ⊢
      rw [glHalf_invProbAt_even]
      linarith
    · subst hm
      rw [show (m + m + 1) / 2 = m by omega] at hn₁ hn₂ ⊢
      linarith [glHalf_invProbAt_odd_le P A m]
  · obtain ⟨ε₁, hε₁, hb₁⟩ := hB.hard (A.reparam (.add .var .var))
    obtain ⟨ε₂, hε₂, hb₂⟩ := hB.hard (glHalfOddPred A)
    refine ⟨fun n => |ε₁ (n / 2)| + |ε₂ (n / 2)|,
      (negligible_abs hε₁).comp_div_two.add (negligible_abs hε₂).comp_div_two, fun n => ?_⟩
    obtain ⟨m, hm | hm⟩ : ∃ m, n = m + m ∨ n = m + m + 1 := ⟨n / 2, by omega⟩
    · subst hm
      dsimp only
      rw [show (m + m) / 2 = m by omega]
      have key : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) ≤
          1 / 2 + ε₁ m := by
        rw [glHalf_predProb_even]; exact hb₁ m
      exact key.trans (by linarith [le_abs_self (ε₁ m), abs_nonneg (ε₂ m)])
    · subst hm
      dsimp only
      rw [show (m + m + 1) / 2 = m by omega]
      have key : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1))
          (A.predictor (m + m + 1) (m + m + 1)) ≤ 1 / 2 + ε₂ m := by
        rw [glHalf_predProb_odd]; exact hb₂ m
      exact key.trans (by linarith [le_abs_self (ε₂ m), abs_nonneg (ε₁ m)])

/-- **One-way permutations with a hard-core bit exist if one-way permutations do**
[PS10, §3.4, p. 86]: the hypothesis `∃ P h, OneWayPermutation P ∧ HardCore P.toFunFamily h`
of `exists_commitment_of_owp_hardCore` (Theorem 126.4), `zk_proof_of_owp_levinReduction` and
`zk_proof_of_mem_NP_of_owp` (Theorem 124.1) follows from `∃ P, OneWayPermutation P` alone, by
`OneWayPermutation.glHalf`. -/
theorem exists_owp_hardCore (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ (P : PermFamily) (b : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily b :=
  let ⟨P, hP⟩ := h
  ⟨P.glHalf, glHalfBit, hP.glHalf⟩

/-- **Pseudorandom generators from any one-way permutation** [PS10, §3.4, p. 84: "a PRG can
be constructed from any one-way permutation"; Theorems 79.4 and 87.3]: if a one-way
permutation exists then a secure pseudorandom generator exists, namely
`owpGenPRG P.glHalf glHalfBit`, `s ↦ glHalf f (s) ‖ glHalfBit s` (`owp_hardcore_prg` applied to
`OneWayPermutation.glHalf`). -/
theorem exists_securePRG_of_owp (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ G : PRG, G.Secure :=
  let ⟨P, hP⟩ := h
  ⟨owpGenPRG P.glHalf glHalfBit, owp_hardcore_prg P.glHalf glHalfBit hP.glHalf.1 hP.glHalf.2⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for ensembles and computational indistinguishability

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.Asymptotic.Ensembles` ([PS10, §3.1.1]: Lemma 71.5, the literal/`1^n`
bridges of Definition 69.4, the multicopy corollary of Lemma 71.6 and the prediction
Lemma 73.8). Everything here is ensemble-free: samplers at one parameter, `Complexity.NUPPT`
machines built by the closure calculus of `TCSlib.Complexity.Randomized.Closure`, and the
statistical-closeness device of `TCSlib.Cryptography.Asymptotic.Sampling`. The file exists
only to keep `Ensembles.lean` within the repository's size limit (workflow §4 (4)); its
declarations live in the inner namespace `TCSlib.Cryptography.EnsembleLemmas` and are not
part of the public API of the campaign.

## Main definitions

* `TCSlib.Cryptography.EnsembleLemmas.coinsEquiv` — the coin-splitting bijection
  `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b` (`Fin.appendEquiv` transported along the
  length equation).
* `TCSlib.Cryptography.EnsembleLemmas.padL` — the padded/truncated string `padFin` as a list.
* `TCSlib.Cryptography.EnsembleLemmas.blocks` — the blockwise bijection
  `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (the copy of `Ensembles.lean`'s private `blocks`).
* `TCSlib.Cryptography.EnsembleLemmas.CopiesLoop` — the state loop sampling `t(n)` copies
  with the challenge planted at a hard-wired position (the multicopy reduction as an FP
  function).

## Main results

* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv`, `acceptProb_coins_fst`,
  `acceptProb_not` — reindexing the coins of a distinguisher.
* `TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton` — no advantage on a
  one-point sample space.
* `TCSlib.Cryptography.EnsembleLemmas.exists_negRed`, `exists_pushRed`, `exists_copiesRed`
  — the machines of Lemmas 73.8, 71.5 and the multicopy corollary.
* `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam`, `acceptProb_reparam_advice`,
  `acceptProb_pushRed`, `acceptProb_negRed` — the acceptance probabilities of the
  reparametrised and composed machines.
* `TCSlib.Cryptography.EnsembleLemmas.statClose_copies`,
  `acceptProb_multicopyRed_congr` — replacing the ideal samplers of the multicopy reduction
  by exactly distributed polynomial-time samplers.
* `TCSlib.Cryptography.EnsembleLemmas.negligible_polyExpr_mul` — a syntactic polynomial
  times a negligible function is negligible.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1.1: Lemmas 71.5, 71.6 and 73.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Lemmas 3.2 and 3.3).
-/

namespace TCSlib.Cryptography.EnsembleLemmas

open Complexity Turing Finset

/-! ### Reindexing acceptance probabilities -/

section Probability

variable {σ τ γ ρ κ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] [Fintype κ]

/-- Relabelling the coin space of a distinguisher by a bijection does not change the
acceptance probability (the coin analogue of `acceptProb_comp_equiv`). -/
theorem acceptProb_coins_equiv (e : κ ≃ ρ) (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => D z (e c)) = acceptProb X D :=
  uprob_eq_of_equiv ((Equiv.refl σ).prodCongr e)
    (q := fun w : σ × ρ => D (X w.1) w.2 = true) fun _ => Iff.rfl

/-- Coins the distinguisher never reads (a second, ignored coin factor) do not change the
acceptance probability. -/
theorem acceptProb_coins_fst [Nonempty κ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z (c : ρ × κ) => D z c.1) = acceptProb X D :=
  (uprob_eq_of_equiv (Equiv.prodAssoc σ ρ κ).symm
    (q := fun w : (σ × ρ) × κ => D (X w.1.1) w.1.2 = true) fun _ => Iff.rfl).trans
    (uprob_fst fun w : σ × ρ => D (X w.1) w.2 = true)

/-- Negating the verdict complements the acceptance probability. -/
theorem acceptProb_not [Nonempty σ] [Nonempty ρ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X (fun z c => !(D z c)) = 1 - acceptProb X D := by
  unfold acceptProb
  rw [← uprob_not]
  congr 1
  funext w
  simp

/-- The probability of a constant event on a nonempty type is its indicator. -/
theorem uprob_const {α : Type*} [Fintype α] [Nonempty α] (p : Prop) [Decidable p] :
    uprob (fun _ : α => p) = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]
    have : (fun _ : α => p) = fun _ => True :=
      funext fun _ => propext ⟨fun _ => trivial, fun _ => hp⟩
    rw [this, uprob_true]
  · rw [if_neg hp]
    have : (fun _ : α => p) = fun _ => False := funext fun _ => propext ⟨hp, False.elim⟩
    rw [this, uprob_false]

/-- Two samplers into a subsingleton type have the same law. -/
theorem statClose_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) : StatClose X Y 0 := by
  classical
  intro T
  have c := X (Classical.arbitrary σ)
  have hX : ∀ s, X s = c := fun s => Subsingleton.elim _ _
  have hY : ∀ t, Y t = c := fun t => Subsingleton.elim _ _
  simp only [hX, hY, uprob_const, sub_self, abs_zero, le_refl]

/-- No distinguisher has an advantage between two samplers into a subsingleton type (the
case `t(n) = 0` of the multicopy corollary). -/
theorem distAdv_eq_zero_of_subsingleton [Subsingleton γ] [Nonempty σ] [Nonempty τ] (X : σ → γ)
    (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D = 0 :=
  le_antisymm (distAdv_le_of_statClose X Y (statClose_of_subsingleton X Y) D) (abs_nonneg _)

end Probability

/-! ### Coin splitting -/

/-- The coin-splitting bijection `{0,1}^a × {0,1}^b ≃ {0,1}^m` for `m = a + b`:
`Fin.appendEquiv` transported along the length equation. -/
def coinsEquiv {m a b : ℕ} (h : m = a + b) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin m → Bool) :=
  (Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h.symm) (Equiv.refl Bool))

/-- The coin string of a split pair is the concatenation of the two coin strings. -/
theorem ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (coinsEquiv h c) = List.ofFn c.1 ++ List.ofFn c.2 := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr h.symm (Fin.append c.1 c.2)).symm

/-- The first `a` coins of a split pair. -/
theorem take_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).take a = List.ofFn c.1 := by
  rw [ofFn_coinsEquiv, List.take_left' List.length_ofFn]

/-- The coins of a split pair after the first `a`. -/
theorem drop_ofFn_coinsEquiv {m a b : ℕ} (h : m = a + b) (c : (Fin a → Bool) × (Fin b → Bool)) :
    (List.ofFn (coinsEquiv h c)).drop a = List.ofFn c.2 := by
  rw [ofFn_coinsEquiv, List.drop_left' List.length_ofFn]

/-! ### Padding as an FP function -/

/-- The padded/truncated string of `padFin` as a list: exactly `k` bits, the bits of `a`
followed by `false`s. -/
def padL (k : ℕ) (a : List Bool) : List Bool := List.ofFn (padFin k a)

/-- `padL` has exactly `k` bits. -/
theorem length_padL (k : ℕ) (a : List Bool) : (padL k a).length = k := List.length_ofFn

/-- `padL k a` is the first `k` bits of `a ++ 0^k`. -/
theorem padL_eq (k : ℕ) (a : List Bool) : padL k a = (a ++ List.replicate k false).take k := by
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp [padL]
  · simp only [padL, List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD, List.getElem_take,
      List.getElem_append]
    split_ifs with h
    · simp [List.getElem?_eq_getElem h]
    · simp [List.getElem?_eq_none_iff.2 (not_lt.1 h)]

/-- Composition of polynomial-time functions, in applied form. -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The all-`false` string `0^{p(|u z|)}` is polynomial-time: the bitwise xor of `1^{p(|u z|)}`
with itself (`Complexity.polyTimeComputable_pairXor`, `Complexity.polyTimeComputable_unaryPoly`). -/
theorem polyTimeComputable_zeros (p : PolyExpr) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) :
    PolyTimeComputable fun z => List.replicate (p.eval (u z).length) false := by
  have h1 := StateLoop.unaryPoly_comp p hu
  convert ptc_comp polyTimeComputable_pairXor (h1.pairEncode h1) using 1
  funext z
  simp

/-- **Padding is polynomial-time:** `z ↦ padL (p(|u z|)) (a z)` for polynomial-time `u`, `a`
(the first `p(|u z|)` bits of `a z ++ 0^{p(|u z|)}`, a typed cut
`Complexity.polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_padL (p : PolyExpr) {u a : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) :
    PolyTimeComputable fun z => padL (p.eval (u z).length) (a z) := by
  convert ptc_comp (polyTimeComputable_pairTakePoly p)
    (hu.pairEncode (ha.append (polyTimeComputable_zeros p hu))) using 1
  funext z
  simp [padL_eq]

/-! ### The negated distinguisher of the prediction lemma -/

/-- Negating a verdict (`[true] ↦ [false]`, anything else `↦ [true]`) is polynomial-time
(`Complexity.polyTimeComputable_ite` on the equality test `Complexity.polyTimeComputable_pairEq`). -/
theorem polyTimeComputable_negVerdict :
    PolyTimeComputable fun w => if w = [true] then [false] else [true] := by
  have htest : PolyTimeComputable fun w => [decide (w = [true])] := by
    convert ptc_comp polyTimeComputable_pairEq
      (polyTimeComputable_id.pairEncode (polyTimeComputable_const [true])) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext w
  simp

/-- **The negated machine** of [PS10, Lemma 73.8]: for an `NUPPT` `D` there is an `NUPPT`
`B` with the same coins outputting `[true]` iff `D` does not output `[true]`
(`Complexity.NUPPT.exists_comp` with the post-processing `polyTimeComputable_negVerdict`). -/
theorem exists_negRed (D : NUPPT) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true] := by
  obtain ⟨B, hc, -, -, hB⟩ := D.exists_comp polyTimeComputable_id polyTimeComputable_negVerdict
  exact ⟨B, hc, hB⟩

/-- The negated machine accepts exactly when the original rejects: its acceptance probability
is the complement. -/
theorem acceptProb_negRed {σ : Type*} [Fintype σ] [Nonempty σ] {B D : NUPPT} (hBc : B.coins = D.coins)
    (hB : ∀ n y r, B.runAtL n y r = if D.runAtL n y r = [true] then [false] else [true])
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = 1 - acceptProb X (D.distinguisher n m) := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hBc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e, ← acceptProb_not]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hB]
  split_ifs <;> simp_all

/-! ### Parameter changes -/

/-- The acceptance probability of `NUPPT.exists_reparam D p` at parameter `n` is that of `D`
at parameter `p(n)`: the coin types correspond along `PolyExpr.eval_subst`. -/
theorem acceptProb_reparam {σ : Type*} [Fintype σ] {B D : NUPPT} {p : PolyExpr}
    (hBc : B.coins = D.coins.subst p) (hB : ∀ n y r, B.runAtL n y r = D.runAtL (p.eval n) y r)
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) = acceptProb X (D.distinguisher (p.eval n) m) := by
  have hlen : D.coinLen (p.eval n) = B.coinLen n := by
    simp [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : D.Coins (p.eval n) ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hofn, hB]

/-- The acceptance probability of `NUPPT.exists_reparam_advice D φ p` at parameter `m` is that
of `D` at parameter `φ m`: the unread coins are an independent uniform factor
(`acceptProb_coins_fst`) after the split `coinsEquiv`. -/
theorem acceptProb_reparam_advice {σ : Type*} [Fintype σ] {A D : NUPPT} {φ : ℕ → ℕ} {p : PolyExpr}
    (hAc : A.coins = D.coins.subst p)
    (hA : ∀ n y r, A.runAtL n y r = D.runAtL (φ n) y (r.take (D.coinLen (φ n))))
    (m : ℕ) (hle : D.coinLen (φ m) ≤ D.coinLen (p.eval m)) (k : ℕ) (X : σ → Fin k → Bool) :
    acceptProb X (A.distinguisher m k) = acceptProb X (D.distinguisher (φ m) k) := by
  have hlen : A.coinLen m = D.coinLen (φ m) + (D.coinLen (p.eval m) - D.coinLen (φ m)) := by
    have : A.coinLen m = D.coinLen (p.eval m) := by
      simp [NUPPT.coinLen, hAc, PolyExpr.eval_subst]
    omega
  rw [← acceptProb_coins_equiv (coinsEquiv hlen)]
  conv_rhs => rw [← acceptProb_coins_fst (κ := Fin (D.coinLen (p.eval m) - D.coinLen (φ m)) → Bool)
    X (D.distinguisher (φ m) k)]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hA, take_ofFn_coinsEquiv]

/-! ### The machine of Lemma 71.5 -/

/-- **The machine of [PS10, Lemma 71.5]:** for `NUPPT`s `M`, `D` and an output length `ℓ'`
there is an `NUPPT` `B` with coins `M.coins + D.coins` that runs `M` on its input with the
first `M.coins n` coins, pads the result to `ℓ'(n)` bits and hands it to `D` with the remaining
coins. The padding is done inside the raw function of the layout, where `1^n` is available
(run-3 audit note P2-4: `NUPPT.exists_comp` sees only `y`).

**Proof sketch.** As `Complexity.NUPPT.exists_seq`: advice `combineAdvice (M.advice n) (D.advice n)`;
the raw function cuts the coins at `M.coins(|1^n|)` (`polyTimeComputable_pairTakePoly`/`pairDropPoly`),
runs `M.output` on `layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pads with
`polyTimeComputable_padL ℓ'` against `inParam z`, and runs `D.output` on
`layout (inParam z) (padded) (pairSndD (inAdvice z)) r₂`; the equation is
`NUPPT.runAtL_ofPolyTime` plus the projection identities. -/
theorem exists_pushRed (M D : NUPPT) (ℓ' : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add M.coins D.coins ∧
      ∀ n y r, B.runAtL n y r =
        D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hr₁ := ptc_comp (polyTimeComputable_pairTakePoly M.coins) hcut
  have hr₂ := ptc_comp (polyTimeComputable_pairDropPoly M.coins) hcut
  have ha := ptc_comp M.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      NUPPT.polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice) hr₁)
  have hpad := polyTimeComputable_padL ℓ' NUPPT.polyTimeComputable_inParam ha
  have hF := ptc_comp D.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hpad
      (ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (NUPPT.combineAdvice (M.advice n) (D.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) M.adv) (.const 2)) D.adv).eval n := fun n => by
    have h₁ := NUPPT.length_combineAdvice_le (M.advice n) (D.advice n)
    have h₂ := M.advice_length n
    have h₃ := D.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨NUPPT.ofPolyTime hF (.add M.coins D.coins) _
    (fun n => NUPPT.combineAdvice (M.advice n) (D.advice n)) hadv, rfl, fun n y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inParam, NUPPT.inArg,
    NUPPT.inAdvice, NUPPT.inCoins]

/-- The acceptance probability of the machine of `exists_pushRed` on a sampler `X` is the
acceptance probability of `D` on the pushed sampler `(s, c) ↦ padFin (ℓ' n) (M(1^n, X s; c))`
(`acceptProb_bind` after the coin split `coinsEquiv`). -/
theorem acceptProb_pushRed {σ : Type*} [Fintype σ] {M D B : NUPPT} {ℓ' : PolyExpr}
    (hBc : B.coins = .add M.coins D.coins)
    (hB : ∀ n y r, B.runAtL n y r =
      D.runAtL n (padL (ℓ'.eval n) (M.runAtL n y (r.take (M.coinLen n)))) (r.drop (M.coinLen n)))
    (n m : ℕ) (X : σ → Fin m → Bool) :
    acceptProb X (B.distinguisher n m) =
      acceptProb (fun z : σ × M.Coins n => padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X z.1)) z.2))
        (D.distinguisher n (ℓ'.eval n)) := by
  have hlen : B.coinLen n = M.coinLen n + D.coinLen n := by simp [NUPPT.coinLen, hBc]
  rw [← acceptProb_coins_equiv (coinsEquiv hlen),
    ← acceptProb_bind X (fun t c => padFin (ℓ'.eval n) (M.runAt n (List.ofFn t) c))
      (D.distinguisher n (ℓ'.eval n))]
  congr 1
  funext z c
  simp only [NUPPT.distinguisher, NUPPT.runAt_eq, hB, take_ofFn_coinsEquiv, drop_ofFn_coinsEquiv,
    padL]

/-! ### Negligible functions and syntactic polynomials -/

/-- A syntactic polynomial times a negligible function is negligible: `p(n) ≤ C(n+1)^c ≤
C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), then `Negligible.mul_pow` and
`Negligible.const_mul`. -/
theorem negligible_polyExpr_mul (p : PolyExpr) {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  refine ((hμ.mul_pow e).const_mul ((C * 2 ^ e : ℕ) : ℝ)).mono ⟨1, fun n hn => ?_⟩
  have hp : (0 : ℝ) ≤ p.eval n := by positivity
  have hC : (0 : ℝ) ≤ ((C * 2 ^ e : ℕ) : ℝ) := by positivity
  have hne : (0 : ℝ) ≤ (n : ℝ) ^ e := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hC, abs_of_nonneg hne]
  have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
  have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
    apply pow_le_pow_left₀ (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc (p.eval n : ℝ) * |μ n| ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * |μ n| :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
          (abs_nonneg _)
    _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * |μ n|) := by push_cast; ring

/-! ### Blocks and chunks -/

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (the copy of the private `blocks` of
`Asymptotic/Ensembles.lean` and `Asymptotic/OneWay.lean`): block `i`, bit `j` is bit
`finProdFinEquiv (i, j) = j + ℓ·i` of the string. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Unfolding `blocks`. -/
theorem blocks_apply (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    blocks q ℓ w i j = w (finProdFinEquiv (i, j)) := rfl

/-- Unfolding `blocks.symm`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (V : Fin q → Fin ℓ → Bool) (x : Fin (q * ℓ)) :
    (blocks q ℓ).symm V x = V (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := rfl

/-- The index `i·ℓ + j` decodes to block `i`, bit `j`. -/
theorem finProdFinEquiv_symm_mk {q ℓ : ℕ} (i : Fin q) (j : Fin ℓ) (h : i * ℓ + j < q * ℓ) :
    finProdFinEquiv.symm (⟨i * ℓ + j, h⟩ : Fin (q * ℓ)) = (i, j) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [finProdFinEquiv]
  ring

/-- The `i`-th chunk of `s` bits of the string of a `q·s`-bit word is its block `i`. -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, blocks_apply]
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

/-- The string of `(blocks q ℓ).symm V` is the concatenation of the `q` block strings
(`List.ofFn_mul`). -/
theorem ofFn_blocks_symm {q ℓ : ℕ} (V : Fin q → Fin ℓ → Bool) (F : ℕ → List Bool)
    (hF : ∀ i (h : i < q), F i = List.ofFn (V ⟨i, h⟩)) :
    List.ofFn ((blocks q ℓ).symm V) = (List.range q).flatMap F := by
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange, List.map_map, List.ofFn_eq_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [Function.comp_apply, hF i i.isLt]
  congr 1
  funext j
  rw [blocks_symm_apply, finProdFinEquiv_symm_mk]

/-- The concatenation of `q` chunks of `ℓ` bits has `q·ℓ` bits. -/
theorem length_flatMap_range (F : ℕ → List Bool) {q ℓ : ℕ} (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range q).flatMap F).length = q * ℓ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append,
      ih fun i hi => hF i (Nat.lt_succ_of_lt hi), List.flatMap_singleton,
      hF q (Nat.lt_succ_self q), Nat.succ_mul]

/-- Truncating the concatenation of `m ≥ q` chunks to `q·ℓ` bits keeps the first `q` chunks. -/
theorem take_flatMap_range (F : ℕ → List Bool) {q m ℓ : ℕ} (hq : q ≤ m)
    (hF : ∀ i < q, (F i).length = ℓ) :
    ((List.range m).flatMap F).take (q * ℓ) = (List.range q).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [List.range_add, List.flatMap_append, List.take_left' (length_flatMap_range F hF)]

/-! ### Exactly distributed samplers under `copies` -/

/-- Splitting a tuple into its head and its tail. -/
def consSplit (κ : Type*) (t : ℕ) : (Fin (t + 1) → κ) ≃ κ × (Fin t → κ) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext <;> simp [Fin.tail_cons]

/-- Exactly distributed samplers stay exactly distributed under `copies`.

**Proof sketch.** Induction on the number of copies `t`. For `t = 0` both samplers take
values in the one-point type `Fin 0 → γ` (`statClose_of_subsingleton`). For `t + 1`,
`StatClose.prod` of the hypothesis with the induction hypothesis gives the pair sampler
`c ↦ (X' (c 0), copies t X' (tail c))`, `StatClose.map` with `Fin.cons` reassembles the
tuple, and `consSplit` reindexes both seed spaces along `(Fin (t+1) → κ) ≃ κ × (Fin t → κ)`;
the composite is `copies (t + 1)` by `Fin.cases`. -/
theorem statClose_copies {κ σ γ : Type*} [Fintype κ] [Fintype σ] {X' : κ → γ} {X : σ → γ}
    (h : StatClose X' X 0) : ∀ t : ℕ, StatClose (copies t X') (copies t X) 0
  | 0 => statClose_of_subsingleton _ _
  | t + 1 => by
    have hp := (h.prod (statClose_copies h t)).map
      fun p : γ × (Fin t → γ) => (Fin.cons p.1 p.2 : Fin (t + 1) → γ)
    rw [add_zero] at hp
    have e := (hp.comp_equiv_left (consSplit κ t)).comp_equiv_right (consSplit σ t)
    have h1 : copies (t + 1) X' =
        fun f => Fin.cons (X' ((consSplit κ t) f).1) (copies t X' ((consSplit κ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies, consSplit]
      · simp [copies, consSplit, Fin.tail]
    have h2 : copies (t + 1) X =
        fun f => Fin.cons (X ((consSplit σ t) f).1) (copies t X ((consSplit σ t) f).2) := by
      funext f i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [copies, consSplit]
      · simp [copies, consSplit, Fin.tail]
    rw [h1, h2]
    exact e

/-- Reindexing `ζ × (S × ρ) ≃ S × (ζ × ρ)`. -/
def swapAux (ζ S ρ : Type*) : ζ × (S × ρ) ≃ S × (ζ × ρ) where
  toFun w := (w.2.1, (w.1, w.2.2))
  invFun v := (v.2.1, (v.1, v.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Replacing the ideal samplers of the multicopy reduction by exactly distributed ones**
leaves the acceptance probability unchanged: the other `t − 1` copies are drawn from
`X'`, `Y'` (statistically identical to `X`, `Y`), the challenge `Z` and the coins of `D` are
auxiliary coins (`StatClose.abs_uprob_sub_le_prod` at `δ = 0` after `statClose_copies` and
`StatClose.prod`). -/
theorem acceptProb_multicopyRed_congr {κX κY σ τ ζ γ ρ : Type*} [Fintype κX] [Fintype κY]
    [Fintype σ] [Fintype τ] [Fintype ζ] [Fintype ρ] {X' : κX → γ} {X : σ → γ} {Y' : κY → γ}
    {Y : τ → γ} (hX : StatClose X' X 0) (hY : StatClose Y' Y 0) (Z : ζ → γ) (t k : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb Z (multicopyRed X' Y' t k D) = acceptProb Z (multicopyRed X Y t k D) := by
  have hG := (statClose_copies hX t).prod (statClose_copies hY t)
  rw [add_zero] at hG
  have key := hG.abs_uprob_sub_le_prod fun (uv : (Fin t → γ) × (Fin t → γ)) (w : ζ × ρ) =>
    D (fun i => if (i : ℕ) < k then uv.2 i else if (i : ℕ) = k then Z w.1 else uv.1 i) w.2 = true
  rw [abs_nonpos_iff, sub_eq_zero] at key
  calc acceptProb Z (multicopyRed X' Y' t k D)
      = uprob fun v : ((Fin t → κX) × (Fin t → κY)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y' v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X' v.1.1 i) v.2.2 = true :=
        uprob_eq_of_equiv (swapAux ζ ((Fin t → κX) × (Fin t → κY)) ρ) fun _ => Iff.rfl
    _ = uprob fun v : ((Fin t → σ) × (Fin t → τ)) × (ζ × ρ) =>
          D (fun i => if (i : ℕ) < k then copies t Y v.1.2 i
            else if (i : ℕ) = k then Z v.2.1 else copies t X v.1.1 i) v.2.2 = true := key
    _ = acceptProb Z (multicopyRed X Y t k D) :=
        (uprob_eq_of_equiv (swapAux ζ ((Fin t → σ) × (Fin t → τ)) ρ) fun _ => Iff.rfl).symm

/-! ### The sampler loop of the multicopy reduction -/

namespace CopiesLoop

/-- The parameter slot `u` of the state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The unary round counter `cnt` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary hybrid index `kk` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- The challenge `z` of the state word. -/
def p₄ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD w)))

/-- The remaining coins `rX` for the copies of `X`. -/
def p₅ (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The remaining coins `rY` for the copies of `Y`. -/
def p₆ (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD (pairSndD w))))

/-- The state word `⟨u, ⟨cnt, ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`. -/
def st (u cnt kk z rX rY : List Bool) : List Bool :=
  pairEncode u (pairEncode cnt (pairEncode kk (pairEncode z (pairEncode rX rY))))

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u cnt kk z rX rY : List Bool) : p₁ (st u cnt kk z rX rY) = u := by
  simp [p₁, st]

/-- Reading the counter. -/
@[simp] theorem p₂_st (u cnt kk z rX rY : List Bool) : p₂ (st u cnt kk z rX rY) = cnt := by
  simp [p₂, st]

/-- Reading the hybrid index. -/
@[simp] theorem p₃_st (u cnt kk z rX rY : List Bool) : p₃ (st u cnt kk z rX rY) = kk := by
  simp [p₃, st]

/-- Reading the challenge. -/
@[simp] theorem p₄_st (u cnt kk z rX rY : List Bool) : p₄ (st u cnt kk z rX rY) = z := by
  simp [p₄, st]

/-- Reading the coins for `X`. -/
@[simp] theorem p₅_st (u cnt kk z rX rY : List Bool) : p₅ (st u cnt kk z rX rY) = rX := by
  simp [p₅, st]

/-- Reading the coins for `Y`. -/
@[simp] theorem p₆_st (u cnt kk z rX rY : List Bool) : p₆ (st u cnt kk z rX rY) = rY := by
  simp [p₆, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The projections are polynomial-time. -/
theorem p₄_poly : PolyTimeComputable p₄ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The projections are polynomial-time. -/
theorem p₅_poly : PolyTimeComputable p₅ :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- The projections are polynomial-time. -/
theorem p₆_poly : PolyTimeComputable p₆ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))

/-- Assembling a state word from six polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ f₄ f₅ f₆ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) (h₄ : PolyTimeComputable f₄)
    (h₅ : PolyTimeComputable f₅) (h₆ : PolyTimeComputable f₆) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) (f₄ z) (f₅ z) (f₆ z) :=
  h₁.pairEncode (h₂.pairEncode (h₃.pairEncode (h₄.pairEncode (h₅.pairEncode h₆))))

/-- `2|fst z| + |snd z| ≤ |z|` for every word (equality plus two on pairs, `0 ≤ |z|` on
malformed words). -/
theorem two_mul_length_pairFstD_add_le (z : List Bool) :
    2 * (pairFstD z).length + (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, pairSndD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z a b h
    subst hz
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    omega

variable (sX sY : PolyExpr)

/-- The step: append a token to the counter and drop one chunk from each coin string
(`sX(|u|)` bits of `rX`, `sY(|u|)` bits of `rY`). -/
def step (w : List Bool) : List Bool :=
  st (p₁ w) (true :: p₂ w) (p₃ w) (p₄ w) ((p₅ w).drop (sX.eval (p₁ w).length))
    ((p₆ w).drop (sY.eval (p₁ w).length))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rX⟩`,
`⟨u, rY⟩`). -/
theorem step_poly : PolyTimeComputable (step sX sY) := by
  convert st_poly p₁_poly (ptc_comp (StateLoop.cons_poly true) p₂_poly) p₃_poly p₄_poly
    (ptc_comp (polyTimeComputable_pairDropPoly sX) (p₁_poly.pairEncode p₅_poly))
    (ptc_comp (polyTimeComputable_pairDropPoly sY) (p₁_poly.pairEncode p₆_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most `12` symbols (the pairing overhead; the coins only
shrink). -/
theorem length_step_le (w : List Bool) : (step sX sY w).length ≤ w.length + 12 := by
  have h₁ := two_mul_length_pairFstD_add_le w
  have h₂ := two_mul_length_pairFstD_add_le (pairSndD w)
  have h₃ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD w))
  have h₄ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD w)))
  have h₅ := two_mul_length_pairFstD_add_le (pairSndD (pairSndD (pairSndD (pairSndD w))))
  have d₅ : ((p₅ w).drop (sX.eval (p₁ w).length)).length ≤ (p₅ w).length := by simp
  have d₆ : ((p₆ w).drop (sY.eval (p₁ w).length)).length ≤ (p₆ w).length := by simp
  simp only [step, st, length_pairEncode, List.length_cons, p₁, p₂, p₃, p₄, p₅, p₆] at *
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    ((step sX sY)^[i] w).length ≤ w.length + 12 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le sX sY ((step sX sY)^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨[], ⟨kk, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩`: after `i` rounds the
counter is `1^i` and `i` chunks have been dropped from each coin string. -/
theorem iterate_step (u kk z rX rY : List Bool) (i : ℕ) :
    (step sX sY)^[i] (st u [] kk z rX rY) =
      st u (List.replicate i true) kk z (rX.drop (i * sX.eval u.length))
        (rY.drop (i * sY.eval u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, List.replicate_succ, List.drop_drop, Nat.succ_mul]

variable (SX SY : List Bool → List Bool) (ℓ : PolyExpr)

/-- The emission at a state word: a padded sample of `Y` from the next `sY(|u|)` coins while
the counter is below the hybrid index, the challenge `z` at the hybrid index, and a padded
sample of `X` from the next `sX(|u|)` coins afterwards. -/
def emit (w : List Bool) : List Bool :=
  if (p₂ w).length < (p₃ w).length then
    padL (ℓ.eval (p₁ w).length) (SY (pairEncode (p₁ w) ((p₆ w).take (sY.eval (p₁ w).length))))
  else if (p₂ w).length = (p₃ w).length then p₄ w
  else padL (ℓ.eval (p₁ w).length) (SX (pairEncode (p₁ w) ((p₅ w).take (sX.eval (p₁ w).length))))

/-- The emission is polynomial-time: two length tests (`StateLoop.lenLe_comp`,
`Complexity.polyTimeComputable_lenEq`), two padded sampler calls (`polyTimeComputable_padL`,
`Complexity.polyTimeComputable_pairTakePoly`) and `Complexity.polyTimeComputable_ite`. -/
theorem emit_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (emit sX sY SX SY ℓ) := by
  have hlt : PolyTimeComputable fun w => [decide ((p₂ w).length < (p₃ w).length)] := by
    exact StateLoop.lenLe_comp p₃_poly (ptc_comp (StateLoop.cons_poly true) p₂_poly)
  have heq : PolyTimeComputable fun w => [decide ((p₂ w).length = (p₃ w).length)] := by
    convert ptc_comp polyTimeComputable_lenEq (p₂_poly.pairEncode p₃_poly) using 1
    funext w
    simp
  have hY := polyTimeComputable_padL ℓ p₁_poly (ptc_comp hSY (p₁_poly.pairEncode
    (ptc_comp (polyTimeComputable_pairTakePoly sY) (p₁_poly.pairEncode p₆_poly))))
  have hX := polyTimeComputable_padL ℓ p₁_poly (ptc_comp hSX (p₁_poly.pairEncode
    (ptc_comp (polyTimeComputable_pairTakePoly sX) (p₁_poly.pairEncode p₅_poly))))
  convert polyTimeComputable_ite hlt hY (polyTimeComputable_ite heq p₄_poly hX) using 1
  funext w
  simp [emit]

/-- The emission at a genuine state word with unary parameter, counter and index. -/
theorem emit_st (n cnt k : ℕ) (z rX rY : List Bool) :
    emit sX sY SX SY ℓ
        (st (List.replicate n true) (List.replicate cnt true) (List.replicate k true) z rX rY) =
      if cnt < k then
        padL (ℓ.eval n) (SY (pairEncode (List.replicate n true) (rY.take (sY.eval n))))
      else if cnt = k then z
      else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true) (rX.take (sX.eval n)))) := by
  simp [emit]

variable (t : PolyExpr)

/-- The loop output: the `t(|x|) + 1` emissions along the orbit of `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (t.eval x.length + 1)).flatMap fun i => emit sX sY SX SY ℓ ((step sX sY)^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 12 t(|x|)`). -/
theorem loopOut_poly (hSX : PolyTimeComputable SX) (hSY : PolyTimeComputable SY) :
    PolyTimeComputable (loopOut sX sY SX SY ℓ t) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit (step_poly sX sY) (emit_poly sX sY SX SY ℓ hSX hSY) t
    (.add .var (.mul (.const 12) t)) fun x i hi => ?_
  have h := length_iterate_step_le sX sY x i
  have h' : 12 * i ≤ 12 * t.eval x.length := Nat.mul_le_mul_left 12 hi
  simp only [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- The loop output on the genuine initial state: chunk `i` is a padded sample of `Y` from
the `i`-th chunk of `rY` below the index `k`, the challenge at `k`, and a padded sample of `X`
from the `i`-th chunk of `rX` above `k`. -/
theorem loopOut_st (n k : ℕ) (z rX rY : List Bool) :
    loopOut sX sY SX SY ℓ t (st (List.replicate n true) [] (List.replicate k true) z rX rY) =
      (List.range (t.eval (st (List.replicate n true) [] (List.replicate k true) z rX rY).length
        + 1)).flatMap fun i =>
          if i < k then
            padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
              ((rY.drop (i * sY.eval n)).take (sY.eval n))))
          else if i = k then z
          else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
            ((rX.drop (i * sX.eval n)).take (sX.eval n)))) := by
  unfold loopOut
  congr 1
  funext i
  rw [iterate_step, emit_st]
  simp

end CopiesLoop

/-- The initial state of the sampler loop as a function of the raw layout
`⟨⟨⟨1^n, ⟨z, 1^k⟩⟩, α⟩, r⟩`: `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨r.take (t·sX)(n), r.drop (t·sX)(n)⟩⟩⟩⟩⟩`. -/
def copiesInit (sX t : PolyExpr) (w : List Bool) : List Bool :=
  CopiesLoop.st (NUPPT.inParam w) [] (pairSndD (NUPPT.inArg w)) (pairFstD (NUPPT.inArg w))
    ((NUPPT.inCoins w).take ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))
    ((NUPPT.inCoins w).drop ((PolyExpr.mul t sX).eval (NUPPT.inParam w).length))

/-- The initial state is polynomial-time in the raw layout. -/
theorem copiesInit_poly (sX t : PolyExpr) : PolyTimeComputable (copiesInit sX t) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  convert CopiesLoop.st_poly NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
    (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg)
    (ptc_comp (polyTimeComputable_pairTakePoly (.mul t sX)) hcut)
    (ptc_comp (polyTimeComputable_pairDropPoly (.mul t sX)) hcut) using 1
  funext w
  simp [copiesInit]

/-- The raw function of the sampler machine: the loop output on the initial state, truncated
to `t(n)·ℓ(n)` bits. -/
def copiesSampler (SX SY : List Bool → List Bool) (sX sY ℓ t : PolyExpr) (w : List Bool) :
    List Bool :=
  (CopiesLoop.loopOut sX sY SX SY ℓ t (copiesInit sX t w)).take
    ((PolyExpr.mul t ℓ).eval (NUPPT.inParam w).length)

/-- The sampler function is polynomial-time. -/
theorem copiesSampler_poly {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) :
    PolyTimeComputable (copiesSampler SX SY sX sY ℓ t) := by
  convert ptc_comp (polyTimeComputable_pairTakePoly (.mul t ℓ))
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (ptc_comp (CopiesLoop.loopOut_poly sX sY SX SY ℓ t hSX hSY) (copiesInit_poly sX t))) using 1
  funext w
  simp [copiesSampler]

/-- **The machine of the multicopy corollary** [PS10, Lemma 71.6; Gar26, Lemma 3.3]: for an
`NUPPT` `D`, polynomial-time samplers `SX`, `SY` with seed lengths `sX`, `sY`, a sample length
`ℓ`, a number of copies `t` and a hybrid index `k n ≤ t n`, there is an `NUPPT` `B` with coins
`t·sX + t·sY + D.coins` that on the challenge `z` and the coins `⟨cX, cY⟩ ++ cD` (the coins of
the samplers in blocks, then the coins of `D`) runs `D` on the tuple with the `i`-th position
holding a padded sample of `Y` from `cY i` for `i < k n`, the challenge at `i = k n`, and a
padded sample of `X` from `cX i` for `i > k n`.

**Proof sketch.** The uniform sampler machine `M₀ := ofPolyTimeUniform copiesSampler_poly`
runs the state loop `CopiesLoop` on `⟨1^n, ⟨[], ⟨1^k, ⟨z, ⟨rX, rY⟩⟩⟩⟩⟩` for `t(|x|) + 1 ≥ t(n)`
rounds and truncates to `t(n)·ℓ(n)` bits (`take_flatMap_range`); the `i`-th chunk is the
`i`-th block of the coins (`take_drop_ofFn_blocks`) and the concatenation of the blocks is the
string of `(blocks t ℓ).symm` (`ofFn_blocks_symm`). The reduction is
`NUPPT.exists_withAdvice (NUPPT.exists_seq M₀ (NUPPT.exists_comp D pairSndD id)) (1^{k n})`,
which hard-wires the hybrid index and hands the tuple to `D` with the remaining coins. -/
theorem exists_copiesRed (D : NUPPT) {SX SY : List Bool → List Bool} (hSX : PolyTimeComputable SX)
    (hSY : PolyTimeComputable SY) (sX sY ℓ t : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ t.eval n) :
    ∃ B : NUPPT, B.coins = .add (.add (.mul t sX) (.mul t sY)) D.coins ∧
      ∀ n (z : Fin (ℓ.eval n) → Bool) (cX : Fin (t.eval n) → Fin (sX.eval n) → Bool)
        (cY : Fin (t.eval n) → Fin (sY.eval n) → Bool) (cD : List Bool),
        B.runAtL n (List.ofFn z)
          (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
            List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) ++ cD) =
        D.runAtL n (List.ofFn ((blocks (t.eval n) (ℓ.eval n)).symm fun i =>
          if (i : ℕ) < k n then padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn (cY i))))
          else if (i : ℕ) = k n then z
          else padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn (cX i)))))) cD := by
  obtain ⟨D₂, hD₂c, -, -, hD₂⟩ := D.exists_comp polyTimeComputable_pairSndD polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ := NUPPT.exists_seq
    (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t) (.add (.mul t sX) (.mul t sY)))
    D₂
  obtain ⟨B, hBc, hB⟩ := C.exists_withAdvice (fun n => List.replicate (k n) true) t
    (fun n => by simpa using hk n)
  refine ⟨B, by rw [hBc, hCc, hD₂c]; rfl, fun n z cX cY cD => ?_⟩
  rw [hB, hC, hD₂]
  have hlen : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).length =
      (NUPPT.ofPolyTimeUniform (copiesSampler_poly hSX hSY sX sY ℓ t)
        (.add (.mul t sX) (.mul t sY))).coinLen n := by
    simp [NUPPT.coinLen]
  rw [List.take_left' hlen, List.drop_left' hlen, id, pairSndD_pairEncode]
  congr 1
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  -- the sampler function on the layout
  have hX' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).take
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) := by
    rw [List.take_left']
    simp
  have hY' : (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX) ++
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop
        ((PolyExpr.mul t sX).eval (List.replicate n true).length) =
      List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY) := by
    rw [List.drop_left']
    simp
  simp only [copiesSampler, copiesInit, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput,
    pairFstD_pairEncode, pairSndD_pairEncode, hX', hY']
  rw [CopiesLoop.loopOut_st]
  set F : ℕ → List Bool := fun i =>
    if i < k n then
      padL (ℓ.eval n) (SY (pairEncode (List.replicate n true)
        (((List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY)).drop (i * sY.eval n)).take
          (sY.eval n))))
    else if i = k n then List.ofFn z
    else padL (ℓ.eval n) (SX (pairEncode (List.replicate n true)
      (((List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX)).drop (i * sX.eval n)).take
        (sX.eval n)))) with hF
  have hFlen : ∀ i < t.eval n, (F i).length = ℓ.eval n := by
    intro i _
    simp only [hF]
    split_ifs <;> simp [length_padL]
  have hq : t.eval n ≤ t.eval (CopiesLoop.st (List.replicate n true) [] (List.replicate (k n) true)
      (List.ofFn z) (List.ofFn ((blocks (t.eval n) (sX.eval n)).symm cX))
      (List.ofFn ((blocks (t.eval n) (sY.eval n)).symm cY))).length + 1 := by
    refine (t.eval_mono ?_).trans (Nat.le_succ _)
    simp only [CopiesLoop.st, length_pairEncode, List.length_replicate]
    omega
  rw [PolyExpr.eval_mul, List.length_replicate, take_flatMap_range F hq hFlen]
  refine (ofFn_blocks_symm _ F fun i hi => ?_).symm
  simp only [hF]
  split_ifs with h₁ h₂
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]
  · rfl
  · simp only [padL, take_drop_ofFn_blocks _ i hi, Equiv.apply_symm_apply]

end TCSlib.Cryptography.EnsembleLemmas
