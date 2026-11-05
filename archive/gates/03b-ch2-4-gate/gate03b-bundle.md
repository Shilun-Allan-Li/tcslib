## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03b-pack.md =====

# Gate 03b ([PS10] ch. 2–4, one-wayness and collections): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/b/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the definitions of one-way functions and of
collections of one-way functions, permutations and trapdoor permutations, and the statements of
the theorems that relate them.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03b-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.2 (book pp. 26–29), the statements of §2.4 (Theorems 35.1 and 35.2,
pp. 33–35), Remark 33.2, §2.5 (pp. 41–42) and §2.10–§2.11 (pp. 55–57).

## Brief for the auditor

Pack 03a's brief applies unchanged: the trusted surface, the six things to hunt for, the
inventory check, restating every definition in your own words, and 1–3 sentences per theorem.
Attempt at least **three adversarial instantiations**, for example:
- a function family that is one-way for a degenerate reason (empty domain at some lengths,
  outputs that leak the input);
- a collection whose sampler is not efficient;
- a trapdoor that does not invert.

Check the run-3a repairs in scope (pack P3: `Collection.sample_spec`, Thm 42.2, the `1^n` form of
Def 26.1, the canonical default pair) instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{OneWay, Collections, Permutations}.lean`, `TCSlib/Cryptography/Candidates/Arithmetic.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (in the bundle for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | pack 03a's files (the machine model, `Negligible`, `Ensemble`, `StatClose`): an earlier pack of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.9 and §2.10 the frozen signatures, §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2, Rem-33.2, Def-41.1, Thm-42.2, Def-55.1, Def-56.1 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` (pack P3) |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the proofs of Thms 35.1 and 42.2 (`OneWayLemmas`, `OneWayYao`, `CollectionsLemmas`), which pack 03h audits for their statements |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/b/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 65 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 21 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 21 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 4 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these four files;
- lint;
- interface use. The declarations cited by ch. 5–8 are:
  - `FunFamily` and `FunFamily.StrongOneWay`;
  - `Collection`, `Collection.HardCore`, `PermCollection` and `TrapdoorCollection`;
  - `Candidates.ArithmeticFP`.

## Specific questions

1. **One-wayness (Defs 26.1, 27.3, 28.4).**
   - Is `FunFamily.StrongOneWay` the source's strong one-wayness: every n.u.p.p.t. inverter given
     `1^n` and `f(x)` succeeds with negligible probability?
   - Is the weak form's "noticeable failure" the source's quantifier order?
   - For worst-case one-wayness, are the `1^n` headline and the literal form `WorstCaseOneWayLit`,
     and the bridges between them, right?
   - What do length-changing functions do to these definitions?
2. **Amplification (Thms 35.1, 35.2; Claim 38.2).** Do the statements say what the source does,
   including the input length of the direct product and the parameters of Claim 38.2?
3. **Collections (Def 41.1, Thm 42.2).**
   - Are the three conditions faithful: efficient sampling of an index, efficient sampling of a
     domain point, and efficient evaluation?
   - The run-3a repair added `sample_spec`, the membership half of Def 41.1 (2). Is that right, and
     is it enough?
   - Is Thm 42.2 stated in both directions at the right strength?
4. **One-way and trapdoor permutations (Defs 55.1, 56.1).**
   - Are "permutation" and "trapdoor" captured: the inversion algorithm with the trapdoor, and
     its correctness on every sampled index?
   - Is the declared deviation "literal `Inv((i, t), y)` not adopted" (P3-5) benign?
5. **`Permutations.lean`.** The permutation sampler uses `permBits n = Nat.size n` and
   `permTrials n = 2n²` (a run-3a repair). Is its failure probability negligible as claimed, and
   are the parameters as stated?
6. **`Candidates/Arithmetic.lean`.**
   - Is the hypothesis bundle `ArithmeticFP` a reasonable stand-in for "these arithmetic operations
     are polynomial-time" (D11; Remark 33.2 on primality)?
   - Is any field stronger than the source's claim, or unsatisfiable?
   - Is any operation missing that the candidates of §2.7–§2.12 need?

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/b/replay.log =====

# closure of pack 03b's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 65 modules, extracted from g03-replay.log
TCSlib/Complexity/ClassNP/CoNP rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CounterProgPolyTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 8s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 6s errors=0 sorry=2
TCSlib/Complexity/PolyHierarchy/Padding rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 11s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 10s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 9s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PPT rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 23s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 102s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 103s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 8s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 6s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 6s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProg rc=0 12s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgRun rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 5s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 9s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 28s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 10s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UnaryTape rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 14s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 138s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Permutations rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 26s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Experiments rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 17s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/b/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03b's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.not_strongOneWay_id: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.StrongOneWay.weak: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.permFromCoins_uniform_of_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_permFromCoins_none_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.Easy.prod: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.claim_38_2: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.weak_to_strong: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.strong_prod_two: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.FunFamily.StrongOneWay.exists_collection_oneWay: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Collection.OneWay.owfFamily_strongOneWay: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_permFromCoins: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_permFromCoins_none_le_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_permFromCoins_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Collection.evalSampled: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_addStr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_subStr: propext, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/b/admissions.txt =====

# declarations with `sorry` in pack 03b's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/b/lint.log =====

# scripts/style_lint.py on pack 03b's files, at a3c5fa8b72e50939822f22364647dc844a3914a0





0 findings in 4 files

## ===== TCSlib/Cryptography/Asymptotic/OneWay.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-way functions, asymptotic layer

The one-way function definitions of [PS10, §2.2] and the hardness amplification theorems of
[PS10, §2.4], stated over the machine layer `Complexity.NUPPT` and the typed concrete
experiments of `TCSlib.Cryptography.Foundations.Experiments` (foundation decisions D2, D3,
D5 of `PassShelatChapter2-4Plan.md`).

A *function family* `FunFamily` is `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with syntactic
polynomial lengths (the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p`, parameter =
input length); `FunFamily.invProbAt 𝓕 A n` is the experiment
`Pr[x ← {0,1}^n; y ← f(x) : f(A(1^n, y)) = y]` for the machine `A`, its output decoded as an
`inLen n`-bit string. The three one-wayness notions of [PS10, Definitions 26.1, 27.3, 28.4]
follow — Definition 26.1 in its `1^n` form `FunFamily.WorstCaseOneWay` (headline) and its
literal form `FunFamily.WorstCaseOneWayLit` (`A(f(x))` only), related by
`WorstCaseOneWay.toLit` and `WorstCaseOneWayLit.toParam` (D5, run-3 audit P3-2) —
then the direct product `FunFamily.prod` with the parameters `yaoBlocks`/`yaoRounds`
(`m = 2nq(n)`, `T = 2nm(n)n^c`) of [PS10, §2.4.3], the theorems `weak_to_strong`
[PS10, Theorem 35.1], `strong_prod_two` [PS10, Theorem 35.2], `claim_38_2` (the parameter
instantiation of the concrete `OneWay.yao_amplification_exp` [Gar26, Theorem 2.1]), the sanity
results `FunFamily.StrongOneWay.weak` and `not_strongOneWay_id` (the adversary class is not
vacuous), and `PermFamily`/`OneWayPermutation` [PS10, Theorems 79.4 and 126.4]. Every
asymptotic theorem is proved by (i) instantiating the concrete reduction at every `n`,
(ii) exhibiting the reduction as a `Complexity.NUPPT` by the closure calculus of
`TCSlib/Complexity/Randomized/`, (iii) negligible-function arithmetic (`not_negligible_iff`).

**Deviation:** domains are typed at each parameter (D5): the direct product `𝓕.prod q` is the
family at parameter `n` with input length `q(n)·inLen(n)` and its adversaries receive `1^n`
where the text's adversary of `f'` receives `1^{n·m(n)}`; the two are interderivable
(`1^{n·m(n)}` is computed from `1^n` by `polyTimeComputable_unaryPoly`, and `n` is recovered
from `n·m(n)` by a polynomial search, `m` being monotone), so the classes coincide. The
deviations of `Easy`, `invProbAt` and `WeakOneWay` are recorded on the declarations.

## Main definitions

* `TCSlib.Cryptography.FunFamily` (`Easy`, `invProbAt`, `ofString`, `LengthRegular`, `blocks`,
  `prod`); `FunFamily.StrongOneWay`, `FunFamily.WeakOneWay`, `FunFamily.WorstCaseOneWay`
  (`1^n` form, headline) and `FunFamily.WorstCaseOneWayLit` (literal form)
  [PS10, Definitions 27.3, 28.4, 26.1].
* `TCSlib.Cryptography.yaoBlocks`, `yaoRounds` — `m = 2nq(n)`, `T = 2nm(n)n^c` [PS10, §2.4.3].
* `TCSlib.Cryptography.PermFamily`, `TCSlib.Cryptography.OneWayPermutation`.

## Main results

* `TCSlib.Cryptography.weak_to_strong` [PS10, Theorem 35.1], `strong_prod_two`
  [PS10, Theorem 35.2], `claim_38_2` (parameter instantiation, [PS10, §2.4.3]),
  `OneWay.invProb_prodFun_le_yaoTry` (concrete one-call planting, lemma C2 of the inventory).
* `TCSlib.Cryptography.FunFamily.StrongOneWay.weak`, `TCSlib.Cryptography.not_strongOneWay_id`
  — sanity and non-vacuity.
* `TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit`,
  `TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam` — the two forms of
  [PS10, Definition 26.1] (always / for injective `outLen`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Function families -/

/-- A family `f n : {0,1}^{inLen n} → {0,1}^{outLen n}` with explicit polynomial lengths: the
typed reading (D5) of the textbook `f : {0,1}* → {0,1}*` at security parameter `n`
[PS10, §2.2]. -/
structure FunFamily where
  /-- The input length at parameter `n`. -/
  inLen : PolyExpr
  /-- The output length at parameter `n`. -/
  outLen : PolyExpr
  /-- The function at parameter `n`. -/
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily

/-- `𝓕` is *easy to compute*: a polynomial-time string function computes `f n x` from
`⟨1^n, x⟩` [PS10, Definitions 26.1 (1) and 27.3 (1)].

**Deviation:** `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead
of a PPT computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`). -/
def Easy (𝓕 : FunFamily) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)

/-- The inversion probability of the machine `A` against `𝓕` at parameter `n`:
`Pr[x ← {0,1}^{inLen n}; y ← f(x); r : f(A(1^n, y; r)) = y]` with the output of `A` decoded as
an `inLen n`-bit string [PS10, Definitions 27.3 and 28.4, the displayed experiment].

**Deviation:** `inverter`: wrong-length output = failure (D5). -/
noncomputable def invProbAt (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : ℝ :=
  invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))

/-- `𝓕` is a *strong one-way function*: easy to compute, and every non-uniform PPT inverts it
with negligible probability [PS10, Definition 27.3]. -/
structure StrongOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n

/-- `𝓕` is a *weak one-way function*: easy to compute, and there is a polynomial `q` such
that every non-uniform PPT inverts it with probability at most `1 - 1/q(n)` for all
sufficiently large `n` [PS10, Definition 28.4].

**Deviation:** `WeakOneWay`: `0 < q n` made explicit (`1 - 1/0 = 1` would make the clause
vacuous). -/
structure WeakOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert with probability `1 - 1/q(n)`. -/
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀,
    𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)

/-- `𝓕` is a *worst-case one-way function*: easy to compute, and no non-uniform PPT inverts
it on every input with probability one [PS10, Definition 26.1], in the `1^n` form: the
adversary receives `1^n` and `f(x)` (`inverter`, D5) and must return an `inLen n`-bit
preimage. This is the headline form of the definition; the literal form (the adversary
receives `f(x)` only) is `WorstCaseOneWayLit`, and the two are related by
`WorstCaseOneWay.toLit` (always) and `WorstCaseOneWayLit.toParam` (injective `outLen`), as
`Ensemble.Indist`/`Ensemble.IndistLit` for [PS10, Definition 69.4].

Repair (run-3 audit P3-2): the frozen headline was the literal form (now `WorstCaseOneWayLit`),
which is vacuously satisfied by length-shrinking families whose output length does not
determine `n` (e.g. the constant family `x ↦ ε`, trivially invertible in the text); the `1^n`
form is now the headline, mirroring D5's treatment of Definition 69.4.

**Deviation:** the adversary receives `1^n` where the text writes `A(f(x))` (D5; the literal
reading is `WorstCaseOneWayLit`); inverses are sought in the domain at the current parameter
(`inverter`, wrong-length output = failure). -/
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(1^n, f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- `𝓕` is a *worst-case one-way function in the literal form* of [PS10, Definition 26.1]:
easy to compute, and no non-uniform PPT inverts it on every input with probability one, the
adversary receiving `f(x)` only (activation at the output length, `inverterLit`, D5) and
returning an `inLen n`-bit preimage.

Repair (run-3 audit P3-2): renamed from `WorstCaseOneWay`; the `1^n` form `WorstCaseOneWay` is
the headline, and `WorstCaseOneWay.toLit`/`WorstCaseOneWayLit.toParam` relate the two.

**Deviation:** satisfied by every length-shrinking family whose output length does not
determine `n` (e.g. the constant family `x ↦ ε` with `inLen = var`, `outLen = 0`), an artefact
of D5's typed inverse: when `|f(x)|` does not determine `n`, the literal adversary cannot know
the required output length `inLen n`. The `1^n` form is the headline; for injective `outLen`
(every family of the text) the two coincide (`toLit`, `toParam`). -/
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
  /-- Easy to compute. -/
  easy : 𝓕.Easy
  /-- Hard to invert: no `A` with `∀ x, Pr[A(f(x)) ∈ f⁻¹(f(x))] = 1`. -/
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
        𝓕.f n x' = 𝓕.f n x) = 1

/-- The output length of a string function on inputs of length `n`, read off at `0^n`. -/
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length

/-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length,
the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`). -/
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
  inLen := .var
  outLen := p
  f _ x i := (f (List.ofFn x)).getD i false

/-- `f` is *length-regular* with output length `p`: `|f x| = p(|x|)` for every `x`. -/
def LengthRegular (f : List Bool → List Bool) (p : PolyExpr) : Prop :=
  ∀ x, (f x).length = p.eval x.length

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation. -/
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The direct product `f'_n = (f_n)^{q n}` of [PS10, Theorem 35.1]:
`f'(x₁, …, x_{q(n)}) = (f(x₁), …, f(x_{q(n)}))` on blocks, encoded as concatenations;
`OneWay.prodFun` [Gar26, Theorem 2.1] blockwise. -/
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily where
  inLen := .mul q 𝓕.inLen
  outLen := .mul q 𝓕.outLen
  f n x := (blocks (q.eval n) (𝓕.outLen.eval n)).symm
    (TCSlib.Cryptography.OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))

/-! ### Unfolding lemmas -/

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 0 ≤ 𝓕.invProbAt A n :=
  invProbOpt_nonneg _ _

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) : 𝓕.invProbAt A n ≤ 1 :=
  invProbOpt_le_one _ _

/-- The inversion probability unfolded: the probability over `x` and the coins `r` that the
activation `A(1^n, f(x); r)` is the encoding of some `x'` with `f(x') = f(x)`. -/
theorem invProbAt_eq_uprob (𝓕 : FunFamily) (A : NUPPT) (n : ℕ) :
    𝓕.invProbAt A n = uprob fun z : (Fin (𝓕.inLen.eval n) → Bool) × A.Coins n =>
      ∃ x', A.runAt n (List.ofFn (𝓕.f n z.1)) z.2 = List.ofFn x' ∧ 𝓕.f n x' = 𝓕.f n z.1 := by
  unfold invProbAt invProbOpt
  congr 1
  funext z
  simp only [NUPPT.inverter_eq_some_iff]

/-! ### The two forms of Definition 26.1 -/

/-- **The `1^n` form implies the literal form** of [PS10, Definition 26.1] (repair of the
run-3 audit, P3-2; the analogue of `Ensemble.Indist.toLit`): a literal inverter `A`, activated at
the output length `|f(x)| = outLen n`, is the `1^n`-inverter `NUPPT.exists_reparam A outLen`,
so if no `1^n`-inverter succeeds on every input, no literal inverter does.

**Proof sketch.** `NUPPT.exists_reparam A 𝓕.outLen` gives `B` with
`B.runAtL n y r = A.runAtL (outLen n) y r` and `B.coins = A.coins.subst outLen`, so
`B.Coins n ≃ A.Coins (outLen n)` (`PolyExpr.eval_subst`, `finCongr`); `uprob_comp_equiv`
transports the success event, and `NUPPT.inverter`/`NUPPT.inverterLit` unfold to the same
`decodeFin` of the same activation (`List.ofFn_congr`). -/
theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit := by
  refine ⟨h.easy, ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨B, hBc, -, hB⟩ := A.exists_reparam 𝓕.outLen
  refine h.hard ⟨B, fun n x => ?_⟩
  have hlen : B.coinLen n = A.coinLen (𝓕.outLen.eval n) := by
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
  let e : A.Coins (𝓕.outLen.eval n) ≃ B.Coins n :=
    Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)
  rw [← uprob_comp_equiv e]
  refine (OneWay.uprob_congr fun r => ?_).trans (hA n x)
  have hofn : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen.symm r).symm
  simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]

/-- **The literal form implies the `1^n` form when the output length determines the
parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
and `B.advice n` at the output length and leaves its extra coins unread.

**Proof sketch.** An injective monotone `outLen.eval` (`PolyExpr.eval_mono`) is strictly
monotone (`Monotone.strictMono_of_injective`), so `n ≤ outLen n` (`StrictMono.id_le`) and
`φ m := the n with outLen n = m` (`0` if none) is majorised by `var`.
`NUPPT.exists_reparam_advice B φ var` gives `A` with
`A.runAtL m y r = B.runAtL (φ m) y (r.take (B.coinLen (φ m)))`; at `m = outLen n` we have
`φ m = n` and `A.Coins m ≃ B.Coins n × (Fin (B.coinLen m − B.coinLen n) → Bool)`
(`Fin.appendEquiv`, `finCongr`, `PolyExpr.eval_mono`); `List.ofFn_fin_append` and
`List.take_left'` identify the literal event with the `1^n` event on the first factor
(`uprob_comp_equiv`, `uprob_fst`). -/
theorem WorstCaseOneWayLit.toParam {𝓕 : FunFamily} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay := by
  classical
  refine ⟨h.easy, ?_⟩
  rintro ⟨B, hB⟩
  have hsm : StrictMono 𝓕.outLen.eval := 𝓕.outLen.eval_mono.strictMono_of_injective hinj
  have hle : ∀ n, n ≤ 𝓕.outLen.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, 𝓕.outLen.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (𝓕.outLen.eval n) = n := by
    intro n
    have hm : ∃ n', 𝓕.outLen.eval n' = 𝓕.outLen.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hinj hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := B.exists_reparam_advice φ .var hφ
  refine h.hard ⟨A, fun n x => ?_⟩
  have hAlen : A.coinLen (𝓕.outLen.eval n) =
      B.coinLen n + (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) := by
    have h1 : A.coinLen (𝓕.outLen.eval n) = B.coinLen (𝓕.outLen.eval n) := by
      simp only [NUPPT.coinLen, hAc, PolyExpr.eval_subst, PolyExpr.eval_var]
    have h2 : B.coinLen n ≤ B.coinLen (𝓕.outLen.eval n) := B.coins.eval_mono (hle n)
    omega
  let e : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool) ≃
      A.Coins (𝓕.outLen.eval n) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hAlen.symm) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have key : ∀ z : B.Coins n × (Fin (B.coinLen (𝓕.outLen.eval n) - B.coinLen n) → Bool),
      (∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) (e z) = some x' ∧
        𝓕.f n x' = 𝓕.f n x) ↔
      ∃ x', B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) z.1 = some x' ∧
        𝓕.f n x' = 𝓕.f n x := by
    intro z
    have hofn : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hAlen.symm (Fin.append z.1 z.2)).symm
    simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hA, hφn, hofn,
      List.take_left', List.length_ofFn]
  rw [OneWay.uprob_congr key]
  exact (uprob_fst fun r : B.Coins n => ∃ x',
    B.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧
      𝓕.f n x' = 𝓕.f n x).trans (hB n x)

/-- On a length-regular `f`, the family `ofString f p` is exactly `f` on encoded strings. -/
theorem ofFn_ofString_f {f : List Bool → List Bool} {p : PolyExpr} (hf : LengthRegular f p)
    (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x) := by
  have hlen : (f (List.ofFn x)).length = p.eval n := by rw [hf, List.length_ofFn]
  refine List.ext_get (by simp [ofString, hlen]) fun i h₁ h₂ => ?_
  simp [ofString, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

/-- The identity family is the identity at every parameter. -/
theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n x = x := by
  have h := ofFn_ofString_f (f := id) (p := .var) (fun x => by simp) n x
  exact List.ofFn_injective (by simpa using h)

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocks q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocks_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocks q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocks_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- The input length of the direct product is `q · inLen`. -/
@[simp] theorem prod_inLen (𝓕 : FunFamily) (q : PolyExpr) : (𝓕.prod q).inLen = .mul q 𝓕.inLen :=
  rfl

/-- The output length of the direct product is `q · outLen`. -/
@[simp] theorem prod_outLen (𝓕 : FunFamily) (q : PolyExpr) :
    (𝓕.prod q).outLen = .mul q 𝓕.outLen := rfl

/-- The direct product unfolded: `prodFun` between the block bijections. -/
theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin (q.eval n * 𝓕.inLen.eval n) → Bool) :
    (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm
      (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x)) := rfl

/-- The inversion probability of the direct product is the concrete `invProbOpt` of
`OneWay.prodFun (f n) (q n)` against the inverter that encodes its challenge tuple by
`blocks` and decodes its answer: the bridge from `𝓕.prod q` to [Gar26, Theorem 2.1].

**Proof sketch.** Reindex the uniform input `x : {0,1}^{q·ℓ}` by the bijection `blocks`
(`uprob_comp_equiv` on the first coordinate); `f'` is `blocks⁻¹ ∘ prodFun ∘ blocks` by
`prod_f`, and `blocks⁻¹` is injective, so the success events coincide pointwise. -/
theorem invProbAt_prod_eq (𝓕 : FunFamily) (q : PolyExpr) (A : NUPPT) (n : ℕ) :
    (𝓕.prod q).invProbAt A n =
      invProbOpt (OneWay.prodFun (𝓕.f n) (q.eval n)) fun ys r =>
        (A.inverter n (q.eval n * 𝓕.inLen.eval n) (q.eval n * 𝓕.outLen.eval n)
          ((blocks (q.eval n) (𝓕.outLen.eval n)).symm ys) r).map (blocks (q.eval n) (𝓕.inLen.eval n)) := by
  unfold invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (blocks (q.eval n) (𝓕.inLen.eval n)) (Equiv.refl _))]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq, prod_f,
    Option.map_eq_some_iff]
  apply propext
  constructor
  · rintro ⟨x', hx', hf⟩
    refine ⟨blocks _ _ x', ⟨x', hx', rfl⟩, ?_⟩
    have := congrArg (blocks (q.eval n) (𝓕.outLen.eval n)) hf
    simpa using this
  · rintro ⟨t, ⟨x', hx', rfl⟩, hf⟩
    exact ⟨x', hx', by simp [hf]⟩

/-- **The direct product is easy to compute.** If `𝓕` is easy then so is `𝓕.prod q`
[PS10, Theorem 35.1, "`f'` is easy to compute"].

**Proof sketch.** Let `F` be the evaluator of `𝓕`. The evaluator of `𝓕.prod q` is the
blockwise evaluator `OneWay.exists_prodEval F inLen q` (an instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word `⟨⟨1^n, cnt⟩, rest⟩`:
while the unary counter `cnt` is shorter than `1^{q(n)}` a round emits `F ⟨1^n, rest.take (inLen n)⟩`
and drops `inLen n` bits, afterwards it emits `[]`; `q` is evaluated at the state-word length
`≥ n`, so exactly `q(n)` rounds emit). Its specification gives the concatenation over `i < q(n)`
of `F ⟨1^n, block i⟩`, which is the concatenation of `List.ofFn (f n (blocks x i))`
(`ofFn_blocks_symm`, the hypothesis on `F`). -/
theorem Easy.prod {𝓕 : FunFamily} (h : 𝓕.Easy) (q : PolyExpr) : (𝓕.prod q).Easy := by
  obtain ⟨F, hF, hFx⟩ := h
  obtain ⟨F', hF', hspec⟩ := OneWay.exists_prodEval hF 𝓕.inLen q
  refine ⟨F', hF', fun n x => ?_⟩
  rw [NUPPT.advInput, hspec, prod_f, ofFn_blocks_symm]
  congr 2
  funext i
  exact hFx n (blocks (q.eval n) (𝓕.inLen.eval n) x i)

end FunFamily

/-! ## Yao's parameters and the concrete one-call reduction -/

/-- The number of blocks `m = 2 n q(n)` of [PS10, §2.4.3] ("we pick `m = 2nq(n)`"), as a
syntactic polynomial. -/
def yaoBlocks (q : PolyExpr) : PolyExpr := .mul (.const 2) (.mul .var q)

/-- The number of repetitions `T = 2 n m(n) n^c` of the one-call inverter [PS10, §2.4.3, the
definition of `A`]: the text's `2nm²p(n)` with `p(n) = n^c` and one factor `m` saved by the
threshold `θ = μ₀/(2m)` of `OneWay.yao_amplification_exp`. -/
def yaoRounds (q : PolyExpr) (c : ℕ) : PolyExpr :=
  .mul (.const 2) (.mul .var (.mul (yaoBlocks q) (.pow .var c)))

/-- `m(n) = 2 n q(n)`. -/
@[simp] theorem eval_yaoBlocks (q : PolyExpr) (n : ℕ) : (yaoBlocks q).eval n = 2 * (n * q.eval n) :=
  rfl

/-- `T(n) = 2 n m(n) n^c`. -/
@[simp] theorem eval_yaoRounds (q : PolyExpr) (c : ℕ) (n : ℕ) :
    (yaoRounds q c).eval n = 2 * (n * ((yaoBlocks q).eval n * n ^ c)) := rfl

/-- `m(n)` is positive for `n ≥ 1` and positive `q`. -/
theorem yaoBlocks_pos (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) {n : ℕ} (hn : 0 < n) :
    0 < (yaoBlocks q).eval n := by
  simp only [eval_yaoBlocks]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos hn (hq n))

namespace OneWay

/-- **One-call planting reduction** (lemma C2 of the Chapter 2 inventory, the concrete
content of [PS10, Theorem 35.2]): for every fixed position `i`, the inverter that samples
fresh inputs `xs`, plants the challenge `y` at position `i` of `(f(x₁), …, f(x_q))`, calls `B`
and returns the `i`-th component of the answer (`yaoTry` at the fixed position `i`) inverts
`f` with at least the probability with which `B` inverts `prodFun f q`. [PS10, Theorem 35.2,
proof]; the text's test "`f(a) = u`" is unnecessary for the inequality.

**Proof sketch.** In the planted experiment `(x, xs, r)` the tuple `update xs i x` is uniform
(`OneWay.uprob_update`), so the planted experiment is the direct-product experiment with the
answer projected to position `i`; an inverse of the whole tuple inverts every coordinate
(`uprob_mono`). -/
theorem invProb_prodFun_le_yaoTry {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (i : Fin q) :
    invProb (prodFun f q) B ≤ invProb f fun y c => yaoTry f B y (i, c) := by
  unfold invProb
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r => f (B (prodFun f q xs) r i) = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  simp only [yaoTry]
  rw [h]
  apply uprob_mono
  rintro ⟨xs, r⟩ hxs
  exact congrFun hxs i

end OneWay

/-- Polynomial times `2^{-n}` is eventually below one. -/
private theorem eventually_poly_mul_two_pow_lt_one (p : PolyExpr) :
    ∃ n₀, ∀ n ≥ n₀, (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n < 1 := by
  obtain ⟨C, e, hCe⟩ := p.eval_le
  have hneg : Negligible fun n => ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow e).const_mul _
  have hμ : Negligible fun n => (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n := by
    refine hneg.mono ⟨1, fun n hn => ?_⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have h1 : (p.eval n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) ^ e := by exact_mod_cast hCe n
    have h2 : ((n : ℝ) + 1) ^ e ≤ (2 * (n : ℝ)) ^ e := by
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (p.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n ≤ (C : ℝ) * (2 * (n : ℝ)) ^ e * (2 : ℝ)⁻¹ ^ n :=
          mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
            (by positivity)
      _ = ((C * 2 ^ e : ℕ) : ℝ) * ((n : ℝ) ^ e * (2 : ℝ)⁻¹ ^ n) := by push_cast; ring
  obtain ⟨n₀, h⟩ := hμ 0
  refine ⟨n₀, fun n hn => lt_of_le_of_lt (le_abs_self _) ?_⟩
  simpa using h n hn

/-- `e^{-n} ≤ 2^{-n}`. -/
private theorem exp_neg_le_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  exact inv_anti₀ (by norm_num) (by linarith)

/-- **Parameter instantiation** [PS10, §2.4.3, Claim 38.2 of the inventory]: with
`m(n) = 2nq(n)` blocks (`yaoBlocks q`) and `T(n) + 1 = 2nm(n)n^c + 1` repetitions
(`yaoRounds q c`), for all large `n` and every `f`, `B` such that `B` inverts `prodFun f (m n)`
with probability at least `1/n^c`, `yaoInverter f B (T n + 1)` inverts `f` with probability
exceeding `1 - 1/q(n) + (T(n) + 1)·2^{-n}` (the margin is the statistical term of the
rejection-sampled positions that `weak_to_strong` subtracts). The concrete inequality is
`OneWay.yao_amplification_exp` [Gar26, Theorem 2.1].

**Deviation:** the text takes `T = 2nm²p(n)` and the threshold `1/(2m²p(n))`; with the
threshold `μ₀/(2m)` of `yao_amplification_exp` one factor `m` is saved. The statistical margin
is absent from the text (exact sampling of `i ← [m]`).

**Proof sketch.** Apply `OneWay.yao_amplification_exp` with `α' := 1/q(n) ≤ 1`, `q := m(n)`
(so `α' m(n) = 2n`), `μ₀ := 1/n^c`, `T' := T(n) + 1` (so `μ₀ T' ≥ 2n m(n)`); it needs
`2e^{-n} < 1/n^c` and yields `invProb f (yaoInverter …) ≥ 1 - 1/(2q(n)) - e^{-n}`. Both this
and the tail bound `e^{-n} + (T(n) + 1) 2^{-n} < 1/(2q(n))` follow from `e^{-n} ≤ 2^{-n}` and
`eventually_poly_mul_two_pow_lt_one` (polynomial times `2^{-n}` is negligible,
`negligible_two_pow_neg`, `Negligible.mul_pow`). `NeZero (m n)` is `yaoBlocks_pos`. -/
theorem claim_38_2 (q : PolyExpr) (hq : ∀ n, 0 < q.eval n) (c : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, ∀ {α β ρ : Type} [Fintype α] [Inhabited α] [DecidableEq β] [Fintype ρ]
      [Nonempty ρ] (f : α → β) (B : (Fin ((yaoBlocks q).eval n) → β) → ρ → (Fin ((yaoBlocks q).eval n) → α)),
      1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun f ((yaoBlocks q).eval n)) B →
      1 - 1 / (q.eval n : ℝ) + ((yaoRounds q c).eval n + 1) * (2 : ℝ)⁻¹ ^ n <
        invProb f (OneWay.yaoInverter f B ((yaoRounds q c).eval n + 1)) := by
  obtain ⟨n₁, h₁⟩ := eventually_poly_mul_two_pow_lt_one (.mul (.const 2) (.pow .var c))
  obtain ⟨n₂, h₂⟩ := eventually_poly_mul_two_pow_lt_one
    (.mul (.add (yaoRounds q c) (.const 2)) (.mul (.const 2) q))
  refine ⟨max 1 (max n₁ n₂), fun n hn => ?_⟩
  set m : ℕ := (yaoBlocks q).eval n with hm
  set T : ℕ := (yaoRounds q c).eval n with hT
  intro α β ρ _ _ _ _ _ f B hμ
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q.eval n := by exact_mod_cast hq n
  have hexp := exp_neg_le_two_pow n
  have hb := h₁ n (le_of_max_le_left (le_of_max_le_right hn))
  have hc := h₂ n (le_of_max_le_right (le_of_max_le_right hn))
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_var,
    PolyExpr.eval_add] at hb hc
  push_cast at hb hc
  have hμ₀ : 2 * Real.exp (-(n : ℝ)) < 1 / (n : ℝ) ^ c := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0 : ℝ) < 2⁻¹ by norm_num) n, pow_pos (show (0:ℝ) < n by linarith) c]
  haveI : NeZero m := ⟨(yaoBlocks_pos q hq hn1).ne'⟩
  have hmR : (m : ℝ) = 2 * (n * q.eval n) := by rw [hm, eval_yaoBlocks]; push_cast; ring
  have hTR : (T : ℝ) = 2 * (n * (m * (n : ℝ) ^ c)) := by rw [hT, eval_yaoRounds]; push_cast; ring
  have hα₁ : 1 / (q.eval n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hqR
  have hq' : 2 * (n : ℝ) ≤ 1 / (q.eval n : ℝ) * (m : ℝ) := by
    have : 1 / (q.eval n : ℝ) * (2 * (n * q.eval n)) = 2 * n := by field_simp
    rw [hmR, this]
  have hT' : 2 * (n : ℝ) * (m : ℝ) ≤ 1 / (n : ℝ) ^ c * ((T + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hTR]
    have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    have : 1 / (n : ℝ) ^ c * (2 * (n * (m * (n : ℝ) ^ c)) + 1) = 2 * n * m + 1 / (n : ℝ) ^ c := by
      field_simp
    rw [this]
    linarith [show 0 < 1 / (n : ℝ) ^ c by positivity]
  have hmain := OneWay.yao_amplification_exp f B (n := n) (α' := 1 / (q.eval n : ℝ))
    (μ₀ := 1 / (n : ℝ) ^ c) (T + 1) hα₁ hq' hT' hμ₀ hμ
  have htail : Real.exp (-(n : ℝ)) + ((T : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n < 1 / (q.eval n : ℝ) / 2 := by
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    rw [lt_div_iff₀ (by norm_num), lt_div_iff₀ (by linarith)]
    nlinarith
  linarith

/-! ## Hardness amplification -/

/-- The block bijection of this file is the one of `OneWayLemmas`/`OneWayYao`. -/
private theorem blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = OneWay.blocksE q ℓ := rfl

/-- **Yao's hardness amplification** [PS10, Theorem 35.1]: for every weak one-way function
`𝓕` there is a polynomial `m` (the proof takes `m(n) = 2nq(n)`, `q` the polynomial of weak
one-wayness) such that the direct product `𝓕.prod m`, `f'(x₁, …, x_{m(n)}) = (f(x₁), …,
f(x_{m(n)}))`, is strongly one-way.

**Deviation:** `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's
`m = 2nq(n)` and a rejection-sampled position (statistical term absorbed). The direct product
is a family at parameter `n` whose adversaries receive `1^n` (module docstring); the text's
`T = 2nm²p(n)` repetitions become `T(n) + 1`, `T(n) = 2nm(n)n^c` (`yaoRounds`).

**Proof sketch.** Let `q_w` be the polynomial of `h.hard` and `m := yaoBlocks q_w`
(`m(n) = 2nq_w(n)`). *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT` and suppose
`fun n => (𝓕.prod m).invProbAt A' n` is not negligible; `not_negligible_iff` gives `c` with
`1/n^c ≤ (𝓕.prod m).invProbAt A' n` for infinitely many `n` (the function is nonnegative,
`invProbAt_nonneg`). Put `T := yaoRounds q_w c`, `k(n) := Nat.size (m(n))` (so
`m(n) ≤ 2^{k(n)} ≤ 2m(n)`, `k(n) ≤ m(n)`) and `ρ := add (mul var m) (add (mul m inLen) A'.coins)`,
the coins of one round: `n` rejection trials of `m(n)` bits (`k(n)` of them read) for the
position, `m(n)` fresh inputs of `inLen(n)` bits, and the coins of `A'`.

*The reduction `A`* (Algorithm 38.5 repeated) is `NUPPT.ofPolyTime` of an FP function of
the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with coins `mul (add T (const 1)) ρ` and advice
`advice n := ⟨A'.advice n, ⟨1^{m n}, ⟨1^{T n}, ⟨1^{k n}, ⟨1^{inLen n}, 1^{A'.coinLen n}⟩⟩⟩⟩⟩`
(length bounded by the `PolyExpr` `2·A'.adv + 2·m + 2·T + 2·m + 2·inLen + 2·A'.coins + 12`,
`eval_mono`; every component but `A'.advice n` is computable from `1^n`, by
`polyTimeComputable_unaryPoly` and `computesFunInTime_lengthBits` for `1^{k n}`, so uniformity
is preserved). It is an instance of `Complexity.polyTimeComputable_iterateFind` with
`R := T`, `P := var` on the state word `w = ⟨⟨⟨1^n, y⟩, advice n⟩, rest⟩`: the step `g` drops
one round of coins (`polyTimeComputable_pairDropPoly ρ` on `⟨1^n, rest⟩`, re-paired by
`polyTimeComputable_layout`; the orbit never grows, so `horbit` holds); the test `acc w` first
checks that `ρ(n)` coins remain (`polyTimeComputable_lenLe` on `⟨1^{ρ n}, rest⟩`,
`polyTimeComputable_unaryPoly ρ`: `R := T` is evaluated at the raw input length `≥ n`, so at
least `T(n) + 1` rounds are run and the rounds without coins fail), cuts the round's coins
(`polyTimeComputable_pairTakePoly ρ`), reads the position
`i := (rejectionSample (m n) (k n) n (first n·m(n) bits, grouped by `blockMap`)).getD 0`
(each `k(n)`-bit trial compared with `1^{m n}` by `polyTimeComputable_lenLe` after unary
conversion, `polyTimeComputable_ite`), evaluates `ỹ_j := F ⟨1^n, x_j⟩` on the `m(n)` fresh
blocks (iteration as in `Easy.prod`), plants `y` at block `i` (`take`/`drop` at the unary
offset `1^{i·outLen n}`, `Turing.FinTM.computesFunInTime_unaryMul`), calls `A'.output` on the
layout `⟨⟨⟨1^n, ỹ⟩, A'.advice n⟩, r'⟩` (`A'.polyTimeComputable_output`,
`polyTimeComputable_layout`), takes block `i` of the answer when its length is `m(n)·inLen(n)`
and `1^{inLen n}` otherwise (`polyTimeComputable_lenEq`, `polyTimeComputable_ite`), and tests
`F ⟨1^n, z_i⟩ = y` (`Complexity.polyTimeComputable_pairEq`); `out w := z_i`; on exhaustion the
`[]` of `iterateFind` is replaced by `1^{inLen n}` (`polyTimeComputable_lenEq`, `_ite`).

*Functional identity.* With the `Inhabited` instance `default := fun _ => true` on
`Fin (inLen n) → Bool`, `B n ỹ r' := blocks ((A'.inverter n _ _ (blocks⁻¹ ỹ) r').getD default)`
and the typed coin sampler `S n : A.Coins n → (Fin (T n + 1) → Fin (m n) × (Fin (m n) → _) × A'.Coins n)`
(per round: position by `(rejectionSample …).getD 0`, inputs by `blocks`, coins verbatim), for
every `y`, `r`: `A.inverter n _ _ y r = some (OneWay.yaoInverter (𝓕.f n) (B n) (T n + 1) y (S n r))`
(`NUPPT.inverter_eq_some_iff`, `runAtL_ofPolyTime`, the `find?` of `iterateFind` against the
`foldr` of `yaoInverter` by induction on the round list, `decodeFin_ofFn`).

*Probability.* `statClose_rejectionSample (m n) (k n) n 0` puts each round's position within
`(1 - m/2^k)^n ≤ (1/2)^n` of uniform (`uprob_rejectionSample_none_le_half_pow`), the other
components are `StatClose.refl`; `StatClose.prod` over the components and the `T n + 1` rounds
(`StatClose.comp_equiv_left` for the coin-string bijection) gives
`StatClose (S n) id ((T n + 1)·(1/2)^n)`, and `StatClose.abs_uprob_sub_le_prod` with the
auxiliary coins `x` yields `𝓕.invProbAt A n ≥ invProb (𝓕.f n) (yaoInverter (𝓕.f n) (B n)
(T n + 1)) - (T n + 1)(1/2)^n` (`invProbAt_eq_uprob`, `invProbOpt_some`).

*Conclusion.* At the infinitely many `n` with `1/n^c ≤ (𝓕.prod m).invProbAt A' n`:
`invProbAt_prod_eq` and `invProbOpt_le_invProb` give `1/n^c ≤ invProb (prodFun (𝓕.f n) (m n)) (B n)`,
so `claim_38_2` (which packages `OneWay.yao_amplification_exp` with `α' = 1/q_w(n)`,
`μ₀ = 1/n^c`, `T' = T n + 1`) gives `𝓕.invProbAt A n > 1 - 1/q_w(n)` for infinitely many
`n`, contradicting `h.hard` for `A` (`∃ n₀, ∀ n ≥ n₀, … ≤ 1 - 1/q_w(n)`).

*Implementation.* The machine, its functional identity and the statistical step are the theorem
`OneWay.exists_yaoReduction` of `TCSlib.Cryptography.Asymptotic.OneWayYao` (sub-machines in
`OneWayLemmas`): the trial length is `kkOf (m n) = ⌊log₂ m(n)⌋ + 1` (carried as `1^{kk}` in the
advice `⟨A'.advice n, 1^{kk}⟩`), each round reads `n·kk` of its `n·m(n)` position bits, and `B n`
is the total inverter `OneWay.yaoB` (block `i` of `A'`'s answer, padded with `true`), which inverts
the direct product at least as often as `A'`. -/
theorem weak_to_strong {𝓕 : FunFamily} (h : FunFamily.WeakOneWay 𝓕) :
    ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q) := by
  obtain ⟨qw, hqw, hhard⟩ := h.hard
  refine ⟨yaoBlocks qw, h.easy.prod _, fun A' => ?_⟩
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  obtain ⟨F, hF, hFx⟩ := h.easy
  have hFe_spec : ∀ n (a : Fin (𝓕.inLen.eval n) → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (𝓕.f n a) :=
    fun n a => hFx n a
  have hm : ∀ n, 1 ≤ n → 0 < (yaoBlocks qw).eval n := fun n hn => yaoBlocks_pos qw hqw hn
  -- the reduction machine of Algorithm 38.5
  obtain ⟨A, hA⟩ := OneWay.exists_yaoReduction 𝓕.inLen 𝓕.outLen (yaoBlocks qw) (yaoRounds qw c)
    𝓕.f hF hFe_spec A' hm
  obtain ⟨n₀, hn₀⟩ := hhard A
  obtain ⟨n₁, hn₁⟩ := claim_38_2 qw hqw c
  obtain ⟨n, hn, hlow⟩ := hc (max 1 (max n₀ n₁))
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnn₀ : n₀ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hnn₁ : n₁ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hlow
  -- the total inverter `yaoB` inverts the direct product at least as often as `A'`
  have hB : 1 / (n : ℝ) ^ c ≤ invProb (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n))
      (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) := by
    refine hlow.trans ?_
    rw [FunFamily.invProbAt_prod_eq]
    unfold invProbOpt invProb
    apply uprob_mono
    rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
    rw [Option.map_eq_some_iff] at hxs'
    obtain ⟨x'', hx'', rfl⟩ := hxs'
    rw [NUPPT.inverter_eq_some_iff, blocks_eq_blocksE] at hx''
    have hyB : OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n
        (OneWay.prodFun (𝓕.f n) ((yaoBlocks qw).eval n) xs) r =
        FunFamily.blocks ((yaoBlocks qw).eval n) (𝓕.inLen.eval n) x'' := by
      funext j
      simp only [OneWay.yaoB]
      rw [hx'', OneWay.padTrue_drop_ofFn]
      rfl
    rw [hyB]
    exact hf
  -- the parameter instantiation and the reduction's bound
  have hclaim := @hn₁ n hnn₁ (Fin (𝓕.inLen.eval n) → Bool) (Fin (𝓕.outLen.eval n) → Bool)
    (A'.Coins n) _ ⟨fun _ => true⟩ _ _ _ (𝓕.f n)
    (OneWay.yaoB 𝓕.inLen 𝓕.outLen (yaoBlocks qw) A' n) hB
  have hred := hA n hn1
  have hup := hn₀ n hnn₀
  unfold FunFamily.invProbAt at hup
  rw [one_div] at hred
  linarith

/-- `blocks q ℓ x i j` reads position `ℓ·i + j` of `x`. -/
private theorem blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- Two blocks: the encoding of `blocks⁻¹ t` is `ofFn (t 0) ++ ofFn (t 1)`. -/
private theorem ofFn_blocks_two_symm (ℓ : ℕ) (t : Fin 2 → Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks 2 ℓ).symm t) = List.ofFn (t 0) ++ List.ofFn (t 1) := by
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]

/-- **The simple security reduction** [PS10, Theorem 35.2]: if `𝓕` is a strong one-way
function then `g(x, y) = (f(x), f(y))`, the direct product with two blocks (input length
`2·inLen(n)`), is a strong one-way function.

**Deviation:** `g` is `𝓕.prod (const 2)` (two blocks of the typed domain), a family at
parameter `n` whose adversaries receive `1^n` rather than `1^{2n}` (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod`. *Hard:* fix `A' : NUPPT`. The reduction `A`
of the text ("choose a random `y`, compute `v ← f(y)`, submit `(u, v)` to `A'`, output `a`")
is `NUPPT.ofPolyTime` of an FP function of the raw input `⟨⟨⟨1^n, u⟩, A'.advice n⟩, r⟩` with
coins `add (mul (const 2) inLen) A'.coins` and advice `A'.advice`: cut the first `2·inLen n`
coins as a fresh pair of blocks whose second block is `y` (`polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly` on `⟨1^n, r⟩`; the first block is the overwritten coordinate of
the planting lemma), evaluate `v := F ⟨1^n, y⟩` with the evaluator of `h.easy`, call `A'.output`
on the layout `⟨⟨⟨1^n, u ++ v⟩, A'.advice n⟩, r'⟩` (`PolyTimeComputable.append`,
`polyTimeComputable_layout`, `A'.polyTimeComputable_output`) and return the first `inLen n`
bits of the answer (`polyTimeComputable_pairTakePoly inLen`; no length test is needed for an
upper bound). Functional identity: `A.runAt n u (xs, r') = (A'.runAt n (u ++ f (xs 1)) r').take (inLen n)`
after reindexing `A.Coins n ≃ (Fin 2 → Fin (inLen n) → Bool) × A'.Coins n` (`blocks`,
`Fin.appendEquiv`, `uprob_comp_equiv`, `ofFn_blocks_symm`). Probability: `invProbAt_prod_eq`
writes `(𝓕.prod 2).invProbAt A' n` as `invProbOpt (prodFun (f n) 2) B'`, the planting lemma
`OneWay.invProbOpt_prodFun_le_yaoTryOpt` at position `0` bounds it by the planted experiment, and
`uprob_mono` (a `2·inLen n`-bit answer of `A'` decodes to the first block of `A`'s answer,
`ofFn_block_eq_take_drop`) gives `(𝓕.prod 2).invProbAt A' n ≤ 𝓕.invProbAt A n`; conclude by
`h.hard A` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem strong_prod_two {𝓕 : FunFamily} (h : FunFamily.StrongOneWay 𝓕) :
    FunFamily.StrongOneWay (𝓕.prod (.const 2)) := by
  classical
  obtain ⟨F, hF, hFx⟩ := h.easy
  refine ⟨h.easy.prod _, fun A' => ?_⟩
  -- the reduction: cut two fresh blocks, evaluate `f` on the second, plant, call `A'`, return
  -- the first block of the answer
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hxs := (polyTimeComputable_pairTakePoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hr' := (polyTimeComputable_pairDropPoly (.mul (.const 2) 𝓕.inLen)).comp hcut
  have hy2 := (polyTimeComputable_pairDropPoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hxs)
  have hv := hF.comp (NUPPT.polyTimeComputable_inParam.pairEncode hy2)
  have hout := A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inArg.append hv) NUPPT.polyTimeComputable_inAdvice hr')
  have hG := (polyTimeComputable_pairTakePoly 𝓕.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode hout)
  let A : NUPPT := NUPPT.ofPolyTime hG (.add (.mul (.const 2) 𝓕.inLen) A'.coins) A'.adv A'.advice
    A'.advice_length
  refine (h.hard A).mono ⟨0, fun n _ => ?_⟩
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  set ℓ := 𝓕.inLen.eval n with hℓ
  set f := 𝓕.f n with hf
  -- the coin bijection `(xs, r') ↦ ⟨xs⟩ ++ r'`
  have hlen : 2 * ℓ + A'.coinLen n = A.coinLen n := rfl
  let e : (Fin 2 → Fin ℓ → Bool) × A'.Coins n ≃ A.Coins n :=
    (Equiv.prodCongr (FunFamily.blocks 2 ℓ).symm (Equiv.refl _)).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)))
  have hofn : ∀ (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      List.ofFn (e (xs, r')) = (List.ofFn (xs 0) ++ List.ofFn (xs 1)) ++ List.ofFn r' := by
    intro xs r'
    rw [← ofFn_blocks_two_symm, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen (Fin.append ((FunFamily.blocks 2 ℓ).symm xs) r')).symm
  -- the functional identity of the reduction
  have hrun : ∀ (y : Fin (𝓕.outLen.eval n) → Bool) (xs : Fin 2 → Fin ℓ → Bool) (r' : A'.Coins n),
      A.runAt n (List.ofFn y) (e (xs, r')) =
        (A'.runAt n (List.ofFn y ++ List.ofFn (f (xs 1))) r').take ℓ := by
    intro y xs r'
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime hG _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    simp only [Function.comp, NUPPT.advInput, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
      NUPPT.inCoins, NUPPT.layout, pairFstD_pairEncode, pairSndD_pairEncode, hofn,
      PolyExpr.eval_mul, PolyExpr.eval_const, List.length_replicate]
    have h2 : (List.ofFn (xs 0) ++ List.ofFn (xs 1)).length = 2 * ℓ := by simp; ring
    rw [List.take_left' h2, List.drop_left' h2,
      List.drop_left' (by simp only [List.length_ofFn]; try exact hℓ)]
    have := hFx n (xs 1)
    simp only [NUPPT.advInput] at this
    rw [this]
    rfl
  -- the planting bound
  let B' : (Fin 2 → Fin (𝓕.outLen.eval n) → Bool) → A'.Coins n → Option (Fin 2 → Fin ℓ → Bool) :=
    fun ys r => (A'.inverter n (2 * ℓ) (2 * 𝓕.outLen.eval n)
      ((FunFamily.blocks 2 (𝓕.outLen.eval n)).symm ys) r).map (FunFamily.blocks 2 ℓ)
  have h1 : (𝓕.prod (.const 2)).invProbAt A' n = invProbOpt (OneWay.prodFun f 2) B' :=
    FunFamily.invProbAt_prod_eq 𝓕 (.const 2) A' n
  have h2 := OneWay.invProbOpt_prodFun_le_yaoTryOpt f B' 0
  refine h1.trans_le (h2.trans ?_)
  unfold FunFamily.invProbAt invProbOpt
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl _) e)]
  apply uprob_mono
  rintro ⟨x, xs, r'⟩ ⟨x', hx', hfx⟩
  refine ⟨x', ?_, hfx⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rw [Option.map_eq_some_iff] at hx'
  obtain ⟨xs', hxs', rfl⟩ := hx'
  simp only [B', Option.map_eq_some_iff] at hxs'
  obtain ⟨x'', hx'', rfl⟩ := hxs'
  rw [NUPPT.inverter_eq_some_iff, ofFn_blocks_two_symm, Function.update_self,
    Function.update_of_ne (by decide), OneWay.prodFun] at hx''
  rw [NUPPT.inverter_eq_some_iff, hrun, hx'']
  have hblk := OneWay.ofFn_block_eq_take_drop x'' 0
  simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero] at hblk
  rw [← hblk]
  rfl

/-- **Strong implies weak** (sanity, [PS10, §2.2, the remark after Definition 28.4]): a strong
one-way function is a weak one-way function with `q = 2`.

**Proof sketch.** Negligibility with `c = 1` gives `invProbAt A n < 1/n ≤ 1/2 = 1 - 1/2` for
all `n ≥ max n₀ 2`. -/
theorem FunFamily.StrongOneWay.weak {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay := by
  refine ⟨h.easy, .const 2, fun _ => by simp, fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.hard A 1
  refine ⟨max n₀ 2, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / (n : ℝ) ^ 1 ≤ 1 / 2 := by
    rw [pow_one]; exact one_div_le_one_div_of_le (by norm_num) hn2
  simp only [PolyExpr.eval_const, Nat.cast_ofNat]
  linarith [le_abs_self (𝓕.invProbAt A n)]

/-- **The identity is not one-way** (non-vacuity of the adversary class, [PS10, §2.2]): the
machine that returns its argument inverts `FunFamily.ofString id var` with probability one at
every parameter, and the constant `1` is not negligible.

**Proof sketch.** `A := NUPPT.ofPolyTimeUniform polyTimeComputable_inArg (const 0)` returns
`y` on `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (`runAtL_ofPolyTimeUniform`, `inArg_layout`); its inverter
decodes `List.ofFn y` to `some y` (`decodeFin_ofFn`), and `(ofString id var).f n` is the
identity (`ofString_id_f`), so `invProbAt … A n = uprob True = 1`; `Negligible (fun _ => 1)`
fails at `c = 0`. -/
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var) := by
  intro h
  let A : NUPPT := NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0)
  have hrun : ∀ n (y : List Bool) (r : A.Coins n), A.runAt n y r = y := by
    intro n y r
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inArg (.const 0)).runAtL n y _ = y
    rw [NUPPT.runAtL_ofPolyTimeUniform]; exact NUPPT.inArg_layout _ _ _ _
  have hone : ∀ n, (FunFamily.ofString id .var).invProbAt A n = 1 := by
    intro n
    rw [FunFamily.invProbAt_eq_uprob]
    have hp : (fun z : (Fin ((FunFamily.ofString id .var).inLen.eval n) → Bool) × A.Coins n =>
        ∃ x', A.runAt n (List.ofFn ((FunFamily.ofString id .var).f n z.1)) z.2 = List.ofFn x' ∧
          (FunFamily.ofString id .var).f n x' = (FunFamily.ofString id .var).f n z.1) =
        fun _ => True := by
      funext z
      refine propext ⟨fun _ => trivial, fun _ => ⟨z.1, ?_, rfl⟩⟩
      rw [hrun, FunFamily.ofString_id_f]
    rw [hp, uprob_true]
  obtain ⟨n₀, hn₀⟩ := h.hard A 0
  have := hn₀ n₀ le_rfl
  simp [hone] at this

/-! ## One-way permutations -/

/-- A family of permutations of `{0,1}^n` (the single one-way permutation of
[PS10, Theorems 79.4 and 126.4]; the *collection* of permutations of [PS10, Definition 55.1] is
`PermCollection` in `Asymptotic/Collections.lean`). -/
structure PermFamily where
  /-- The permutation at parameter `n`. -/
  f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)

/-- The function family underlying a permutation family: `inLen = outLen = var`. -/
def PermFamily.toFunFamily (P : PermFamily) : FunFamily where
  inLen := .var
  outLen := .var
  f n := P.f n

/-- `P` is a *one-way permutation* when its underlying family is strongly one-way
[PS10, §2.12 and Theorem 79.4]. -/
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay

/-- The function of a permutation family is the permutation. -/
@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin n → Bool) :
    P.toFunFamily.f n x = P.f n x := rfl

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Collections.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Complexity.PolyHierarchy.Padding
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collections of one-way functions, one-way permutations, trapdoor permutations

The *collection* notions of [PS10, §2.5, §2.10, §2.11]: a family `{f_i : D_i → R_i}_{i ∈ I}`
with a PPT index generator `Gen(1^n)`, a PPT domain sampler, a PPT evaluator and the hardness
clause `Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y] ≤ ε(n)`
[PS10, Definition 41.1]; collections of one-way permutations [PS10, Definition 55.1]; trapdoor
permutations with their inverter [PS10, Definition 56.1]; the hard-core predicate for a
collection (the unnumbered collection form of [PS10, Definition 78.3], used by Lemma 84.1,
Theorem 104.4 and Theorem 126.4); and the equivalence with single strong one-way functions
[PS10, Theorem 42.2].

A `Collection` (foundation decisions D3–D5, D10) has string indices `i : List Bool`, at each
index a finite inhabited domain `D i` with an encoding `encD i` and a total decoder `decD i`,
the string function `f i`, two uniform `NUPPT`s `gen` (`Gen(1^n) = ⟨i, t⟩`, `index`/`trap`)
and `sample`, and a polynomial-time evaluator `eval` agreeing with `f` on encoded elements.
The sampler is required to be within a negligible statistical distance of uniform on `D i`
(`SampleClose`, D10), while the hardness experiment `invProbAt` draws the *ideal* uniform
`x ← D_i`: the average over the generator's coins of the probability, over `x ← D_i` and
the adversary's coins, that the decoded answer is a preimage of `f_i(x)`.

Theorem 42.2: (⇐) a strong one-way family `𝓕` gives the collection `FunFamily.toCollection`
with `Gen(1^n) = ⟨1^n, []⟩`, `D_{1^n} = {0,1}^{inLen n}`, `f_{1^n} = f n`, which is one-way
(`FunFamily.StrongOneWay.toCollection_oneWay`, proved); (⇒, the exercise of the text) the
function `g(r₁, r₂) = ⟨i, f_i(x)⟩`, `i = Gen(1^n; r₁)`, `x = Sample(i; r₂)`, is
`Collection.owfFamily`, strongly one-way by `Collection.OneWay.owfFamily_strongOneWay`
(proved: the evaluator and the collection inverter are built in the FP calculus with the
padding evaluator `padStr` of `TCSlib.Cryptography.Asymptotic.CollectionsLemmas`), from which
the headline `Collection.OneWay.exists_strongOneWay` is proved.

**Deviation:** `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible
statistical distance of uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i`
(`uexp` over `Gen`'s coins).

**Deviation:** the adversary of [PS10, Definitions 41.1 (4), 56.1 (5)] is a non-uniform PPT
(the standing convention of [PS10, p. 26]), receives `1^n`, and its answer is decoded by
`decD i` (a non-decoding answer is a failure, D5); "`f(A(1^n, i, y)) = y`" is read as `f_i`;
the bound `e(k)` of Definition 56.1 (5) is `ε(n)`.

Repair (run-3 audit P3-1): the frozen `Collection` did not tie the evaluator to the sampler
on non-canonical strings, so [PS10, Theorem 42.2 ⇒] was unprovable; the membership half of
[PS10, Definition 41.1 (2)] ("returns an element of `D_i`") is now the field
`Collection.sample_spec`, from which `Collection.EvalSampled` (every sampled string decodes and
`eval` agrees with `f` on it) is derived (`Collection.evalSampled`).

## Main definitions

* `TCSlib.Cryptography.Collection` (`sample_spec`, `index`, `trap`, `SampleClose`,
  `invProbAt`), `TCSlib.Cryptography.Collection.OneWay` — collections of one-way functions
  [PS10, Definition 41.1]; `TCSlib.Cryptography.Collection.HardCore` — hard-core predicate
  for a collection [PS10, Definition 78.3, collection form].
* `TCSlib.Cryptography.PermCollection`, `PermCollection.OneWay` [PS10, Definition 55.1];
  `TCSlib.Cryptography.TrapdoorCollection`, `TrapdoorCollection.OneWay`
  [PS10, Definition 56.1].
* `TCSlib.Cryptography.FunFamily.toCollection`, `Complexity.NUPPT.withIndexParam`
  [PS10, Theorem 42.2 ⇐]; `TCSlib.Cryptography.Collection.owfRaw`, `Collection.owfFamily`,
  `Collection.OutLenBound`, `Collection.EvalSampled`, `TCSlib.Cryptography.splitCoins`
  [PS10, Theorem 42.2 ⇒].

## Main results

* `TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay`,
  `FunFamily.StrongOneWay.exists_collection_oneWay` — [PS10, Theorem 42.2 ⇐] (proved).
* `TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay` (proved from the explicit
  form), `Collection.OneWay.owfFamily_strongOneWay` — [PS10, Theorem 42.2 ⇒] (proved).
* `TCSlib.Cryptography.ofFn_splitCoins_fst`, `ofFn_splitCoins_snd`, `ofFn_splitCoins_symm` —
  the coin split `splitCoins` is `List.take`/`List.drop` on the encoded coin string.
* `TCSlib.Cryptography.Collection.evalSampled` — honest evaluation on sampled strings, from
  `sample_spec`.
* `TCSlib.Cryptography.Collection.exists_outLenBound`,
  `Collection.padFin_append_true_injective` — `g` has a polynomial, losslessly padded output.
* `TCSlib.Cryptography.TrapdoorCollection.inv_preimage`,
  `TCSlib.Cryptography.PermCollection.f_injective` — sanity for Definitions 55.1 and 56.1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5 Definition 41.1, Theorem 42.2; §2.10 Definition 55.1; §2.11 Definition 56.1;
  §3.3.3 Definition 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Collections -/

/-- A *collection of functions* `{f_i : D_i → R_i}_{i ∈ I}` [PS10, Definition 41.1 (1)–(3)]:
string indices, finite inhabited domains with encoding and total decoder, the string function
`f i`, a uniform `NUPPT` index generator `Gen(1^n) = ⟨i, t⟩` (`t` ignored by plain
collections), a uniform `NUPPT` domain sampler `Sample(1^n, i)` whose outputs at generated
indices are elements of `D_i` on which the evaluator computes `f_i` (`sample_spec`, the
membership half of clause (2)), and a polynomial-time evaluator `eval ⟨i, x⟩ = f i x` on
encoded elements. The uniformity and hardness clauses are the predicates `SampleClose` and
`OneWay`.

Repair (run-3 audit P3-1): the field `sample_spec` was added (see its docstring). -/
structure Collection where
  /-- The domain `D_i` at the index `i`. -/
  D : List Bool → Type
  /-- Every domain is finite ("uniformly random element of `D_i`"). -/
  [fintypeD : ∀ i, Fintype (D i)]
  /-- Every domain is inhabited (the default of a failed decoding). -/
  [inhabitedD : ∀ i, Inhabited (D i)]
  /-- The string encoding of an element of `D_i`. -/
  encD : ∀ i, D i → List Bool
  /-- The total decoder: wrong strings decode to `none`. -/
  decD : ∀ i, List Bool → Option (D i)
  /-- Decoding inverts encoding. -/
  decD_encD : ∀ i x, decD i (encD i x) = some x
  /-- The function `f_i : D_i → {0,1}*`. -/
  f : ∀ i, D i → List Bool
  /-- The index generator `Gen`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The domain sampler. -/
  sample : NUPPT
  /-- The sampler is a PPT. -/
  sample_uniform : sample.Uniform
  /-- The evaluator on encoded pairs `⟨i, x⟩`. -/
  eval : List Bool → List Bool
  /-- The evaluator is polynomial-time. -/
  eval_poly : PolyTimeComputable eval
  /-- The evaluator computes `f_i` on encoded elements. -/
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  /-- The sampler returns elements of `D_i` [PS10, Definition 41.1 (2), "returns a uniformly
  random element of `D_i`"]: every string it outputs at an index generated by `Gen(1^n)`
  decodes to some `x ∈ D_i`, and the evaluator computes `f_i(x)` on that string.

  Repair (run-3 audit P3-1): this clause was missing from the frozen structure (D10 relaxed
  the *uniformity* of the sampler to `SampleClose`, not the *membership* of its outputs), which
  made [PS10, Theorem 42.2 ⇒] (`Collection.OneWay.exists_strongOneWay`) unprovable: nothing
  tied the sampler's outputs to `D_i` or the evaluator to `f_i` off the canonical encodings. -/
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
      eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) =
        f (pairFstD (gen.runAt n [] r)) x

attribute [instance] Collection.fintypeD Collection.inhabitedD

namespace Collection

/-- The index `i` output by `Gen(1^n; r)`: the first component of `⟨i, t⟩`. -/
def index (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)

/-- The trapdoor `t` output by `Gen(1^n; r)`: the second component [PS10, Definition 56.1 (2)]. -/
def trap (F : Collection) (n : ℕ) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)

/-- The domain sampler is within `δ n` of uniform on `D_i` for every index output by
`Gen(1^n)`: the decoded output of `Sample(1^n, i; s)` on uniform coins `s` is `StatClose` to
the uniform element of `D_i` [PS10, Definition 41.1 (2)].

**Deviation:** domain samplers within negligible statistical distance of uniform (D10). -/
def SampleClose (F : Collection) (δ : ℕ → ℝ) : Prop :=
  ∀ n (r : F.gen.Coins n),
    StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s))
      (fun x : F.D (F.index n r) => some x) (δ n)

/-- The inversion experiment of [PS10, Definition 41.1 (4)]:
`Pr[i ← Gen(1^n); x ← D_i; y ← f_i(x) : f_i(A(1^n, i, y)) = y]`: the average over the
generator's coins of the probability, over the ideal uniform `x ∈ D_i` and the coins of `A`,
that `A(1^n, ⟨i, y⟩)` decodes to a preimage `x'` of `y` under `f_i`.

**Deviation:** hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins); the
answer is decoded by `decD i` (a non-decoding answer is a failure, D5). -/
noncomputable def invProbAt (F : Collection) (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : F.gen.Coins n =>
    uprob fun z : F.D (F.index n r) × A.Coins n =>
      ∃ x', F.decD (F.index n r)
          (A.runAt n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2) = some x' ∧
        F.f (F.index n r) x' = F.f (F.index n r) z.1

/-- A *collection of one-way functions* [PS10, Definition 41.1]: the sampler is negligibly
close to uniform (clause (2)) and every non-uniform PPT inverts with negligible probability
(clause (4)); clauses (1) and (3) are the data of `Collection`. -/
structure OneWay (F : Collection) : Prop where
  /-- The domain sampler is within a negligible distance of uniform. -/
  sampleClose : ∃ δ : ℕ → ℝ, Negligible δ ∧ F.SampleClose δ
  /-- Hard to invert: negligible inversion probability for every `A`. -/
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n

/-- `{h_i}` is a *hard-core predicate for the collection* `F` (the collection form of
[PS10, Definition 78.3], unnumbered, used by Lemma 84.1, Algorithm 104.3, Theorem 126.4):
`h_i(x)` is polynomial-time computable from `⟨i, x⟩`, and for every non-uniform PPT `A` there
is a negligible `ε` with `Pr[i ← Gen(1^n); x ← D_i : A(1^n, ⟨i, f_i(x)⟩) = h_i(x)] ≤ 1/2 + ε(n)`
for all `n` (average over `Gen`'s coins, ideal uniform `x`).

**Deviation:** the single-function `A(1^n, f(x))` becomes `A(1^n, ⟨i, f_i(x)⟩)` with the
index drawn by `Gen`; the verdict is the string `[true]` (D5). -/
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop :=
  (∃ H : List Bool → List Bool, PolyTimeComputable H ∧ ∀ i x, H (pairEncode i (F.encD i x)) = [h i x]) ∧
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    uexp (fun r : F.gen.Coins n =>
      uprob fun z : F.D (F.index n r) × A.Coins n =>
        A.distinguisherL n (pairEncode (F.index n r) (F.f (F.index n r) z.1)) z.2 = h (F.index n r) z.1)
      ≤ 1 / 2 + ε n

/-! ### Unfolding and sanity lemmas -/

/-- The encoding of `D_i` is injective (it has the left inverse `decD i`). -/
theorem encD_injective (F : Collection) (i : List Bool) : Function.Injective (F.encD i) :=
  fun x y h => Option.some_injective _ ((F.decD_encD i x).symm.trans (by rw [h, F.decD_encD]))

/-- The inversion probability is nonnegative. -/
theorem invProbAt_nonneg (F : Collection) (A : NUPPT) (n : ℕ) : 0 ≤ F.invProbAt A n := by
  unfold invProbAt uexp
  exact div_nonneg (Finset.sum_nonneg fun r _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The inversion probability is at most one. -/
theorem invProbAt_le_one (F : Collection) (A : NUPPT) (n : ℕ) : F.invProbAt A n ≤ 1 := by
  haveI : Nonempty (F.gen.Coins n) := ⟨fun _ => false⟩
  unfold invProbAt
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end Collection

/-! ## Permutations and trapdoor permutations -/

/-- A *collection of permutations* [PS10, Definition 55.1]: every `f_i` is a permutation of
`D_i` (`f_i = encD_i ∘ perm_i`, `perm_i : D_i ≃ D_i`, so `R_i = D_i` up to encoding);
one-wayness is `PermCollection.OneWay`. -/
structure PermCollection extends Collection where
  /-- The permutation of `D_i`. -/
  perm : ∀ i, D i ≃ D i
  /-- `f_i` is the encoded permutation. -/
  f_perm : ∀ i x, f i x = encD i (perm i x)

/-- A *collection of one-way permutations* [PS10, Definition 55.1]: the underlying collection
is one-way. -/
def PermCollection.OneWay (P : PermCollection) : Prop := P.toCollection.OneWay

/-- `f_i` is injective on `D_i`: the composite of the injective encoding and a bijection. -/
theorem PermCollection.f_injective (P : PermCollection) (i : List Bool) :
    Function.Injective (P.f i) := by
  intro x y h
  rw [P.f_perm, P.f_perm] at h
  exact (P.perm i).injective (P.encD_injective i h)

/-- A *collection of trapdoor permutations* [PS10, Definition 56.1 (1)–(4), (6)]: a collection
of permutations with a uniform `NUPPT` inverter `Inv(1^n, ⟨t, y⟩)` that, for every
`⟨i, t⟩ ← Gen(1^n)` and `y ∈ D_i`, decodes to `f_i^{-1}(y)` for every coin string; the
hardness clause (5) is `TrapdoorCollection.OneWay`.

**Deviation:** the inverter receives `1^n` and the trapdoor `t` only, where the text gives it
"`(i, t)` from `Gen`"; the index is recoverable from the trapdoor in every candidate, which
therefore packs it into `t` (RSA's `Gen` outputs `⟨⟨N, e⟩, ⟨N, d⟩⟩` for the text's
`[(N, e), d]`, Rabin's trapdoor `⟨p, q⟩` determines `N`) — run-3 audit P3-5, the literal
`Inv(1^n, ⟨⟨i, t⟩, y⟩)` form was not adopted. "`f_i^{-1}(y)`, `y ∈ R_i`" is
`(perm i).symm y`, `y ∈ D_i` (the range is `D_i` up to encoding). -/
structure TrapdoorCollection extends PermCollection where
  /-- The trapdoor inverter `Inv`. -/
  inv : NUPPT
  /-- `Inv` is a PPT. -/
  inv_uniform : inv.Uniform
  /-- `Inv(1^n, ⟨t, y⟩)` decodes to `f_i^{-1}(y)` for every coin string. -/
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)

/-- A collection of trapdoor permutations that is hard to invert without the trapdoor
[PS10, Definition 56.1 (5)]: the underlying collection is one-way. **Deviation:** the text's
bound "`≤ e(k)`" is `ε(n)` (source error). -/
def TrapdoorCollection.OneWay (T : TrapdoorCollection) : Prop := T.toCollection.OneWay

/-- **The trapdoor inverter wins the inversion game on every `y`** (sanity for
[PS10, Definition 56.1 (6)]): its decoded answer `x'` satisfies `f_i(x') = encD i y`. -/
theorem TrapdoorCollection.inv_preimage (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n)
    (y : T.D (T.index n r)) (s : T.inv.Coins n) :
    ∃ x', T.decD _ (T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s) = some x' ∧
      T.f (T.index n r) x' = T.encD (T.index n r) y :=
  ⟨(T.perm _).symm y, T.inv_spec n r y s, by rw [T.f_perm, Equiv.apply_symm_apply]⟩

/-! ## Theorem 42.2 (⇐): a strong one-way function is a collection -/

/-- The machine `B(1^n, y) = A(1^n, ⟨1^n, y⟩)`: `A` with the unary parameter prepended to its
argument as the index of `FunFamily.toCollection`; same coins, same advice. -/
noncomputable def _root_.Complexity.NUPPT.withIndexParam (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (f := fun z => A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inParam z) (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg)
      NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    A.coins A.adv A.advice A.advice_length

/-- `withIndexParam` has the coins of `A`. -/
@[simp] theorem _root_.Complexity.NUPPT.coins_withIndexParam (A : NUPPT) :
    A.withIndexParam.coins = A.coins := rfl

/-- The activation of `withIndexParam`: `B(1^n, y; r) = A(1^n, ⟨1^n, y⟩; r)`. -/
theorem _root_.Complexity.NUPPT.withIndexParam_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.withIndexParam.Coins n) :
    A.withIndexParam.runAt n y r = A.runAt n (pairEncode (List.replicate n true) y) r := by
  rw [NUPPT.runAt_eq]
  unfold NUPPT.withIndexParam
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

namespace FunFamily

variable (𝓕 : FunFamily) (F : List Bool → List Bool) (hF : PolyTimeComputable F)
  (hspec : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x))

/-- The index generator of `toCollection` on `1^n`: `⟨1^n, []⟩` (stated on the machine so that
the definition can discharge `sample_spec`). -/
private theorem toCollection_gen_runAt (n : ℕ)
    (r : (NUPPT.ofPolyTimeUniform
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)).Coins n) :
    (NUPPT.ofPolyTimeUniform
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)).runAt n [] r =
      pairEncode (List.replicate n true) [] := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The sampler of `toCollection` returns its coins (stated on the machine so that the
definition can discharge `sample_spec`). -/
private theorem toCollection_sample_runAt (n : ℕ) (i : List Bool)
    (s : (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen).Coins n) :
    (NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen).runAt n i s = List.ofFn s := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inCoins]

/-- **The collection of a single function family** [PS10, Theorem 42.2 ⇐]: indices `1^n`
(`Gen(1^n) = ⟨1^n, []⟩`, no coins), domains `D_i = {0,1}^{inLen |i|}` encoded by `List.ofFn`
and decoded by `decodeFin`, `f_i = f_{|i|}`, the sampler returning its `inLen n` coins, and
the evaluator `F` of `𝓕.Easy` on `⟨1^{|i|}, x⟩`. The sampler's output `List.ofFn s` decodes to
`s` and `F` computes `f n s` on it (`sample_spec`, by `decodeFin_ofFn` and `hspec`).

**Deviation:** the text's "`I = {0}`, `D_0 = ℕ`" becomes the unary parameter as the index
with the domain `{0,1}^{inLen n}` at `i = 1^n` (the domain must depend on `n`, D5). -/
noncomputable def toCollection : Collection where
  D i := Fin (𝓕.inLen.eval i.length) → Bool
  encD _ x := List.ofFn x
  decD i w := decodeFin (𝓕.inLen.eval i.length) w
  decD_encD _ x := decodeFin_ofFn x
  f i x := List.ofFn (𝓕.f i.length x)
  gen := NUPPT.ofPolyTimeUniform
    (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := NUPPT.ofPolyTimeUniform NUPPT.polyTimeComputable_inCoins 𝓕.inLen
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval z := F (pairEncode (List.replicate (pairFstD z).length true) (pairSndD z))
  eval_poly := hF.comp
    ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  eval_spec i x := by
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    exact hspec i.length x
  sample_spec n r s := by
    rw [toCollection_sample_runAt]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    revert s
    rw [toCollection_gen_runAt, pairFstD_pairEncode, List.length_replicate]
    intro s
    exact ⟨s, decodeFin_ofFn s, hspec n s⟩

/-- The index generated by `toCollection` is `1^n`. -/
theorem toCollection_index (n : ℕ) (r : (𝓕.toCollection F hF hspec).gen.Coins n) :
    (𝓕.toCollection F hF hspec).index n r = List.replicate n true := by
  unfold Collection.index toCollection
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The sampler of `toCollection` returns its coins. -/
theorem toCollection_sample (n : ℕ) (i : List Bool) (s : (𝓕.toCollection F hF hspec).sample.Coins n) :
    (𝓕.toCollection F hF hspec).sample.runAt n i s = List.ofFn s := by
  unfold toCollection
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inCoins]

/-- The sampler of `toCollection` is exactly uniform (`δ = 0`). -/
theorem toCollection_sampleClose : (𝓕.toCollection F hF hspec).SampleClose fun _ => 0 := by
  intro n r
  generalize hidx : (𝓕.toCollection F hF hspec).index n r = i
  have hi : i.length = n := by rw [← hidx, toCollection_index, List.length_replicate]
  subst hi
  have hX : (fun s : (𝓕.toCollection F hF hspec).sample.Coins i.length =>
      (𝓕.toCollection F hF hspec).decD i ((𝓕.toCollection F hF hspec).sample.runAt i.length i s)) =
      fun s => some s := by
    funext s
    rw [toCollection_sample]
    exact decodeFin_ofFn s
  rw [hX]
  exact StatClose.refl _

/-- A string decodes to `x'` iff it is `List.ofFn x'` (private copy, cf. `inverter_eq_some_iff`). -/
private theorem decodeFin_eq_some_iff {ℓ : ℕ} (w : List Bool) (x' : Fin ℓ → Bool) :
    decodeFin ℓ w = some x' ↔ w = List.ofFn x' := by
  constructor
  · intro h
    have hw : w.length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    rw [h, decodeFin_ofFn]

/-- **The inversion experiment of `toCollection` is that of `𝓕`** against the machine
`withIndexParam A`, which prepends the index `1^n` to its argument.

**Proof sketch.** The generator has no coins, so the average is the value at any `r`; there
the index is `1^n` (`toCollection_index`), the domain is `{0,1}^{inLen n}` and the decoder is
`decodeFin`, so the success event is that of `invProbAt_eq_uprob` for `withIndexParam A`
(`withIndexParam_runAt`, `decodeFin_eq_some_iff`, `List.ofFn_inj`). -/
theorem toCollection_invProbAt (A : NUPPT) (n : ℕ) :
    (𝓕.toCollection F hF hspec).invProbAt A n = 𝓕.invProbAt A.withIndexParam n := by
  haveI : Nonempty ((𝓕.toCollection F hF hspec).gen.Coins n) := ⟨fun _ => false⟩
  unfold Collection.invProbAt
  rw [← OneWay.uexp_const (α := (𝓕.toCollection F hF hspec).gen.Coins n)
    (𝓕.invProbAt A.withIndexParam n)]
  congr 1
  funext r
  generalize hidx : (𝓕.toCollection F hF hspec).index n r = i
  have hi : i.length = n := by rw [← hidx, toCollection_index, List.length_replicate]
  subst hi
  rw [toCollection_index] at hidx
  rw [invProbAt_eq_uprob]
  refine OneWay.uprob_congr fun z => ?_
  show (∃ x', decodeFin (𝓕.inLen.eval i.length)
      (A.runAt i.length (pairEncode i (List.ofFn (𝓕.f i.length z.1))) z.2) = some x' ∧
      List.ofFn (𝓕.f i.length x') = List.ofFn (𝓕.f i.length z.1)) ↔ _
  simp only [NUPPT.withIndexParam_runAt, hidx, decodeFin_eq_some_iff, List.ofFn_inj]

/-- **A strong one-way function is a collection of one-way functions**
[PS10, Theorem 42.2 ⇐], explicit form: for every strong one-way family `𝓕` with evaluator
`F`, the collection `𝓕.toCollection F` is one-way.

**Proof sketch.** The sampler is exactly uniform (`toCollection_sampleClose`, `δ = 0`); the
inversion probability is `𝓕.invProbAt (withIndexParam A) n` (`toCollection_invProbAt`),
negligible by `h.hard`. -/
theorem StrongOneWay.toCollection_oneWay (h : 𝓕.StrongOneWay) :
    (𝓕.toCollection F hF hspec).OneWay where
  sampleClose := ⟨fun _ => 0, fun c => ⟨1, fun n hn => by
      rw [abs_zero]
      exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩,
    toCollection_sampleClose 𝓕 F hF hspec⟩
  hard A := by
    simpa only [toCollection_invProbAt] using h.hard A.withIndexParam

/-- **A strong one-way function gives a collection of one-way functions**
[PS10, Theorem 42.2 ⇐]: the collection `toCollection` built from the evaluator of `h.easy`. -/
theorem StrongOneWay.exists_collection_oneWay {𝓕 : FunFamily} (h : 𝓕.StrongOneWay) :
    ∃ G : Collection, G.OneWay := by
  obtain ⟨F, hF, hspec⟩ := h.easy
  exact ⟨_, FunFamily.StrongOneWay.toCollection_oneWay 𝓕 F hF hspec h⟩

end FunFamily

/-! ## Theorem 42.2 (⇒): a collection gives a strong one-way function -/

/-- A string of `a + b` bits as an `a`-bit and a `b`-bit string: the coins `(r₁, r₂)` of
[PS10, Theorem 42.2]. -/
def splitCoins (a b : ℕ) : (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The first half of `splitCoins a b r` is the first `a` bits of the encoding of `r`. -/
theorem ofFn_splitCoins_fst (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).1 = (List.ofFn r).take a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_take,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow, Fin.castAdd, Fin.castLE]

/-- The second half of `splitCoins a b r` is the encoding of `r` after its first `a` bits. -/
theorem ofFn_splitCoins_snd (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).2 = (List.ofFn r).drop a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_drop,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow, Fin.natAdd]

/-- The encoding of the coin string assembled from two halves is the concatenation of the
encodings of the halves. -/
theorem ofFn_splitCoins_symm (a b : ℕ) (r₁ : Fin a → Bool) (r₂ : Fin b → Bool) :
    List.ofFn ((splitCoins a b).symm (r₁, r₂)) = List.ofFn r₁ ++ List.ofFn r₂ := by
  set r := (splitCoins a b).symm (r₁, r₂) with hr
  have h1 : (splitCoins a b r).1 = r₁ := by rw [hr, Equiv.apply_symm_apply]
  have h2 : (splitCoins a b r).2 = r₂ := by rw [hr, Equiv.apply_symm_apply]
  rw [← h1, ← h2, ofFn_splitCoins_fst, ofFn_splitCoins_snd, List.take_append_drop]

namespace Collection

variable (G : Collection)

/-- The raw string `⟨i, eval ⟨i, w⟩⟩` of the function `g(r₁, r₂)` of [PS10, Theorem 42.2 ⇒],
`i = Gen(1^n; r₁)`, `w = Sample(1^n, i; r₂)` the sampled encoded `x ∈ D_i`; the second
component is `f_i(x)` by `Collection.sample_spec` (`EvalSampled`). -/
def owfRaw (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) : List Bool :=
  pairEncode (G.index n r₁)
    (G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂)))

/-- `L` bounds the length of the raw output of `g` strictly (room for the end marker). -/
def OutLenBound (L : PolyExpr) : Prop :=
  ∀ n (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n), (G.owfRaw n r₁ r₂).length < L.eval n

/-- *Honest evaluation on sampled strings*: every string output by the sampler at a
generated index decodes to some `x ∈ D_i` and the evaluator computes `f_i(x)` on it
[PS10, Definition 41.1 (2)–(3)] — the content of the field `Collection.sample_spec`, stated
with `index` (`Collection.evalSampled`); kept as a named predicate for the consumers that
quote it (`PublicKey`). -/
def EvalSampled : Prop :=
  ∀ n (r : G.gen.Coins n) (s : G.sample.Coins n), ∃ x,
    G.decD (G.index n r) (G.sample.runAt n (G.index n r) s) = some x ∧
      G.eval (pairEncode (G.index n r) (G.sample.runAt n (G.index n r) s)) = G.f (G.index n r) x

/-- **Every collection evaluates honestly on sampled strings**: `EvalSampled` is the field
`sample_spec` read through `index` (repair of the run-3 audit, P3-1; previously an
underivable hypothesis). -/
theorem evalSampled : G.EvalSampled := G.sample_spec

/-- **The function `g(r₁, r₂) = ⟨i, f_i(x)⟩`** of [PS10, Theorem 42.2 ⇒, proof idea] as a
family: input length `|r₁| + |r₂|` (the coins of `Gen` and `Sample`), output length `L`, the
raw string followed by the marker `1` and zero-padded to `L n` bits (recovered by
`splitAtLastTrue`).

**Deviation:** explicit output length `L` (D9) and marker padding for a typed output;
`OutLenBound L` holds for a suitable `L` (`exists_outLenBound`). -/
def owfFamily (L : PolyExpr) : FunFamily where
  inLen := .add G.gen.coins G.sample.coins
  outLen := L
  f n r := padFin (L.eval n)
    (G.owfRaw n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) r).1
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) r).2 ++ [true])

/-- The padding of a short string is the string followed by zeros. -/
theorem ofFn_padFin_of_le {ℓ : ℕ} {w : List Bool} (hw : w.length ≤ ℓ) :
    List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_ofFn, padFin, List.getD_eq_getElem?_getD]
  rw [List.getElem_append]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp

/-- **Marker padding is injective** on strings shorter than the padding length: the family
`owfFamily` loses no information about `⟨i, f_i(x)⟩`. -/
theorem padFin_append_true_injective {ℓ : ℕ} {s s' : List Bool} (hs : s.length < ℓ)
    (hs' : s'.length < ℓ) (h : padFin ℓ (s ++ [true]) = padFin ℓ (s' ++ [true])) : s = s' := by
  have h1 := congrArg List.ofFn h
  rw [ofFn_padFin_of_le (by simp; omega), ofFn_padFin_of_le (by simp; omega)] at h1
  have h2 := congrArg splitAtLastTrue h1
  simp only [List.append_assoc, List.singleton_append, PolyHierarchy.splitAtLastTrue_marker,
    Option.some.injEq] at h2
  exact h2

/-- `|A(1^n, y; r)|` is bounded by the time bound at the length
`8n + 14 + 4|y| + 2·adv(n) + coins(n)` of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.Coins n) :
    (A.runAt n y r).length ≤
      A.Ct * (8 * n + 14 + 4 * y.length + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  refine (A.output_length_le _).trans ?_
  unfold NUPPT.timeBound
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have := A.advice_length n
  simp only [length_pairEncode, NUPPT.length_advInput, List.length_ofFn, NUPPT.coinLen]
  omega

/-- The syntactic polynomial bounding `|A(1^n, y)|` when `|y| ≤ Y(n)` (`length_runAt_le`). -/
def _root_.Complexity.NUPPT.runLenPoly (A : NUPPT) (Y : PolyExpr) : PolyExpr :=
  (PolyExpr.normal A.Ct A.ct).subst
    (.add (.add (.mul (.const 8) .var) (.const 14))
      (.add (.mul (.const 4) Y) (.add (.mul (.const 2) A.adv) A.coins)))

/-- Evaluation of `runLenPoly`. -/
theorem _root_.Complexity.NUPPT.eval_runLenPoly (A : NUPPT) (Y : PolyExpr) (n : ℕ) :
    (A.runLenPoly Y).eval n =
      A.Ct * (8 * n + 14 + 4 * Y.eval n + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  rw [NUPPT.runLenPoly, PolyExpr.eval_subst, PolyExpr.eval_normal]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  ring

/-- `|A(1^n, y)| ≤ runLenPoly A Y (n)` whenever `|y| ≤ Y(n)`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le_runLenPoly (A : NUPPT) {Y : PolyExpr} (n : ℕ)
    {y : List Bool} (hy : y.length ≤ Y.eval n) (r : A.Coins n) :
    (A.runAt n y r).length ≤ (A.runLenPoly Y).eval n := by
  rw [NUPPT.eval_runLenPoly]
  refine (A.length_runAt_le n y r).trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- **The output of `g` has polynomial length**: a syntactic polynomial `L` with
`|⟨i, eval ⟨i, w⟩⟩| < L(n)` for all coins, from the time bounds of `Gen`, `Sample` and `eval`.

**Proof sketch.** `|i| ≤ Q₁(n) := runLenPoly Gen 0`, `|w| ≤ Q₂(n) := runLenPoly Sample Q₁`,
`|eval ⟨i, w⟩| ≤ C(2Q₁ + 2 + Q₂ + 1)^c =: Q₃(n)` (constants of `eval_poly.output_length_le`),
and `|⟨i, ·⟩| = 2|i| + 2 + |·|`, so `L := 2Q₁ + 3 + Q₃` works. -/
theorem exists_outLenBound : ∃ L : PolyExpr, G.OutLenBound L := by
  obtain ⟨C, c, hC⟩ := G.eval_poly.output_length_le
  set Q₁ : PolyExpr := G.gen.runLenPoly (.const 0) with hQ₁
  set Q₂ : PolyExpr := G.sample.runLenPoly Q₁ with hQ₂
  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
  refine ⟨.add (.add (.mul (.const 2) Q₁) (.const 3)) Q₃, fun n r₁ r₂ => ?_⟩
  have hi : (G.index n r₁).length ≤ Q₁.eval n :=
    (length_pairFstD_le _).trans (G.gen.length_runAt_le_runLenPoly n (by simp) r₁)
  have hw : (G.sample.runAt n (G.index n r₁) r₂).length ≤ Q₂.eval n :=
    G.sample.length_runAt_le_runLenPoly n hi r₂
  have he : (G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂))).length ≤
      Q₃.eval n := by
    refine (hC _).trans ?_
    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  simp only [owfRaw, length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-! ### The evaluator of `g` -/

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The index `i = Gen(1^n; r₁)` computed from the unary parameter `u = 1^n` and the coin
string `r`: `Gen`'s output on the layout `⟨⟨⟨u, []⟩, []⟩, r.take (gen.coins |u|)⟩`, first
component. -/
private def owfIndexStr (u r : List Bool) : List Bool :=
  pairFstD (G.gen.output (NUPPT.layout u [] [] (r.take (G.gen.coins.eval u.length))))

/-- The raw string `⟨i, eval ⟨i, Sample(1^n, i; r₂)⟩⟩` of `g` computed from `u = 1^n` and the
coin string `r` (`r₂ = r.drop (gen.coins |u|)`, the sampler on the layout
`⟨⟨⟨u, i⟩, []⟩, r₂⟩`): the string form of `owfRaw` (`owfRawStr_eq`). -/
private def owfRawStr (u r : List Bool) : List Bool :=
  pairEncode (G.owfIndexStr u r) (G.eval (pairEncode (G.owfIndexStr u r)
    (G.sample.output (NUPPT.layout u (G.owfIndexStr u r) [] (r.drop (G.gen.coins.eval u.length))))))

/-- The index computation is polynomial-time on `⟨u, r⟩` (`polyTimeComputable_pairTakePoly`,
`NUPPT.polyTimeComputable_layout`, `NUPPT.polyTimeComputable_output`). -/
private theorem owfIndexStr_poly :
    PolyTimeComputable fun z => G.owfIndexStr (pairFstD z) (pairSndD z) :=
  ptc_comp polyTimeComputable_pairFstD (ptc_comp G.gen.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD (polyTimeComputable_const [])
      (polyTimeComputable_const []) (polyTimeComputable_pairTakePoly G.gen.coins)))

/-- The raw string of `g` is polynomial-time on `⟨u, r⟩` (`polyTimeComputable_pairDropPoly`,
the sampler's and the evaluator's output functions, pairing). -/
private theorem owfRawStr_poly :
    PolyTimeComputable fun z => G.owfRawStr (pairFstD z) (pairSndD z) :=
  have hw : PolyTimeComputable fun z => G.sample.output (NUPPT.layout (pairFstD z)
      (G.owfIndexStr (pairFstD z) (pairSndD z)) []
      ((pairSndD z).drop (G.gen.coins.eval (pairFstD z).length))) :=
    ptc_comp G.sample.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD G.owfIndexStr_poly
        (polyTimeComputable_const []) (polyTimeComputable_pairDropPoly G.gen.coins))
  G.owfIndexStr_poly.pairEncode (ptc_comp G.eval_poly (G.owfIndexStr_poly.pairEncode hw))

/-- On `u = 1^n` and the encoded coins `r₁ ++ r₂`, the index computation is `index n r₁`
(`Gen` is uniform, so its advice is `[]`; the cut at `gen.coins n` is `List.take_left'`). -/
private theorem owfIndexStr_eq (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) :
    G.owfIndexStr (List.replicate n true) (List.ofFn r₁ ++ List.ofFn r₂) = G.index n r₁ := by
  unfold owfIndexStr Collection.index NUPPT.runAt NUPPT.layout NUPPT.advInput
  rw [List.length_replicate, List.take_left' (by simp [NUPPT.coinLen]), G.gen_uniform n]

/-- On `u = 1^n` and the encoded coins `r₁ ++ r₂`, the raw string of `g` is `owfRaw n r₁ r₂`
(`Sample` is uniform; the cut at `gen.coins n` is `List.drop_left'`). -/
private theorem owfRawStr_eq (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) :
    G.owfRawStr (List.replicate n true) (List.ofFn r₁ ++ List.ofFn r₂) = G.owfRaw n r₁ r₂ := by
  unfold owfRawStr owfRaw
  rw [owfIndexStr_eq, List.length_replicate, List.drop_left' (by simp [NUPPT.coinLen])]
  unfold NUPPT.runAt NUPPT.layout NUPPT.advInput
  rw [G.sample_uniform n]

/-- **`g` is easy to compute** [PS10, Theorem 42.2 ⇒, "`g` is easy"]: the evaluator on
`⟨1^n, r⟩` pads `owfRawStr 1^n r ++ [true]` to `L n` bits (`polyTimeComputable_padStr`);
its value on `⟨1^n, List.ofFn r⟩` is `List.ofFn (g n r)` by `owfRawStr_eq`,
`ofFn_splitCoins_fst/snd` and `ofFn_padFin_eq_padStr`. -/
private theorem owfFamily_easy (L : PolyExpr) : (G.owfFamily L).Easy := by
  have hF : PolyTimeComputable fun z =>
      padStr L (pairFstD z) (G.owfRawStr (pairFstD z) (pairSndD z) ++ [true]) := by
    have h := ptc_comp (polyTimeComputable_padStr L)
      (polyTimeComputable_pairFstD.pairEncode (G.owfRawStr_poly.append (polyTimeComputable_const [true])))
    convert h using 1
    funext z
    simp
  refine ⟨_, hF, fun n x => ?_⟩
  have hx : List.ofFn x =
      List.ofFn (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) x).1 ++
        List.ofFn (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) x).2 := by
    rw [← ofFn_splitCoins_symm, Prod.mk.eta, Equiv.symm_apply_apply]
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, owfFamily]
  rw [hx, owfRawStr_eq, ← ofFn_padFin_eq_padStr, List.length_replicate]

/-! ### The collection inverter built from an inverter of `g` -/

/-- The raw function of the collection inverter obtained from an inverter `A'` of `g`, on
the layout `⟨⟨⟨u, ⟨i, y⟩⟩, α⟩, ρ⟩`: pad `⟨i, y⟩ ++ [true]` to `L(|u|)` bits (this is
`List.ofFn (g n r)` whenever `⟨i, y⟩ = owfRaw n r₁ r₂`), run `A'` on it with the advice `α`
and the coins `ρ`, drop the first `gen.coins(|u|)` bits of its answer and run the sampler on
the rest at the index `i`. -/
private def collInvRaw (L : PolyExpr) (A' : NUPPT) (z : List Bool) : List Bool :=
  G.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) []
    ((A'.output (NUPPT.layout (NUPPT.inParam z)
        (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
        (NUPPT.inCoins z))).drop
      (G.gen.coins.eval (NUPPT.inParam z).length)))

/-- The raw inverter function is polynomial-time.

**Proof sketch.** Four compositions in the FP calculus: the padding
`polyTimeComputable_padStr L` on `⟨inParam z, inArg z ++ [true]⟩`; `A'.output`
(`NUPPT.polyTimeComputable_output`) on the layout assembled by
`NUPPT.polyTimeComputable_layout`; the cut `polyTimeComputable_pairDropPoly G.gen.coins` on
`⟨inParam z, answer⟩`; and `Sample`'s output on the layout `⟨⟨⟨u, fst (inArg z)⟩, []⟩, rest⟩`.
Each `convert … using 1; funext; simp` discharges the projection identities
`pairFstD_pairEncode`/`pairSndD_pairEncode`. -/
private theorem collInvRaw_poly (L : PolyExpr) (A' : NUPPT) :
    PolyTimeComputable (G.collInvRaw L A') := by
  have hpad : PolyTimeComputable fun z =>
      padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true]) := by
    have h := ptc_comp (polyTimeComputable_padStr L)
      (NUPPT.polyTimeComputable_inParam.pairEncode
        (NUPPT.polyTimeComputable_inArg.append (polyTimeComputable_const [true])))
    convert h using 1
    funext z
    simp
  have hA : PolyTimeComputable fun z => A'.output (NUPPT.layout (NUPPT.inParam z)
      (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
      (NUPPT.inCoins z)) :=
    ptc_comp A'.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hpad
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
  have hdrop : PolyTimeComputable fun z => (A'.output (NUPPT.layout (NUPPT.inParam z)
      (padStr L (NUPPT.inParam z) (NUPPT.inArg z ++ [true])) (NUPPT.inAdvice z)
      (NUPPT.inCoins z))).drop (G.gen.coins.eval (NUPPT.inParam z).length) := by
    have h := ptc_comp (polyTimeComputable_pairDropPoly G.gen.coins)
      (NUPPT.polyTimeComputable_inParam.pairEncode hA)
    convert h using 1
    funext z
    simp
  have h := ptc_comp G.sample.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg)
      (polyTimeComputable_const []) hdrop)
  exact h

/-- The collection inverter `A(1^n, ⟨i, y⟩)` built from an inverter `A'` of `g`
[PS10, Theorem 42.2 ⇒, the reduction]: `collInvRaw` packaged as a machine with the coins
and the advice of `A'`. -/
private noncomputable def collInverter (L : PolyExpr) (A' : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (G.collInvRaw_poly L A') A'.coins A'.adv A'.advice A'.advice_length

/-- The activation of the collection inverter: pad, call `A'`, drop `gen.coins n` bits,
sample at the first component of the argument (`Sample` is uniform). -/
private theorem collInverter_runAt (L : PolyExpr) (A' : NUPPT) (n : ℕ) (y : List Bool)
    (ρ : A'.Coins n) :
    (G.collInverter L A').runAt n y ρ =
      G.sample.runAtL n (pairFstD y)
        ((A'.runAt n (padStr L (List.replicate n true) (y ++ [true])) ρ).drop (G.gen.coinLen n)) := by
  have h := NUPPT.runAtL_ofPolyTime (G.collInvRaw_poly L A') A'.coins A'.adv A'.advice
    A'.advice_length n y (List.ofFn ρ)
  rw [NUPPT.runAt_eq]
  refine h.trans ?_
  simp [collInvRaw, NUPPT.runAtL, NUPPT.runAt, NUPPT.advInput, NUPPT.layout, NUPPT.inParam,
    NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins, NUPPT.coinLen, G.sample_uniform n]

/-- Honest evaluation on sampled strings at an index known to equal `i`
(`Collection.evalSampled` transported along `index n r₁ = i`). -/
private theorem exists_decD_of_index_eq {n : ℕ} (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n)
    {i : List Bool} (hi : G.index n r₁ = i) :
    ∃ x : G.D i, G.decD i (G.sample.runAt n i r₂) = some x ∧
      G.eval (pairEncode i (G.sample.runAt n i r₂)) = G.f i x := by
  subst hi
  exact G.evalSampled n r₁ r₂

/-- **Functional identity of the reduction.** If `A'` inverts `g` on the coins
`(r₁, r₂)` — its answer is the encoding of some `z'` with `g n z' = g n (r₁, r₂)` — then the
sampled string at `(r₁, r₂)` decodes to some `x ∈ D_i` (`i = index n r₁`) and the collection
inverter's answer on `⟨i, f_i(x)⟩` decodes to a preimage of `f_i(x)`.

**Proof sketch.** `evalSampled` gives `x` with `owfRaw n r₁ r₂ = ⟨i, f_i(x)⟩`;
`padFin_append_true_injective` (with `OutLenBound`) turns `g n z' = g n (r₁, r₂)` into
`owfRaw n z'₁ z'₂ = owfRaw n r₁ r₂`, whose components give `index n z'₁ = i` and
`eval ⟨i, Sample(i; z'₂)⟩ = f_i(x)`; the inverter's answer is `Sample(i; z'₂)`
(`collInverter_runAt`, `ofFn_padFin_eq_padStr`, `ofFn_splitCoins_snd`), which decodes to an
`x'` with `f_i(x') = eval ⟨i, Sample(i; z'₂)⟩ = f_i(x)` (`exists_decD_of_index_eq`). -/
private theorem collInverter_success (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT)
    (n : ℕ) (r₁ : G.gen.Coins n) (r₂ : G.sample.Coins n) (ρ : A'.Coins n)
    (z' : Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool)
    (hz' : A'.runAt n (List.ofFn ((G.owfFamily L).f n
      ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂)))) ρ = List.ofFn z')
    (hg : (G.owfFamily L).f n z' =
      (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂))) :
    ∃ x, G.decD (G.index n r₁) (G.sample.runAt n (G.index n r₁) r₂) = some x ∧
      ∃ x', G.decD (G.index n r₁) ((G.collInverter L A').runAt n
          (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ) = some x' ∧
        G.f (G.index n r₁) x' = G.f (G.index n r₁) x := by
  obtain ⟨x, hx1, hx2⟩ := G.evalSampled n r₁ r₂
  refine ⟨x, hx1, ?_⟩
  have hraw : G.owfRaw n r₁ r₂ = pairEncode (G.index n r₁) (G.f (G.index n r₁) x) := by
    unfold owfRaw
    rw [hx2]
  have hg' : G.owfRaw n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 = G.owfRaw n r₁ r₂ := by
    have h := hg
    simp only [owfFamily, Equiv.apply_symm_apply] at h
    exact padFin_append_true_injective (hL n _ _) (hL n r₁ r₂) h
  have hidx : G.index n (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1 = G.index n r₁ := by
    have h := congrArg pairFstD hg'
    simpa only [owfRaw, pairFstD_pairEncode] using h
  have hev : G.eval (pairEncode (G.index n r₁) (G.sample.runAt n (G.index n r₁)
      (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2)) = G.f (G.index n r₁) x := by
    have h := congrArg pairSndD hg'
    simp only [owfRaw, pairSndD_pairEncode] at h
    rw [hidx] at h
    rw [h, hx2]
  have hout : (G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ =
      G.sample.runAt n (G.index n r₁) (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 := by
    rw [collInverter_runAt, pairFstD_pairEncode, ← hraw]
    have hpad : padStr L (List.replicate n true) (G.owfRaw n r₁ r₂ ++ [true]) =
        List.ofFn ((G.owfFamily L).f n
          ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, r₂))) := by
      simp only [owfFamily, Equiv.apply_symm_apply]
      rw [← ofFn_padFin_eq_padStr, List.length_replicate]
    rw [hpad, hz', NUPPT.runAt_eq, ← ofFn_splitCoins_snd]
  rw [hout]
  obtain ⟨x', hx'1, hx'2⟩ := G.exists_decD_of_index_eq
    (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').1
    (splitCoins (G.gen.coinLen n) (G.sample.coinLen n) z').2 hidx
  exact ⟨x', hx'1, by rw [← hx'2, hev]⟩

/-- **The fibre inequality.** For a fixed `r₁` (index `i`), the probability over
`(r₂, ρ)` that `A'` inverts `g` is at most the probability over the ideal `(x, ρ)` that the
collection inverter inverts `f_i`, plus the sampler's distance `δ n` from uniform.

**Proof sketch.** `collInverter_success` is a pointwise implication from the `g`-event to
`P (decD i (Sample(i; r₂))) ρ`, where `P o ρ` says that `o = some x` and the inverter wins
on `⟨i, f_i(x)⟩` (`uprob_mono`); `StatClose.abs_uprob_sub_le_prod` with `h.sampleClose`
moves from the sampled `x` to the ideal uniform `x` at the cost `δ n`; on `some x` the event
`P` is the collection event (`uprob_congr`). -/
private theorem fiber_le (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT) {δ : ℕ → ℝ}
    (hδ : G.SampleClose δ) (n : ℕ) (r₁ : G.gen.Coins n) :
    uprob (fun v : G.sample.Coins n × A'.Coins n => ∃ z',
      A'.runAt n (List.ofFn ((G.owfFamily L).f n
        ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1)))) v.2 = List.ofFn z' ∧
      (G.owfFamily L).f n z' =
        (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1))) ≤
    uprob (fun z : G.D (G.index n r₁) × A'.Coins n => ∃ x', G.decD (G.index n r₁)
        ((G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) z.1)) z.2) =
          some x' ∧ G.f (G.index n r₁) x' = G.f (G.index n r₁) z.1) + δ n := by
  let P : Option (G.D (G.index n r₁)) → A'.Coins n → Prop := fun o ρ => ∃ x, o = some x ∧
    ∃ x', G.decD (G.index n r₁) ((G.collInverter L A').runAt n
      (pairEncode (G.index n r₁) (G.f (G.index n r₁) x)) ρ) = some x' ∧
      G.f (G.index n r₁) x' = G.f (G.index n r₁) x
  have hclose := (abs_le.1 ((hδ n r₁).abs_uprob_sub_le_prod P)).2
  have h1 : uprob (fun v : G.sample.Coins n × A'.Coins n => ∃ z',
      A'.runAt n (List.ofFn ((G.owfFamily L).f n
        ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1)))) v.2 = List.ofFn z' ∧
      (G.owfFamily L).f n z' =
        (G.owfFamily L).f n ((splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (r₁, v.1))) ≤
      uprob (fun v : G.sample.Coins n × A'.Coins n =>
        P (G.decD (G.index n r₁) (G.sample.runAt n (G.index n r₁) v.1)) v.2) := by
    refine uprob_mono fun v hv => ?_
    obtain ⟨z', hz', hg⟩ := hv
    exact G.collInverter_success L hL A' n r₁ v.1 v.2 z' hz' hg
  have h2 : uprob (fun z : G.D (G.index n r₁) × A'.Coins n => P (some z.1) z.2) =
      uprob (fun z : G.D (G.index n r₁) × A'.Coins n => ∃ x', G.decD (G.index n r₁)
        ((G.collInverter L A').runAt n (pairEncode (G.index n r₁) (G.f (G.index n r₁) z.1)) z.2) =
          some x' ∧ G.f (G.index n r₁) x' = G.f (G.index n r₁) z.1) := by
    refine OneWay.uprob_congr fun z => ?_
    simp only [P, Option.some.injEq, exists_eq_left']
  linarith

/-- **The inversion probability of `g` is at most that of the collection plus the sampling
error**: `(G.owfFamily L).invProbAt A' n ≤ G.invProbAt (collInverter A') n + δ n`.

**Proof sketch.** `invProbAt_eq_uprob`; reindex the uniform input by `splitCoins` and
reassociate (`uprob_comp_equiv`); average over `r₁` (`uprob_prod`); on each fibre apply
`fiber_le`; the right-hand side is `uexp (fun r₁ => ⋯ + δ n)` by `uexp_add`, `uexp_const`. -/
private theorem invProbAt_owfFamily_le (L : PolyExpr) (hL : G.OutLenBound L) (A' : NUPPT)
    {δ : ℕ → ℝ} (hδ : G.SampleClose δ) (n : ℕ) :
    (G.owfFamily L).invProbAt A' n ≤ G.invProbAt (G.collInverter L A') n + δ n := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  rw [FunFamily.invProbAt_eq_uprob]
  let e : G.gen.Coins n × (G.sample.Coins n × A'.Coins n) ≃
      (Fin (G.gen.coinLen n + G.sample.coinLen n) → Bool) × A'.Coins n :=
    (Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (splitCoins (G.gen.coinLen n) (G.sample.coinLen n)).symm (Equiv.refl _))
  rw [← uprob_comp_equiv e, uprob_prod]
  unfold Collection.invProbAt
  rw [← OneWay.uexp_const (α := G.gen.Coins n) (δ n), ← OneWay.uexp_add]
  exact OneWay.uexp_mono fun r₁ => G.fiber_le L hL A' hδ n r₁

/-- **The collection's function `g` is a strong one-way function** [PS10, Theorem 42.2 ⇒],
explicit form: if `G` is a collection of one-way functions and `L` bounds the output of `g`,
then `G.owfFamily L` is strongly one-way.

Repair (run-3 audit P3-1): the former hypothesis `hG : G.EvalSampled` is dropped — it is
`G.evalSampled`, from the new field `sample_spec`.

**Deviation (Theorem 42.2 ⇒):** the explicit output length `L` (D9).

**Proof sketch.** *Easy.* The evaluator on `⟨1^n, r⟩` is an FP function: cut `r` into
`r₁`/`r₂` (`polyTimeComputable_pairTakePoly`/`_pairDropPoly G.gen.coins`), run `G.gen.output`
on the layout `⟨⟨⟨1^n, []⟩, []⟩, r₁⟩` (`NUPPT.polyTimeComputable_layout`, `gen_uniform`),
project `i` (`pairFstD`), run `G.sample.output` on `⟨⟨⟨1^n, i⟩, []⟩, r₂⟩`, apply `G.eval_poly`
to `⟨i, w⟩`, pair, append the marker `[true]` and `0^{L n}` (`PolyTimeComputable.append`,
`polyTimeComputable_unaryPoly L` mapped to zeros by `polyTimeComputable_blockMap (const 1)`
with the constant `[false]`), keep the first `L n` bits (`polyTimeComputable_pairTakePoly L`
on `⟨1^n, ·⟩`); the result is `List.ofFn (padFin (L n) (owfRaw ++ [true]))` by
`ofFn_padFin_of_le` and `OutLenBound`. *Hard.* Fix `A' : NUPPT`. The reduction
`A(1^n, ⟨i, y⟩; ρ)` (advice and coins of `A'`) pads `⟨i, y⟩ ++ [true]` to `L n` bits as above,
calls `A'.output` on `⟨⟨⟨1^n, t⟩, A'.advice n⟩, ρ⟩`, checks that the answer `z` has length
`gen.coins(n) + sample.coins(n)` (`polyTimeComputable_lenEq`, `_ite`), splits it into
`(r₁', r₂')` and outputs `G.sample.output ⟨⟨⟨1^n, i⟩, []⟩, r₂'⟩`. Functional identity: when
`A'` returns `z` with `g(z) = padFin (L n) (⟨i, y⟩ ++ [true])`, `padFin_append_true_injective`
and `pairEncode_injective` give `index n r₁' = i` and `eval ⟨i, w'⟩ = y` for
`w' := sample(1^n, i; r₂')`, and `G.evalSampled` decodes `w'` to an `x'` with `f_i(x') = y`.
Probability: for fixed `r₁` (index `i`) the `g`-experiment on `(r₂, ρ)` is the collection
experiment on `(x, ρ)` with `x := decD i (sample(i; r₂))` (`G.evalSampled` gives
`y = f_i(x)`), so `uprob_prod` over `r₁`, `uprob_comp_equiv (splitCoins …)`, `uprob_mono` (the
pointwise implication) and `StatClose.abs_uprob_sub_le_prod` with `h.sampleClose` give
`(G.owfFamily L).invProbAt A' n ≤ G.invProbAt A n + δ n` (`invProbAt_eq_uprob`); conclude by
`h.hard A`, `Negligible.add` and `Negligible.mono` (`invProbAt_nonneg`). -/
theorem OneWay.owfFamily_strongOneWay {G : Collection} (h : G.OneWay)
    {L : PolyExpr} (hL : G.OutLenBound L) : (G.owfFamily L).StrongOneWay where
  easy := G.owfFamily_easy L
  hard A' := by
    obtain ⟨δ, hδneg, hδ⟩ := h.sampleClose
    refine Negligible.mono ((h.hard (G.collInverter L A')).add hδneg) ⟨0, fun n _ => ?_⟩
    have hδ0 : 0 ≤ δ n := (hδ n fun _ => false).nonneg
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _),
      abs_of_nonneg (add_nonneg (Collection.invProbAt_nonneg _ _ _) hδ0)]
    exact G.invProbAt_owfFamily_le L hL A' hδ n

/-- **A collection of one-way functions gives a strong one-way function**
[PS10, Theorem 42.2 ⇒, "left as an exercise"]: the function `g(r₁, r₂) = ⟨i, f_i(x)⟩` with
`i = Gen(1^n; r₁)` and `x = Sample(i; r₂)`.

Repair (run-3 audit P3-1): provable from the explicit form once `Collection.sample_spec` ties
the sampler to `D_i` (previously the frozen statement was unprovable from the frozen fields).

**Proof sketch.** Take `L` from `exists_outLenBound G` and `𝓕 := G.owfFamily L`;
`owfFamily_strongOneWay h hL`. -/
theorem OneWay.exists_strongOneWay {F : Collection} (h : F.OneWay) :
    ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay :=
  let ⟨L, hL⟩ := F.exists_outLenBound
  ⟨F.owfFamily L, h.owfFamily_strongOneWay hL⟩

end Collection

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Permutations.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Group.End
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rejection-sampled random permutations

The permutation sampler of the Pass–shelat campaign (foundation decision D10): Fisher–Yates
with offsets drawn by the rejection sampler `rejectionSample` of `Asymptotic/Sampling.lean`,
one independent block of coins per position. `permFromCoins n k T` uses `T` trials of `k`
bits for each of the `n` positions; conditioned on success it is a uniformly random
permutation of `Fin n` (`permFromCoins_uniform_of_some`), it fails with probability at most
`n (1 - 1/2^k)^T` (`uprob_permFromCoins_none_le`), and with any default on failure it is
`StatClose` to a uniform permutation within that term (`statClose_permFromCoins`, an instance
of `statClose_getD_of_uniform_of_some`). The campaign parameters are `permBits n = Nat.size n`
bits per trial (so `n ≤ 2^k ≤ 2n`) and `permTrials n = 2n²` trials per position, for which
the failure term has the closed form `n · 2^{-n}` (`uprob_permFromCoins_none_le_two_pow`,
`statClose_permFromCoins_two_pow`). These are the permutations `σ, π ← S_n` of the honest
parties and simulators of [PS10, Protocols 118.3 and 120.6] and the colour permutations of
[PS10, Protocol 127.5]; the string-level parties read their coins into the `n × T × k` table
by `coinTable` (`ZeroKnowledge/Encoding.lean`) and the consumers are stated in terms of the
parameters defined here. (The section was split off `Asymptotic/Sampling.lean` to respect the
file-size limit.)

**Deviation:** [PS10] samples `σ ← S_n` exactly, in expected polynomial time; here the
sampler is truncated to `permTrials n` trials per position and the protocol theorems carry
the explicit statistical term `n · 2^{-n}` (D10, deviations register #11 and #15).

**Deviation (from the frozen signature of `uprob_permFromCoins_none_le`):** the frozen bound
`n * (1/2)^T` is false for the frozen definition of `permFromCoins` (the position `i = n - 1`
samples `Fin 1` with `k` bits and fails with probability `(1 - 1/2^k)^T`; for `n = 3`, `k = 2`,
`T = 10` this is `(3/4)^10 > 3 · 2^{-10}`). The lemma is stated with the provable bound
`n * (1 - 1/2^k)^T`; per-trial failure `≤ 1/2` holds for a single `rejectionSample` with
`2^k ≤ 2 m` (`uprob_rejectionSample_none_le_half_pow`).

**Repair (run-3 audit P2-1):** the frozen parameters `permFromCoins n n n` of the
graph-isomorphism prover fail with probability at least `1 - n/2^n` (the last position has
range `1` and `n` bits per trial), so this file now owns the campaign parameters `permBits`,
`permTrials`, the general `StatClose` form `statClose_permFromCoins` and the closed form
`n · 2^{-n}` at those parameters; the consumers (`ZeroKnowledge/GraphIsomorphism.lean`:
`samplePerm`, `permCoinLen`, `permFailBound`; `ZeroKnowledge/Encoding.lean`:
`polyTimeComputable_encPermFromCoins`) are stated in terms of them.

## Main definitions

* `TCSlib.Cryptography.fisherYates`, `TCSlib.Cryptography.permFromCoins` — a permutation of
  `Fin n` from offsets, and from rejection-sampled offsets.
* `TCSlib.Cryptography.permBits`, `TCSlib.Cryptography.permTrials` — the campaign parameters
  of the permutation sampler (`Nat.size n` bits per trial, `2n²` trials per position).
* `TCSlib.Cryptography.liftSucc`, `TCSlib.Cryptography.fyOffsets` — the lift of a permutation of
  `Fin n` to `Fin (n + 1)` fixing `0`, and the finset of in-range offset tuples.

## Main results

* `TCSlib.Cryptography.fisherYates_succ`, `TCSlib.Cryptography.fisherYates_injOn`,
  `TCSlib.Cryptography.exists_fyOffsets` — the Fisher–Yates recursion through
  `Equiv.Perm.decomposeFin`, and the offset map is a bijection from the `n!` in-range offset
  tuples onto the permutations.
* `TCSlib.Cryptography.uprob_pi_forall_dep` — independent coordinates with position-dependent
  events multiply (the dependent form of `OneWay.uprob_pi_forall`).
* `TCSlib.Cryptography.permFromCoins_uniform_of_some`,
  `TCSlib.Cryptography.uprob_permFromCoins_none_le`,
  `TCSlib.Cryptography.statClose_permFromCoins` — the permutation sampler: uniform
  conditioned on success, failure at most `n (1 - 1/2^k)^T`, `StatClose` form.
* `TCSlib.Cryptography.le_two_pow_permBits`, `TCSlib.Cryptography.two_pow_permBits_le` —
  `n ≤ 2^{permBits n} ≤ 2n`.
* `TCSlib.Cryptography.uprob_permFromCoins_none_le_two_pow`,
  `TCSlib.Cryptography.statClose_permFromCoins_two_pow` — the closed form `n · 2^{-n}` at the
  campaign parameters.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6, Theorem 122.3; §4.7 Protocol 127.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
-/

namespace TCSlib.Cryptography

open Finset

/-! ### Random permutations -/

/-- Fisher–Yates from offsets: `c i` is reduced modulo the number of remaining positions.
The permutation is `swap 0 (0 + c 0) ∘ swap 1 (1 + c 1) ∘ ⋯ ∘ swap (n-1) (n-1)` (the last
factor is applied first); the offset tuple `(c i mod (n - i))_i ↦ π` is a bijection from
`∏ Fin (n - i)` onto the permutations of `Fin n`. -/
def fisherYates (n : ℕ) (c : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  (List.finRange n).foldr
    (fun i σ => Equiv.swap i ⟨(i + c i % (n - i)) % n,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.isLt; omega))⟩ * σ) 1

/-- A permutation from `n` rejection samplers (`T` trials of `k` bits for position `i`,
range `n - i`); uniform conditioned on `some`. The permutations `π ← S_n` of the prover and
simulator of [PS10, Protocol 120.6] and the colour permutations of [PS10, Protocol 127.5]. -/
def permFromCoins (n k T : ℕ) (b : Fin n → Fin T → Fin k → Bool) : Option (Equiv.Perm (Fin n)) :=
  if h : ∀ i : Fin n, (rejectionSample (n - i) k T (b i)).isSome then
    some (fisherYates n fun i => ((rejectionSample (n - i) k T (b i)).get (h i)).val)
  else none

/-- The permutation sampler fails exactly when some position's rejection sampler fails. -/
theorem permFromCoins_eq_none_iff (n k T : ℕ) (b : Fin n → Fin T → Fin k → Bool) :
    permFromCoins n k T b = none ↔ ∃ i : Fin n, rejectionSample (n - i) k T (b i) = none := by
  unfold permFromCoins
  split_ifs with h
  · simp only [false_iff, not_exists]
    intro i hi
    simpa [hi] using h i
  · simp only [true_iff]
    by_contra hc
    push_neg at hc
    exact h fun i => Option.isSome_iff_ne_none.2 (hc i)

/-! ### The Fisher–Yates offset map is a bijection -/

/-- The lift of a permutation of `Fin n` to `Fin (n + 1)` fixing `0`: `decomposeFin.symm (0, e)`,
with `liftSucc e 0 = 0` and `liftSucc e x.succ = (e x).succ`. -/
def liftSucc {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

/-- The lift fixes `0`. -/
@[simp] theorem liftSucc_zero {n : ℕ} (e : Equiv.Perm (Fin n)) : liftSucc e 0 = 0 := by
  simp [liftSucc, Equiv.Perm.decomposeFin_symm_apply_zero]

/-- The lift acts as `e` on successors. -/
@[simp] theorem liftSucc_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n) :
    liftSucc e x.succ = (e x).succ := by
  simp [liftSucc, Equiv.Perm.decomposeFin_symm_apply_succ]

/-- The lift of the identity is the identity. -/
theorem liftSucc_one {n : ℕ} : liftSucc (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x <;> simp

/-- The lift is multiplicative. -/
theorem liftSucc_mul {n : ℕ} (e e' : Equiv.Perm (Fin n)) :
    liftSucc (e * e') = liftSucc e * liftSucc e' := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x <;> simp [Equiv.Perm.mul_apply]

/-- The lift of a transposition is the transposition of the successors. -/
theorem liftSucc_swap {n : ℕ} (a b : Fin n) :
    liftSucc (Equiv.swap a b) = Equiv.swap a.succ b.succ := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · rw [liftSucc_zero, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm
      (Fin.succ_ne_zero b).symm]
  · rw [liftSucc_succ, Equiv.swap_apply_def, Equiv.swap_apply_def]
    by_cases h1 : x = a
    · subst h1
      simp
    · by_cases h2 : x = b
      · subst h2
        simp [h1, Fin.succ_inj]
      · simp [h1, h2, Fin.succ_inj]

/-- `decomposeFin.symm (p, e)` is the transposition `(0 p)` after the lift of `e`. -/
theorem decomposeFin_symm_eq {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * liftSucc e := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.mul_apply]
  · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.mul_apply]

/-- Folding the lifted transpositions is the lift of the fold (`liftSucc` is multiplicative). -/
theorem foldr_swap_succ {n : ℕ} (s : Fin n → Fin n) : ∀ l : List (Fin n),
    l.foldr (fun i σ => Equiv.swap i.succ (s i).succ * σ) 1 =
      liftSucc (l.foldr (fun i σ => Equiv.swap i (s i) * σ) 1)
  | [] => liftSucc_one.symm
  | i :: l => by
    rw [List.foldr_cons, List.foldr_cons, liftSucc_mul, liftSucc_swap, foldr_swap_succ s l]

/-- **The Fisher–Yates recursion:** for in-range offsets (`c i < n + 1 - i`), the permutation on
`n + 1` positions is `decomposeFin.symm (c 0, fisherYates n (c ∘ succ))` — the transposition of
position `0` with `c 0` after the lifted permutation of the remaining positions.

**Proof sketch.** `List.finRange_succ` and `List.foldr_map` split off the factor at position `0`,
whose target is `c 0` (no modulus wraps). The factor at position `i.succ` is
`swap i.succ (i + 1 + c i.succ)`, the lift of the factor `swap i (i + c i.succ)` of
`fisherYates n (c ∘ succ)` (again no modulus wraps since `c i.succ < n - i`), so the remaining
fold is the lift of the inner fold (`foldr_swap_succ`), and `decomposeFin_symm_eq` assembles the
product. -/
theorem fisherYates_succ {n : ℕ} (c : Fin (n + 1) → ℕ) (hc : ∀ i, c i < n + 1 - i) :
    fisherYates (n + 1) c = Equiv.Perm.decomposeFin.symm
      (⟨c 0, by simpa using hc 0⟩, fisherYates n (fun i => c i.succ)) := by
  rw [decomposeFin_symm_eq]
  unfold fisherYates
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  congr 1
  · congr 1
    apply Fin.ext
    have h0 : c 0 < n + 1 := by simpa using hc 0
    simp only [Fin.val_zero, Nat.sub_zero, Nat.zero_add, Nat.mod_eq_of_lt h0]
  · rw [← foldr_swap_succ (fun i : Fin n =>
      (⟨(↑i + c i.succ % (n - ↑i)) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
        have := i.isLt; omega))⟩ : Fin n))]
    congr 1
    funext i σ
    congr 2
    apply Fin.ext
    have h1 : c i.succ < n - i := by
      have := hc i.succ
      rwa [Fin.val_succ, Nat.add_sub_add_right] at this
    have h2 := i.isLt
    simp only [Fin.val_succ]
    rw [Nat.add_sub_add_right, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The Fisher–Yates offset map is injective on in-range offsets:** two offset tuples with
`c i, c' i < n - i` giving the same permutation are equal.

**Proof sketch.** Induction on `n` through `fisherYates_succ`: `decomposeFin.symm` is injective,
so the first offsets agree and the permutations of the tails agree, and the induction
hypothesis (the tails are in range since `c i.succ < n + 1 - (i + 1) = n - i`) gives the rest
(`Fin.cases`). -/
theorem fisherYates_injOn : ∀ (n : ℕ) (c c' : Fin n → ℕ), (∀ i, c i < n - i) →
    (∀ i, c' i < n - i) → fisherYates n c = fisherYates n c' → c = c'
  | 0, _, _, _, _, _ => funext fun i => i.elim0
  | n + 1, c, c', hc, hc', h => by
    rw [fisherYates_succ c hc, fisherYates_succ c' hc'] at h
    have h' := Equiv.Perm.decomposeFin.symm.injective h
    rw [Prod.mk.injEq, Fin.mk.injEq] at h'
    obtain ⟨h0, htail⟩ := h'
    have hbound : ∀ (d : Fin (n + 1) → ℕ), (∀ i, d i < n + 1 - i) →
        ∀ i : Fin n, d i.succ < n - i := by
      intro d hd i
      have := hd i.succ
      rwa [Fin.val_succ, Nat.add_sub_add_right] at this
    have htail' := fisherYates_injOn n _ _ (hbound c hc) (hbound c' hc') htail
    funext i
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun htail' i

/-- The in-range offset tuples `(c i < n - i)_i` as a finset of `Fin n → ℕ`. -/
def fyOffsets (n : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun i : Fin n => Finset.range (n - i)

/-- Membership in `fyOffsets n`. -/
theorem mem_fyOffsets {n : ℕ} {c : Fin n → ℕ} : c ∈ fyOffsets n ↔ ∀ i, c i < n - i := by
  simp [fyOffsets, Fintype.mem_piFinset]

/-- `∏ i < n, (n - i) = n!`. -/
theorem prod_sub_eq_factorial : ∀ n : ℕ, ∏ i : Fin n, (n - (i : ℕ)) = n.factorial
  | 0 => by simp
  | n + 1 => by
    rw [Fin.prod_univ_succ, Nat.factorial_succ, ← prod_sub_eq_factorial n]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]

/-- There are `n!` in-range offset tuples. -/
theorem card_fyOffsets (n : ℕ) : (fyOffsets n).card = n.factorial := by
  rw [fyOffsets, Fintype.card_piFinset]
  simp only [Finset.card_range]
  exact prod_sub_eq_factorial n

/-- **Every permutation is a Fisher–Yates permutation of a unique in-range offset tuple**
(existence half): the injective image (`fisherYates_injOn`) of the `n!` offset tuples
(`card_fyOffsets`) in the `n!` permutations (`Fintype.card_perm`) is everything
(`Finset.eq_univ_of_card`). -/
theorem exists_fyOffsets {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ c ∈ fyOffsets n, fisherYates n c = π := by
  have hinj : Set.InjOn (fisherYates n) (fyOffsets n) := fun c hc c' hc' h =>
    fisherYates_injOn n c c' (mem_fyOffsets.1 hc) (mem_fyOffsets.1 hc') h
  have hcard : ((fyOffsets n).image (fisherYates n)).card = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Finset.card_image_of_injOn hinj, card_fyOffsets, Fintype.card_perm, Fintype.card_fin]
  have hmem : π ∈ (fyOffsets n).image (fisherYates n) := by
    rw [Finset.eq_univ_of_card _ hcard]
    exact Finset.mem_univ _
  exact Finset.mem_image.1 hmem

/-- **Independent coordinates with position-dependent events multiply:** the probability that
every coordinate `i` of a uniform tuple satisfies its own event `P i` is the product of the
probabilities (the position-dependent form of `OneWay.uprob_pi_forall`: `Nat.card` of the
dependent product of subtypes, `Equiv.subtypePiEquivPi`, `Nat.card_pi`). -/
theorem uprob_pi_forall_dep {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → α → Prop) :
    uprob (fun xs : ι → α => ∀ i, P i (xs i)) = ∏ i, uprob (P i) := by
  unfold uprob
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := P)), Nat.card_pi, Fintype.card_fun,
    ← Finset.card_univ (α := ι), ← Finset.prod_const, Nat.cast_prod, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- The event `{permFromCoins n k T b = some σ}` for `σ = fisherYates n c` with in-range offsets
`c` is the conjunction over the positions of `{rejectionSample (n - i) k T (b i) = some (c i)}`.

**Proof sketch.** Unfold `permFromCoins`. When every position succeeds, the output is
`fisherYates` of the sampled offsets, which are in range, so it equals `σ` iff the sampled
offsets are `c` (`fisherYates_injOn`), i.e. iff every position samples `c i`
(`Option.some_get`). When some position fails, the output is `none ≠ some σ` and the
conjunction fails at that position. -/
theorem permFromCoins_eq_some_iff {n k T : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n → ℕ)
    (hc : ∀ i, c i < n - i) (hσ : fisherYates n c = σ) (b : Fin n → Fin T → Fin k → Bool) :
    permFromCoins n k T b = some σ ↔
      ∀ i : Fin n, rejectionSample (n - i) k T (b i) = some ⟨c i, hc i⟩ := by
  unfold permFromCoins
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · intro hfy
      have hd : (fun i : Fin n => ((rejectionSample (n - i) k T (b i)).get (h i)).val) = c :=
        fisherYates_injOn n _ _ (fun i => Fin.isLt _) hc (hfy.trans hσ.symm)
      intro i
      rw [← Option.some_get (h i)]
      congr 1
      exact Fin.ext (congrFun hd i)
    · intro hall
      rw [← hσ]
      congr 1
      funext i
      have := hall i
      rw [← Option.some_get (h i), Option.some_inj] at this
      rw [this]
  · constructor
    · intro h'
      exact absurd h' (by simp)
    · intro hall
      exact absurd (fun i => by rw [hall i]; rfl) h

/-- Conditioned on success, `permFromCoins` is a uniformly random permutation: any two
permutations are output with the same probability ([PS10, Protocol 120.6], "`π ← S_n`";
[PS10, Protocol 127.5], the random colour permutation).

**Proof sketch.** The positions use disjoint coins, so the events
`{rejectionSample (n - i) k T (b i) = some (c i)}` are independent across `i` (product form
of `OneWay.uprob_pi_forall` for position-dependent predicates: `Nat.card` of a dependent
product of subtypes, `Equiv.subtypePiEquivPi` and `Nat.card_pi`), each of probability
`q_i = (1 - f_i) / (n - i)` by `rejectionSample_uniform_of_some` and
`uprob_rejectionSample_none` (`0 < n - i ≤ 2^k` from `hk`). The offset map
`c ↦ fisherYates n c` is injective on `∏ Fin (n - i)`: by `List.finRange_succ` and
`List.foldr_map`, `fisherYates (n+1) c = Equiv.Perm.decomposeFin.symm (c 0, fisherYates n (c ∘ succ))`
(the factor at position `j.succ` is `swap j.succ b.succ`, the image of `swap j b` under
`e ↦ decomposeFin.symm (0, e)`, which is multiplicative by `decomposeFin_symm_apply_zero/succ`;
no modulus wraps since `c i < n - i`), so `decomposeFin` being a bijection gives `c 0 = c' 0`
and the induction hypothesis the rest. Every permutation is attained since
`Fintype.card (∀ i, Fin (n - i)) = n! = Fintype.card (Perm (Fin n))` (`Fin.prod_univ_succ`,
`Fintype.card_perm`, `Fintype.bijective_iff_injective_and_card`). Hence
`{permFromCoins = some π}` is the event `{∀ i, rejectionSample (n - i) k T (b i) = some (c_π i)}`
for the single offset tuple `c_π`, of probability `∏ q_i`, independent of `π`. (Proved through
`exists_fyOffsets`, `permFromCoins_eq_some_iff` and `uprob_pi_forall_dep` of the preceding
section.) -/
theorem permFromCoins_uniform_of_some (n k T : ℕ) (hk : n ≤ 2 ^ k) (π π' : Equiv.Perm (Fin n)) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π) =
      uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π') := by
  obtain ⟨c, hc, hcπ⟩ := exists_fyOffsets π
  obtain ⟨c', hc', hcπ'⟩ := exists_fyOffsets π'
  have hL := uprob_pi_forall_dep (ι := Fin n) (α := Fin T → Fin k → Bool)
    (fun i x => rejectionSample (n - i) k T x = some ⟨c i, (mem_fyOffsets.1 hc) i⟩)
  have hR := uprob_pi_forall_dep (ι := Fin n) (α := Fin T → Fin k → Bool)
    (fun i x => rejectionSample (n - i) k T x = some ⟨c' i, (mem_fyOffsets.1 hc') i⟩)
  rw [OneWay.uprob_congr (permFromCoins_eq_some_iff π c (mem_fyOffsets.1 hc) hcπ),
    OneWay.uprob_congr (permFromCoins_eq_some_iff π' c' (mem_fyOffsets.1 hc') hcπ'), hL, hR]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  exact rejectionSample_uniform_of_some (n - i) k T (by omega) (by omega) _ _

/-- The permutation sampler fails with probability at most `n (1 - 1/2^k)^T` (union bound over
the `n` positions, each failing with probability `(1 - (n-i)/2^k)^T ≤ (1 - 1/2^k)^T`).

**Deviation (from the frozen signature):** the frozen bound `n * (1/2)^T` is false for the
frozen `permFromCoins` (position `n - 1` samples `Fin 1` with `k` bits: `n = 3`, `k = 2`,
`T = 10` gives failure `≥ (3/4)^10 > 3 · 2^{-10}`); the bound is corrected to
`n * (1 - 1/2^k)^T`, which is what the frozen definition supports.

**Proof sketch.** `permFromCoins_eq_none_iff`, the union bound `uprob_exists_le`, projection
of the uniform coin table to position `i` (`HardcoreBit.pushesUniform_eval`),
`uprob_rejectionSample_none` at range `n - i ≥ 1`, and monotonicity of `x ↦ x^T`. -/
theorem uprob_permFromCoins_none_le (n k T : ℕ) (hk : n ≤ 2 ^ k) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = none) ≤
      n * (1 - 1 / 2 ^ k : ℝ) ^ T := by
  rw [OneWay.uprob_congr fun b => permFromCoins_eq_none_iff n k T b]
  have hex : ∀ b : Fin n → Fin T → Fin k → Bool,
      (∃ i : Fin n, rejectionSample (n - i) k T (b i) = none) ↔
        ∃ i ∈ (univ : Finset (Fin n)), rejectionSample (n - i) k T (b i) = none := by
    simp
  rw [OneWay.uprob_congr hex]
  refine (uprob_exists_le univ fun (i : Fin n) (b : Fin n → Fin T → Fin k → Bool) =>
    rejectionSample (n - i) k T (b i) = none).trans ?_
  have hterm : ∀ i : Fin n,
      uprob (fun b : Fin n → Fin T → Fin k → Bool => rejectionSample (n - i) k T (b i) = none) ≤
        (1 - 1 / 2 ^ k : ℝ) ^ T := by
    intro i
    have hi := i.isLt
    rw [(HardcoreBit.pushesUniform_eval i).uprob_eq
      (fun c : Fin T → Fin k → Bool => rejectionSample (n - i) k T c = none),
      uprob_rejectionSample_none _ _ _ (by omega) (by omega)]
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact_mod_cast (show n - (i : ℕ) ≤ 2 ^ k by omega)
    · gcongr
      exact_mod_cast (show 1 ≤ n - (i : ℕ) by omega)
  calc ∑ i : Fin n,
        uprob (fun b : Fin n → Fin T → Fin k → Bool => rejectionSample (n - i) k T (b i) = none)
      ≤ ∑ _i : Fin n, (1 - 1 / 2 ^ k : ℝ) ^ T := sum_le_sum fun i _ => hterm i
    _ = n * (1 - 1 / 2 ^ k : ℝ) ^ T := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Fallback-to-default form of the permutation sampler: with the identity (or any `d`) on
failure, `permFromCoins n k T` is within `n (1 - 1/2^k)^T` of a uniformly random permutation
of `Fin n` (D10; [PS10, Protocols 118.3, 120.6 and 127.5], "`σ ← S_n`"). The argument is
`statClose_getD_of_uniform_of_some` with `permFromCoins_uniform_of_some` and
`uprob_permFromCoins_none_le`.

**Repair (run-3 audit P2-1):** added; the consumers previously restated this argument. -/
theorem statClose_permFromCoins (n k T : ℕ) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b : Fin n → Fin T → Fin k → Bool => (permFromCoins n k T b).getD d)
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (n * (1 - 1 / 2 ^ k : ℝ) ^ T) :=
  statClose_getD_of_uniform_of_some _ (permFromCoins_uniform_of_some n k T hk)
    (uprob_permFromCoins_none_le n k T hk) d

/-! ### The campaign parameters of the permutation sampler -/

/-- Bits per trial of the campaign's permutation sampler: `Nat.size n`, the least `k` with
`n < 2^k`, so that `n ≤ 2^k ≤ 2n` (`le_two_pow_permBits`, `two_pow_permBits_le`) and every
rejection trial of every position accepts with probability at least `1/(2n)` (D10).

**Repair (run-3 audit P2-1):** the frozen parameters (`n` bits per trial) accept a trial of
position `i` with probability `(n - i)/2^n`, so the frozen sampler `permFromCoins n n n`
failed with probability at least `1 - n/2^n`. -/
def permBits (n : ℕ) : ℕ := Nat.size n

/-- Trials per position of the campaign's permutation sampler: `2n²`, so that every position
fails with probability at most `(1 - 1/(2n))^{2n²} ≤ 2^{-n}` and the whole sampler with
probability at most `n · 2^{-n}` (`uprob_permFromCoins_none_le_two_pow`) (D10).

**Repair (run-3 audit P2-1):** the frozen `n` trials per position gave no negligible bound. -/
def permTrials (n : ℕ) : ℕ := 2 * n * n

/-- `n ≤ 2^{permBits n}`: the range of every position fits in the trial bits
(`Nat.lt_size_self`). -/
theorem le_two_pow_permBits (n : ℕ) : n ≤ 2 ^ permBits n := (Nat.lt_size_self n).le

/-- `permBits n ≤ n`: the sampler uses at most `n` bits per trial (`Nat.size_le`,
`Nat.lt_two_pow_self`), so its coin consumption `n · permTrials n · permBits n` is at most
`2n⁴`. -/
theorem permBits_le (n : ℕ) : permBits n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

/-- `2^{permBits n} ≤ 2n` for `n ≥ 1`: a trial of `permBits n` bits is at most twice the
range `n` (`Nat.size_le`: `2^{size n - 1} ≤ n`). -/
theorem two_pow_permBits_le {n : ℕ} (hn : 0 < n) : 2 ^ permBits n ≤ 2 * n := by
  have hs : 0 < Nat.size n := Nat.size_pos.2 hn
  have h : 2 ^ (Nat.size n - 1) ≤ n := by
    by_contra hc
    push_neg at hc
    have := Nat.size_le.2 hc
    omega
  calc 2 ^ permBits n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [permBits, ← pow_succ']
        congr 1
        omega
    _ ≤ 2 * n := by omega

/-- At the campaign parameters the permutation sampler fails with probability at most
`n · 2^{-n}` (D10; the sampling term of [PS10, Propositions 118.4 and 120.7, Theorem 122.3]
in the campaign's statements).

**Proof sketch.** `uprob_permFromCoins_none_le` with `k = permBits n`, then
`1 - 1/2^k ≤ 1 - 1/(2n)` (`two_pow_permBits_le`) and
`(1 - 1/(2n))^{2n·n} = ((1 - 1/(2n))^{2n})^n ≤ (1/2)^n` (`one_sub_inv_pow_le_half`); the case
`n = 0` is `0 ≤ 0`. -/
theorem uprob_permFromCoins_none_le_two_pow (n : ℕ) :
    uprob (fun b : Fin n → Fin (permTrials n) → Fin (permBits n) → Bool =>
        permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n := by
  refine (uprob_permFromCoins_none_le n _ _ (le_two_pow_permBits n)).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  have h2k : (2 : ℝ) ^ permBits n ≤ 2 * n := by exact_mod_cast two_pow_permBits_le hn
  have hpos : (0 : ℝ) < 2 ^ permBits n := by positivity
  have hstep : (1 - 1 / 2 ^ permBits n : ℝ) ≤ 1 - 1 / ((2 * n : ℕ) : ℝ) := by
    have := one_div_le_one_div_of_le hpos h2k
    push_cast
    linarith
  have h0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ permBits n := by
    rw [sub_nonneg, div_le_one hpos]
    exact one_le_pow₀ (by norm_num)
  have h0' : (0 : ℝ) ≤ 1 - 1 / ((2 * n : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  calc (1 - 1 / 2 ^ permBits n : ℝ) ^ permTrials n
      ≤ (1 - 1 / ((2 * n : ℕ) : ℝ)) ^ permTrials n := pow_le_pow_left₀ h0 hstep _
    _ = ((1 - 1 / ((2 * n : ℕ) : ℝ)) ^ (2 * n)) ^ n := by rw [← pow_mul, permTrials]
    _ ≤ (1 / 2) ^ n :=
        pow_le_pow_left₀ (pow_nonneg h0' _) (one_sub_inv_pow_le_half (2 * n) (by omega)) n
    _ = (2 : ℝ)⁻¹ ^ n := by rw [one_div]

/-- At the campaign parameters the permutation sampler, with any default on failure, is
within `n · 2^{-n}` of a uniformly random permutation of `Fin n` (D10): the statistical term
carried by the graph-isomorphism statements ([PS10, Propositions 118.4 and 120.7,
Theorem 122.3]). `statClose_getD_of_uniform_of_some` with `permFromCoins_uniform_of_some` and
`uprob_permFromCoins_none_le_two_pow`. -/
theorem statClose_permFromCoins_two_pow (n : ℕ) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b : Fin n → Fin (permTrials n) → Fin (permBits n) → Bool =>
        (permFromCoins n (permBits n) (permTrials n) b).getD d)
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (n * (2 : ℝ)⁻¹ ^ n) :=
  statClose_getD_of_uniform_of_some _
    (permFromCoins_uniform_of_some n _ _ (le_two_pow_permBits n))
    (uprob_permFromCoins_none_le_two_pow n) d

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Candidates/Arithmetic.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.NumberTheory.Primality
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial-time arithmetic hypothesis bundle

The candidate one-way functions of [PS10, §2.3, §2.7–§2.12] are "easy to compute", "easy to
sample" and their reductions run in polynomial time because binary multiplication, addition,
(truncated) subtraction, division with remainder, the extended Euclidean algorithm
[PS10, Algorithm 43.2], modular exponentiation [PS10, Algorithm 45.5], comparison, the bit
length and primality testing [PS10, §2.6.5, Remark on p. 33 (AKS)] are polynomial-time
computable on binary numerals.
The repository has no machines for binary arithmetic (inventory finding F1), so, by the
campaign's decision (plan `PassShelatChapter2-4Plan.md`, decision log "conditional
candidates", foundation decision D11), these facts are taken as an **explicit hypothesis
bundle** `ArithmeticFP`, never as axioms: every number-theoretic candidate theorem of the
campaign is stated under `H : ArithmeticFP`, and `#print axioms` stays clean.

Conventions. Numbers on tapes are binary numerals, most significant bit first, read by
`TCSlib.Cryptography.NumberTheory.listToNat` (leading zeros allowed) and written in a
prescribed width by `natToList k N` (the `k` low-order bits of `N`, most significant first;
exact when `N < 2^k`). The typed `k`-bit strings `Fin k → Bool` of the experiments are read
by `TCSlib.Cryptography.bitsToNat` and written by `natToBits k N`; the two conventions agree
through `List.ofFn` (`bitsToNat_eq_listToNat`, `natToList`). Arguments of the arithmetic
functions are paired with `Turing.pairEncode`.

**Deviation:** [PS10] treats the arithmetic algorithms as given (§2.6 gives their operation
counts; the `NumberTheory` modules formalize those); here their polynomial-time
computability on strings is a hypothesis, discharged by a future machine-building campaign.

## Main definitions

* `TCSlib.Cryptography.Candidates.natToBits`, `natToList` — fixed-width binary numerals.
* `TCSlib.Cryptography.Candidates.mulStr`, `addStr`, `subStr`, `divModStr`, `xgcdStr`,
  `modExpStr`, `leStr`, `sizeStr`, `primeStr` — the string functions of the bundle
  (`addStr`, `subStr`, `sizeStr` added by the run-3 audit repair P7-1: the reductions of
  §2.9–§2.12 decrement, add and subtract numerals and read bit lengths).
* `TCSlib.Cryptography.Candidates.ArithmeticFP` — the hypothesis bundle (a `Prop`
  structure).

## Main results

* `TCSlib.Cryptography.Candidates.listToNat_natToList`,
  `TCSlib.Cryptography.Candidates.bitsToNat_natToBits`,
  `TCSlib.Cryptography.Candidates.natToBits_bitsToNat` — the encodings are mutually
  inverse on numbers below `2^k`.
* `TCSlib.Cryptography.Candidates.natToBits_injOn` — `natToBits k` is injective below `2^k`.
* `TCSlib.Cryptography.Candidates.listToNat_addStr`,
  `TCSlib.Cryptography.Candidates.listToNat_subStr` — addition and truncated subtraction of
  numerals are lossless at the widths of the bundle.
* `TCSlib.Cryptography.Candidates.val_units_pow` — `(x^e).val = x.val^e mod M` in `Z_M^*`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3 (multiplication), §2.6.1–§2.6.6 (Euclid, modular exponentiation, primality
  testing), Remark on p. 33 (AKS).)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009 (the string-function class FP, `Complexity.PolyTimeComputable`).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory

/-! ## Fixed-width binary numerals -/

/-- The `k`-bit binary numeral of `N`, most significant bit first: bit `i` is the
`(k - 1 - i)`-th binary digit of `N` (the `k` low-order digits of `N`; exact when
`N < 2^k`). The inverse of `TCSlib.Cryptography.bitsToNat` on `Fin k → Bool`. -/
def natToBits (k N : ℕ) : Fin k → Bool := fun i => N.testBit (k - 1 - i)

/-- The `k`-bit binary numeral of `N` as a string (most significant bit first). -/
def natToList (k N : ℕ) : List Bool := List.ofFn (natToBits k N)

/-- `natToList` has length `k`. -/
@[simp] theorem length_natToList (k N : ℕ) : (natToList k N).length = k := by
  simp [natToList]

/-- The `0`-bit numeral is empty (moved from `RSA.lean`, run-3 audit P7-6). -/
theorem natToList_zero (N : ℕ) : natToList 0 N = [] := by simp [natToList]

/-- Dropping the last bit of a `(k+1)`-bit numeral of `N` gives the `k`-bit numeral of
`N / 2`. -/
theorem natToBits_succ_castSucc (k N : ℕ) (i : Fin k) :
    natToBits (k + 1) N (Fin.castSucc i) = natToBits k (N / 2) i := by
  simp only [natToBits, Fin.coe_castSucc]
  have h : k + 1 - 1 - (i : ℕ) = (k - 1 - i) + 1 := by have := i.2; omega
  rw [h, Nat.testBit_succ]

/-- The last bit of a `(k+1)`-bit numeral of `N` is the parity of `N`. -/
theorem natToBits_succ_last (k N : ℕ) : natToBits (k + 1) N (Fin.last k) = N.testBit 0 := by
  simp [natToBits]

/-- `listToNat` of the `k`-bit numeral of `N` is `N mod 2^k` (the numeral keeps the `k`
low-order digits). -/
theorem listToNat_natToList_eq_mod (k N : ℕ) : listToNat (natToList k N) = N % 2 ^ k := by
  induction k generalizing N with
  | zero => simp [natToList, listToNat, Nat.mod_one]
  | succ k ih =>
    rw [natToList, List.ofFn_succ', List.concat_eq_append]
    simp only [natToBits_succ_castSucc, natToBits_succ_last]
    rw [listToNat, List.foldl_concat, ← listToNat, ← natToList, ih, pow_succ', Nat.mod_mul]
    have h0 : (if N.testBit 0 then 1 else 0) = N % 2 := by
      have := Nat.toNat_testBit N 0
      simp only [pow_zero, Nat.div_one] at this
      rw [← this]
      cases N.testBit 0 <;> rfl
    rw [h0]
    omega

/-- **The encodings are inverse** (reading): `listToNat (natToList k N) = N` for `N < 2^k`. -/
theorem listToNat_natToList {k N : ℕ} (h : N < 2 ^ k) : listToNat (natToList k N) = N := by
  rw [listToNat_natToList_eq_mod, Nat.mod_eq_of_lt h]

/-- `bitsToNat` of the `k`-bit numeral of `N` is `N` for `N < 2^k`. -/
theorem bitsToNat_natToBits {k N : ℕ} (h : N < 2 ^ k) : bitsToNat (natToBits k N) = N := by
  rw [bitsToNat_eq_listToNat]
  exact listToNat_natToList h

/-- **The encodings are inverse** (writing): the `k`-bit numeral of `bitsToNat b` is `b`. -/
theorem natToBits_bitsToNat {k : ℕ} (b : Fin k → Bool) : natToBits k (bitsToNat b) = b :=
  bitsToNat_injective (bitsToNat_natToBits (bitsToNat_lt b))

/-- `natToBits k` is injective on numbers below `2^k`. -/
theorem natToBits_injOn {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k)
    (h : natToBits k M = natToBits k N) : M = N := by
  rw [← bitsToNat_natToBits hM, ← bitsToNat_natToBits hN, h]

/-- `natToList k` is injective on numbers below `2^k`. -/
theorem natToList_injOn {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k)
    (h : natToList k M = natToList k N) : M = N :=
  natToBits_injOn hM hN (List.ofFn_injective h)

/-- `listToNat` of an `n`-bit string is below `2^n`. -/
theorem listToNat_lt_two_pow (w : List Bool) : listToNat w < 2 ^ w.length := by
  have h := bitsToNat_lt (fun i : Fin w.length => w.get i)
  rw [bitsToNat_eq_listToNat] at h
  simpa using h

/-! ## The string functions of the bundle -/

/-- Binary multiplication: `⟨a, b⟩ ↦ a · b` as an `(|a| + |b|)`-bit numeral (lossless: the
product of an `|a|`-bit and a `|b|`-bit number has at most `|a| + |b|` bits). -/
def mulStr (z : List Bool) : List Bool :=
  natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z))

/-- Binary addition: `⟨a, b⟩ ↦ a + b` as an `(|a| + |b|)`-bit numeral (lossless,
`listToNat_addStr`: `a + b < 2^{|a|} + 2^{|b|} ≤ 2^{|a| + |b|}` when both numerals are nonempty,
and `a + b = b` when `a` is empty). Repair (run-3 audit P7-1): added to the bundle; the
reductions of [PS10, §2.12] add numerals (the CRT sum of Theorem 58.3, the increment
`(p+1)/4`). -/
def addStr (z : List Bool) : List Bool :=
  natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) + listToNat (pairSndD z))

/-- Truncated subtraction: `⟨a, b⟩ ↦ a ∸ b` (`0` when `b > a`) as an `|a|`-bit numeral
(lossless, `listToNat_subStr`). The decrement `p − 1` of `Φ(N) = (p−1)(q−1)` [PS10, p. 47]
is `subStr ⟨p, [true]⟩`, and `(x − z) mod N` is `(x + (N ∸ (z mod N))) mod N`. Repair (run-3
audit P7-1): added to the bundle. -/
def subStr (z : List Bool) : List Bool :=
  natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z))

/-- Bit length: `w ↦ 1^{Nat.size N}` for `N = listToNat w`, the length of the numeral of `N`
with its leading zeros stripped (`Nat.size N = ⌈log₂ (N + 1)⌉`, `N < 2^{Nat.size N} ≤ 2N` for
`N ≥ 1`), written in unary — the form in which lengths drive the cuts
`Complexity.polyTimeComputable_pairTakePoly`. Repair (run-3 audit P7-1): added to the bundle;
the rejection samplers of [PS10, §2.9–§2.12, §3.x] read `k = Nat.size N` bits per trial. -/
def sizeStr (w : List Bool) : List Bool := List.replicate (Nat.size (listToNat w)) true

/-- Division with remainder: `⟨a, b⟩ ↦ ⟨a / b, a mod b⟩`, the quotient as an `|a|`-bit and
the remainder as a `|b|`-bit numeral (Lean's convention `a / 0 = 0`, `a mod 0 = a`). -/
def divModStr (z : List Bool) : List Bool :=
  pairEncode (natToList (pairFstD z).length (listToNat (pairFstD z) / listToNat (pairSndD z)))
    (natToList (pairSndD z).length (listToNat (pairFstD z) % listToNat (pairSndD z)))

/-- The extended Euclidean algorithm [PS10, Algorithm 43.2] in the form the candidates use:
`⟨a, b⟩ ↦ ⟨gcd(a, b), a⁻¹ mod b⟩`, both as `|b|`-bit numerals, where `a⁻¹ mod b` is
`ZMod.inv` (the Bézout coefficient of `a` reduced modulo `b`; the inverse of `a` in `Z_b^*`
when `gcd(a, b) = 1`, [PS10, Claim 44.5 and Theorem 46.8]). -/
def xgcdStr (z : List Bool) : List Bool :=
  pairEncode (natToList (pairSndD z).length (Nat.gcd (listToNat (pairFstD z)) (listToNat (pairSndD z))))
    (natToList (pairSndD z).length
      (ZMod.val ((listToNat (pairFstD z) : ZMod (listToNat (pairSndD z)))⁻¹)))

/-- Modular exponentiation [PS10, Algorithm 45.5]: `⟨a, ⟨x, N⟩⟩ ↦ a^x mod N` as an
`|N|`-bit numeral. -/
def modExpStr (z : List Bool) : List Bool :=
  natToList (pairSndD (pairSndD z)).length
    (listToNat (pairFstD z) ^ listToNat (pairFstD (pairSndD z)) % listToNat (pairSndD (pairSndD z)))

/-- Comparison: `⟨a, b⟩ ↦ [a ≤ b]`. -/
def leStr (z : List Bool) : List Bool :=
  [decide (listToNat (pairFstD z) ≤ listToNat (pairSndD z))]

/-- Primality test: `w ↦ [w is prime]` (the hypothesis of
`TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt`). -/
def primeStr (w : List Bool) : List Bool := [decide (listToNat w).Prime]

/-- **The polynomial-time arithmetic hypothesis bundle** (plan decision "conditional
candidates", D11; inventory items Rem-33.2, Rem-43.6, Rem-48.2 and findings F1/F6):
binary multiplication, addition, truncated subtraction, division with remainder, the
extended Euclidean algorithm [PS10, Algorithm 43.2, Claim 43.3], modular exponentiation
[PS10, Algorithm 45.5, Theorem 45.6], comparison, the bit length and primality testing
[PS10, p. 33 and §2.6.5] are polynomial-time computable on binary numerals
(`Complexity.PolyTimeComputable`).

**Deviation:** [PS10] uses these algorithms freely; the campaign states each candidate
result under this explicit hypothesis instead of building the machines, adding no axiom.

Repair (run-3 audit P7-1): the fields `add`, `sub` and `size` were added — the generators,
samplers and reductions of [PS10, §2.9–§2.12] decrement (`Φ(N) = (p−1)(q−1)`), subtract
modulo `N` (`gcd(x − z, N)`, Algorithm 62.9), add (the CRT root formula, Theorem 58.3) and
read bit lengths (`k = Nat.size N` bits per rejection trial); all three are derivable from
`mul` and `divMod` in principle (`a + b = ((2^{2k} + a)(2^{2k} + b) mod 2^{4k}) / 2^{2k}`, the
bit length by a search with `le`), but that is the machine building the campaign excludes.
Every field is a true statement about a total FP function, so the bundle is satisfiable. -/
structure ArithmeticFP : Prop where
  /-- Binary multiplication is polynomial-time. -/
  mul : PolyTimeComputable mulStr
  /-- Binary addition is polynomial-time (run-3 audit P7-1). -/
  add : PolyTimeComputable addStr
  /-- Truncated binary subtraction is polynomial-time (run-3 audit P7-1). -/
  sub : PolyTimeComputable subStr
  /-- Division with remainder is polynomial-time. -/
  divMod : PolyTimeComputable divModStr
  /-- The extended Euclidean algorithm (gcd and modular inverse) is polynomial-time
  [PS10, Claim 43.3]. -/
  xgcd : PolyTimeComputable xgcdStr
  /-- Modular exponentiation is polynomial-time [PS10, Theorem 45.6]. -/
  modExp : PolyTimeComputable modExpStr
  /-- Comparison of binary numerals is polynomial-time. -/
  le : PolyTimeComputable leStr
  /-- The bit length (in unary) of a binary numeral is polynomial-time (run-3 audit P7-1). -/
  size : PolyTimeComputable sizeStr
  /-- Primality testing is polynomial-time [PS10, p. 33, AKS]. -/
  prime : PolyTimeComputable primeStr

/-! ### Unfolding lemmas -/

/-- `mulStr` on an encoded pair. -/
@[simp] theorem mulStr_pairEncode (a b : List Bool) :
    mulStr (pairEncode a b) = natToList (a.length + b.length) (listToNat a * listToNat b) := by
  simp [mulStr]

/-- `mulStr` on the numerals of `M` and `N` (widths `k` and `l`) is the `(k + l)`-bit numeral
of `M · N`. -/
theorem mulStr_natToList (k l M N : ℕ) (hM : M < 2 ^ k) (hN : N < 2 ^ l) :
    mulStr (pairEncode (natToList k M) (natToList l N)) = natToList (k + l) (M * N) := by
  rw [mulStr_pairEncode, length_natToList, length_natToList, listToNat_natToList hM,
    listToNat_natToList hN]

/-- `addStr` on an encoded pair. -/
@[simp] theorem addStr_pairEncode (a b : List Bool) :
    addStr (pairEncode a b) = natToList (a.length + b.length) (listToNat a + listToNat b) := by
  simp [addStr]

/-- `subStr` on an encoded pair. -/
@[simp] theorem subStr_pairEncode (a b : List Bool) :
    subStr (pairEncode a b) = natToList a.length (listToNat a - listToNat b) := by
  simp [subStr]

/-- `sizeStr w` is the unary bit length of the number read from `w`. -/
@[simp] theorem length_sizeStr (w : List Bool) : (sizeStr w).length = Nat.size (listToNat w) := by
  simp [sizeStr]

/-- The sum of the numbers read from two numerals is below `2^{|a| + |b|}`.

**Proof sketch.** If one numeral is empty it reads as `0` and the claim is
`listToNat_lt_two_pow` of the other; otherwise `a, b ≤ 2^{|a|} − 1, 2^{|b|} − 1` and
`2^{|a|} + 2^{|b|} ≤ 2^{|a|} · 2^{|b|}` since both powers are at least `2`
(`(x − 1)(y − 1) ≥ 1`, `nlinarith`). -/
theorem listToNat_add_lt_two_pow (a b : List Bool) :
    listToNat a + listToNat b < 2 ^ (a.length + b.length) := by
  have ha := listToNat_lt_two_pow a
  have hb := listToNat_lt_two_pow b
  rcases Nat.eq_zero_or_pos a.length with h0 | hpos
  · rw [h0] at ha ⊢
    simp only [pow_zero, Nat.lt_one_iff] at ha
    rw [ha, zero_add, zero_add]
    exact hb
  rcases Nat.eq_zero_or_pos b.length with h0' | hpos'
  · rw [h0'] at hb ⊢
    simp only [pow_zero, Nat.lt_one_iff] at hb
    rw [hb, add_zero, add_zero]
    exact ha
  have h2a : 2 ≤ 2 ^ a.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a.length := Nat.pow_le_pow_right (by norm_num) hpos
  have h2b : 2 ≤ 2 ^ b.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b.length := Nat.pow_le_pow_right (by norm_num) hpos'
  rw [pow_add]
  nlinarith

/-- **Addition is lossless**: `addStr ⟨a, b⟩` reads back as `a + b`. -/
theorem listToNat_addStr (a b : List Bool) :
    listToNat (addStr (pairEncode a b)) = listToNat a + listToNat b := by
  rw [addStr_pairEncode, listToNat_natToList (listToNat_add_lt_two_pow a b)]

/-- **Truncated subtraction is lossless**: `subStr ⟨a, b⟩` reads back as `a ∸ b`. -/
theorem listToNat_subStr (a b : List Bool) :
    listToNat (subStr (pairEncode a b)) = listToNat a - listToNat b := by
  rw [subStr_pairEncode]
  exact listToNat_natToList (lt_of_le_of_lt (Nat.sub_le _ _) (listToNat_lt_two_pow a))

/-- `leStr` on an encoded pair. -/
@[simp] theorem leStr_pairEncode (a b : List Bool) :
    leStr (pairEncode a b) = [decide (listToNat a ≤ listToNat b)] := by
  simp [leStr]

/-- `modExpStr` on an encoded triple. -/
@[simp] theorem modExpStr_pairEncode (a x N : List Bool) :
    modExpStr (pairEncode a (pairEncode x N)) =
      natToList N.length (listToNat a ^ listToNat x % listToNat N) := by
  simp [modExpStr]

/-- `primeStr` is the primality test of `exists_samplePrime_nuppt`. -/
theorem primeStr_eq : primeStr = fun w : List Bool => [decide (listToNat w).Prime] := rfl

/-- The residue of `x^e` is `x.val^e mod M` for a unit `x` of `Z_M` (any modulus `M ≠ 0`): the
form in which the evaluators `modExpStr` compute the permutations `x ↦ x^e` and `x ↦ x²`
(moved from `RSA.lean`, run-3 audit P7-6). -/
theorem val_units_pow (M : ℕ) [NeZero M] (x : (ZMod M)ˣ) (e : ℕ) :
    ((x ^ e : (ZMod M)ˣ) : ZMod M).val = (x : ZMod M).val ^ e % M := by
  rw [Units.val_pow_eq_pow_val, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]

/-- The product of two `k`-bit numbers is below `2^(k + k)`. -/
theorem mul_lt_two_pow_add {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k) : M * N < 2 ^ (k + k) := by
  rw [pow_add]
  exact Nat.mul_lt_mul'' hM hN

end TCSlib.Cryptography.Candidates
