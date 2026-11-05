## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03g-pack.md =====

# Gate 03g ([PS10] ch. 2–4, 3-colouring zero knowledge): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/g/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the graph 3-colouring language and its encodings, the commitment-based protocol of §4.7 and its parties, the soundness and efficiency of the repeated protocol, the simulator and its analysis, and the headline zero-knowledge theorem for 3COL behind Thm 124.1.
- **This pack gates fills.** Its files hold **3 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03g-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.7 (book pp. 124–129).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a malicious verifier that asks an edge outside the graph;
- a graph encoding with no edges, or an ill-formed instance;
- a simulator that is efficient only because the number of repetitions is bounded by the advice.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/{Language, Machines, Parties, Protocol, ProtocolProofs, Simulator, SimulatorLemmas, SimulatorMachine, SimulatorNumeric}.lean` and the facade `ZeroKnowledge/ThreeColoring.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | pack 03e's files (interaction, ZK definitions, commitments, NP); `ZeroKnowledge/NP.lean` |
| Design record | `briefs/pass-shelat/DESIGN.md` (§2.15 the frozen ch. 4 signatures, with D8; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Thm-124.1, Def-124.a, Claim-124.b–e, Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; graph isomorphism (pack 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/g/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 356 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   25 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 13 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 7 use only the standard axioms, and
   6 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 3 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 20 findings in 10 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines (`audits/pass-shelat/Checks.lean`);
- admissions: the 3 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **The language and relation** (`R3COL_witnessRelation`, sorried). Is the relation the
   source's: valid encodings, a proper colouring, a polynomially bounded witness? Is its
   polynomial-time verifier claim true?
2. **The protocol (Prot 127.5) and its repetition** (`colRep_efficientProverProof`, sorried).
   - Is the soundness error `(1 − 1/|E|)^{n|E|} ≤ e^{−n}` stated at the right number of
     repetitions?
   - Is the prover's efficiency stated given the witness?
3. **The simulator (Alg 128.7) and `col_zk`** (sorried).
   - Is ZK stated against every n.u.p.p.t. verifier with auxiliary input?
   - Is the truncation (D8's strict simulators) declared?
   - Does the error bound `|x| ε_B(√|x|) + e^{−n}` reduce to the commitment's hiding as the
     sketch claims?
4. **Run-3a's blocker P11-1** (3COL) was repaired. Check the repair.
5. **Thm 124.1** (form (A): ZK for every `(L, R_L)` with an explicit Levin reduction to 3COL).
   Is the headline's dependence on these three `sorry`s, and on the hypotheses of form (A),
   correctly declared?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.

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

## ===== briefs/pass-shelat/inventory-ch4.md =====

# Inventory — [PS10] Chapter 4, *Knowledge* (§4.1–4.9)

Run 1 (understand & design) of the Pass–shelat Chapters 2–4 campaign. Source:
`blueprint/src/references/pass-shelat-2010-ch4.raw.md` (plus Appendix B,
`…-appendix.raw.md`, for witness relations). Results are cited as `[PS10, <page>.<counter>]`.

This file is the input of the statement-phase planners. Every item below is one Lean
declaration (or a tight cluster of declarations in one file). Items the chapter leaves
unnumbered carry page-letter ids (`Def-114.a`, `Claim-117.c`, …); campaign infrastructure
items specific to Chapter 4 carry `Inf-4.<k>` ids.

## 0. Reading guide and conventions

* **Two layers, as in the Garg campaign (plan D2).** Every protocol statement has a
  *concrete* form at one common input `x` (typed objects — graphs on `Fin n`, permutations,
  `Fin 3`-colourings; coins ranging over arbitrary finite types; all probabilities are
  `TCSlib.Cryptography.uprob` over the product of the coin types, all indistinguishability
  statements are `distAdv` bounds) and an *asymptotic* form (string common input, PPT /
  nuPPT machines of plan D3/D4, negligible functions of `|x|`). The chapter's mathematics
  lives entirely in the concrete layer; the asymptotic layer adds (i) string encodings
  (`Inf-4.1`), (ii) machine closure for the honest parties and simulators (`Inf-4.2`,
  `Inf-4.3`), (iii) the negligibility bookkeeping `2^{-n(x)}`, `e^{-n(x)}` versus `|x|`
  (`Inf-4.4`).
* **Interaction model (plan D8).** An interactive machine is a *next-message function*
  `(x, z, r, received) ↦ message` plus an output function of the final view; a protocol is a
  pair with a fixed polynomial number of rounds; executions are obtained by iterating the two
  functions; `view_A = (x, z_A, r_A, M_A)`, `transcript = (M_A, M_B)`, `out_A = A.out(view_A)`.
  No tapes, states or idle transitions are modelled (Deviation, recorded once in
  `Interaction.lean`).
* **Simulators are strict PPT (plan D8).** The two rewinding simulators (123.4, 128.7) are
  truncated at `n` resp. `n·|E|` attempts and output `⊥` on failure; the resulting theorems
  are *statistical* zero-knowledge with error `2^{-n}` (GI) and a computational bound with an
  additional `e^{-n}` term (3COL). The perfect-simulation lemma is proved as stated
  (conditioned on success). Expected polynomial time (Def-121.a) and the untruncated loop
  (Claim-123.a) are deferred.
* **Scope.** `core` = mandatory content of the plan; `optional` = feasible, nice to have;
  `deferred` = cited without proof in the text and used by nothing downstream, or outside
  the frozen model (expected PPT, §7.2.1 sequential composition, Shamir).
* **Difficulty** 1 (trivial) … 5 (research-level or large machine-building fill).

### Dependencies on the Chapter 2/3 inventories (ids as used there)

Def-23.4 (PPT), Def-23.5 (running time, worst case over coins), Def-24.6 (computes with
probability 1), Def-24.7 (private-key encryption scheme), Def-26.8 (nuPPT, advice form),
Def-27.2 (negligible), Def-27.3 (strong OWF; "one-way permutation" = length-preserving
bijective OWF, single-function reading as in Thm 79.4), Def-55.1 (OWP collection — *not* the
form used in §4.7), Def-69.3/69.4 (ensembles, `≈`), Lem-71.5 (closure under efficient
operations), Lem-71.6 (hybrid lemma), Lem-73.8 (prediction lemma), Def-78.3 (hard-core
predicate), Thm-87.3 (Goldreich–Levin, for the unconditional form of Thm-126.4), Def-91.1
(single-message secure encryption), Def-93.1 (multi-message security, the model for
Claim-126.a), Def-102.1/102.2 (PKE), Thm-104.4 (whose proof is reused verbatim for
Claim-127.c).

### Design questions the panel must settle (DQ)

* **DQ1 — exact uniform sampling of `S_n`, of an edge of `E`, of `S_3`.** With a worst-case
  bounded coin *string* (D3) a PPT cannot sample `σ ∈ S_n` exactly uniformly (`n! ∤ 2^ℓ`),
  nor an edge of `E` when `|E|` is not a power of two. Options: (A) keep D3 and prove
  near-uniform samplers with statistical error `≤ 2^{-n}` at the machine level (every bound
  of the chapter gains a `2^{-n}` term; a large machine-building task); (B) let honest
  strategies and simulators draw their coins uniformly from a *finite type* `ρ n` whose
  elements have polynomial-length encodings, the next-message machine reading the encoding
  (D3 is the special case `ρ n = Fin ℓ → Bool`). Adversaries (`V*`, `P*`, `D`) keep D3/D4.
  Recommendation: (B), recorded as a Deviation; the concrete layer is written over arbitrary
  finite coin types either way, so the choice only affects `Inf-4.2`.
* **DQ2 — typed common inputs.** Concrete-layer protocols take typed common inputs
  (`SimpleGraph (Fin n) × SimpleGraph (Fin n)`, `SimpleGraph (Fin n)`); the asymptotic
  definitions (116.1, 121.1, 121.2) are over `List Bool` and are instantiated through the
  adjacency-matrix encoding and total decoding with defaults (`Inf-4.1`).
* **DQ3 — Theorem 124.1 needs Levin (witness-preserving) reductions**, which neither
  the text's Appendix B nor the repository (`Complexity.NPHard` is Karp-only;
  `SATtoColor.SATtoColorReduction` is graph-level, with the colouring witness `private`)
  provides. Core form: ZK for every `(L, R_L)` that Levin-reduces to 3COL
  (Thm-124.1 + Claim-124.d); the "every language in NP" form takes string-level Levin
  NP-hardness of 3COL as a hypothesis (Claim-124.b/124.c deferred).
* **DQ4 — commitment security parameter.** Def 126.3 infers `n` from `|v|`; Protocol 127.5
  commits to 2-bit colours. The formal `Com` takes `n` explicitly and the colour is padded to
  `n` bits (Deviation; see Prot-127.5).
* **DQ5 — sequential repetition.** The text proves ZK for *one* iteration and defers the
  `n`-fold / `n|E|`-fold protocols to §7.2.1 (Claim-123.c, outside Chapters 2–4). Core
  theorems are stated for the single-iteration protocols (soundness error `1/2` resp.
  `1 − 1/|E|`) *and* for the repeated protocols' completeness/soundness; the repeated
  protocols' ZK is stated with Claim-123.c as an explicit hypothesis or left sorried under a
  sketch (deferred).

## 1. Existing Lean the chapter builds on (verified by `lake env lean` on 2026-10-27)

| Declaration (fully qualified) | File | Use in Chapter 4 |
| --- | --- | --- |
| `TCSlib.Cryptography.uprob`, `uexp`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_eq_card_filter` | `TCSlib/Cryptography/Foundations/Probability.lean` | all probability statements |
| `TCSlib.Cryptography.abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `half_le_uprob_good` | same | hybrids in 112.2(ii), 126.a, 127.d, 129.d |
| `TCSlib.Cryptography.acceptProb`, `distAdv`, `predProb`, `acceptProb_comp_equiv`, `distAdv_le_statDist` | `Foundations/Experiments.lean` | ZK/hiding advantages; statistical ZK ⇒ computational |
| `TCSlib.Cryptography.Negligible`, `.add`, `.mul_pow`, `.const_mul`, `.mono`, `negligible_two_pow_neg`, `not_negligible_iff` | `Foundations/Negligible.lean` | every asymptotic statement |
| `TCSlib.Cryptography.uprob_eq_of_equiv`, `acceptProb_fst`, `acceptProb_snd`, `acceptProb_bind`, `acceptProb_update`, `pushSampler`, `sunglassRed`, `distAdv_sunglassRed`, `distAdv_comp`, `mixDist`, `distAdv_mixDist_eq`, `copies`, `multicopyRed`, `exists_multicopyRed_ge`, `distAdv_multicopyAvgRed` | `Pseudorandom/Indistinguishability.lean` | closure (Lem-71.5) and multi-copy hybrids (Claim-126.a, 127.d, 129.d) |
| `TCSlib.Cryptography.owpGen`, `owpGenNot`, `owpPair`, `owpPredictor`, `uprob_bool_prod`, `predProb_owpPredictor_false`, `predProb_owpPredictor_true`, `exists_owpPredictor` | `Pseudorandom/GeneratorFromPermutation.lean` | **exact** concrete content of commitment hiding (Claim-127.c) with `β := Unit` |
| `TCSlib.Cryptography.PushesUniform`, `pushesUniform_equiv`, `uprob_eq_one_of_forall`, `forall_of_uprob_eq_one`, `uprob_prod_and` | `HardcoreBit/Basic.lean` | uniform-permutation invariance (Lem-119.a), probability-1 completeness |
| `TCSlib.Cryptography.OneWay.uprob_pi_forall`, `uprob_eq_one_div_card`, `uprob_and_le_mul`, `uprob_congr` | `OneWayFunctions/Basic.lean` | counting lemmas Lem-119.c, Lem-127.g |
| `TCSlib.InformationTheory.statDist`, `statDist_triangle`, `FinDist.map`, `FinDist.uniform` | `TCSlib/InformationTheory/{StatisticalDistance,FinDist}.lean` | statistical ZK (Def-122.a, Thm-122.3.trunc, Claim-129.c) |
| `Schnorr.Transcript`, `honest`, `simulate`, `reindex`, `schnorr_completeness`, `schnorr_soundness`, `schnorr_hvzk` | `TCSlib/Cryptography/SchnorrProtocol.lean` | template (not reusable code): 3-move sigma protocol, HVZK by bijective reindexing = Thm-122.3.hv |
| `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.P_subset_NP` | `TCSlib/Complexity/ClassNP/NP.lean` | Def-191.11, Claim-117.c, Claim-118.b |
| `Complexity.P`, `Complexity.mem_P_iff`, `Complexity.DTIME` | `ClassP/{P,DTIME}.lean` | verifier predicates in `P` |
| `Complexity.PolyTimeReducible` (`≤ₚ`), `NPHard`, `NPComplete`, `mem_P_of_polyTimeReducible` | `ClassNP/Reductions.lean` | Karp reductions (Def-124.a extends to Levin) |
| `Complexity.PolyTimeComputable`, `.comp`, `.pairEncode`, `polyTimeComputable_ite`, `pairFstD`, `pairSndD`, `polyTimeComputable_lenEq` | `ClassNP/{PolyTime,PolyTimePairing}.lean` | machine-level PPT-ness of honest strategies (Inf-4.2) |
| `Complexity.SAT3`, `Complexity.SAT3_NPComplete` | `ClassNP/SAT.lean`, `CookLevin/Hardness.lean` | Claim-124.b |
| `Complexity.coNP` | `ClassNP/CoNP.lean` | Claim-118.c |
| `SATtoColor.Is3Colorable`, `ReductionGraph`, `SATtoColorReduction`, `SATtoColorCompleteness`, `Sat3` (`sat3Coloring` is `private`) | `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` | Def-124.f, Claim-124.b/c |
| `Turing.FinTM`, `FinTM.ComputesInTime`, `ComputesFunInTime` | `TCSlib/Complexity/TuringMachine/Finite.lean` | machine layer |
| `Turing.pairEncode`, `pairDecode`, `pairDecode_pairEncode` | `TuringMachine/Encoding.lean` | encodings of views/messages (Inf-4.1) |
| `Turing.FinTM.DecidesWithAdviceInTime`, `DTIMEAdvice`, `PAdvicePoly` | `CircuitComplexity/Advice.lean` | nuPPT distinguishers (D4) |
| `Turing.FinTM.exists_loopFindTM`, `exists_loopTM`, `exists_emitLoopTM` | `TuringMachine/Build/Loop.lean` | truncated simulators as machines (Inf-4.3, via plan's `Randomized/Repetition.lean`) |
| Mathlib `SimpleGraph.Iso` (`≃g`), `SimpleGraph.Iso.map`, `SimpleGraph.map`, `map_map`, `map_id`, `map_symm`, `comap_symm`, `map_adj` | `Mathlib/Combinatorics/SimpleGraph/Maps.lean` | `σ(G)`, isomorphism (Def-117.e) |
| Mathlib `SimpleGraph.Coloring`, `Colorable`, `Coloring.mk`, `Coloring.valid`, `instance Fintype (Coloring G α)` | `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` | 3COL (Def-124.f) |
| Mathlib `SimpleGraph.edgeFinset`, `mem_edgeFinset`, `fintypeEdgeSet`, `instance Fintype (SimpleGraph V)` (Basic.lean:110) | `Mathlib/Combinatorics/SimpleGraph/{Finite,Basic}.lean` | random edge of `E`, finiteness of graphs |
| Mathlib `Equiv.Perm`, `Fintype (Perm α)` (`Equiv.instFintype`/`fintypePerm`), `Fintype.card_perm`, `Equiv.mulRight` | `Mathlib/Data/Fintype/Perm.lean`, `Mathlib/Algebra/Group/…` | uniform permutations, `S_3` pair lemma |
| Mathlib `Real.add_one_le_exp`, `Real.one_sub_div_pow_le_exp_neg` | `Mathlib/Analysis/Complex/Exponential.lean` | Claim-125.a |

Nothing in the repository formalizes interaction, views, simulators, commitments, graph
isomorphism as a language, or the `3COL` language; `TCSlib/Cryptography/MPC/BGW/Privacy.lean`
(`linear_perfectPrivacy`: a bijection of the dealer's coins fixing a coalition's view) is the
closest "perfect simulation by reindexing" precedent and is a model for Claim-123.b.

## 2. Inventory table

Columns: id · kind · title · scope · difficulty · proposed file (under
`TCSlib/Cryptography/ZeroKnowledge/` unless absolute) · existing Lean (short) · depends on.

| id | kind | title | scope | diff | file | existing Lean | depends on |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Def-111.1 | Definition | Zero-knowledge (private-key) encryption | core | 2 | Encryption.lean | `distAdv`, `acceptProb`, `Negligible` | Def-24.7, Def-23.4, Def-26.8, Def-27.2 |
| Def-111.a | Definition | Perfect zero-knowledge encryption | optional | 1 | Encryption.lean | `FinDist.map`, `statDist` | Def-111.1 |
| Def-111.b | Definition | Zero-knowledge public-key encryption | optional | 2 | Encryption.lean | `distAdv` | Def-102.1 |
| Thm-112.2 | Theorem | Secure ⇔ zero-knowledge (private key) | core | 2 | Encryption.lean | — | Thm-112.2.i, Thm-112.2.ii |
| Thm-112.2.i | Theorem | Security ⇒ zero-knowledge | core | 2 | Encryption.lean | `distAdv` (sampler equality), PPT closure | Def-91.1, Def-111.1, Def-24.6 |
| Thm-112.2.ii | Theorem | Zero-knowledge ⇒ security | core | 1 | Encryption.lean | `abs_sub_le`, `Negligible.const_mul` | Def-91.1, Def-111.1 |
| Claim-112.a | Claim | The equivalence for public-key encryption | optional | 2 | Encryption.lean | as 112.2 | Def-102.2, Def-111.b |
| Claim-112.b | Claim | Perfect ZK encryption ⇔ perfect secrecy | optional | 1 | Encryption.lean | `FinDist.map` | Def-111.a |
| Def-114.a | Definition | Interactive machine as a next-message strategy | core | 2 | Interaction.lean | — (new model) | Def-23.4 |
| Def-114.b | Definition | Protocol (pair of strategies, round order, round bound) | core | 1 | Interaction.lean | — | Def-114.a |
| Def-115.a | Definition | Execution `A_{r1}(x,z1) ↔ B_{r2}(x,z2)` | core | 2 | Interaction.lean | — | Def-114.b |
| Def-115.b | Definition | Views `view_A`, `view_B`, joint view | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.c | Definition | Transcript | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.d | Definition | Outputs `out_X(e)`, `out(v)` | core | 1 | Interaction.lean | — | Def-115.b |
| Def-116.a | Definition | Random executions (samplers from the coin product) | core | 1 | Interaction.lean | `uprob`, `uprob_prod`, `acceptProb` | Def-115.a |
| Def-116.b | Definition | Time complexity of an ITM; PPT strategies | core | 3 | Interaction.lean | plan `Randomized/PPT.lean`, `pairEncode`, `FinTM.ComputesInTime` | Def-23.5, Def-114.a |
| Def-116.1 | Definition | Interactive proof system | core | 2 | InteractiveProofs.lean | `uprob`, `Negligible` | Def-116.b, Def-115.d, Def-116.a |
| Def-117.a | Definition | Soundness error `s(n)`; constant-error proofs | core | 1 | InteractiveProofs.lean | — | Def-116.1 |
| Def-117.b | Definition | The class `IP` | optional | 1 | InteractiveProofs.lean | `Language Bool` | Def-116.1 |
| Claim-117.c | Claim | `NP ⊆ IP` (send the certificate) | optional | 3 | InteractiveProofs.lean | `Complexity.NP`, `mem_P_iff` | Def-116.1, Def-191.11, Inf-4.2 |
| Claim-117.d | Claim | `IP = PSPACE` (Shamir, cited) | deferred | 5 | — | — | Def-117.b |
| Def-117.e | Definition | Graphs on `Fin n`, `σ(G)`, isomorphism via permutations | core | 2 | GraphIsomorphism.lean | `SimpleGraph.map`, `Iso.map`, `map_map`, `map_id`, `map_symm`, `Equiv.Perm` | — |
| Def-118.a | Definition | `L_iso`, `L_niso`, witness relation `R_iso` | core | 2 | GraphIsomorphism.lean | `SimpleGraph.Iso` | Def-117.e, Inf-4.1 |
| Claim-118.b | Claim | `L_iso ∈ NP` (string level) | optional | 4 | GraphIsomorphism.lean | `Complexity.NP`, `mem_NP_iff_exists_length_le` | Def-118.a, Inf-4.1 |
| Claim-118.c | Claim | `L_niso ∈ coNP` | deferred | 4 | GraphIsomorphism.lean | `Complexity.coNP` | Claim-118.b |
| Prot-118.3 | Protocol | Graph non-isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `Fintype (Perm α)` | Def-114.b, Def-117.e |
| Lem-119.a | Lemma | Uniformly permuted isomorphic graphs are identically distributed | core | 2 | GraphIsomorphism.lean | `uprob_comp_equiv`, `pushesUniform_equiv`, `Equiv.mulRight` | Def-117.e |
| Lem-119.b | Lemma | `n`-fold GNI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod`, `uprob_eq_of_equiv` | Lem-119.a, Lem-119.c |
| Lem-119.c | Lemma | Adaptive guessing lemma `Pr[∀i, b_i = g_i(b_{<i}, w)] = 2^{-n}` | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_div_card`, `uprob_prod` | — |
| Lem-119.d | Lemma | GNI completeness (unbounded prover, probability 1) | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_of_forall` | Prot-118.3, Lem-120.b |
| Prop-118.4 | Proposition | Protocol 118.3 is an interactive proof for `L_niso` | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-119.b, Lem-119.d, Def-116.1, Inf-4.2, Inf-4.4 |
| Def-119.5 | Definition | Interactive proof with efficient prover w.r.t. `R_L` | core | 2 | InteractiveProofs.lean | — | Def-116.1, Def-191.11 |
| Def-119.e | Definition | Interactive argument (nuPPT cheating provers) | optional | 2 | InteractiveProofs.lean | `DecidesWithAdviceInTime` (D4) | Def-116.1, Def-26.8 |
| Claim-119.f | Claim | Poly-time GNI prover would put `L_niso` in NP (informal) | deferred | 4 | — | — | Claim-118.c |
| Prot-120.6 | Protocol | Graph isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `SimpleGraph.map` | Def-114.b, Def-118.a |
| Lem-120.a | Lemma | Completeness algebra `π(G0) = H`, `(π∘σ⁻¹)(G1) = H` | core | 1 | GraphIsomorphism.lean | `map_map`, `map_symm` | Def-117.e |
| Lem-120.b | Lemma | A graph is isomorphic to at most one of two non-isomorphic graphs | core | 1 | GraphIsomorphism.lean | `map_map` | Def-117.e |
| Lem-120.c | Lemma | Single-iteration GI soundness `≤ 1/2` | core | 2 | GraphIsomorphism.lean | `uprob_prod`, `uprob_bool_prod` | Lem-120.b |
| Lem-120.d | Lemma | `n`-fold GI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod` | Lem-119.c, Lem-120.b |
| Prop-120.7 | Proposition | Protocol 120.6 is an interactive proof for `L_iso` with efficient prover | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-120.a, Lem-120.d, Def-119.5, Inf-4.2, Inf-4.4 |
| Def-121.1 | Definition | Honest-verifier zero-knowledge | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-119.5, Def-115.b, Def-26.8 |
| Def-121.2 | Definition | Zero-knowledge (every PPT `V*`) | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-121.1, Def-116.b |
| Def-121.a | Definition | Expected polynomial time | deferred | 4 | — | `uexp` | Def-23.5 |
| Def-122.a | Definition | Perfect and statistical zero-knowledge | core | 2 | Defs.lean | `statDist`, `distAdv_le_statDist` | Def-121.2 |
| Claim-122.b | Claim | View-based ZK ⇔ output-based ZK (exercise) | optional | 3 | Defs.lean | `distAdv_sunglassRed` | Def-121.2, Lem-71.5 |
| Claim-122.c | Claim | ZK against PPT `V*` with auxiliary input covers nuPPT `V*` | deferred | 3 | — | — | Def-121.2, Def-26.8 |
| Thm-122.3 | Theorem | Protocol 120.6 is a (statistical, single-iteration) ZK proof for `L_iso` | core | 4 | GraphIsomorphismZK.lean | `distAdv_le_statDist`, `negligible_two_pow_neg` | Prop-120.7, Thm-122.3.trunc, Claim-123.d, Claim-123.c |
| Thm-122.3.hv | Theorem | Honest-verifier perfect ZK of one GI iteration by reindexing | core | 2 | GraphIsomorphismZK.lean | `Schnorr.schnorr_hvzk` (template), `acceptProb_comp_equiv` | Prot-120.6, Lem-120.a, Def-121.1 |
| Thm-122.3.trunc | Theorem | Truncated simulator: `Pr[⊥] = 2^{-n}`, `statDist ≤ 2^{-n}` | core | 4 | GraphIsomorphismZK.lean | `uprob_prod`, `statDist`, `distAdv_le_statDist` | Alg-123.4, Lem-123.5, Claim-123.b |
| Alg-123.4 | Algorithm | Simulator for GI (truncated at `n` attempts) | core | 3 | GraphIsomorphismZK.lean | `Fintype (Perm α)` | Prot-120.6, Def-114.a |
| Lem-123.5 | Lemma | `H ~ π(G0)` independent of `b'`; `Pr[b = b'] = 1/2` | core | 2 | GraphIsomorphismZK.lean | `uprob_bool_prod`, `uprob_prod`, `uprob_comp_equiv` | Lem-119.a, Alg-123.4 |
| Claim-123.a | Claim | Untruncated simulator has expected 2 trials | deferred | 3 | — | `uexp` | Def-121.a, Lem-123.5 |
| Claim-123.b | Claim | Perfect simulation conditioned on success | core | 4 | GraphIsomorphismZK.lean | `uprob_eq_of_equiv`, BGW `linear_perfectPrivacy` (precedent) | Lem-123.5, Lem-120.a |
| Claim-123.c | Claim | Sequential repetition preserves ZK (§7.2.1) | deferred | 5 | — | — | Def-121.2 |
| Claim-123.d | Claim | Truncated GI simulator is strict PPT | core | 4 | GraphIsomorphismZK.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-123.4 |
| Thm-124.1 | Theorem | OWP ⇒ ZK proofs for NP (Levin-reducible form) | core | 4 | NP.lean | `Complexity.NP`, `PolyTimeReducible` | Thm-126.4, Prop-127.6, Claim-124.d, Def-124.a |
| Def-124.a | Definition | Levin (witness-preserving) reduction | core | 2 | NP.lean | `PolyTimeReducible`, `PolyTimeComputable` | Def-191.11 |
| Claim-124.b | Claim | 3COL is NP-complete at the string level | deferred | 5 | NP.lean | `SAT3_NPComplete`, `SATtoColorReduction` | Inf-4.1 |
| Claim-124.c | Claim | Witness transformation 3SAT → 3COL (`sat3Coloring`) | deferred | 4 | NP.lean | `SATtoColorCompleteness` (private `sat3Coloring`) | Claim-124.b |
| Claim-124.d | Claim | ZK proofs are preserved under Levin reductions | core | 3 | NP.lean | — | Def-124.a, Def-121.2, Def-119.5 |
| Claim-124.e | Claim | One-way functions suffice (cited) | deferred | 5 | — | — | Thm-124.1 |
| Def-124.f | Definition | The language 3COL and its witness relation (typed) | core | 1 | ThreeColoring.lean | `SimpleGraph.Colorable`, `Coloring`, `SATtoColor.Is3Colorable` | — |
| Claim-125.a | Claim | `(1 − 1/m)^{n·m} ≤ e^{-n}` (soundness after `n·|E|` rounds) | core | 1 | ThreeColoring.lean | `Real.one_sub_div_pow_le_exp_neg`, `Real.add_one_le_exp` | — |
| Def-126.3 | Definition | Commitment scheme (binding, hiding) | core | 2 | Commitment.lean | `distAdv`, `Negligible`, `PolyTimeComputable` | Def-26.8, Def-27.2 |
| Claim-126.a | Claim | Every commitment scheme is multi-value hiding | core | 3 | Commitment.lean | `exists_hybrid_gap`, `mixDist`, `exists_multicopyRed_ge` (generalize) | Def-126.3, Lem-71.6 |
| Thm-126.4 | Theorem | OWP (with hard-core predicate) ⇒ commitment schemes | core | 3 | Commitment.lean | `exists_owpPredictor` | Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d, Def-78.3, Thm-87.3 |
| Alg-127.a | Construction | `Com(b,r) = (f(r), b ⊕ h(r))`; bitwise `n`-bit scheme | core | 1 | Commitment.lean | `owpGen`, `owpGenNot` (`β := Unit`) | Def-27.3, Def-78.3 |
| Claim-127.b | Claim | Binding of Alg-127.a | core | 1 | Commitment.lean | `Equiv.injective` | Alg-127.a |
| Claim-127.c | Claim | Hiding of the single-bit scheme = predictor reduction | core | 2 | Commitment.lean | `predProb_owpPredictor_false/true`, `exists_owpPredictor` | Alg-127.a, Def-78.3, Lem-73.8 |
| Claim-127.d | Claim | Bitwise scheme hiding by hybrid ("show this!") | core | 3 | Commitment.lean | `exists_hybrid_gap`, `acceptProb_update`, `Negligible.mul_pow` | Claim-127.c, Lem-71.6 |
| Prot-127.5 | Protocol | ZK protocol for 3-colouring (single and `n·|E|`-fold) | core | 3 | ThreeColoring.lean | `edgeFinset`, `Fintype (Perm (Fin 3))` | Def-126.3, Def-124.f, Def-114.b |
| Claim-127.e | Claim | Completeness of Protocol 127.5 | core | 1 | ThreeColoring.lean | `Coloring.valid`, `uprob_eq_one_of_forall` | Prot-127.5 |
| Lem-127.f | Lemma | Committed colouring from binding; a bad edge exists | core | 2 | ThreeColoring.lean | — | Def-126.3, Def-124.f |
| Lem-127.g | Lemma | Adaptive sequential soundness with escape probability `1/m` | core | 3 | ThreeColoring.lean | `uprob_prod`, `uprob_and_le_mul` | Lem-119.c (model) |
| Claim-127.h | Claim | Soundness of Protocol 127.5: `≤ (1−1/|E|)^{n|E|} ≤ e^{-n}` | core | 3 | ThreeColoring.lean | — | Lem-127.f, Lem-127.g, Claim-125.a |
| Prop-127.6 | Proposition | Protocol 127.5 is a ZK proof for 3COL | core | 4 | ThreeColoring.lean | — | Claim-127.e, Claim-127.h, Prop-128.8, Inf-4.2, Inf-4.4, Claim-123.c |
| Alg-128.7 | Algorithm | Simulator for 3-colouring (truncated at `n·|E|` attempts) | core | 3 | ThreeColoring.lean | — | Prot-127.5, Def-114.a |
| Claim-128.a | Claim | The 3COL simulator is strict PPT | core | 4 | ThreeColoring.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-128.7 |
| Prop-128.8 | Proposition | ZK of the 3COL simulator (computational) | core | 5 | ThreeColoring.lean | `abs_sub_le`, `distAdv_le_statDist`, `Negligible.add` | Claim-129.a, Claim-129.c, Claim-129.d |
| Claim-129.a | Claim | `S ≡ S'` (random distinct pair = permuted witness colours) | core | 2 | ThreeColoring.lean | `uprob_comp_equiv` | Lem-129.b, Alg-128.7 |
| Lem-129.b | Lemma | `π ↦ (π a, π b)` is a bijection `S_3 ≃ {(u,v) ∣ u ≠ v}` | core | 2 | ThreeColoring.lean | `Fintype.card_perm`, `decide` | — |
| Claim-129.c | Claim | `S''` fails w.p. `(1−1/|E|)^{n|E|}` and is perfect given success | core | 4 | ThreeColoring.lean | `uprob_prod`, `statDist` | Alg-128.7, Claim-123.b (model) |
| Claim-129.d | Claim | `S' ≈ S''` by hybrids over attempts and multi-value hiding | core | 5 | ThreeColoring.lean | `exists_hybrid_gap`, `distAdv_sunglassRed`, `mixDist`, `Negligible.mul_pow` | Claim-126.a, Lem-71.5, Lem-71.6 |
| Def-191.10 | Definition | `DP` (deterministic polynomial time) | optional | 1 | `TCSlib/Complexity/ClassP/P.lean` (exists) | `Complexity.P` | — |
| Def-191.11 | Definition | NP via witness relations, `R_L(x)` | core | 1 | InteractiveProofs.lean (typed) / `ClassNP/NP.lean` (exists) | `Complexity.NP`, `mem_NP_iff_exists_length_le` | — |
| Def-192.12 | Definition | `BPP` | optional | 2 | plan `Randomized/PPT.lean` | — | Def-23.4 |
| Inf-4.1 | Infrastructure | String encodings of graphs, permutations, colourings, messages, views | core | 4 | Encoding.lean (new) | `pairEncode`, `pairFstD`, `PolyTimeComputable.pairEncode` | — |
| Inf-4.2 | Infrastructure | Machine-level PPT-ness of honest parties; sampling (DQ1) | core | 5/3 | Encoding.lean + protocol files | `PolyTimeComputable.*`, `polyTimeComputable_ite` | Inf-4.1, Def-116.b |
| Inf-4.3 | Infrastructure | Restart loops with a bounded number of attempts as strict PPT | core | 4 | plan `TCSlib/Complexity/Randomized/Repetition.lean` | `exists_loopFindTM` | Def-116.b |
| Inf-4.4 | Infrastructure | `2^{-n(x)}`, `e^{-n(x)}` negligible in `|x|` when `n(x) ≥ √(|x|/C)` | core | 2 | Defs.lean | `negligible_two_pow_neg`, `Negligible.mono` | — |

## 3. Statements, reuse notes, text issues (one entry per item)

### §4.2 Zero-knowledge encryption — `ZeroKnowledge/Encryption.lean`

**Def-111.1 (ZK encryption).** A private-key scheme `(Gen, Enc, Dec)` [Def-24.7] is
zero-knowledge if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `n` ∀ `m ∈ {0,1}^n`:
`|Pr[k ← Gen(1^n); c ← Enc_k(m) : D(c) = 1] − Pr[c ← S(1^n) : D(c) = 1]| ≤ ε(n)`.
Concrete layer at `n`: samplers `encS n m : ρ_G n × ρ_E n → C n`, `S n : ρ_S n → C n`,
bound `distAdv (encS n m) (S n) (D n) ≤ ε n`. *Reuse:* `distAdv` is exactly the
quantity; the asymptotic wrapper quantifies `S` over PPT samplers and `D` over nuPPT
distinguishers of the ensemble layer. *Note:* the message `m` is fixed per `n` (no
adversarial message ensemble beyond "∀ m"); `S` gets `1^n` only.

**Def-111.a (perfect ZK encryption).** As Def-111.1 with the two distributions identical:
`FinDist.map (encS n m) uniform = FinDist.map (S n) uniform` for all `n, m` (equivalently
`distAdv … D = 0` for every `D`, even unbounded).

**Def-111.b (ZK PKE).** `(Gen, Enc, Dec)` [Def-102.1] is ZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negl
`ε` ∀ `n`, `m ∈ {0,1}^n`: `D` distinguishes `{(pk,sk) ← Gen(1^n) : (pk, Enc_pk(m))}` and
`{(pk,sk) ← Gen(1^n) : (pk, S(pk, 1^n))}` with advantage `≤ ε(n)`. Note the simulator is
given `pk` and the distinguisher sees `pk`.

**Thm-112.2.** Hypotheses: `Gen`, `Enc` PPT; a deterministic polynomial-time `M` with
`M(1^n) ∈ {0,1}^n` for every `n`. Conclusion: Def-91.1 ⇔ Def-111.1. Split:

* **Thm-112.2.i (secure ⇒ ZK).** Take `S(1^n) := Enc_k(M(1^n))` with `k ← Gen(1^n)`,
  coins `(g, e)`. For every `D`, `n`, `m`: the sampler of `S(1^n)` *is* the sampler of
  `Enc_k(M(1^n))`, so `distAdv (encS n m) (S n) D = distAdv (encS n m) (encS n (M n)) D ≤ ε_D(n)`
  by Def-91.1 with `m0 := m`, `m1 := M(1^n)`. Concrete content: definitional equality of
  samplers. Asymptotic bridge: `S` is PPT by closure (composition of `M`, `Gen`, `Enc`;
  plan `Randomized/Closure.lean`). *Text issue:* the proof by contradiction via "infinitely
  many `n`" is unnecessary; also `M(1^n)` must be deterministic for the sampler identity
  (a randomized `M` would still work via averaging over its coins).
* **Thm-112.2.ii (ZK ⇒ secure).** For all `D`, `n`, `m1`, `m2`:
  `distAdv (encS n m1) (encS n m2) D ≤ distAdv (encS n m1) (S n) D + distAdv (S n) (encS n m2) D ≤ 2 ε(n)`
  (triangle inequality `abs_sub_le`, then `Negligible.const_mul`). The text's "hybrid
  lemma with `1/(2p(n))`" is this two-step chain.

**Claim-112.a.** The same equivalence for PKE (Def-102.2 ⇔ Def-111.b) with
`S(pk, 1^n) := Enc_pk(M(1^n))`; identical proof (the point: encryption under `pk` is
publicly samplable). Optional.

**Claim-112.b.** Perfect ZK encryption ⇔ perfect secrecy (`Enc_k(m) ≡ Enc_k(m')` for all
`m, m'` at every `n`): `S := Enc_k(m_0)` for the fixed message `m_0 = M(1^n)`, both
directions are rewriting of distribution equalities. Perfect secrecy is a Chapter 1 notion;
state the concrete form only. Optional.

### §4.4 Interactive protocols — `ZeroKnowledge/Interaction.lean`

**Def-114.a (ITM as a strategy).** Concrete form, parametrized by a common-input type `X`,
auxiliary-input type `Z`, a finite coin type `ρ`, and a message type `Msg`:
`next : X → Z → ρ → List Msg → Msg` (the message sent after having *received* the listed
messages) and `out : X → Z → ρ → List Msg → Out`. String form: `X = Z = Msg = Out = List Bool`,
`ρ = Fin ℓ → Bool`. Deviation (D8): no tapes/states; "entering the idle state" is returning
from `next`; halting is handled by the protocol's round bound. The honest prover's witness
is its auxiliary input `z`.

**Def-114.b (protocol).** `Protocol A B := (A : Strategy …, B : Strategy …, first : Bool,
rounds : ℕ)`; in round `i` the active party is `A` iff `i` has the parity of `first`. All
protocols of the chapter have fixed round counts (GNI: 2 rounds per iteration, `V` first;
GI and 3COL: 3 rounds per iteration, `P` first).

**Def-115.a (execution).** For `x, z1, z2, r1, r2`, the pair
`((x, z1, r1, M_A), (x, z2, r2, M_B))` where `M_A` (resp. `M_B`) is the list of messages
received by `A` (resp. `B`), defined by structural recursion on the round index:
the sender's message in round `i` is its `next` applied to its received messages so far.
Notation `A_{r1}(x,z1) ↔ B_{r2}(x,z2)`. Lean: `exec P x z1 z2 r1 r2 : View × View`,
with `View := X × Z × ρ × List Msg` (typed per party).

**Def-115.b (views).** `viewA := (exec …).1`, `viewB := (exec …).2`; the execution itself is
the joint view.

**Def-115.c (transcript).** `(M_A, M_B)` of an execution (projection).

**Def-115.d (outputs).** `out_X(e) := X.out (view_X e)`; `out(v) := X.out v` for a view `v`
of `X`. For verifiers `Out = Bool` (accept).

**Def-116.a (random executions).** The distribution `A(x,z1) ↔ B(x,z2)` is the sampler
`(r1, r2) ↦ exec … r1 r2` on the uniform product `ρ_A × ρ_B`; `view`, `out` distributions
are its post-compositions. Plugs directly into `uprob`, `acceptProb`, `distAdv`
(`uprob_prod` for conditioning on one party's coins). No new content.

**Def-116.b (time complexity, PPT strategy).** `A` has time complexity `t` if for every
`B`, `x`, `z_a`, `z_b` and all coins, `A(x, z_a)` halts within `t(|x|)` steps in the
interaction. Formal: a strategy is PPT if there are `C, c, R` and a `FinTM Bool` computing
`next` (and `out`) on `pairEncode x (pairEncode z (pairEncode (enc r) (encodeList received)))`
within `C·(|x|+1)^c` steps *for every* `z`, `r`, `received` (bound in `|x|` only, as in the
text; the machine cannot read more than `C(|x|+1)^c` bits of `z`), coins of length
`C_r·(|x|+1)^{c_r}` (or a typed coin space per DQ1), and at most `R(|x|)` rounds. Deviation:
per-message bound instead of a total bound (total `≤ R·t`). Depends on the frozen
`Randomized/PPT.lean` signatures.

### §4.5 Interactive proofs — `ZeroKnowledge/InteractiveProofs.lean`, `GraphIsomorphism.lean`

**Def-116.1 (interactive proof).** `(P, V)` is an interactive proof system for `L` if `V` is
PPT (Def-116.b) and (1) completeness: ∀ `x ∈ L` ∃ `y` ∀ `z`:
`Pr_{r_P, r_V}[out_V[P_{r_P}(x,y) ↔ V_{r_V}(x,z)] = 1] = 1`; (2) soundness: ∃ negligible `ε`
∀ `x ∉ L` ∀ strategies `P*` (arbitrary function, arbitrary finite coin type, *no* auxiliary
input) ∀ `z`: `Pr[out_V[P*(x) ↔ V(x,z)] = 0] > 1 − ε(|x|)`. Formalized with
`Pr[out_V = 1] ≤ ε(|x|)` (equivalent up to the strictness of the inequality, immaterial for
negligible `ε`; `out_V : Bool`). The quantification over `P*` with an arbitrary coin type is
universe-polymorphic; use coin strings `Fin ℓ → Bool` for arbitrary `ℓ` (WLOG deterministic
`P*` by averaging — record as a lemma). *Text issue:* "`> 1 − e`" strict.

**Def-117.a (soundness error).** Same with `1 − ε(|x|)` replaced by `1 − s(|x|)` for a given
`s : ℕ → ℝ` (e.g. constant `1/2`). Used for the single-iteration protocols.

**Def-117.b (IP).** `IP := {L : Language Bool | ∃ (P V), IsInteractiveProof P V L}`.

**Claim-117.c (NP ⊆ IP).** For `L ∈ Complexity.NP` (certificate length `C(|x|+1)^c`,
verifier `V ∈ P` on `x ++ u`): the one-round protocol "P sends `u`; `V` accepts iff
`|u| = C(|x|+1)^c ∧ x ++ u ∈ V`" is an interactive proof with soundness error `0`.
Completeness: the witness `u`; soundness: for `x ∉ L` no `u` is accepted. Machine content:
package the `P`-decider (`mem_P_iff`) as a PPT strategy (time poly in `|x|` since `|u|` is
poly in `|x|`). Optional (the text states it as trivial).

**Claim-117.d (IP = PSPACE).** Cited (Shamir). Deferred; nothing downstream.

**Def-117.e (graphs, `σ(G)`, isomorphism).** Graphs on `n` vertices are
`SimpleGraph (Fin n)`; for `σ : Equiv.Perm (Fin n)`, `σ(G) := G.map σ.toEmbedding`
(edges `{σ u, σ v}`); `G1 ≅ G2 :⇔ ∃ σ, σ(G1) = G2`. Lemmas: `σ(τ(G)) = (σ * τ)(G)`
(`SimpleGraph.map_map`, note `Equiv.Perm` multiplication order), `1(G) = G`
(`map_id`), `σ(G) = H ↔ G = σ⁻¹(H)` (`map_symm`/`comap_symm`), injectivity of
`G ↦ σ(G)`, `≅` is an equivalence relation, and the bridge
`Nonempty (G1 ≃g G2) ↔ G1 ≅ G2` (`SimpleGraph.Iso.map σ G1 : G1 ≃g σ(G1)` one way;
`RelIso.toEquiv` and `map_adj` the other). Finiteness: `Fintype (SimpleGraph (Fin n))`
(Mathlib `Basic.lean:110`) and `Fintype (Perm (Fin n))`. Decidability of `G = H` and of
`G.Adj`: use classical decidability at the concrete layer; the machine layer works on the
adjacency-matrix encoding (Inf-4.1).

**Def-118.a (`L_iso`, `L_niso`, `R_iso`).** Typed: `L_iso n := {(G0, G1) | G0 ≅ G1}`,
`R_iso (G0,G1) σ :⇔ σ(G0) = G1`, `L_niso n := {(G0, G1) | ¬ G0 ≅ G1}` (same vertex count by
typing). String forms via Inf-4.1 (pairs of adjacency matrices; malformed strings decode to
a default pair and are *not* in `L_niso`). The text's "same number of vertices" condition is
the typing.

**Claim-118.b (`L_iso ∈ NP`).** String level: certificate = encoding of `σ` (length
`≤ C(|x|+1)^c`), verifier computes `σ(G0)` and compares with `G1` in polynomial time.
Optional; the typed `R_iso` is what Defs 119.5/121.x consume.

**Claim-118.c (`L_niso ∈ coNP`).** The complement (malformed, or isomorphic) is in NP by
Claim-118.b. Deferred.

**Prot-118.3 (GNI).** Common input `x = (G0, G1)`, `n` vertices each. One iteration:
`V` draws `b : Bool` and `σ ∈ S_n` uniformly, sends `H := σ(G_b)`; `P` replies `b'`; `V`
accepts iff `b' = b`. Honest (unbounded) prover: `b' := decide (H ≅ G0) ? 0 : 1`
(classical). `n`-fold: `n` sequential iterations with fresh `(b_i, σ_i)`; `V` accepts iff all
accept; modelled as a `2n`-round protocol with verifier coins `Fin n → Bool × Perm (Fin n)`.
The prover's reply is decoded as a bit (any message other than `[true]` counts as `0`).
*Text issue:* "Repeat the procedure `|G1|` times" means `n` times.

**Lem-119.a.** If `σ₀(G0) = G1` then for uniform `σ ∈ S_n` the samplers `σ ↦ σ(G0)` and
`σ ↦ σ(G1)` have the same distribution: `σ(G1) = (σ * σ₀)(G0)` and `σ ↦ σ * σ₀` is a
bijection (`Equiv.mulRight`, `uprob_comp_equiv`). Hence for uniform `(b, σ)`, the pair
`(b, σ(G_b))` has the distribution of `(b, σ(G0))` with `b` independent of the graph.

**Lem-119.c (adaptive guessing).** For every finite `W` and every family
`g : (i : Fin n) → (Fin i → Bool) → W → Bool`:
`uprob (fun (b, w) : (Fin n → Bool) × W => ∀ i, b i = g i (fun j => b (Fin.castLT j _)) w) = 2^{-n}`.
Proof: for each `w` exactly one `b` satisfies the constraint (recursion on `n`, `Fin.snoc`),
then `uprob_eq_one_div_card`/`uprob_prod`. This is the engine of all `2^{-n}` soundness
bounds against adaptive provers.

**Lem-119.b (GNI soundness).** If `G0 ≅ G1` (via `σ₀`) then for every `P*` (coins `r`) and
`z`: `Pr_{b, σ, r}[∀ i < n, b'_i = b_i] ≤ 2^{-n}` where `b'_i` is `P*`'s reply after seeing
`H_1, …, H_i`. Proof: change variables `σ'_i := if b_i then σ_i * σ₀ else σ_i` (bijection of
`(b, σ)`), so every `H_i = σ'_i(G0)` is a function of `σ'` alone; then `b'_i = g_i(σ', r)`
and Lem-119.c (with `W := (Fin n → Perm) × ρ_{P*}`) gives exactly `2^{-n}`.

**Lem-119.d (GNI completeness).** If `¬ G0 ≅ G1` then for all `b, σ`: `σ(G_b) ≅ G_b` and
`¬ σ(G_b) ≅ G_{1−b}` (Lem-120.b), so the honest prover's `b' = b`; the `n`-fold verifier
accepts with probability `1` (`uprob_eq_one_of_forall`).

**Prop-118.4.** Protocol 118.3 (`n`-fold) is an interactive proof for `L_niso`: completeness
Lem-119.d (witness `y` irrelevant), soundness `2^{-n(x)} ≤ ε(|x|)` negligible (Inf-4.4),
`V` PPT (Inf-4.2; `σ(G)` and the comparison `b' = b`). *Text issues:* the proof writes
`G1, G2` for `G0, G1`; "the Prover runs in exponential time" is modelled by an arbitrary
function; "each iteration is independent of all prior iterations" hides the adaptive-prover
argument (Lem-119.b).

**Def-119.5 (efficient prover).** `(P, V)` is an interactive proof for `L` with efficient
prover w.r.t. `R_L` if `P` is PPT (time poly in `|x|`, witness `y` as auxiliary input) and
completeness holds for **every** `y ∈ R_L(x)` (Def-116.1 asks for *some* `y`).

**Def-119.e (interactive argument).** Soundness quantified over nuPPT `P*` only (D4
machines with advice; `P*` may receive `z`). Optional.

**Claim-119.f.** "A polynomial-time prover would imply `L_niso ∈ NP`": informal, not a
precise theorem (a deterministic PPT prover together with the public-coin verifier gives an
NP witness only after de-randomization). Deferred, not formalized.

**Prot-120.6 (GI).** Common input `(G0, G1)`, prover witness `σ` with `σ(G0) = G1`. One
iteration: `P` draws `π ∈ S_n` uniformly, sends `H := π(G0)`; `V` sends uniform `b`; `P`
sends `γ := if b then π * σ⁻¹ else π` (as functions: `γ = π ∘ σ⁻¹` so that
`γ(G1) = π(σ⁻¹(G1)) = π(G0) = H`); `V` accepts iff `γ(G_b) = H`. `n`-fold: sequential with
fresh `π_i`, `b_i`. `V`'s message is decoded as a bit by `P`. *Text issue:* the composition
order of `π · σ^{-1}` must be fixed (right-to-left as functions).

**Lem-120.a.** `σ(G0) = G1 → π(G0) = H → (π * σ⁻¹)(G1) = H` (`map_map`, `map_symm`);
hence the honest prover is accepted with probability `1` in every iteration, for every
witness `σ` (Def-119.5's "every `y`").

**Lem-120.b.** `¬ G0 ≅ G1 → ¬ (H ≅ G0 ∧ H ≅ G1)` (symmetry and transitivity of `≅`).

**Lem-120.c (single-iteration soundness).** If `¬ G0 ≅ G1` then for every `P*` (coins `r`)
and `z`: `Pr_{b, r}[γ(G_b) = H] ≤ 1/2` where `H = H(r)` and `γ = γ(r, b)`: for fixed `r`,
by Lem-120.b at most one `b` admits a `γ` with `γ(G_b) = H`; `b` is uniform and independent
of `H` (`uprob_prod`, `uprob_bool_prod`).

**Lem-120.d (`n`-fold soundness).** `Pr[all n iterations accept] ≤ 2^{-n}` for every
`P*`: with `g_i(b_{<i}, r) :=` the unique good bit for `H_i` (or `false`), acceptance in
all rounds implies `∀ i, b_i = g_i(b_{<i}, r)`; apply `uprob_mono` and Lem-119.c. This also
formalizes the remark "the protocol can be repeated … to drive the error as low as desired".

**Prop-120.7.** Protocol 120.6 (`n`-fold) is an interactive proof for `L_iso` with efficient
prover w.r.t. `R_iso`: completeness Lem-120.a for every witness, soundness `2^{-n} ≤ ε(|x|)`
(Inf-4.4), `P` and `V` PPT (permutation composition/inversion, `σ(G)`, graph equality:
Inf-4.2). *Text errors:* stated "for `L_niso`" (it is `L_iso`); the proof's
"`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" has the maps reversed and uses `G1, G2` for
`G0, G1`; the proof only argues `1/2` per iteration.

### §4.6 Zero-knowledge — `ZeroKnowledge/Defs.lean`, `GraphIsomorphismZK.lean`

**Def-121.1 (HVZK).** `(P, V)` an interactive proof with efficient prover for `L` with
witness relation `R_L`. HVZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV x y z) (S x z) D ≤ ε(|x|)` where
`viewV x y z : ρ_P × ρ_V → View_V` is the honest verifier's view sampler and
`S x z : ρ_S → View_V` (`S` outputs a *view*, i.e. `(x, z, r_V, messages received)`).
*Text issue:* `e(n)` with `n` undefined — read `n = |x|`.

**Def-121.2 (ZK).** ∀ PPT `V*` ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV* x y z) (S x z) D ≤ ε(|x|)`. Deviation (D8): `S` strict
PPT instead of expected PPT (stronger demand on `S`). `V*` is PPT with auxiliary input `z`
(the text's remark on non-uniformity, Claim-122.c).

**Def-121.a (expected PPT).** Expected running time over the machine's own coins polynomial.
Deferred (D8); would need a sampler with unbounded coin usage.

**Def-122.a (perfect / statistical ZK).** Perfect: the two distributions identical for all
`x, y, z` (then `distAdv = 0` for every `D`). Statistical (campaign addition, needed for
Thm-122.3): `statDist (view distribution) (S distribution) ≤ δ(|x|)` with `δ` negligible —
implies Def-121.2 for every `D` by `distAdv_le_statDist`, and `δ := 2^{-n}` is the GI case.
*Note:* the GMR definition lets a perfect simulator output `⊥` with probability `≤ 1/2`;
the text does not.

**Claim-122.b (view vs output).** Replacing `view_{V*}` by `out_{V*}` gives an equivalent
definition: (⇒) `out` is a PPT function of the view, so `S' := out_{V*} ∘ S` works by
closure (`distAdv_sunglassRed`, Lem-71.5); (⇐) apply the output-based definition to the
PPT `V*'` that outputs its own view. Optional.

**Claim-122.c.** ZK against PPT `V*` with auxiliary input already covers nuPPT `V*` (advice
as part of `z`, simulator receives the same advice). Deferred (needs a nuPPT verifier
notion; remark only).

**Thm-122.3.** Protocol 120.6 is a zero-knowledge interactive proof for `L_iso` with the
canonical witness relation `R_iso`. Formalized as: (a) Prop-120.7; (b) **single iteration**:
for every `V*` (any strategy with finite coins at the concrete layer; PPT at the asymptotic
layer) the truncated simulator `S_n` (Alg-123.4) satisfies
`statDist (viewV* x σ z) (S_n x z) ≤ 2^{-n}` for all `(G0,G1) ∈ L_iso`, `σ ∈ R_iso`, `z`
(Thm-122.3.trunc), hence statistical ZK with `ε = 2^{-n(x)}` (Inf-4.4) and `S_n` PPT
(Claim-123.d); (c) the `n`-fold protocol: ZK under the sequential-composition hypothesis
Claim-123.c (deferred). *Text issue:* "perfect" becomes statistical because of truncation
(D8); the text proves one iteration only.

**Thm-122.3.hv (HVZK, perfect, by reindexing).** Simulator: draw `b : Bool`, `γ ∈ S_n`
uniformly, output `(x, z, b, [γ(G_b), γ])`. For `σ(G0) = G1`, the honest view sampler
`(π, b) ↦ (x, z, b, [π(G0), if b then π * σ⁻¹ else π])` equals the simulator sampler
composed with the bijection `(π, b) ↦ (if b then π * σ⁻¹ else π, b)` (Lem-120.a), so the
two distributions are identical (`acceptProb_comp_equiv`). Same shape as
`Schnorr.schnorr_hvzk` (`reindex`), which is the template.

**Alg-123.4 (GI simulator, truncated).** `S_n(x, z)` with coins
`(b', π, r) : Fin n → Bool × Perm (Fin n) × ρ_{V*}`: for attempt `k = 0, …, n−1`: `H_k := π_k(G_{b'_k})`;
`b_k :=` bit decoded from `V*.next x z r_k [H_k]`; if `b_k = b'_k` output
`some (x, z, r_k, [H_k, π_k])` (the view of `V*`), else continue; after `n` failures output
`none` (`⊥`). Deviation: truncation (strict PPT) instead of restart until success.

**Lem-123.5.** For `(G0,G1) ∈ L_iso`, in one attempt: (i) the sampler
`(b', π) ↦ (b', π(G_{b'}))` has the distribution of `(b', π) ↦ (b', π(G0))`, so `H` is
independent of `b'` and distributed as `π(G0)` (Lem-119.a); (ii) for every function
`V*` and every `z`: `Pr_{b', π, r}[V*(x, z, r, [H]) = b'] = 1/2` (`b` depends on
`(H, r, z)` only; condition on `(H, r)` and use `uprob_bool_prod`).

**Claim-123.a.** Expected number of attempts of the untruncated simulator is `2`. Deferred
(Def-121.a).

**Claim-123.b (perfect simulation given success).** For every view `v`:
`Pr_{b', π, r}[attempt outputs v ∧ b = b'] = (1/2) · Pr_{π, r}[viewV*(x, σ, z)(π, r) = v]`.
Proof: for fixed `r` the real execution is `π ↦ (H = π(G0), b = V*(H, r), γ = if b then π * σ⁻¹ else π)`;
the successful attempts are `(b', π')` with `H = π'(G_{b'})`, `b = V*(H, r) = b'`, output
`π'`; the map `(b', π') ↦ π := if b' then π' * σ else π'` (so that `π(G0) = H` and
`γ = π'`) is a bijection from `{(b', π') | success}` onto `Perm` with `b' = b(π)`; hence the
two counts agree up to the factor `1/2` from the `b'` coordinate (`uprob_eq_of_equiv`,
`uprob_prod`). Model: `TCSlib.MPC.BGW.linear_perfectPrivacy` (perfect privacy by a coin
bijection).

**Thm-122.3.trunc.** `Pr[S_n = ⊥] = 2^{-n}` (attempts use disjoint coins; each fails with
probability exactly `1/2` by Lem-123.5(ii); `uprob_prod`/`OneWay.uprob_pi_forall`) and for
every `v`: `Pr[S_n = some v] = (1 − 2^{-n}) · Pr[view = v]` (sum over the first successful
attempt of `2^{-k} · (1/2) · Pr[view = v]`, Claim-123.b); therefore
`statDist (S_n) (some ∘ view) = 2^{-n}` and `distAdv (S_n x z) (some ∘ viewV* x σ z) D ≤ 2^{-n}`
for every `D` (`distAdv_le_statDist`).

**Claim-123.c.** Sequential repetition of a ZK protocol is ZK (§7.2.1). Deferred (outside
Chapters 2–4; needs the auxiliary-input hybrid over iterations). Stated as a hypothesis
where the `n`-fold theorems need it.

**Claim-123.d.** `S_n` is strict PPT when `V*` is: `n` attempts of (sample, `π(G)`, one call
of `V*` with fresh coins, compare) — plan `Randomized/Repetition.lean` on top of
`Turing.FinTM.exists_loopFindTM` (first accepting round's payload). Machine-level; the
load-bearing infrastructure item of the chapter together with Claim-128.a.

### §4.7 Zero-knowledge for NP — `ZeroKnowledge/NP.lean`

**Thm-124.1.** If one-way permutations exist then every language in NP has a ZK proof.
Formalized in three forms: **(A, core)** for every `(L, R_L)` and every Levin reduction
`(f, w)` from `(L, R_L)` to `(3COL, R_3COL)` (Def-124.a, string level through Inf-4.1), the
composed protocol — both parties compute `x' := f(x)`, the prover additionally `y' := w(x, y)`,
then run Protocol 127.5 — is a ZK proof with efficient prover for `L` (Claim-124.d applied to
Prop-127.6, with the commitment scheme from Thm-126.4). **(B, optional/deferred)** "every
`L ∈ Complexity.NP`" follows from (A) given string-level Levin NP-hardness of 3COL
(Claim-124.b + Claim-124.c), stated as an explicit hypothesis. **(C, optional)** with an
*unbounded* honest prover a Karp reduction suffices (the prover finds a colouring of `f(x)`
classically) — but Def-121.2 requires an efficient prover, so (C) is only a remark.
*Text issues:* "Cook's reduction can be applied to the witness `y`" requires a Levin
reduction, never defined in the text; "execute protocol `(P, V)` on `x'`" should be
`(P', V')`; the theorem silently needs a hard-core predicate for the OWP (Thm-87.3).

**Def-124.a (Levin reduction).** `(f, w)` with `PolyTimeComputable f`, `w` polynomial-time
in `(x, y)` (two-argument via `pairEncode`), `∀ x, x ∈ L ↔ f x ∈ L'`, and
`∀ x y, R_L x y → R_{L'} (f x) (w x y)`. Extends `Complexity.PolyTimeReducible` (Karp).

**Claim-124.b (3COL NP-complete, string level).** `3COL := {x | (decodeGraph x).Colorable 3}`;
NP membership (colouring certificate) and NP-hardness via `SAT3 ≤ₚ 3COL`. The repository
has `Complexity.SAT3_NPComplete` and the graph-level `SATtoColor.SATtoColorReduction`
(on `SATtoColor.Sat3 V`, a different 3SAT syntax from `CNF.decode`); the poly-time string
reduction machine is missing — large machine-building task. Deferred.

**Claim-124.c (witness transformation 3SAT → 3COL).** The colouring built from a satisfying
assignment is `SATtoColor.sat3Coloring` (declared `private`; its validity is the content of
`SATtoColorCompleteness`). A Levin reduction needs it as a poly-time string function.
Deferred with Claim-124.b.

**Claim-124.d (ZK transfers along Levin reductions).** If `(P', V')` is a ZK proof with
efficient prover for `(L', R_{L'})` and `(f, w)` is a Levin reduction from `(L, R_L)`, then
`P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)` is a ZK proof with efficient prover for
`(L, R_L)`: completeness from `R_L x y → R_{L'} (f x) (w x y)`; soundness: `x ∉ L → f x ∉ L'`
and a cheating `P*` for `x` is a cheating prover for `f x`; ZK: for `V*`, let
`V*'(x', (x, z)) := V*(x, z)` (recovers `x` from its auxiliary input, ignores `x'`), then
`viewV*[P(x,y) ↔ V*(x,z)] = viewV*'[P'(f x, w x y) ↔ V*'(f x, (x,z))]` up to relabelling,
and `S(x, z) := S'(f x, (x, z))`; PPT-ness of `P`, `V`, `V*'`, `S` by composition with `f`,
`w`. Negligibility: `ε'(|f x|)` with `|f x| ≤ poly(|x|)` and `|f x| ≥ …` — needs
`f` length-nondecreasing or a `Negligible.mono`-type lemma for polynomially related
parameters (record).

**Claim-124.e.** General one-way functions suffice (Naor commitments). Deferred.

**Def-124.f (3COL, `R_3COL`).** Typed: `3COL n := {G : SimpleGraph (Fin n) | G.Colorable 3}`
(`= Nonempty (G.Coloring (Fin 3))`, literally `SATtoColor.Is3Colorable G`); witness
relation `R_3COL G c :⇔ ∀ u v, G.Adj u v → c u ≠ c v` for `c : Fin n → Fin 3`
(`SimpleGraph.Coloring.mk`). Colours `{1,2,3}` are `Fin 3`.

**Claim-125.a.** For `m ≥ 1`: `(1 − 1/m)^{n·m} ≤ exp(−n) ≤ 2^{-n}`. From
`Real.one_sub_div_pow_le_exp_neg` (`(1 − t/N)^N ≤ exp(−t)` with `N = n·m`, `t = n`) or
`Real.add_one_le_exp`. Pure real analysis; the text writes `≈ e^{-n}`.

### §4.7.1 Commitments — `ZeroKnowledge/Commitment.lean`

**Def-126.3 (commitment scheme).** A deterministic polynomial-time `Com` and polynomial `ℓ`
with (1) binding: ∀ `n`, ∀ `v0 ≠ v1 ∈ {0,1}^n`, ∀ `r0, r1 ∈ {0,1}^{ℓ(n)}`:
`Com(v0, r0) ≠ Com(v1, r1)`; (2) hiding: ∀ nuPPT `D` ∃ negligible `ε` ∀ `n`,
`v0, v1 ∈ {0,1}^n`: `distAdv (fun r => Com n v0 r) (fun r => Com n v1 r) D ≤ ε(n)`.
Concrete: `Com n : (Fin n → Bool) → (Fin (ℓ n) → Bool) → C n`. Deviation (DQ4): `n` is an
explicit argument (the text infers it from `|v|`). *Text error:* binding as printed omits
`v0 ≠ v1` and is unsatisfiable (`v0 = v1`, `r0 = r1`).

**Claim-126.a (multi-value hiding).** For every commitment scheme, polynomial `q`, nuPPT `D`
∃ negligible `ε` ∀ `n`, `(v_i), (v'_i) ∈ ({0,1}^n)^{q(n)}`:
`distAdv ((r_i) ↦ (Com n v_i r_i)_i) ((r_i) ↦ (Com n v'_i r_i)_i) D ≤ ε(n)`. Proof: hybrids
`H_k` (coordinates `< k` from `v'`, `≥ k` from `v`), `exists_hybrid_gap`; the reduction for
index `k` gets a commitment to `v_k` or `v'_k`, samples the other coordinates' commitments
itself (`Com` is poly-time; `acceptProb_update` plants the challenge), so advantage
`≥ ε_D/q(n)`; non-uniform choice of `k` or the averaged `mixDist` reduction. Generalizes
`exists_multicopyRed_ge` (identical pair in all coordinates) — a per-coordinate version is
needed (new concrete lemma; propose it for `Indistinguishability`-style reuse but keep a
private copy here per the ownership rule). Needed by Claim-129.d.

**Thm-126.4.** If `f` is a one-way permutation (length-preserving bijection at every `n`,
Def-27.3) with hard-core predicate `h` (Def-78.3), then Alg-127.a is a commitment scheme:
`Com` poly-time (from `f`, `h` poly-time), binding (Claim-127.b), hiding (Claim-127.c for one
bit, Claim-127.d for `n` bits). Unconditional-from-OWP form: apply Goldreich–Levin
(Thm-87.3) to get `(g, ⟨·,·⟩)` with `g(x, r) = (f x, r)` a OWP — optional, depends on the
Chapter 3 asymptotic GL theorem. *Text issue:* OWP here is a single function (Thm 79.4's
usage), not the collection of Def 55.1; the existence of `h` is not mentioned.

**Alg-127.a (construction).** `Com₁ n b r := (f n r, b ⊕ h n r)` for `r ∈ {0,1}^n`
(`ℓ(n) = n`); `Com n v (r_1, …, r_n) := (Com₁ n (v i) (r i))_i` (`ℓ(n) = n²`). With the
Garg layer: `owpGen f B : α × Unit → α × Unit × Bool` is `Com₁(0, ·)` and `owpGenNot f B`
is `Com₁(1, ·)` up to the `Unit` coordinate.

**Claim-127.b (binding).** `f n` injective ⇒ `Com₁ n b0 r0 = Com₁ n b1 r1 → r0 = r1 → b0 = b1`;
for the `n`-bit scheme, `v0 ≠ v1` differ at some `i`, and coordinate `i` separates.

**Claim-127.c (single-bit hiding, concrete).** For every `D : C → ρ → Bool`:
`predProb (owpPair f) B (owpPredictor D flip) = 1/2 ± distAdv (Com₁ 0) (Com₁ 1) D / 2`
for the appropriate `flip`, i.e. a distinguisher with advantage `ε` yields a predictor of
`h(r)` from `f(r)` with success exactly `1/2 + ε/2` — this **is**
`predProb_owpPredictor_false`/`_true` with `β := Unit` (`acceptProb` is invariant under the
`Unit` coordinate, `acceptProb_fst`). Asymptotic: if `h` is hard-core then
`distAdv ≤ 2 ε_h(n)` with the predictor nuPPT (one extra coin, one call of `D`). "Identical
to the proof of Theorem 104.4" (prediction lemma Lem-73.8 + XOR trick).

**Claim-127.d (bitwise hybrid, "show this!").** Hiding of `Com₁` ⇒ hiding of `Com`:
hybrids over the `n` bits (`exists_hybrid_gap`), the reduction plants the challenge
commitment at bit `k` and samples the others (`acceptProb_update`); advantage `≥ ε/n`;
`Negligible.mul_pow`. Special case of Claim-126.a with `q = n`, values single bits.

### §4.7.2 Graph 3-colouring — `ZeroKnowledge/ThreeColoring.lean`

**Prot-127.5.** Common input `G : SimpleGraph (Fin n)` with `m := |E|` (`E := G.edgeFinset`);
prover witness `c : Fin n → Fin 3` with `R_3COL G c`. One iteration: `P` draws
`π ∈ Perm (Fin 3)` and `r_i ∈ {0,1}^{ℓ(n)}` (`i < n`) uniformly and sends
`com_i := Com n (pad (π (c i))) (r_i)`; `V` sends a uniform edge `e = {i, j} ∈ E`; `P` sends
the openings `(π (c i), r_i, π (c j), r_j)`; `V` accepts iff `e ∈ E`,
`Com n (pad c'_i) r_i = com_i`, `Com n (pad c'_j) r_j = com_j` and `c'_i ≠ c'_j`.
`n·m`-fold: sequential with fresh `π`, `r`. Deviations: the opening check (the text's
"`V` accepts iff `c'_i ≠ c'_j`" is unsound without it); colours padded to `n` bits
(DQ4, requires `n ≥ 2`); if `E = ∅` the verifier accepts outright (every edgeless graph is
3-colourable; the text's "random edge" is undefined). *Text errors:* witness listed as
`c0, …, cm` (should be `c1, …, cn`).

**Claim-127.e (completeness).** For `R_3COL G c`, any `π`, `r`: `π (c i) ≠ π (c j)` on every
edge (`Coloring.valid`, `π` injective) and the openings verify; `V` accepts with
probability `1` in every iteration (`uprob_eq_one_of_forall`).

**Lem-127.f (committed colouring).** From binding: for each commitment string `com`, there
is at most one `v ∈ {0,1}^n` with `∃ r, Com n v r = com`; let `c̃ k : Option (Fin 3)` be the
colour it decodes to (if any). An opening accepted by `V` on edge `{i, j}` forces
`c'_i = c̃ i`, `c'_j = c̃ j`. If `¬ G.Colorable 3` then for every `c̃` there is an edge
`{i, j} ∈ E` with `c̃ i = c̃ j` or one endpoint undefined (else `c̃` would be a proper
colouring, after sending `none` to any colour), on which no opening is accepted.

**Lem-127.g (adaptive sequential soundness, escape `1/m`).** For `k` rounds with uniform
challenges `e_i ∈ Fin m` (or `E`) and any `Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m)`
with `∀ i h w, (Bad i h w).Nonempty`:
`uprob (fun (e, w) => ∀ i, e i ∉ Bad i (e|_{<i}) w) ≤ (1 − 1/m)^k`. Proof by induction with
`uprob_prod`. Lem-119.c is the equality case `m = 2`, `|Bad| = 1`.

**Claim-127.h (soundness of 127.5).** If `¬ G.Colorable 3` (and `m ≥ 1`) then for every
`P*` (coins `r`) and `z`: `Pr[V accepts all n·m iterations] ≤ (1 − 1/m)^{n·m} ≤ e^{-n}`:
in iteration `i`, given the history, the committed colouring `c̃_i` has a bad edge
(Lem-127.f), the verifier's uniform edge hits it with probability `≥ 1/m` and then the
iteration rejects; Lem-127.g, Claim-125.a. *Text error:* "repeated `|E|²` times".

**Prop-127.6.** Protocol 127.5 is a ZK proof for 3COL: (a) interactive proof with efficient
prover w.r.t. `R_3COL`: Claim-127.e, Claim-127.h with `e^{-n(x)}` negligible in `|x|`
(Inf-4.4), `P`, `V` PPT (`Com` poly-time, edge sampling per DQ1, Inf-4.2); (b) ZK of the
single iteration: Prop-128.8 + Claim-128.a; (c) the `n·m`-fold protocol's ZK under
Claim-123.c (deferred).

**Alg-128.7 (3COL simulator, truncated).** `S(x, z)` with coins per attempt
`(e' = {i', j'} ∈ E, (a, b) ∈ {(u, v) : Fin 3 × Fin 3 | u ≠ v}, r : Fin n → {0,1}^{ℓ(n)}, r_{V*})`:
`c'_{i'} := a`, `c'_{j'} := b`, `c'_k := 0` otherwise; `com_k := Com n (pad c'_k) r_k`;
`e :=` edge decoded from `V*.next x z r_{V*} [com]`; if `e = e'` output
`some (x, z, r_{V*}, [com, (a, r_{i'}, b, r_{j'})])` else next attempt; after `n·m` attempts
output `none`. *Text issues:* "`k ∈ [m] \ {i', j'}`" should be `[n]`; `(i, j) = (i', j')`
is equality of unordered edges.

**Claim-128.a.** `S` is strict PPT when `V*` is (loop of `n·m` attempts, each with `n`
evaluations of `Com` and one call of `V*`): Inf-4.3.

**Prop-128.8.** ∀ PPT `V*` ∀ nuPPT `D` ∃ negligible `ε` ∀ `G ∈ 3COL`, `c ∈ R_3COL(G)`, `z`:
`distAdv (viewV* G c z) (S G z) D ≤ ε(|x|)`. Proof chain (all at the concrete layer, then
negligibility): `S ≡ S'` (Claim-129.a), `distAdv(S', S'') ≤ (n·m) · ε_Com` (Claim-129.d),
`statDist(S'', view) ≤ e^{-n}` (Claim-129.c); triangle inequality, `Negligible.add`,
`Negligible.mul_pow`. The hardest theorem of the chapter. *Text issues:* hybrid count
`2n|E|` (there are `n|E|` attempts); the sub-hybrid `S̃_e` over `6|E|` values of
`(i', j', π)` is unnecessary (the reduction samples them; non-uniformly one may fix the
best); typo "in `S̃_{e+1}` … whereas in `S̃_{e+1}`"; the last step uses multi-value hiding
(Claim-126.a) and closure (Lem-71.5).

**Claim-129.a (`S ≡ S'`).** `S'` receives the witness `c` and sets
`(c'_{i'}, c'_{j'}) := (π (c i'), π (c j'))` for uniform `π ∈ S_3` instead of a uniform
distinct pair; since `c i' ≠ c j'` on an edge, Lem-129.b makes the two samplers equal in
distribution; everything else is identical.

**Lem-129.b.** For `a ≠ b : Fin 3`, `π ↦ (π a, π b)` is a bijection
`Perm (Fin 3) ≃ {p : Fin 3 × Fin 3 // p.1 ≠ p.2}` (both sides have `6` elements,
`Fintype.card_perm`; injectivity since a permutation of `Fin 3` is determined by two values;
or `decide` after enumeration).

**Claim-129.c (`S''`).** `S''` commits to `pad (π (c k))` for **all** `k` (like the honest
prover) but still restarts unless `e = e'`: (i) `e'` is independent of `V*`'s reply (the
commitments do not depend on `e'`), so each attempt succeeds with probability exactly `1/m`
and `Pr[S'' = ⊥] = (1 − 1/m)^{n·m} ≤ e^{-n}` (`uprob_prod`, Claim-125.a); (ii) conditioned
on success the output is the honest view (commitments and openings with the prover's
distribution of `(π, r)`, edge `e` chosen by `V*`), as in Claim-123.b; hence
`statDist (S'') (some ∘ view) ≤ e^{-n}` and `distAdv ≤ e^{-n}` for every `D`.

**Claim-129.d (`S' ≈ S''`).** `S'` and `S''` differ only in the `n − 2` unopened commitments
of each attempt (`pad 0` versus `pad (π (c k))`). Hybrids `S_k` (attempts `< k` as `S''`,
`≥ k` as `S'`), `k = 0, …, n·m`; `exists_hybrid_gap` gives an adjacent pair with gap
`≥ δ/(n·m)`; the reduction for index `k` samples `(e', π, r_{V*})` of attempt `k` and all
other attempts itself, receives the commitment vector for the unopened positions from the
multi-value hiding challenger (Claim-126.a with `q = n`, values `pad 0` vs `pad (π (c ·))`,
the two opened positions committed by the reduction), simulates the restart logic, and runs
`D`; by `distAdv_sunglassRed`/`acceptProb_bind` its advantage equals the hybrid gap. It is
nuPPT by closure (Lem-71.5). Conclusion: `distAdv(S', S'') ≤ n·m · ε_Com(n)`, negligible.

### Appendix B

**Def-191.10 (DP).** Deterministic polynomial time = `Complexity.P` (exists). Alias only.

**Def-191.11 (NP via witness relations).** `L ∈ NP` iff ∃ `R_L ⊆ {0,1}* × {0,1}*`
poly-time recognizable and polynomial `p` with `x ∈ L ↔ ∃ y, |y| ≤ p(|x|) ∧ (x, y) ∈ R_L`;
`R_L(x) := {y | (x, y) ∈ R_L}`. Existing: `Complexity.mem_NP_iff_exists_length_le` is this
form with `p(N) = C(N+1)^c` and the pair `pairEncode x y` in a `P` language — the bridge is
a one-line unfolding. Chapter 4 consumes only the typed relation `R : X → Y → Prop` with
`L = {x | ∃ y, R x y}`. *Text error:* "`R_L(x) = {y : (x, y) ∈ L}`" should read `∈ R_L`.

**Def-192.12 (BPP).** Not used by Chapter 4; optional, trivial once `Randomized/PPT.lean`
is frozen.

### Infrastructure specific to Chapter 4

**Inf-4.1 (encodings).** `encGraph : SimpleGraph (Fin n) → List Bool` (adjacency matrix
`Fin n → Fin n → Bool`, row-major, prefixed by `n` in unary or binary via `pairEncode`),
`decGraph : List Bool → Σ n, SimpleGraph (Fin n)` total with default; same for
`Perm (Fin n)` (image list), `Fin 3`-colourings, message lists (`pairEncode`-folded) and
views. Length bounds `|encGraph G| ≤ C·(n+1)²`, decode-encode identities, and
`PolyTimeComputable` of the (de)coders. New file `ZeroKnowledge/Encoding.lean` (proposed
split; not in the plan's layout).

**Inf-4.2 (honest parties as machines; DQ1).** `PolyTimeComputable` facts for `σ(G)`,
`π * σ⁻¹`, `G = H`, `e ∈ E`, `Com` evaluation on encoded inputs, and the sampling of
`σ ∈ S_n`, `e ∈ E`, `π ∈ S_3` from coins (option A: near-uniform with error `2^{-n}`,
machine level, difficulty 5; option B: typed coin spaces, difficulty 3). Every `IsPPT`
side-condition of Props 118.4, 120.7, 127.6 lives here.

**Inf-4.3 (bounded restart loops).** The plan's `Randomized/Repetition.lean`: a PPT that
runs a PPT body up to `N(|x|)` times with fresh coins and returns the first accepted payload
(`exists_loopFindTM`). Consumed by Claim-123.d and Claim-128.a.

**Inf-4.4 (negligibility in `|x|`).** If `|encGraph G| ≥ n(G)²/C` (or `n ≥ Nat.sqrt (|x| / C)`)
then `fun N => (2:ℝ)⁻¹ ^ Nat.sqrt (N / C)` and `fun N => Real.exp (−Nat.sqrt (N / C))` are
negligible (`negligible_two_pow_neg` composed with the sub-polynomial growth of `sqrt`;
`Negligible.mono`). Converts the chapter's per-vertex bounds into Def-116.1's `ε(|x|)`.

## 4. Text errors and gaps found in Chapter 4 (for the plan's error list)

1. Proposition 120.7 says "interactive proof for `L_niso`"; it is for `L_iso` (already in the plan).
2. Definition 126.3, binding: the quantifier omits `v0 ≠ v1`; as printed the condition is unsatisfiable.
3. Proposition 127.6's proof: "repeated `|E|²` times" vs. the protocol's `n|E|` (already in the plan).
4. Protocol 127.5 lists the witness as `c0, c1, …, cm`; it is `c1, …, cn`. Simulator 128.7 writes "`k ∈ [m] \ {i', j'}`" for `[n]`.
5. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`": without checking that the openings match the commitments the protocol is unsound; also undefined for `E = ∅`; and `Com` applied to 2-bit colours has security parameter 2 under Definition 126.3 (the colour must be padded or `Com` given `1^n`).
6. Proof of Proposition 120.7: "`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" reverses the maps and renames the graphs; the correct identities are `π(G0) = H`, `(π∘σ⁻¹)(G1) = H`.
7. Theorem 122.3 claims (perfect) ZK for Protocol 120.6 with `n` iterations; the proof covers one iteration and relies on §7.2.1 (sequential composition), which is outside Chapters 2–4.
8. Definitions 121.1, 121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined (intended `n = |x|`).
9. Proof of Proposition 128.8: the hybrid count `2n|E|` does not match the `n|E|` attempts; "in `S̃_{e+1}` … whereas in `S̃_{e+1}`" (second should be `S̃_e`); the `6|E|`-step sub-hybrid is unnecessary.
10. §4.7, Step 2: "Cook's reduction can be applied to the witness" needs a Levin (witness-preserving) reduction, never defined; "execute protocol `(P, V)` on `x'`" should be `(P', V')`.
11. Theorem 126.4 uses a single one-way permutation `f` with a hard-core predicate `h`, whereas Definition 55.1 defines OWPs as collections and the existence of `h` (Theorem 87.3) is not invoked.
12. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
13. Proof of Proposition 118.4 uses `G1, G2` for `G0, G1`; "exponential time prover" is only an upper bound on what an unbounded prover needs.
14. The chapter never states that "choose a random permutation `σ ∈ S_n`" / "a random edge" cannot be done exactly by a PPT with a bounded coin string (DQ1).

## 5. Proposed file split (plan layout, with one addition)

```
TCSlib/Cryptography/ZeroKnowledge.lean                    facade (## Contents)
TCSlib/Cryptography/ZeroKnowledge/Encryption.lean         Def-111.1/a/b, Thm-112.2(.i,.ii), Claim-112.a/b
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean        Def-114.a … Def-116.b
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean  Def-116.1, 117.a/b, Claim-117.c, Def-119.5, 119.e, Def-191.11 (typed)
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean           Inf-4.1 (new; string encodings and their poly-time (de)coders)
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean   Def-117.e, 118.a, Claim-118.b, Prot-118.3, Lem-119.a–d, Prop-118.4, Prot-120.6, Lem-120.a–d, Prop-120.7
TCSlib/Cryptography/ZeroKnowledge/Defs.lean               Def-121.1, 121.2, 122.a, Claim-122.b, Inf-4.4
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean Thm-122.3(.hv,.trunc), Alg-123.4, Lem-123.5, Claim-123.b/d
TCSlib/Cryptography/ZeroKnowledge/Commitment.lean         Def-126.3, Claim-126.a, Alg-127.a, Claim-127.b/c/d, Thm-126.4
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean      Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e/h, Lem-127.f/g, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a/c/d, Lem-129.b
TCSlib/Cryptography/ZeroKnowledge/NP.lean                 Def-124.a, Thm-124.1, Claim-124.d (Claim-124.b/c as hypotheses)
```

`GraphIsomorphism.lean` and `ThreeColoring.lean` are at risk of exceeding 600 lines; split
`ThreeColoring.lean` into `ThreeColoring/Protocol.lean` (protocol, completeness,
soundness) and `ThreeColoring/Simulator.lean` (Alg-128.7 … Claim-129.d) if so.

## 6. Risk notes for the planners

* The chapter's hard core is three "perfect simulation by coin bijection" arguments
  (Claim-123.b, Claim-129.c) and one reduction with an internal restart loop (Claim-129.d);
  everything else is bookkeeping. Budget the fill accordingly.
* Both truncated simulators and the `n`-fold protocols need the Repetition infrastructure
  (Inf-4.3) and DQ1's answer before their PPT side-conditions can be stated.
* Thm-124.1's "every NP language" form is blocked on a string-level Levin reduction to 3COL
  (Claim-124.b/c); state it with the reduction as a hypothesis.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/g/replay.log =====

# closure of pack 03g's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 356 modules, extracted from g03-replay.log
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
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 33s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 16s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 19s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 14s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 138s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Permutations rc=0 11s errors=0 sorry=0
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
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 15s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 15s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 18s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 16s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 13s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 11s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0
TCSlib/Programs/Compat rc=0 3s errors=0 sorry=0
TCSlib/Programs/Util/List rc=0 9s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/g/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03g's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.colVerify_honest: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_bad_edge: propext, Quot.sound
TCSlib.Cryptography.uprob_col_cheat_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.R3COL_witnessRelation: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.col_efficientProverProofErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.colRep_efficientProverProof: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.colRep_interactiveProof: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_colSimTruncH: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_colSimRed_ge: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.col_zk: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.col_hvzk: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.col_zeroKnowledgeProof: propext, sorryAx, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/g/admissions.txt =====

# declarations with `sorry` in pack 03g's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:778 TCSlib.Cryptography.R3COL_witnessRelation
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:851 TCSlib.Cryptography.colRep_efficientProverProof
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean:764 TCSlib.Cryptography.col_zk

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/g/lint.log =====

# scripts/style_lint.py on pack 03g's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean: module docstring missing `## Main definitions`
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:95: `polyTimeComputable_loopState'` proof is 37 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:151: `polyTimeComputable_flatMap_range` proof is 26 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:181: `iterSnd_poly` proof is 27 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:332: public `theorem countTrue_zero` has no docstring
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:334: public `theorem countTrue_succ` has no docstring
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:360: `countTrue_poly` proof is 30 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:596: public `theorem natOfBits_zero` has no docstring
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:598: public `theorem natOfBits_succ` has no docstring
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:627: `natOfBits_poly` proof is 31 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:661: `findSome?_finRange_eq` proof is 25 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean:723: `sampleVal_poly` proof is 29 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean: module docstring missing `## Main definitions`
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean:218: `checkStr_poly` proof is 38 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean:312: `proverRepStr_poly` proof is 23 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:661: `colProtocol_sound` proof is 99 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean: module docstring missing `## Main definitions`
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:204: `colVerifier_next_eq` proof is 46 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:252: `colProverRep_next_eq` proof is 25 lines, no **Proof sketch.**
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:279: `colVerifierRep_next_eq` proof is 37 lines, no **Proof sketch.**






20 findings in 10 files

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.Asymptotic.Adversary
import Mathlib.Combinatorics.SimpleGraph.Coloring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Graph 3-colouring: the language, its witnesses, edges, colours and samplers

The combinatorial and sampling preliminaries of the zero-knowledge protocol for graph
3-colouring [PS10, §4.7]: the language of 3-colourable graphs and its witness relation
[PS10, Theorem 124.1, step 1] (Def-124.f), the enumeration of the edges of a graph (the set
`E` of [PS10, Protocol 127.5]), the bound `(1 - 1/m)^{nm} ≤ e^{-n}` of the soundness analysis
(Claim-125.a), colours as `n`-bit committed values (DQ4), and the rejection samplers of the
honest parties for the colour permutation `π ← S₃` and the edge `e ← E` (D10).

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours
(`ThreeColorable` agrees with Mathlib's `SimpleGraph.Colorable 3` on simple graphs,
`threeColorable_ofSimpleGraph_iff`). The edges are listed in lexicographic order
(`edgeList`), the verifier's challenge is an index into that list, sent in unary
(`edgeMsg`) and decoded totally (`edgeIdxOfMsg`).

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation and `edgeList`
lists the *ordered* pairs `(u, v)` with `G u v` (loops included), so for the text's symmetric
loopless `G = (V, E)` the formal `|E| := edgeCount G` is `2|E|`: one iteration has soundness
error `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|` times; the challenge is
uniform over the ordered pairs, i.e. uniform over the undirected edges, and the bound
`(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. Throughout `ThreeColoring/`, `|E|` means `edgeCount G`.

**Deviation (DQ4, D10):** colours are padded to `n` bits (`padColor`; the text commits to
2-bit colours, i.e. at security parameter `2`); `π` and `e` are sampled by rejection from the
bit tapes (`samplePerm3`, `sampleEdgeIdx`) within statistical error `(1/4)^T`, `(1/2)^T`.

## Main definitions

* `TCSlib.Cryptography.ProperColoring`, `TCSlib.Cryptography.ThreeColorable`,
  `TCSlib.Cryptography.L3COL`, `TCSlib.Cryptography.R3COL` — 3-colourings, the language of
  3-colourable graphs and its witness relation (Def-124.f).
* `TCSlib.Cryptography.edgeList`, `TCSlib.Cryptography.edgeCount`,
  `TCSlib.Cryptography.edgeOf`, `TCSlib.Cryptography.edgeAt` — the edges and their indices.
* `TCSlib.Cryptography.encColor`, `TCSlib.Cryptography.decColor`,
  `TCSlib.Cryptography.padColor` — colours as 2-bit strings and as `n`-bit values.
* `TCSlib.Cryptography.sampleIdx`, `TCSlib.Cryptography.samplePerm3`,
  `TCSlib.Cryptography.sampleEdgeIdx`, `TCSlib.Cryptography.edgeMsg`,
  `TCSlib.Cryptography.edgeIdxOfMsg` — the samplers and the challenge encoding.

## Main results

* `TCSlib.Cryptography.mem_L3COL_iff`, `TCSlib.Cryptography.encGraph_mem_L3COL_iff`,
  `TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff` — the language and its witnesses.
* `TCSlib.Cryptography.mem_edgeList_iff`, `TCSlib.Cryptography.edgeAt_adj`,
  `TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero`,
  `TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable` — edges (all proved).
* `TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp`, `TCSlib.Cryptography.exp_neg_le_inv_two_pow`
  — `(1 - 1/m)^{nm} ≤ e^{-n} ≤ 2^{-n}` (Claim-125.a, proved).
* `TCSlib.Cryptography.padColor_injective` — padding to `n ≥ 2` bits is injective (proved).
* `TCSlib.Cryptography.statClose_samplePerm3`, `TCSlib.Cryptography.statClose_sampleEdgeIdx`
  — the samplers are statistically close to uniform (D10, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### 3-colourings and the language `3COL` (Def-124.f) -/

/-- A proper 3-colouring of the graph `G` [PS10, §4.7, Theorem 124.1, step 1]: the endpoints
of every edge receive different colours (`c : Fin n → Fin 3`, colours `{1, 2, 3}` as `Fin 3`). -/
def ProperColoring {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Prop :=
  ∀ u v, G u v = true → c u ≠ c v

instance {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Decidable (ProperColoring G c) := by
  unfold ProperColoring
  infer_instance

/-- A graph is 3-colourable when it has a proper 3-colouring [PS10, §4.7] (Def-124.f, typed). -/
def ThreeColorable {n : ℕ} (G : Graph n) : Prop := ∃ c, ProperColoring G c

/-- The graph of a Mathlib simple graph on `Fin n` as a Boolean relation. -/
def Graph.ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : Graph n :=
  fun u v => decide (H.Adj u v)

/-- Sanity: for a simple graph the notion agrees with Mathlib's `SimpleGraph.Colorable 3`
(a `Coloring` into `Fin 3` is exactly a proper 3-colouring). -/
theorem threeColorable_ofSimpleGraph_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    ThreeColorable (Graph.ofSimpleGraph H) ↔ H.Colorable 3 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {u v} h => hc u v (decide_eq_true h)⟩
  · rintro ⟨C⟩
    exact ⟨C, fun u v h => C.valid (of_decide_eq_true h)⟩

/-- The language of 3-colourable graphs [PS10, §4.7, "Graph 3-Coloring"] (Def-124.f): the
adjacency-matrix encodings of the 3-colourable graphs. -/
def L3COL : Language Bool := {x | ∃ (n : ℕ) (G : Graph n), x = encGraph G ∧ ThreeColorable G}

/-- The witness relation of `3COL` [PS10, §4.7] (Def-124.f): `y` is the encoding of a proper
3-colouring of the graph encoded by `x`. -/
def R3COL (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G : Graph n) (c : Fin n → Fin 3),
    x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c

/-- `x ∈ 3COL` iff `x` has a witness for `R_3COL`. -/
theorem mem_L3COL_iff (x : List Bool) : x ∈ L3COL ↔ ∃ y, R3COL x y := by
  constructor
  · rintro ⟨n, G, rfl, c, hc⟩
    exact ⟨encColoring c, n, G, c, rfl, rfl, hc⟩
  · rintro ⟨y, n, G, c, rfl, -, hc⟩
    exact ⟨n, G, rfl, c, hc⟩

/-- An encoded graph is in `3COL` iff the graph is 3-colourable (`decGraph_encGraph`
identifies the graph from its encoding). -/
theorem encGraph_mem_L3COL_iff {n : ℕ} (G : Graph n) : encGraph G ∈ L3COL ↔ ThreeColorable G := by
  constructor
  · rintro ⟨n', G', h, hG'⟩
    have hd := decGraph_encGraph G
    rw [h, decGraph_encGraph] at hd
    cases hd
    exact hG'
  · intro h
    exact ⟨n, G, rfl, h⟩

/-! ### Edges -/

/-- The list of edges of `G`: the **ordered** pairs `(u, v)` with `G u v = true` (loops
included), in lexicographic order — the set `E` of [PS10, Protocol 127.5] in the formal model;
in the docstrings of `ThreeColoring/` the notation `|E|` means `edgeCount G = (edgeList G).length`.

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation, so `E` is the
list of ordered pairs `(u, v)` with `G u v`; for a symmetric loopless graph (the text's
`G = (V, E)`) `edgeCount G = 2|E|`, one iteration of the protocol has soundness error
`1 − 1/(2|E|)` and the repeated protocol runs `n · edgeCount G = 2n|E|` iterations. The
verifier's challenge is uniform over the ordered pairs, i.e. uniform over the text's
undirected edges, and the bound `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged; a loop `(u, u)` is an
edge and makes the graph non-colourable, as it should. -/
def edgeList {n : ℕ} (G : Graph n) : List (Fin n × Fin n) :=
  (List.finRange n ×ˢ List.finRange n).filter fun p => G p.1 p.2

/-- The number `m` of (ordered) edge pairs of `G`, written `|E|` in the docstrings of
`ThreeColoring/` — for a symmetric loopless graph twice the `|E| = m` of
[PS10, Protocol 127.5] (see `edgeList`; run-3 audit P11-3). -/
abbrev edgeCount {n : ℕ} (G : Graph n) : ℕ := (edgeList G).length

/-- A pair is in the edge list iff it is an edge. -/
theorem mem_edgeList_iff {n : ℕ} (G : Graph n) (p : Fin n × Fin n) :
    p ∈ edgeList G ↔ G p.1 p.2 = true := by
  rcases p with ⟨u, v⟩
  simp [edgeList, List.mem_filter, List.mem_finRange]

/-- The edge of index `e : Fin |E|`. -/
def edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) : Fin n × Fin n := (edgeList G).get e

/-- The endpoints of `edgeOf G e` are adjacent. -/
theorem edgeOf_adj {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    G (edgeOf G e).1 (edgeOf G e).2 = true :=
  (mem_edgeList_iff G _).1 (List.get_mem _ _)

/-- Every edge is `edgeOf G e` for some index `e`. -/
theorem exists_edgeOf_eq {n : ℕ} (G : Graph n) {u v : Fin n} (h : G u v = true) :
    ∃ e : Fin (edgeCount G), edgeOf G e = (u, v) := by
  obtain ⟨e, he⟩ := List.mem_iff_get.1 ((mem_edgeList_iff G (u, v)).2 h)
  exact ⟨e, he⟩

/-- The edge of the (arbitrary) index `e : ℕ`, reduced modulo `|E|`; `none` iff `E = ∅`
(the total decoding of the verifier's challenge). -/
def edgeAt {n : ℕ} (G : Graph n) (e : ℕ) : Option (Fin n × Fin n) := (edgeList G)[e % edgeCount G]?

/-- On an in-range index `edgeAt` is `edgeOf`. -/
theorem edgeAt_eq_some_edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    edgeAt G e = some (edgeOf G e) := by
  unfold edgeAt edgeOf
  rw [Nat.mod_eq_of_lt e.isLt, List.getElem?_eq_getElem e.isLt, List.get_eq_getElem]

/-- The endpoints of `edgeAt G e` are adjacent. -/
theorem edgeAt_adj {n : ℕ} (G : Graph n) {e : ℕ} {p : Fin n × Fin n} (h : edgeAt G e = some p) :
    G p.1 p.2 = true :=
  (mem_edgeList_iff G p).1 (List.mem_of_getElem? h)

/-- With at least one edge every index decodes to an edge. -/
theorem edgeAt_isSome {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    ∃ p, edgeAt G e = some p :=
  ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hm)⟩

/-- `edgeAt` is `none` exactly when there are no edges. -/
theorem edgeAt_eq_none_iff {n : ℕ} (G : Graph n) (e : ℕ) : edgeAt G e = none ↔ edgeCount G = 0 := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨p, hp⟩ := edgeAt_isSome G (Nat.pos_of_ne_zero hm) e
    rw [h] at hp
    exact Option.noConfusion hp
  · intro h
    unfold edgeAt
    rw [List.getElem?_eq_none_iff]
    change (edgeList G).length = 0 at h
    rw [h]
    exact Nat.zero_le _

/-- An edgeless graph is 3-colourable (constant colouring). -/
theorem threeColorable_of_edgeCount_eq_zero {n : ℕ} {G : Graph n} (h : edgeCount G = 0) :
    ThreeColorable G := by
  refine ⟨fun _ => 0, fun u v huv => ?_⟩
  have hmem := (mem_edgeList_iff G (u, v)).2 huv
  rw [List.length_eq_zero_iff.1 h] at hmem
  exact absurd hmem (List.not_mem_nil)

/-- A graph that is not 3-colourable has an edge. -/
theorem edgeCount_pos_of_not_threeColorable {n : ℕ} {G : Graph n} (h : ¬ ThreeColorable G) :
    0 < edgeCount G :=
  Nat.pos_of_ne_zero fun h0 => h (threeColorable_of_edgeCount_eq_zero h0)

/-! ### Claim-125.a -/

/-- `(1 - 1/m)^{n m} ≤ e^{-n}` for `m ≥ 1` [PS10, proof of Proposition 127.6,
"`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Claim-125.a): `Real.one_sub_div_pow_le_exp_neg` with `N := n m`
and `t := n`, after rewriting `n / (n m) = 1 / m`. -/
theorem one_sub_inv_pow_mul_le_exp (m n : ℕ) (hm : 0 < m) :
    (1 - 1 / (m : ℝ)) ^ (n * m) ≤ Real.exp (-(n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := n * m) (t := (n : ℝ))
    (by exact_mod_cast Nat.le_mul_of_pos_right n hm)
  have hnm : (n : ℝ) / ((n * m : ℕ) : ℝ) = 1 / m := by
    rw [Nat.cast_mul]
    field_simp
  rwa [hnm] at h

/-- `e^{-n} ≤ 2^{-n}` (the text's "`≈ e^{-n}`" bounded by the dyadic negligible function):
`2 ≤ e` by `Real.add_one_le_exp`. -/
theorem exp_neg_le_inv_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [Real.exp_neg, show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul, ← inv_pow]
  exact pow_le_pow_left₀ (by positivity)
    (inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])) n

/-! ### Colours as `n`-bit values (DQ4) -/

/-- The two-bit encoding of a colour (`encColoring` of a one-vertex colouring). -/
def encColor (a : Fin 3) : List Bool := encColoring fun _ : Fin 1 => a

/-- The total decoding of a colour from a string (`decColoring` at one vertex). -/
def decColor (w : List Bool) : Fin 3 := decColoring 1 w 0

/-- Decoding an encoded colour gives the colour back. -/
@[simp] theorem decColor_encColor (a : Fin 3) : decColor (encColor a) = a :=
  congrFun (decColoring_encColoring fun _ : Fin 1 => a) 0

/-- A colour padded to an `n`-bit value (DQ4): the two bits of `encColor a` followed by
zeros. The value committed to by the prover of [PS10, Protocol 127.5] at security parameter
`n`. -/
def padColor (n : ℕ) (a : Fin 3) : Fin n → Bool := padFin n (encColor a)

/-- The two-bit encodings of distinct colours differ in one of the two bits. -/
theorem encColor_getD_ne {a b : Fin 3} (hab : a ≠ b) :
    (encColor a).getD 0 false ≠ (encColor b).getD 0 false ∨
      (encColor a).getD 1 false ≠ (encColor b).getD 1 false := by
  revert a b
  decide

/-- Padding to `n ≥ 2` bits is injective on colours. -/
theorem padColor_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (padColor n) := by
  intro a b h
  by_contra hab
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [padColor, padFin] at h0 h1
  rcases encColor_getD_ne hab with hne | hne
  · exact hne h0
  · exact hne h1

/-! ### Samplers of the honest parties (D10) -/

/-- `T` rejection trials of `k` bits read consecutively from a tape (bit `j` of trial `t` at
position `t k + j`), the first accepted value in `Fin m` (`rejectionSample`, D10). -/
def sampleIdx (m k T : ℕ) (r : List Bool) : Option (Fin m) :=
  rejectionSample m k T fun t j => r.getD (t * k + j) false

/-- The six permutations of the three colours enumerated by `Fin 6`. -/
noncomputable def perm3Equiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_perm, Fintype.card_fin]; rfl)).symm

/-- The honest prover's colour permutation `π ← S₃` of [PS10, Protocol 127.5] from the first
`3T` bits of its tape: `T` rejection trials of three bits (success probability `6/8` each),
the identity on failure (D10). -/
noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
  ((sampleIdx 6 3 T r).map perm3Equiv).getD 1

/-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
the index `0` on failure (D10). -/
def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
  ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0

/-- With at least one edge the sampled index is in range. -/
theorem sampleEdgeIdx_lt {m : ℕ} (hm : 0 < m) (T : ℕ) (r : List Bool) : sampleEdgeIdx m T r < m := by
  unfold sampleEdgeIdx
  cases sampleIdx m (Nat.size m) T r with
  | none => simpa using hm
  | some e => simp [e.isLt]

/-- The unary encoding of the verifier's challenge: the edge index `e` as `1^e`. -/
def edgeMsg (e : ℕ) : List Bool := List.replicate e true

/-- The total decoding of a challenge string as an edge index in `[m]`: its length modulo `m`
(every string names an edge when `E ≠ ∅`). -/
def edgeIdxOfMsg (m : ℕ) (w : List Bool) : ℕ := w.length % m

/-- The challenge `1^e` decodes to `e` when `e < m`. -/
@[simp] theorem edgeIdxOfMsg_edgeMsg {m e : ℕ} (he : e < m) : edgeIdxOfMsg m (edgeMsg e) = e := by
  simp [edgeIdxOfMsg, edgeMsg, Nat.mod_eq_of_lt he]

/-- The decoded index is in range when `m > 0`. -/
theorem edgeIdxOfMsg_lt {m : ℕ} (hm : 0 < m) (w : List Bool) : edgeIdxOfMsg m w < m :=
  Nat.mod_lt _ hm

/-- A tape of `T k` bits read as `T` trials of `k` bits: bit `j` of trial `t` is tape bit
`finProdFinEquiv (t, j) = t k + j` (the curried `finProdFinEquiv`). -/
private def tapeEquiv (T k : ℕ) : (Fin (T * k) → Bool) ≃ (Fin T → Fin k → Bool) where
  toFun r t j := r (finProdFinEquiv (t, j))
  invFun b i := b (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv r := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv b := by
    funext t j
    simp

/-- Bit `t k + j` of the tape `List.ofFn r` is entry `(t, j)` of its trial table. -/
private theorem ofFn_getD_tape {T k : ℕ} (r : Fin (T * k) → Bool) (t : Fin T) (j : Fin k) :
    (List.ofFn r).getD (t * k + j) false = tapeEquiv T k r t j := by
  have hm : ((finProdFinEquiv (t, j) : Fin (T * k)) : ℕ) = t * k + j := by
    simp only [finProdFinEquiv_apply_val]
    ring
  show _ = r (finProdFinEquiv (t, j))
  rw [← hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _),
    Option.getD_some, Fin.eta]

/-- On a tape of exactly `T k` bits, `sampleIdx` is `rejectionSample` on the trial table. -/
private theorem sampleIdx_ofFn (m k T : ℕ) (r : Fin (T * k) → Bool) :
    sampleIdx m k T (List.ofFn r) = rejectionSample m k T (tapeEquiv T k r) := by
  unfold sampleIdx
  congr 1
  funext t j
  exact ofFn_getD_tape r t j

/-- The permutation sampler is within `(1/4)^T` of a uniform permutation of the colours (D10).

**Proof sketch.** `statClose_rejectionSample 6 3 T` (with `6 ≤ 2³`) gives closeness
`(1 - 6/8)^T = (1/4)^T` of `(rejectionSample 6 3 T b).getD d` to the identity on `Fin 6`; the
tape-to-trials map `r ↦ (t, j) ↦ r.getD (3t + j)` on `Fin (T * 3) → Bool` is the bijection
`finProdFinEquiv` curried (`StatClose.comp_equiv_left`), and `perm3Equiv` is a bijection
with `perm3Equiv d = 1` for the right default `d` (`StatClose.map`, `StatClose.comp_equiv_right`). -/
theorem statClose_samplePerm3 (T : ℕ) :
    StatClose (fun r : Fin (T * 3) → Bool => samplePerm3 T (List.ofFn r))
      (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) ((1 / 4 : ℝ) ^ T) := by
  have h := (((statClose_rejectionSample 6 3 T (by norm_num) (by norm_num)
    (perm3Equiv.symm 1)).map perm3Equiv).comp_equiv_right perm3Equiv.symm).comp_equiv_left
    (tapeEquiv T 3)
  have hδ : (1 - ((6 : ℕ) : ℝ) / 2 ^ 3) ^ T = (1 / 4) ^ T := by norm_num
  rw [hδ] at h
  convert h using 2 with r σ
  · simp only [samplePerm3, sampleIdx_ofFn]
    cases rejectionSample 6 3 T (tapeEquiv T 3 r) with
    | none => simp
    | some i => simp
  · simp

/-- The edge sampler is within `(1/2)^T` of a uniform edge index (D10).

**Proof sketch.** `statClose_rejectionSample m (Nat.size m) T` with `m ≤ 2^{size m}`
(`Nat.lt_size_self`) gives closeness `(1 - m/2^{size m})^T`; since `2^{size m} ≤ 2m` for
`m ≥ 1` (`Nat.size_le`, `Nat.lt_size`), `1 - m/2^{size m} ≤ 1/2` and `pow_le_pow_left₀`;
the tape-to-trials map is the curried `finProdFinEquiv` (`StatClose.comp_equiv_left`), and
`sampleEdgeIdx` is `Fin.val` of the sampler's `getD ⟨0, hm⟩`. -/
theorem statClose_sampleEdgeIdx {m : ℕ} (hm : 0 < m) (T : ℕ) :
    StatClose (fun r : Fin (T * Nat.size m) → Bool =>
        (⟨sampleEdgeIdx m T (List.ofFn r), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : Fin m → Fin m) ((1 / 2 : ℝ) ^ T) := by
  have hk : m ≤ 2 ^ Nat.size m := (Nat.lt_size_self m).le
  have hpos : 0 < Nat.size m := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (Nat.sub_lt hpos one_pos)
  have h2 : 2 ^ Nat.size m ≤ 2 * m := by
    have : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have h := (statClose_rejectionSample m (Nat.size m) T hm hk ⟨0, hm⟩).comp_equiv_left
    (tapeEquiv T (Nat.size m))
  have h2k : (0 : ℝ) < 2 ^ Nat.size m := by positivity
  have hm' : (m : ℝ) ≤ 2 ^ Nat.size m := by exact_mod_cast hk
  have h2' : (2 : ℝ) ^ Nat.size m ≤ 2 * m := by exact_mod_cast h2
  have hle : (1 - (m : ℝ) / 2 ^ Nat.size m) ^ T ≤ (1 / 2 : ℝ) ^ T := by
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact hm'
    · have : (1 / 2 : ℝ) ≤ m / 2 ^ Nat.size m := by
        rw [div_le_div_iff₀ (by norm_num) h2k]
        linarith
      linarith
  convert h.mono hle using 2 with r
  apply Fin.ext
  simp only [sampleEdgeIdx, sampleIdx_ofFn]
  cases rejectionSample m (Nat.size m) T (tapeEquiv T (Nat.size m) r) with
  | none => simp
  | some i => simp

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: machines behind the honest parties

Proof infrastructure for the efficiency theorems of `ThreeColoring/Protocol.lean`
(`colProver_efficient`, `colVerifier_efficient`, `colProverRep_efficient`,
`colVerifierRep_efficient`, inventory item Inf-4.2) and for the decider clause of
`R3COL_witnessRelation` [PS10, §4.7, Protocol 127.5]. The honest parties of the protocol
are exhibited as polynomial-time functions of the interactive machine layout
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`ilayout`, `efficient_of_polyTime`), assembled from
the unary FP toolkit of `ZeroKnowledge/EncodingMachines.lean` (numbers travel in unary,
`polyTimeComputable_firstIdx`, `polyTimeComputable_of_getD`, `polyTimeComputable_stateFind`)
and the typed coin cuts of `Complexity/Randomized/Primitives.lean`.

This file holds the generic pieces (the parties themselves as string functions are in
`ThreeColoring/Parties.lean`, the identification with the strategies of `Protocol.lean` in
`ThreeColoring/ProtocolProofs.lean`):

* counted loops bounded along the genuine orbit only (`polyTimeComputable_loopState'`),
  concatenating loops over a data-dependent range (`polyTimeComputable_flatMap_range`), and
  the iterated second projection (`iterSnd_poly`, the message-selection `msgAt`);
* zero padding (`padTo`) with the identities `List.ofFn (padFin L w) = padTo L w` and
  `List.ofFn (fun j => r.getD (b + j) false) = padTo L (r.drop b)` that turn the parties'
  typed values and randomness blocks into string operations;
* the **numeric model of the edge list**: `edgeList G` is, through the index
  `(u, v) ↦ v + n u` of `finProdFinEquiv`, the increasing list of positions `j < n²` whose
  bit of the adjacency matrix is set (`map_edgeList`); hence `edgeCount G` is the bit count
  `countTrue` and `edgeOf G e` is the `e`-th set position `nthTrue` (`edgeCount_eq`,
  `edgeOf_val`), both computed by counted loops and bounded searches;
* the **numeric model of the samplers**: `bitsToNat` of a tape window is the loop value
  `natOfBits`, and the rejection sampler is the first accepted trial (`sampleVal`,
  `map_val_sampleIdx_getD`); the colour permutation reaches the machine as the six-bit table
  `permTable π` of the images of the three colours (`permTable_samplePerm3`), a table lookup
  on the sampled index;
* colours as numbers: `decColoring`, `decColor` and `encColor` numerically (`colorVal`,
  `encColorOfVal`, `colorFromTable`).

## Main results

* `TCSlib.Cryptography.ColMachines.polyTimeComputable_loopState'`,
  `ColMachines.polyTimeComputable_flatMap_range`, `ColMachines.iterSnd_poly` — loops.
* `TCSlib.Cryptography.ColMachines.map_edgeList`, `ColMachines.edgeCount_eq`,
  `ColMachines.edgeOf_val` — the numeric model of the edge list.
* `TCSlib.Cryptography.ColMachines.map_val_sampleIdx_getD`, `ColMachines.permTable_samplePerm3`
  — the numeric model of the samplers.
* `TCSlib.Cryptography.ColMachines.countTrue_poly`, `ColMachines.nthTrue_poly`,
  `ColMachines.natOfBits_poly`, `ColMachines.sampleVal_poly`, `ColMachines.tableOfIdx_poly`,
  `ColMachines.colorVal_poly`, `ColMachines.encColorOfVal_poly` — the unary machines.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### Generic tools -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- Composition of polynomial-time functions in applied form (`fun z => g (f z)` rather than
`g ∘ f`, so that later unifications never have to unfold `Function.comp` against a large
definition). -/
theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- **Counted loops bounded along the genuine orbit:** `EncodingMachines.polyTimeComputable_loopState`
with the length bound required only of the states `loopState upd init x i`, `i ≤ N x`
(the update may lengthen arbitrary words). Same proof: a state loop
(`EncodingMachines.polyTimeComputable_stateFind`, data in `EncodingMachines.CountLoop`). -/
theorem polyTimeComputable_loopState' {upd init : List Bool → List Bool}
    (hupd : PolyTimeComputable upd) (hinit : PolyTimeComputable init)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true)
    (B : PolyExpr)
    (hstate : ∀ x i, i ≤ N x → (loopState upd init x i).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => loopState upd init x (N x) := by
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNR : ∀ x, N x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hbound : ∀ x i, i ≤ N x →
      (orbit (CountLoop.start init) (CountLoop.step upd) x i).length ≤
        (PolyExpr.add (.mul (.const 2) (PolyExpr.normal C c)) (.add (.const 2) B)).eval
          x.length := by
    intro x i hi
    rw [CountLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have h1 := hstate x i hi
    have h2 := hNR x
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hfirst : ∀ x i, i < N x →
      CountLoop.acc N (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x i)) =
        false := by
    intro x i hi
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc, hi]
  have hlast : ∀ x, CountLoop.acc N
      (pairEncode x (orbit (CountLoop.start init) (CountLoop.step upd) x (N x))) = true := by
    intro x
    rw [CountLoop.orbit_eq]
    simp [CountLoop.acc]
  have h := polyTimeComputable_stateFind (CountLoop.start_poly hinit) (CountLoop.step_poly hupd)
    (CountLoop.acc_poly hN) CountLoop.out_poly (PolyExpr.normal C c) _ N hNR hbound hfirst hlast
  convert h using 1
  funext x
  rw [CountLoop.orbit_eq]
  simp [CountLoop.out]

/-- Emitting `E i` at the indices `i < L` of `List.range N` gives the concatenation of the
`E i` over `i < min N L` (`EncodingMachines.flatMap_range_ite_eq` for arbitrary chunks). -/
theorem flatMap_range_ite (E : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then E i else []) =
      (List.range (min N L)).flatMap E
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite E L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- **Concatenating loops over a data-dependent range:** if the chunk `E z i` is a
polynomial-time function of `⟨1^i, z⟩` and the range `n z` is a unary function, then
`z ↦ E z 0 ++ ⋯ ++ E z (n z - 1)` is polynomial-time computable (an instance of
`Complexity.polyTimeComputable_iterateEmit` on the counter step `EncodingMachines.cstep`, as
`EncodingMachines.polyTimeComputable_of_getD`). -/
theorem polyTimeComputable_flatMap_range {E : List Bool → ℕ → List Bool}
    (hE : PolyTimeComputable fun w => E (pairSndD w) (pairFstD w).length)
    {n : List Bool → ℕ} (hn : PolyTimeComputable fun z => List.replicate (n z) true) :
    PolyTimeComputable fun z => (List.range (n z)).flatMap (E z) := by
  obtain ⟨C, c, hC⟩ := hn.output_length_le
  have hnP : ∀ z, n z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have htest : PolyTimeComputable fun w => [decide ((pairFstD w).length < n (pairSndD w))] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD) (hn.comp polyTimeComputable_pairSndD)
  have hemit := polyTimeComputable_ite htest hE (polyTimeComputable_const [])
  have hL := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hL.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : n z ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hnP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]

/-- **The iterated second projection** `pairSndD^[i z] (s z)` is polynomial-time for a
polynomial-time `s` and a unary `i`: a counted loop whose states never exceed `|s z|`
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem iterSnd_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {i : List Bool → ℕ} (hi : PolyTimeComputable fun z => List.replicate (i z) true) :
    PolyTimeComputable fun z => pairSndD^[i z] (s z) := by
  have hupd : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z j, loopState (fun w => pairSndD (pairSndD (pairSndD w))) s z j =
      pairSndD^[j] (s z) := by
    intro z j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [loopState_succ, ih, pairSndD_pairEncode, pairSndD_pairEncode,
        Function.iterate_succ_apply']
  have hlen : ∀ (w : List Bool) (j : ℕ), (pairSndD^[j] w).length ≤ w.length := by
    intro w j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ((Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le _)).trans ih
  obtain ⟨C, c, hC⟩ := hs.output_length_le
  have h := polyTimeComputable_loopState' hupd hs hi (PolyExpr.normal C c) fun z j _ => by
    rw [hclosed]
    exact (hlen _ _).trans (by simpa [PolyExpr.eval_normal] using hC z)
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The interactive layout and its projections -/

/-- The interactive machine layout of a strategy activation,
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`Strategy.ofNUPPT`, `NUPPT.runAtL`). -/
def ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) : List Bool :=
  NUPPT.layout (List.replicate x.length true)
    (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r

/-- A strategy whose next-message function is a polynomial-time function `F` of the machine
layout `ilayout x z hist r` is efficient: `NUPPT.ofPolyTimeUniform` of `F` with the strategy's
coin polynomial is the uniform machine computing it (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem efficient_of_polyTime (S : Strategy) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (h : ∀ x z r hist, S.next x z r hist = F (ilayout x z hist r)) : S.Efficient :=
  ⟨NUPPT.ofPolyTimeUniform hF S.coins, NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => by
      rw [h, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The common-input slot of the interactive layout. -/
def argX (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inArg w))

/-- The auxiliary-input slot of the interactive layout. -/
def argZ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg w))

/-- The encoded-messages slot of the interactive layout. -/
def argM (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The common input of a layout. -/
@[simp] theorem argX_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argX (ilayout x z hist r) = x := by
  simp [argX, ilayout]

/-- The auxiliary input of a layout. -/
@[simp] theorem argZ_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argZ (ilayout x z hist r) = z := by
  simp [argZ, ilayout]

/-- The encoded messages of a layout. -/
@[simp] theorem argM_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    argM (ilayout x z hist r) = Strategy.encodeMsgs hist := by
  simp [argM, ilayout]

/-- The coins of a layout. -/
@[simp] theorem inCoins_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    NUPPT.inCoins (ilayout x z hist r) = r := by
  simp [ilayout]

/-- The common-input projection is polynomial-time. -/
theorem argX_poly : PolyTimeComputable argX :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The auxiliary-input projection is polynomial-time. -/
theorem argZ_poly : PolyTimeComputable argZ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The messages projection is polynomial-time. -/
theorem argM_poly : PolyTimeComputable argM :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-! ### Zero padding -/

/-- `L` zeros from a unary length (the bit-extraction principle with the constant bit `0`). -/
theorem zeros_poly {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => List.replicate (L x) false := by
  refine polyTimeComputable_of_getD (F := fun x => List.replicate (L x) false) ?_ ?_
  · convert polyTimeComputable_const [false] using 1
    funext w
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  · simpa using hL

/-- Padding a word with zeros to length `L` (and truncating to `L`): the string form of the
typed value `padFin L w` (`ofFn_padFin`). -/
def padTo (L : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate L false).take L

/-- Padding to a unary length is polynomial-time. -/
theorem padTo_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun x => List.replicate (L x) true) :
    PolyTimeComputable fun x => padTo (L x) (s x) :=
  truncate_poly (hs.append (zeros_poly hL)) hL

/-- The padded word has length `L`. -/
theorem length_padTo (L : ℕ) (w : List Bool) : (padTo L w).length = L := by
  simp [padTo]

/-- The bits of the padded word below `L` are the bits of `w` read with default `false`. -/
theorem getD_padTo (L : ℕ) (w : List Bool) {i : ℕ} (hi : i < L) :
    (padTo L w).getD i false = w.getD i false := by
  rw [padTo, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_append,
    List.getD_eq_getElem?_getD]
  split_ifs with h
  · rfl
  · have hw : w[i]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hw, List.getElem?_replicate]
    split_ifs <;> rfl

/-- The typed value `padFin L w` as a string is the padded word. -/
theorem ofFn_padFin (L : ℕ) (w : List Bool) : List.ofFn (padFin L w) = padTo L w := by
  apply List.ext_getElem
  · simp [length_padTo]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    show w.getD i false = (padTo L w)[i]
    rw [← getD_padTo L w (by simpa [length_padTo] using h2), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-- A block of `L` bits read with default `false` from position `b` of a tape is the padded
`drop`. -/
theorem ofFn_getD_add (r : List Bool) (b L : ℕ) :
    List.ofFn (fun j : Fin L => r.getD (b + j) false) = padTo L (r.drop b) := by
  rw [← ofFn_padFin]
  congr 1
  funext j
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ### Counting set bits -/

/-- The number of set bits among the first `j` positions of `x` (read with default `false`). -/
def countTrue (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => countTrue x j + (x.getD j false).toNat

@[simp] theorem countTrue_zero (x : List Bool) : countTrue x 0 = 0 := rfl

@[simp] theorem countTrue_succ (x : List Bool) (j : ℕ) :
    countTrue x (j + 1) = countTrue x j + (x.getD j false).toNat := rfl

/-- At most `j` of the first `j` bits are set. -/
theorem countTrue_le (x : List Bool) (j : ℕ) : countTrue x j ≤ j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [countTrue_succ]
    have := Bool.toNat_le (x.getD j false)
    omega

/-- The bit count is monotone in the prefix length. -/
theorem countTrue_mono (x : List Bool) {i j : ℕ} (h : i ≤ j) : countTrue x i ≤ countTrue x j := by
  induction j with
  | zero =>
    rw [Nat.le_zero.1 h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · rw [countTrue_succ]
      exact (ih (by omega)).trans (Nat.le_add_right _ _)
    · rw [show i = j + 1 by omega]

/-- The unary bit count of a prefix of a polynomial-time word is polynomial-time: a counted
loop appending a token for each set bit (`polyTimeComputable_loopState'`, states of length
`countTrue ≤ N`). -/
theorem countTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true) :
    PolyTimeComputable fun z => List.replicate (countTrue (s z) (N z)) true := by
  let upd : List Bool → List Bool := fun w =>
    if (s (pairFstD w)).getD (pairFstD (pairSndD w)).length false then
      true :: pairSndD (pairSndD w) else pairSndD (pairSndD w)
  have hupd : PolyTimeComputable upd :=
    polyTimeComputable_ite
      (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (countTrue (s z) i) true := by
    intro z i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        countTrue_succ]
      cases (s z).getD i false <;> simp [List.replicate_succ]
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hN
    (PolyExpr.normal C c) fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact (countTrue_le _ _).trans (hi.trans (by simpa [PolyExpr.eval_normal] using hC z))
  convert h using 1
  funext z
  rw [hclosed]

/-! ### The `e`-th set bit -/

/-- The position of the `e`-th set bit (0-based) among the first `N` positions of `x`: the
least `j < N` whose bit is set and preceded by exactly `e` set bits, `N` if there is none. -/
noncomputable def nthTrue (x : List Bool) (N e : ℕ) : ℕ :=
  firstIdx (fun j => x.getD j false && decide (countTrue x j = e)) N

/-- The `e`-th set position in unary is polynomial-time (`polyTimeComputable_firstIdx` with
the test `bit j ∧ countTrue j = e` on `⟨1^j, z⟩`). -/
theorem nthTrue_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun z => List.replicate (N z) true)
    {e : List Bool → ℕ} (he : PolyTimeComputable fun z => List.replicate (e z) true) :
    PolyTimeComputable fun z => List.replicate (nthTrue (s z) (N z) (e z)) true :=
  polyTimeComputable_firstIdx
    (p := fun z j => (s z).getD j false && decide (countTrue (s z) j = e z))
    (polyTimeComputable_and
      (getBit_poly (hs.comp polyTimeComputable_pairSndD) (unaryLength_poly polyTimeComputable_pairFstD))
      (eqTest_poly
        (countTrue_poly (hs.comp polyTimeComputable_pairSndD)
          (unaryLength_poly polyTimeComputable_pairFstD))
        (he.comp polyTimeComputable_pairSndD)))
    hN

/-- Filtering `List.range (N + 1)` by the bits of `x` appends position `N` iff its bit is set. -/
theorem filter_range_succ (x : List Bool) (N : ℕ) :
    (List.range (N + 1)).filter (fun j => x.getD j false) =
      (List.range N).filter (fun j => x.getD j false) ++ (if x.getD N false then [N] else []) := by
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

/-- The filtered range has `countTrue x N` elements. -/
theorem length_filter_range (x : List Bool) (N : ℕ) :
    ((List.range N).filter (fun j => x.getD j false)).length = countTrue x N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [filter_range_succ, List.length_append, ih, countTrue_succ]
    cases x.getD N false <;> simp

/-- The `e`-th element of the filtered range is the set position `j` preceded by exactly `e`
set bits. -/
theorem getElem?_filter_range (x : List Bool) {N e j : ℕ} (hj : j < N)
    (hbit : x.getD j false = true) (hcnt : countTrue x j = e) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some j := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [filter_range_succ]
    rcases Nat.lt_or_ge j N with h | h
    · have hlt : e < countTrue x N := by
        have h1 := countTrue_mono x (Nat.succ_le_of_lt h)
        rw [countTrue_succ, hbit, hcnt] at h1
        simpa using h1
      rw [List.getElem?_append_left (by rw [length_filter_range]; exact hlt)]
      exact ih h
    · have hjN : j = N := by omega
      subst hjN
      rw [List.getElem?_append_right (by rw [length_filter_range, hcnt]),
        length_filter_range, hcnt, Nat.sub_self, if_pos hbit]
      rfl

/-- Every rank `e < countTrue x N` is realised by a set position below `N`. -/
theorem exists_nth_set (x : List Bool) :
    ∀ N e, e < countTrue x N → ∃ j < N, x.getD j false = true ∧ countTrue x j = e := by
  intro N
  induction N with
  | zero => intro e h; simp at h
  | succ N ih =>
    intro e he
    rcases Nat.lt_or_ge e (countTrue x N) with h | h
    · obtain ⟨j, hj, hb, hc⟩ := ih e h
      exact ⟨j, by omega, hb, hc⟩
    · rw [countTrue_succ] at he
      have hb : x.getD N false = true := by
        cases hx : x.getD N false
        · rw [hx] at he; simp at he; omega
        · rfl
      refine ⟨N, Nat.lt_succ_self N, hb, ?_⟩
      rw [hb] at he
      simp at he
      omega

/-- For `e < countTrue x N`, `nthTrue x N e` is below `N`, its bit is set, and exactly `e` set
bits precede it. -/
theorem nthTrue_spec (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    nthTrue x N e < N ∧ x.getD (nthTrue x N e) false = true ∧ countTrue x (nthTrue x N e) = e := by
  obtain ⟨j, hj, hb, hc⟩ := exists_nth_set x N e he
  have hlt : nthTrue x N e < N := by
    refine firstIdx_lt_iff.2 ⟨j, hj, ?_⟩
    rw [hb, hc]
    simp
  have hq := q_firstIdx (q := fun j => x.getD j false && decide (countTrue x j = e)) hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨hlt, hq.1, hq.2⟩

/-- The `e`-th element of the filtered range is `nthTrue x N e`. -/
theorem getElem?_filter_range_nthTrue (x : List Bool) {N e : ℕ} (he : e < countTrue x N) :
    ((List.range N).filter (fun j => x.getD j false))[e]? = some (nthTrue x N e) :=
  let h := nthTrue_spec x he
  getElem?_filter_range x h.1 h.2.1 h.2.2

/-! ### The numeric model of the edge list -/

/-- The row-major indices of the lexicographically ordered pairs `Fin m × Fin n` enumerate
`range (m n)`. -/
theorem flatMap_range_mul (n : ℕ) :
    ∀ m, (List.range m).flatMap (fun u => (List.range n).map (fun v => v + n * u)) =
      List.range (m * n)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul n m, List.flatMap_singleton,
      Nat.succ_mul, List.range_add]
    congr 1
    apply List.map_congr_left
    intro v _
    ring

/-- The indices `v + n u` of the lexicographically ordered pairs of `finRange n ×ˢ finRange n`
enumerate `range (n²)` (`finProdFinEquiv`). -/
theorem map_product_finRange (n : ℕ) :
    (List.finRange n ×ˢ List.finRange n).map
        (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      List.range (n * n) := by
  rw [← flatMap_range_mul n n]
  show (List.product (List.finRange n) (List.finRange n)).map _ = _
  unfold List.product
  rw [List.map_flatMap]
  conv_rhs => rw [← List.map_coe_finRange n, List.flatMap_map]
  congr 1
  funext u
  rw [List.map_map, List.map_map]
  congr 1

/-- **The numeric model of the edge list:** through the index `(u, v) ↦ v + n u` of
`finProdFinEquiv`, the lexicographically ordered edge list of a graph whose adjacency bit
`(u, v)` is bit `v + n u` of the word `x` is the increasing list of set positions `j < n²` of
`x` (`List.filter_map` and `map_product_finRange`). -/
theorem map_edgeList {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    (edgeList G).map (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)) =
      (List.range (n * n)).filter (fun j => x.getD j false) := by
  rw [← map_product_finRange, List.filter_map]
  unfold edgeList
  congr 1
  apply List.filter_congr
  rintro ⟨u, v⟩ _
  exact hG u v

/-- The number of edges is the number of set bits among the `n²` matrix positions. -/
theorem edgeCount_eq {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) :
    edgeCount G = countTrue x (n * n) := by
  have := congrArg List.length (map_edgeList G x hG)
  rwa [List.length_map, length_filter_range] at this

/-- The endpoints of the edge of index `e` are the quotient and remainder by `n` of the
`e`-th set position `nthTrue x (n²) e` of the adjacency word. -/
theorem edgeOf_val {n : ℕ} (G : Graph n) (x : List Bool)
    (hG : ∀ u v, G u v = x.getD (finProdFinEquiv (u, v)) false) (e : Fin (edgeCount G)) :
    ((edgeOf G e).1 : ℕ) = nthTrue x (n * n) e / n ∧
      ((edgeOf G e).2 : ℕ) = nthTrue x (n * n) e % n := by
  have he : (e : ℕ) < countTrue x (n * n) := by
    rw [← edgeCount_eq G x hG]
    exact e.isLt
  have h1 : ((edgeList G).map
      (fun p : Fin n × Fin n => ((finProdFinEquiv p : Fin (n * n)) : ℕ)))[(e : ℕ)]? =
      some ((finProdFinEquiv (edgeOf G e) : Fin (n * n)) : ℕ) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem e.isLt, Option.map_some]
    rfl
  rw [map_edgeList G x hG, getElem?_filter_range_nthTrue x he, Option.some.injEq,
    finProdFinEquiv_apply_val] at h1
  have hn : 0 < n := (edgeOf G e).1.pos
  have hv := (edgeOf G e).2.isLt
  constructor
  · rw [h1, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hv, zero_add]
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- The adjacency matrix of a graph decoded from `x` is the matrix read from `x` (the
hypothesis of `map_edgeList` for `decGraph`). -/
theorem decGraph_apply (x : List Bool) (u v : Fin (decGraph x).1) :
    (decGraph x).2 u v = x.getD (finProdFinEquiv (u, v)) false := rfl

/-- Re-encoding the graph decoded from `x` truncates `x` to its first `n²` bits, `n = √|x|`. -/
theorem encGraph_decGraph_eq_take (x : List Bool) :
    encGraph (decGraph x).2 = x.take ((decGraph x).1 * (decGraph x).1) := by
  apply List.ext_getElem
  · rw [length_encGraph, List.length_take,
      min_eq_left (show (decGraph x).1 * (decGraph x).1 ≤ x.length from Nat.sqrt_le _)]
  · intro i h1 h2
    have hi : i < x.length := by
      rw [List.length_take] at h2
      omega
    rw [List.getElem_take]
    simp only [encGraph, List.getElem_ofFn]
    show x.getD (finProdFinEquiv (finProdFinEquiv.symm ⟨i, _⟩)) false = x[i]
    rw [Equiv.apply_symm_apply, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]

/-! ### The numeric model of the samplers -/

/-- The number read (most significant bit first) from the `k` bits of `s` at positions
`b, …, b + k - 1` (default `false`): the loop value of `bitsToNat` on a tape window. -/
def natOfBits (s : List Bool) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * natOfBits s b j + (s.getD (b + j) false).toNat

@[simp] theorem natOfBits_zero (s : List Bool) (b : ℕ) : natOfBits s b 0 = 0 := rfl

@[simp] theorem natOfBits_succ (s : List Bool) (b j : ℕ) :
    natOfBits s b (j + 1) = 2 * natOfBits s b j + (s.getD (b + j) false).toNat := rfl

/-- A `k`-bit window reads as a number below `2^k`. -/
theorem natOfBits_lt (s : List Bool) (b : ℕ) : ∀ k, natOfBits s b k < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [natOfBits_succ, pow_succ]
    have := natOfBits_lt s b k
    have := Bool.toNat_le (s.getD (b + k) false)
    omega

/-- `bitsToNat` of a tape window is `natOfBits` (`List.ofFn_succ_last`, `List.foldl_append`). -/
theorem bitsToNat_eq_natOfBits (s : List Bool) (b : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => s.getD (b + j) false) = natOfBits s b k
  | 0 => rfl
  | k + 1 => by
    have ih := bitsToNat_eq_natOfBits s b k
    unfold bitsToNat at ih ⊢
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc]
    rw [ih, natOfBits_succ]
    show (2 * natOfBits s b k + if s.getD (b + k) false = true then 1 else 0) =
      2 * natOfBits s b k + (s.getD (b + k) false).toNat
    cases s.getD (b + k) false <;> rfl

/-- **Reading a window as a number is polynomial-time** when `2^k` is polynomially bounded:
a counted loop doubling the accumulator and adding the next bit (`polyTimeComputable_loopState'`,
states `1^{natOfBits} < 1^{2^k}`). -/
theorem natOfBits_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {b : List Bool → ℕ} (hb : PolyTimeComputable fun z => List.replicate (b z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (natOfBits (s z) (b z) (k z)) true := by
  let upd : List Bool → List Bool := fun w =>
    List.replicate (2 * (pairSndD (pairSndD w)).length +
      ((s (pairFstD w)).getD (b (pairFstD w) + (pairFstD (pairSndD w)).length) false).toNat) true
  have hupd : PolyTimeComputable upd :=
    unaryAdd_poly
      (unaryMul_poly (unaryConst_poly 2)
        (unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
      (unaryOfTest_poly (getBit_poly (hs.comp polyTimeComputable_pairFstD)
        (unaryAdd_poly (hb.comp polyTimeComputable_pairFstD)
          (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))))
  have hclosed : ∀ z i, loopState upd (fun _ => []) z i =
      List.replicate (natOfBits (s z) (b z) i) true := by
    intro z i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [loopState_succ, ih]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        natOfBits_succ]
  have h := polyTimeComputable_loopState' hupd (polyTimeComputable_const []) hk Bd
    fun z i hi => by
      rw [hclosed, List.length_replicate]
      exact ((natOfBits_lt _ _ _).le.trans (Nat.pow_le_pow_right (by norm_num) hi)).trans (hBd z)
  convert h using 1
  funext z
  rw [hclosed]

/-- `List.findSome?` over `finRange T` of a test-and-value function returns the value at the
first accepted index (`firstIdx`), `none` if no index below `T` is accepted. -/
theorem findSome?_finRange_eq {α : Type*} {T : ℕ} (f : Fin T → Option α) (q : ℕ → Bool)
    (v : ℕ → α) (hf : ∀ t : Fin T, f t = if q t then some (v t) else none) :
    (List.finRange T).findSome? f =
      if firstIdx q T < T then some (v (firstIdx q T)) else none := by
  by_cases h : firstIdx q T < T
  · rw [if_pos h, List.findSome?_eq_some_iff]
    refine ⟨(List.finRange T).take (firstIdx q T), ⟨firstIdx q T, h⟩,
      (List.finRange T).drop (firstIdx q T + 1), ?_, ?_, ?_⟩
    · conv_lhs => rw [← List.take_append_drop (firstIdx q T) (List.finRange T)]
      congr 1
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      simp
    · rw [hf, if_pos (q_firstIdx h)]
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 ha
      rw [hf]
      have hlt : ((List.finRange T)[i] : ℕ) < firstIdx q T := by
        simp only [List.getElem_finRange, Fin.cast_mk]
        exact lt_of_lt_of_le hi (min_le_left _ _)
      rw [if_neg (by simpa using firstIdx_min hlt)]
  · rw [if_neg h, List.findSome?_eq_none_iff]
    intro t _
    rw [hf]
    have hT : firstIdx q T = T := le_antisymm firstIdx_le (not_lt.1 h)
    rw [if_neg (by simpa using firstIdx_eq_iff.1 hT t t.isLt)]

/-- The index of the first accepted trial of `T` rejection trials of `k` bits on the tape `s`
(a value below `m` is accepted), `T` if none is accepted. -/
noncomputable def firstTrial (s : List Bool) (m k T : ℕ) : ℕ :=
  firstIdx (fun t => decide (natOfBits s (t * k) k < m)) T

/-- The value of the rejection sampler as a number, with default `d` on failure. -/
noncomputable def sampleVal (s : List Bool) (m k T d : ℕ) : ℕ :=
  if firstTrial s m k T < T then natOfBits s (firstTrial s m k T * k) k else d

/-- The rejection sampler of `Language.lean`, numerically: the value read at the first accepted
trial. -/
theorem map_val_sampleIdx (m k T : ℕ) (s : List Bool) :
    (sampleIdx m k T s).map Fin.val =
      if firstTrial s m k T < T then some (natOfBits s (firstTrial s m k T * k) k) else none := by
  unfold sampleIdx rejectionSample
  rw [List.map_findSome?]
  apply findSome?_finRange_eq (q := fun t => decide (natOfBits s (t * k) k < m))
    (v := fun t => natOfBits s (t * k) k)
  intro t
  simp only [Function.comp, uniformFromBits, bitsToNat_eq_natOfBits]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by simpa using h2)
  · exact absurd (by simpa using h2) h1
  · rfl

/-- The total rejection sampler with default `d` is `sampleVal`. -/
theorem map_val_sampleIdx_getD (m k T : ℕ) (s : List Bool) (d : ℕ) :
    ((sampleIdx m k T s).map Fin.val).getD d = sampleVal s m k T d := by
  rw [map_val_sampleIdx]
  unfold sampleVal
  split_ifs <;> rfl

/-- **The rejection sampler is polynomial-time** (in unary, when `2^k` is polynomially
bounded): the first accepted trial by `polyTimeComputable_firstIdx` with the window test
`natOfBits_poly`, then the value at that trial. -/
theorem sampleVal_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {m : List Bool → ℕ} (hm : PolyTimeComputable fun z => List.replicate (m z) true)
    {k : List Bool → ℕ} (hk : PolyTimeComputable fun z => List.replicate (k z) true)
    {T : List Bool → ℕ} (hT : PolyTimeComputable fun z => List.replicate (T z) true)
    {d : List Bool → ℕ} (hd : PolyTimeComputable fun z => List.replicate (d z) true)
    (Bd : PolyExpr) (hBd : ∀ z, 2 ^ k z ≤ Bd.eval z.length) :
    PolyTimeComputable fun z => List.replicate (sampleVal (s z) (m z) (k z) (T z) (d z)) true := by
  have hBd' : ∀ w : List Bool, 2 ^ k (pairSndD w) ≤ Bd.eval w.length := fun w =>
    (hBd _).trans (Bd.eval_mono
      ((Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le w)))
  have hwin : PolyTimeComputable fun w =>
      List.replicate (natOfBits (s (pairSndD w)) ((pairFstD w).length * k (pairSndD w))
        (k (pairSndD w))) true :=
    natOfBits_poly (hs.comp polyTimeComputable_pairSndD)
      (unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD)
        (hk.comp polyTimeComputable_pairSndD))
      (hk.comp polyTimeComputable_pairSndD) Bd hBd'
  have hfirst : PolyTimeComputable fun z =>
      List.replicate (firstTrial (s z) (m z) (k z) (T z)) true :=
    polyTimeComputable_firstIdx (p := fun z t => decide (natOfBits (s z) (t * k z) (k z) < m z))
      (ltTest_poly hwin (hm.comp polyTimeComputable_pairSndD)) hT
  have hval : PolyTimeComputable fun z =>
      List.replicate (natOfBits (s z) (firstTrial (s z) (m z) (k z) (T z) * k z) (k z)) true :=
    natOfBits_poly hs (unaryMul_poly hfirst hk) hk Bd hBd
  convert polyTimeComputable_ite (ltTest_poly hfirst hT) hval hd using 1
  funext z
  simp only [decide_eq_true_eq]
  unfold sampleVal
  split_ifs <;> rfl

/-! ### The colour permutation as a table -/

/-- The six-bit table of a colour permutation: the encodings of the images of the three
colours. -/
def permTable (σ : Equiv.Perm (Fin 3)) : List Bool :=
  encColor (σ 0) ++ encColor (σ 1) ++ encColor (σ 2)

/-- The table of the permutation of index `i < 6` under `perm3Equiv`, the identity's table for
`i ≥ 6` (the sampler's failure value). -/
noncomputable def tableOfIdx (i : ℕ) : List Bool :=
  if i = 0 then permTable (perm3Equiv 0) else if i = 1 then permTable (perm3Equiv 1) else
  if i = 2 then permTable (perm3Equiv 2) else if i = 3 then permTable (perm3Equiv 3) else
  if i = 4 then permTable (perm3Equiv 4) else if i = 5 then permTable (perm3Equiv 5) else
  permTable 1

/-- On the indices below `6` the table lookup is the table of `perm3Equiv`. -/
theorem tableOfIdx_perm3Equiv (i : Fin 6) : tableOfIdx i = permTable (perm3Equiv i) := by
  fin_cases i <;> simp [tableOfIdx]

/-- The honest prover's permutation table is the table lookup on the sampled index (default
`6`, the identity). -/
theorem permTable_samplePerm3 (T : ℕ) (s : List Bool) :
    permTable (samplePerm3 T s) = tableOfIdx (sampleVal s 6 3 T 6) := by
  rw [← map_val_sampleIdx_getD]
  unfold samplePerm3
  cases sampleIdx 6 3 T s with
  | none => simp [tableOfIdx]
  | some i =>
    simp only [Option.map_some, Option.getD_some]
    exact (tableOfIdx_perm3Equiv i).symm

/-- The table lookup is polynomial-time (seven constant tables selected by equality tests on
the unary index). -/
theorem tableOfIdx_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun z => List.replicate (f z) true) :
    PolyTimeComputable fun z => tableOfIdx (f z) := by
  have t : ∀ c : ℕ, PolyTimeComputable fun z => [decide (f z = c)] := fun c =>
    eqTest_poly hf (unaryConst_poly c)
  convert polyTimeComputable_ite (t 0) (polyTimeComputable_const (permTable (perm3Equiv 0)))
    (polyTimeComputable_ite (t 1) (polyTimeComputable_const (permTable (perm3Equiv 1)))
      (polyTimeComputable_ite (t 2) (polyTimeComputable_const (permTable (perm3Equiv 2)))
        (polyTimeComputable_ite (t 3) (polyTimeComputable_const (permTable (perm3Equiv 3)))
          (polyTimeComputable_ite (t 4) (polyTimeComputable_const (permTable (perm3Equiv 4)))
            (polyTimeComputable_ite (t 5) (polyTimeComputable_const (permTable (perm3Equiv 5)))
              (polyTimeComputable_const (permTable 1))))))) using 1
  funext z
  simp [tableOfIdx]

/-- The two bits of a table at colour `a`: bits `2a` and `2a + 1`. -/
def colorFromTable (tbl : List Bool) (a : ℕ) : List Bool :=
  [tbl.getD (2 * a) false, tbl.getD (2 * a + 1) false]

/-- The encoding of a colour, numerically: `[a / 2 = 1, a % 2 = 1]`. -/
theorem encColor_eq (a : Fin 3) : encColor a = [decide (a.val / 2 = 1), decide (a.val % 2 = 1)] := by
  fin_cases a <;> rfl

/-- Looking up colour `a` in the table of `σ` gives the encoding of `σ a`. -/
theorem colorFromTable_permTable (σ : Equiv.Perm (Fin 3)) (a : Fin 3) :
    colorFromTable (permTable σ) a = encColor (σ a) := by
  fin_cases a <;> simp [colorFromTable, permTable, encColor_eq]

/-- The table lookup of a colour is polynomial-time (two bit extractions). -/
theorem colorFromTable_poly {tbl : List Bool → List Bool} (htbl : PolyTimeComputable tbl)
    {a : List Bool → ℕ} (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => colorFromTable (tbl z) (a z) :=
  ptc_congr ((getBit_poly htbl (unaryMul_poly (unaryConst_poly 2) ha)).append
    (getBit_poly htbl (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) ha) (unaryConst_poly 1))))
    fun _ => rfl

/-! ### Colours as numbers -/

/-- The colour of vertex `u` read from an encoded colouring: `(2 b₀ + b₁) mod 3` from bits
`2u`, `2u + 1`. -/
def colorVal (y : List Bool) (u : ℕ) : ℕ :=
  (2 * (y.getD (2 * u) false).toNat + (y.getD (2 * u + 1) false).toNat) % 3

/-- `decColoring` numerically. -/
theorem decColoring_val (n : ℕ) (y : List Bool) (u : Fin n) :
    ((decColoring n y u : Fin 3) : ℕ) = colorVal y u := by
  have h0 : ((finProdFinEquiv (u, (0 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u := by
    rw [finProdFinEquiv_apply_val]
    simp
  have h1 : ((finProdFinEquiv (u, (1 : Fin 2)) : Fin (n * 2)) : ℕ) = 2 * u + 1 := by
    rw [finProdFinEquiv_apply_val]
    simp
    omega
  show (2 * (y.getD (finProdFinEquiv (u, (0 : Fin 2))) false).toNat +
    (y.getD (finProdFinEquiv (u, (1 : Fin 2))) false).toNat) % 3 = _
  rw [h0, h1]
  rfl

/-- `decColor` numerically. -/
theorem decColor_val (w : List Bool) : ((decColor w : Fin 3) : ℕ) = colorVal w 0 := by
  rw [decColor, decColoring_val]
  rfl

/-- The colour value of a vertex is polynomial-time in unary. -/
theorem colorVal_poly {y : List Bool → List Bool} (hy : PolyTimeComputable y)
    {u : List Bool → ℕ} (hu : PolyTimeComputable fun z => List.replicate (u z) true) :
    PolyTimeComputable fun z => List.replicate (colorVal (y z) (u z)) true := by
  have h2u := unaryMul_poly (unaryConst_poly 2) hu
  have h := modNum_poly
    (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) (unaryOfTest_poly (getBit_poly hy h2u)))
      (unaryOfTest_poly (getBit_poly hy (unaryAdd_poly h2u (unaryConst_poly 1)))))
    (unaryConst_poly 3)
  convert h using 1
  funext z
  rw [modNum_eq]
  rfl

/-- The encoding of a colour from its value: `[a / 2 = 1, a % 2 = 1]`. -/
def encColorOfVal (a : ℕ) : List Bool := [decide (a / 2 = 1), decide (a % 2 = 1)]

/-- `encColor` is `encColorOfVal` of the colour's value. -/
theorem encColor_eq_ofVal (a : Fin 3) : encColor a = encColorOfVal a := encColor_eq a

/-- The colour encoding from a unary value is polynomial-time. -/
theorem encColorOfVal_poly {a : List Bool → ℕ}
    (ha : PolyTimeComputable fun z => List.replicate (a z) true) :
    PolyTimeComputable fun z => encColorOfVal (a z) := by
  have h1 := eqTest_poly (divNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  have h2 := eqTest_poly (modNum_poly ha (unaryConst_poly 2)) (unaryConst_poly 1)
  convert h1.append h2 using 1
  funext z
  simp [encColorOfVal, divNum_eq, modNum_eq]

/-! ### Message encodings -/

/-- A pair is the pair with empty second component followed by the second component. -/
theorem pairEncode_eq_append_nil (a b : List Bool) : pairEncode a b = pairEncode a [] ++ b := by
  simp [pairEncode]

/-- An encoded message list is the concatenation of the self-delimiting messages
`pairEncode m []`. -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap (fun m => pairEncode m []) := by
  induction l with
  | nil => rfl
  | cons m h ih => rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih, pairEncode_eq_append_nil]

/-- `List.ofFn f` is the image of `range n` under any `ℕ`-indexed extension of `f`. -/
theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (F : ℕ → α)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) : List.ofFn f = (List.range n).map F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h i (by simpa using h1)

/-- The `i`-th second projection of an encoded history drops its first `i` messages. -/
theorem iterate_pairSndD_encodeMsgs (hist : List (List Bool)) :
    ∀ i, pairSndD^[i] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop i) := by
  intro i
  induction i generalizing hist with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases hist with
    | nil =>
      show pairSndD^[i] [] = []
      exact Function.iterate_fixed rfl i
    | cons m h => rw [Strategy.encodeMsgs_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- An encoded history is empty iff the history is. -/
theorem encodeMsgs_eq_nil_iff (hist : List (List Bool)) :
    Strategy.encodeMsgs hist = [] ↔ hist = [] := by
  cases hist with
  | nil => simp
  | cons m h => simp [pairEncode]

/-- A history is no longer than its encoding. -/
theorem length_le_length_encodeMsgs (hist : List (List Bool)) :
    hist.length ≤ (Strategy.encodeMsgs hist).length := by
  induction hist with
  | nil => exact le_rfl
  | cons m h ih =>
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons]
    omega

/-- The `i`-th message of a history (default `[]`) is the first projection after `i` second
projections of its encoding (`Strategy.pairFstD_encodeMsgs`). -/
theorem getD_eq_pairFstD_iterate (hist : List (List Bool)) (i : ℕ) :
    hist.getD i [] = pairFstD (pairSndD^[i] (Strategy.encodeMsgs hist)) := by
  rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD]

/-- The last message of a history (default `[]`) is its message of index `length - 1`. -/
theorem getLastD_eq_getD (hist : List (List Bool)) : hist.getLastD [] = hist.getD (hist.length - 1) [] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The number of messages of an encoded history: the number of second projections needed to
reach the empty word, searched below `|M| + 1`. -/
noncomputable def histLen (M : List Bool) : ℕ :=
  firstIdx (fun i => decide (pairSndD^[i] M = [])) (M.length + 1)

/-- `histLen` recovers the length of the history. -/
theorem histLen_encodeMsgs (hist : List (List Bool)) :
    histLen (Strategy.encodeMsgs hist) = hist.length := by
  unfold histLen
  apply firstIdx_eq_of
  · exact Nat.lt_succ_of_le (length_le_length_encodeMsgs hist)
  · rw [iterate_pairSndD_encodeMsgs, List.drop_length]
    simp
  · intro i hi
    rw [iterate_pairSndD_encodeMsgs, decide_eq_false_iff_not, encodeMsgs_eq_nil_iff,
      ← List.length_eq_zero_iff, List.length_drop]
    omega

/-- The message count of an encoded history is polynomial-time in unary. -/
theorem histLen_poly : PolyTimeComputable fun M => List.replicate (histLen M) true :=
  polyTimeComputable_firstIdx (p := fun M i => decide (pairSndD^[i] M = []))
    (isNil_poly.comp (iterSnd_poly polyTimeComputable_pairSndD
      (unaryLength_poly polyTimeComputable_pairFstD)))
    (unaryAdd_poly (unaryLength_poly polyTimeComputable_id) (unaryConst_poly 1))

/-- An encoded `ofFn` list is the concatenation of the self-delimiting messages
`pairEncode (F i) []` over `i < n`, for any `ℕ`-indexed extension `F` of `f`. -/
theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (f : Fin n → List Bool) (F : ℕ → List Bool)
    (h : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = F k) :
    Strategy.encodeMsgs (List.ofFn f) = (List.range n).flatMap (fun i => pairEncode (F i) []) := by
  rw [ofFn_eq_map_range f F h, encodeMsgs_eq_flatMap, List.flatMap_map]

/-- With at least one edge, `edgeAt G e` is the edge of index `e mod |E|`. -/
theorem edgeAt_eq_some_of_pos {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    edgeAt G e = some (edgeOf G ⟨e % edgeCount G, Nat.mod_lt _ hm⟩) := by
  unfold edgeAt
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hm)]
  rfl

end TCSlib.Cryptography.ColMachines

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the honest parties as string functions

The honest parties of [PS10, Protocol 127.5] as polynomial-time functions of the interactive
machine layout `⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`ColMachines.ilayout`), assembled from the
numeric models of `ThreeColoring/Machines.lean` and the unary FP toolkit of
`ZeroKnowledge/EncodingMachines.lean` (inventory item Inf-4.2 for Protocol 127.5):

* the one-iteration prover `proverStr` (commitment vector `commitStr`, opening `openStr`), the
  one-iteration verifier `verifierStr` (challenge `eOf`, check `checkStr`, verdict `verdictStr`),
  and the parties of the `n|E|`-fold protocol `proverRepStr`, `verifierRepStr`;
* their polynomial-time proofs (`proverStr_poly`, `verifierStr_poly`, `proverRepStr_poly`,
  `verifierRepStr_poly`), every number travelling in unary;
* the **layout lemmas** (`nOf_ilayout`, `mOf_ilayout`, `eOf_ilayout`, `commitStr_ilayout`,
  `openStr_ilayout`, …) that read the string functions on a layout `ilayout x z hist r` back
  as the typed operations of the strategies (`multiCom`, `samplePerm3`, `decColoring`,
  `sampleEdgeIdx`, `edgeOf`), which is what `ThreeColoring/ProtocolProofs.lean` uses to identify
  them with the next-message functions of `Protocol.lean`.

## Main results

* `TCSlib.Cryptography.ColMachines.proverStr_poly`, `ColMachines.verifierStr_poly`,
  `ColMachines.proverRepStr_poly`, `ColMachines.verifierRepStr_poly` — the parties are
  polynomial-time when `Com` is.
* `TCSlib.Cryptography.ColMachines.commitStr_ilayout`, `ColMachines.openStr_ilayout`,
  `ColMachines.eOf_ilayout`, `ColMachines.eRep_ilayout` — the layout lemmas.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColMachines

open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

/-! ### The honest parties as string functions -/

/-- Applying an index-parametrised polynomial-time function (polynomial-time in `⟨1^i, w⟩`) at
a unary index `f w` is polynomial-time. -/
theorem ptc_apply_unary {F : List Bool → ℕ → List Bool}
    (hF : PolyTimeComputable fun v => F (pairSndD v) (pairFstD v).length)
    {f : List Bool → ℕ} (hf : PolyTimeComputable fun w => List.replicate (f w) true) :
    PolyTimeComputable fun w => F w (f w) :=
  ptc_congr (hF.comp (hf.pairEncode polyTimeComputable_id)) fun w => by simp

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length :=
  (Nat.le_add_left _ _).trans (length_pairFstD_add_pairSndD_le z)

/-- The common input of a layout is no longer than the layout. -/
theorem length_argX_le (w : List Bool) : (argX w).length ≤ w.length :=
  (length_pairFstD_le _).trans ((length_pairFstD_le _).trans ((length_pairSndD_le _).trans
    ((length_pairFstD_le _).trans (length_pairFstD_le _))))

section Parties

variable (Com : List Bool → List Bool) (ℓ : PolyExpr)

/-- The vertex count `n = √|x|` read off the layout. -/
def nOf (w : List Bool) : ℕ := Nat.sqrt (argX w).length

/-- The randomness length `ℓ(n)` of the commitments. -/
def LOf (w : List Bool) : ℕ := ℓ.eval (nOf w)

/-- The number of (ordered) edges `|E| = countTrue x n²` read off the layout. -/
def mOf (w : List Bool) : ℕ := countTrue (argX w) (nOf w * nOf w)

/-- The prover's colour permutation as a table: the sampler on the first `3|x|` coins. -/
noncomputable def tblOf (w : List Bool) : List Bool :=
  tableOfIdx (sampleVal ((NUPPT.inCoins w).take (3 * (argX w).length)) 6 3 (argX w).length 6)

/-- The encoding of the permuted colour of vertex `i`. -/
noncomputable def colBits (w : List Bool) (i : ℕ) : List Bool :=
  colorFromTable (tblOf w) (colorVal (argZ w) i)

/-- The randomness block of vertex `i`: `ℓ(n)` coins after the first `3|x| + i ℓ(n)`. -/
def blk (w : List Bool) (i : ℕ) : List Bool :=
  padTo (LOf ℓ w) ((NUPPT.inCoins w).drop (3 * (argX w).length + i * LOf ℓ w))

/-- The commitment to the permuted colour of vertex `i`. -/
noncomputable def comAt (w : List Bool) (i : ℕ) : List Bool :=
  Com (pairEncode (padTo (nOf w) (colBits w i)) (blk ℓ w i))

/-- The prover's first message: the encoded list of the `n` commitments. -/
noncomputable def commitStr (w : List Bool) : List Bool :=
  (List.range (nOf w)).flatMap fun i => pairEncode (comAt Com ℓ w i) []

/-- The prover's opening of the edge named by the challenge (first received message). -/
noncomputable def openStr (w : List Bool) : List Bool :=
  let e := (pairFstD (argM w)).length % mOf w
  let j := nthTrue (argX w) (nOf w * nOf w) e
  pairEncode (pairEncode (colBits w (j / nOf w)) (blk ℓ w (j / nOf w)))
    (pairEncode (colBits w (j % nOf w)) (blk ℓ w (j % nOf w)))

/-- The honest prover of one iteration as a function of the layout. -/
noncomputable def proverStr (w : List Bool) : List Bool :=
  if argM w = [] then commitStr Com ℓ w else if mOf w = 0 then [] else openStr ℓ w

/-- The vertex count is polynomial-time in unary. -/
theorem nOf_poly : PolyTimeComputable fun w => List.replicate (nOf w) true :=
  unarySqrt_poly (unaryLength_poly argX_poly)

/-- The randomness length is polynomial-time in unary. -/
theorem LOf_poly : PolyTimeComputable fun w => List.replicate (LOf ℓ w) true :=
  unaryPolyOf_poly ℓ nOf_poly

/-- The edge count is polynomial-time in unary. -/
theorem mOf_poly : PolyTimeComputable fun w => List.replicate (mOf w) true :=
  countTrue_poly argX_poly (unaryMul_poly nOf_poly nOf_poly)

/-- The permutation table is polynomial-time. -/
theorem tblOf_poly : PolyTimeComputable tblOf := by
  have hr : PolyTimeComputable fun w => (NUPPT.inCoins w).take (3 * (argX w).length) :=
    ptc_congr ((polyTimeComputable_pairTakePoly (.mul (.const 3) .var)).comp
      (argX_poly.pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp
  exact tableOfIdx_poly (sampleVal_poly hr (unaryConst_poly 6) (unaryConst_poly 3)
    (unaryLength_poly argX_poly) (unaryConst_poly 6) (.const 8) fun _ => by simp)

/-- The permuted colour bits are polynomial-time in `⟨1^i, w⟩`. -/
theorem colBits_poly : PolyTimeComputable fun v => colBits (pairSndD v) (pairFstD v).length :=
  colorFromTable_poly (tblOf_poly.comp polyTimeComputable_pairSndD)
    (colorVal_poly (argZ_poly.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))

/-- The randomness blocks are polynomial-time in `⟨1^i, w⟩`. -/
theorem blk_poly : PolyTimeComputable fun v => blk ℓ (pairSndD v) (pairFstD v).length := by
  have hb : PolyTimeComputable fun v => List.replicate
      (3 * (argX (pairSndD v)).length + (pairFstD v).length * LOf ℓ (pairSndD v)) true :=
    unaryAdd_poly
      (unaryMul_poly (unaryConst_poly 3) (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD)))
      (unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD)
        ((LOf_poly ℓ).comp polyTimeComputable_pairSndD))
  have hdrop : PolyTimeComputable fun v => (NUPPT.inCoins (pairSndD v)).drop
      (3 * (argX (pairSndD v)).length + (pairFstD v).length * LOf ℓ (pairSndD v)) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      (hb.pairEncode (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD)))
      fun v => by simp
  exact padTo_poly hdrop ((LOf_poly ℓ).comp polyTimeComputable_pairSndD)

/-- The commitments are polynomial-time in `⟨1^i, w⟩` when `Com` is. -/
theorem comAt_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun v => comAt Com ℓ (pairSndD v) (pairFstD v).length :=
  hCom.comp ((padTo_poly colBits_poly (nOf_poly.comp polyTimeComputable_pairSndD)).pairEncode
    (blk_poly ℓ))

/-- The prover's first message is polynomial-time (`polyTimeComputable_flatMap_range`). -/
theorem commitStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (commitStr Com ℓ) :=
  polyTimeComputable_flatMap_range (E := fun w i => pairEncode (comAt Com ℓ w i) [])
    ((comAt_poly Com ℓ hCom).pairEncode (polyTimeComputable_const [])) nOf_poly

/-- The prover's opening is polynomial-time. -/
theorem openStr_poly : PolyTimeComputable (openStr ℓ) := by
  have he : PolyTimeComputable fun w => List.replicate ((pairFstD (argM w)).length % mOf w) true := by
    simpa only [modNum_eq] using
      modNum_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp argM_poly)) mOf_poly
  have hj := nthTrue_poly argX_poly (unaryMul_poly nOf_poly nOf_poly) he
  have hu : PolyTimeComputable fun w => List.replicate
      (nthTrue (argX w) (nOf w * nOf w) ((pairFstD (argM w)).length % mOf w) / nOf w) true := by
    simpa only [divNum_eq] using divNum_poly hj nOf_poly
  have hv : PolyTimeComputable fun w => List.replicate
      (nthTrue (argX w) (nOf w * nOf w) ((pairFstD (argM w)).length % mOf w) % nOf w) true := by
    simpa only [modNum_eq] using modNum_poly hj nOf_poly
  exact ((ptc_apply_unary colBits_poly hu).pairEncode (ptc_apply_unary (blk_poly ℓ) hu)).pairEncode
    ((ptc_apply_unary colBits_poly hv).pairEncode (ptc_apply_unary (blk_poly ℓ) hv))

/-- The honest prover of one iteration is polynomial-time when `Com` is. -/
theorem proverStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (proverStr Com ℓ) := by
  have h := polyTimeComputable_ite (isNil_poly.comp argM_poly) (commitStr_poly Com ℓ hCom)
    (polyTimeComputable_ite (eqTest_poly mOf_poly (unaryConst_poly 0)) (polyTimeComputable_const [])
      (openStr_poly ℓ))
  exact ptc_congr h fun w => by simp only [proverStr, decide_eq_true_eq, Function.comp_apply]

/-- The verifier's challenge: the rejection-sampled edge index on its tape. -/
noncomputable def eOf (w : List Bool) : ℕ :=
  sampleVal (NUPPT.inCoins w) (mOf w) (Nat.size (mOf w)) (argX w).length 0

/-- The challenge is polynomial-time in unary (`2^{size |E|} ≤ 2|E| + 1 ≤ 2|w| + 1`). -/
theorem eOf_poly : PolyTimeComputable fun w => List.replicate (eOf w) true :=
  sampleVal_poly NUPPT.polyTimeComputable_inCoins mOf_poly (unarySize_poly mOf_poly)
    (unaryLength_poly argX_poly) (unaryConst_poly 0) (.add (.mul (.const 2) .var) (.const 1))
    fun w => by
      have h1 := two_pow_size_le_two_mul_succ (mOf w)
      have h2 : mOf w ≤ w.length :=
        (countTrue_le _ _).trans ((Nat.sqrt_le _).trans (length_argX_le w))
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega

/-- The verifier's check of one iteration on the words `x`, `com`, `opn`, the challenge `e`, the
randomness length `L`, the vertex count `n` and the edge count `m`: the openings have randomness
of length `L`, both match the commitments at the endpoints of the `(e mod m)`-th edge, and the
two colours differ. -/
noncomputable def checkStr (L n m : ℕ) (x com opn : List Bool) (e : ℕ) : Bool :=
  let j := nthTrue x (n * n) (e % m)
  let a := colorVal (pairFstD (pairFstD opn)) 0
  let ri := pairSndD (pairFstD opn)
  let b := colorVal (pairFstD (pairSndD opn)) 0
  let rj := pairSndD (pairSndD opn)
  decide (ri.length = L ∧ rj.length = L ∧
    Com (pairEncode (padTo n (encColorOfVal a)) ri) = pairFstD (pairSndD^[j / n] com) ∧
    Com (pairEncode (padTo n (encColorOfVal b)) rj) = pairFstD (pairSndD^[j % n] com) ∧ a ≠ b)

/-- The check is polynomial-time in its (polynomial-time, unary) components. -/
theorem checkStr_poly (hCom : PolyTimeComputable Com)
    {L n m : List Bool → ℕ} (hL : PolyTimeComputable fun w => List.replicate (L w) true)
    (hn : PolyTimeComputable fun w => List.replicate (n w) true)
    (hm : PolyTimeComputable fun w => List.replicate (m w) true)
    {x com opn : List Bool → List Bool} (hx : PolyTimeComputable x) (hcom : PolyTimeComputable com)
    (hopn : PolyTimeComputable opn)
    {e : List Bool → ℕ} (he : PolyTimeComputable fun w => List.replicate (e w) true) :
    PolyTimeComputable fun w => [checkStr Com (L w) (n w) (m w) (x w) (com w) (opn w) (e w)] := by
  have hem : PolyTimeComputable fun w => List.replicate (e w % m w) true := by
    simpa only [modNum_eq] using modNum_poly he hm
  have hj := nthTrue_poly hx (unaryMul_poly hn hn) hem
  have hu : PolyTimeComputable fun w =>
      List.replicate (nthTrue (x w) (n w * n w) (e w % m w) / n w) true := by
    simpa only [divNum_eq] using divNum_poly hj hn
  have hv : PolyTimeComputable fun w =>
      List.replicate (nthTrue (x w) (n w * n w) (e w % m w) % n w) true := by
    simpa only [modNum_eq] using modNum_poly hj hn
  have ha := colorVal_poly (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp hopn))
    (unaryConst_poly 0)
  have hb := colorVal_poly (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hopn))
    (unaryConst_poly 0)
  have hri := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hopn)
  have hrj := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hopn)
  have t1 := eqTest_poly (unaryLength_poly hri) hL
  have t2 := eqTest_poly (unaryLength_poly hrj) hL
  have t3 := polyTimeComputable_pairEq.comp
    ((hCom.comp ((padTo_poly (encColorOfVal_poly ha) hn).pairEncode hri)).pairEncode
      (polyTimeComputable_pairFstD.comp (iterSnd_poly hcom hu)))
  have t4 := polyTimeComputable_pairEq.comp
    ((hCom.comp ((padTo_poly (encColorOfVal_poly hb) hn).pairEncode hrj)).pairEncode
      (polyTimeComputable_pairFstD.comp (iterSnd_poly hcom hv)))
  have t5 := not_poly (eqTest_poly ha hb)
  have h := polyTimeComputable_and t1 (polyTimeComputable_and t2
    (polyTimeComputable_and t3 (polyTimeComputable_and t4 t5)))
  convert h using 1
  funext w
  simp only [checkStr, Bool.decide_and, decide_not, pairFstD_pairEncode, pairSndD_pairEncode,
    Function.comp_apply]

/-- The verifier's verdict: well-formedness, and either no edges or `n ≥ 2` with the check. -/
noncomputable def verdictStr (w : List Bool) : Bool :=
  decide (argX w = (argX w).take (nOf w * nOf w)) &&
    (decide (mOf w = 0) || (decide (2 ≤ nOf w) &&
      checkStr Com (LOf ℓ w) (nOf w) (mOf w) (argX w) (pairFstD (argM w))
        (pairFstD (pairSndD (argM w))) (eOf w)))

/-- The verdict is polynomial-time when `Com` is. -/
theorem verdictStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun w => [verdictStr Com ℓ w] := by
  have hwf : PolyTimeComputable fun w => [decide (argX w = (argX w).take (nOf w * nOf w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      (argX_poly.pairEncode (truncate_poly argX_poly (unaryMul_poly nOf_poly nOf_poly))))
      fun w => by simp
  exact polyTimeComputable_and hwf (or_poly (eqTest_poly mOf_poly (unaryConst_poly 0))
    (polyTimeComputable_and (leTest_poly (unaryConst_poly 2) nOf_poly)
      (checkStr_poly Com hCom (LOf_poly ℓ) nOf_poly mOf_poly argX_poly
        (polyTimeComputable_pairFstD.comp argM_poly)
        (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp argM_poly)) eOf_poly)))

/-- The verifier of one iteration as a function of the layout: `[false]` on the empty history,
the unary challenge after the commitments, the verdict after the openings, `[false]` later. -/
noncomputable def verifierStr (w : List Bool) : List Bool :=
  if argM w = [] then [false]
  else if pairSndD (argM w) = [] then List.replicate (eOf w) true
  else if pairSndD (pairSndD (argM w)) = [] then [verdictStr Com ℓ w]
  else [false]

/-- The verifier of one iteration is polynomial-time when `Com` is. -/
theorem verifierStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (verifierStr Com ℓ) := by
  have h := polyTimeComputable_ite (isNil_poly.comp argM_poly) (polyTimeComputable_const [false])
    (polyTimeComputable_ite (isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)) eOf_poly
      (polyTimeComputable_ite
        (isNil_poly.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp argM_poly)))
        (verdictStr_poly Com ℓ hCom) (polyTimeComputable_const [false])))
  exact ptc_congr h fun w => by simp only [verifierStr, decide_eq_true_eq, Function.comp_apply]

/-- The number of coins of one iteration of the prover at common-input length `N`:
`3N + N ℓ(N)`. -/
def proverCoinsOf (N : ℕ) : ℕ := 3 * N + N * ℓ.eval N

/-- The prover of the repeated protocol as a function of the layout: iteration
`t = |hist| / 2` runs the one-iteration prover on the `t`-th coin block and on the history
`[]` or `[last message]` according to the parity of `|hist|`. -/
noncomputable def proverRepStr (w : List Bool) : List Bool :=
  let h := histLen (argM w)
  let c := proverCoinsOf ℓ (argX w).length
  if h / 2 < nOf w * mOf w then
    proverStr Com ℓ (NUPPT.layout (List.replicate (argX w).length true)
      (pairEncode (pairEncode (argX w) (argZ w))
        (if h % 2 = 0 then [] else pairEncode (pairFstD (pairSndD^[h - 1] (argM w))) []))
      [] (((NUPPT.inCoins w).drop (h / 2 * c)).take c))
  else []

/-- The prover of the repeated protocol is polynomial-time when `Com` is. -/
theorem proverRepStr_poly (hCom : PolyTimeComputable Com) : PolyTimeComputable (proverRepStr Com ℓ) := by
  have hh := histLen_poly.comp argM_poly
  have ht : PolyTimeComputable fun w => List.replicate (histLen (argM w) / 2) true := by
    simpa only [divNum_eq] using divNum_poly hh (unaryConst_poly 2)
  have hpar : PolyTimeComputable fun w => [decide (histLen (argM w) % 2 = 0)] := by
    simpa only [modNum_eq] using eqTest_poly (modNum_poly hh (unaryConst_poly 2)) (unaryConst_poly 0)
  have hxl := unaryLength_poly argX_poly
  have hc : PolyTimeComputable fun w => List.replicate (proverCoinsOf ℓ (argX w).length) true :=
    unaryAdd_poly (unaryMul_poly (unaryConst_poly 3) hxl) (unaryMul_poly hxl (unaryPolyOf_poly ℓ hxl))
  have hdrop : PolyTimeComputable fun w =>
      (NUPPT.inCoins w).drop (histLen (argM w) / 2 * proverCoinsOf ℓ (argX w).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly ht hc).pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp
  have hslice := truncate_poly hdrop hc
  have hlast : PolyTimeComputable fun w => pairFstD (pairSndD^[histLen (argM w) - 1] (argM w)) :=
    polyTimeComputable_pairFstD.comp (iterSnd_poly argM_poly (unarySub_poly hh (unaryConst_poly 1)))
  have hM := polyTimeComputable_ite hpar (polyTimeComputable_const [])
    (hlast.pairEncode (polyTimeComputable_const []))
  have hlay := NUPPT.polyTimeComputable_layout hxl ((argX_poly.pairEncode argZ_poly).pairEncode hM)
    (polyTimeComputable_const []) hslice
  have h := polyTimeComputable_ite (ltTest_poly ht (unaryMul_poly nOf_poly mOf_poly))
    (ptc_comp (proverStr_poly Com ℓ hCom) hlay) (polyTimeComputable_const [])
  exact ptc_congr h fun w => by simp only [proverRepStr, decide_eq_true_eq]

/-- The challenge of iteration `t` of the repeated verifier: the sampler on the `t`-th block of
`(|x| + 1)²` coins. -/
noncomputable def eRep (w : List Bool) (t : ℕ) : ℕ :=
  sampleVal (((NUPPT.inCoins w).drop (t * ((argX w).length + 1) ^ 2)).take (((argX w).length + 1) ^ 2))
    (mOf w) (Nat.size (mOf w)) (argX w).length 0

/-- The challenges of the repeated verifier are polynomial-time in `⟨1^t, w⟩`. -/
theorem eRep_poly : PolyTimeComputable fun v => List.replicate (eRep (pairSndD v) (pairFstD v).length) true := by
  have hB : PolyTimeComputable fun v => List.replicate (((argX (pairSndD v)).length + 1) ^ 2) true :=
    unaryPolyOf_poly (.pow (.add .var (.const 1)) 2)
      (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD))
  have hdrop : PolyTimeComputable fun v => (NUPPT.inCoins (pairSndD v)).drop
      ((pairFstD v).length * ((argX (pairSndD v)).length + 1) ^ 2) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly (unaryLength_poly polyTimeComputable_pairFstD) hB).pairEncode
        (NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD))) fun v => by simp
  have hm := mOf_poly.comp polyTimeComputable_pairSndD
  exact sampleVal_poly (truncate_poly hdrop hB) hm (unarySize_poly hm)
    (unaryLength_poly (argX_poly.comp polyTimeComputable_pairSndD)) (unaryConst_poly 0)
    (.add (.mul (.const 2) .var) (.const 1)) fun v => by
      have h1 := two_pow_size_le_two_mul_succ (mOf (pairSndD v))
      have h2 : mOf (pairSndD v) ≤ v.length :=
        (countTrue_le _ _).trans ((Nat.sqrt_le _).trans
          ((length_argX_le _).trans (length_pairSndD_le v)))
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega

/-- The check of iteration `t` of the repeated verifier on messages `2t`, `2t + 1`. -/
noncomputable def checkRep (w : List Bool) (t : ℕ) : Bool :=
  checkStr Com (LOf ℓ w) (nOf w) (mOf w) (argX w) (pairFstD (pairSndD^[2 * t] (argM w)))
    (pairFstD (pairSndD^[2 * t + 1] (argM w))) (eRep w t)

/-- The iteration checks are polynomial-time in `⟨1^t, w⟩` when `Com` is. -/
theorem checkRep_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun v => [checkRep Com ℓ (pairSndD v) (pairFstD v).length] := by
  have h2t := unaryMul_poly (unaryConst_poly 2) (unaryLength_poly polyTimeComputable_pairFstD)
  exact checkStr_poly Com hCom ((LOf_poly ℓ).comp polyTimeComputable_pairSndD)
    (nOf_poly.comp polyTimeComputable_pairSndD) (mOf_poly.comp polyTimeComputable_pairSndD)
    (argX_poly.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_pairFstD.comp (iterSnd_poly (argM_poly.comp polyTimeComputable_pairSndD) h2t))
    (polyTimeComputable_pairFstD.comp (iterSnd_poly (argM_poly.comp polyTimeComputable_pairSndD)
      (unaryAdd_poly h2t (unaryConst_poly 1))))
    eRep_poly

/-- The verdict of the repeated verifier: well-formedness, and either no edges or `n ≥ 2` with
every one of the `n|E|` iteration checks passing (no failing iteration below `n|E|`). -/
noncomputable def verdictRepStr (w : List Bool) : Bool :=
  decide (argX w = (argX w).take (nOf w * nOf w)) &&
    (decide (mOf w = 0) || (decide (2 ≤ nOf w) &&
      decide (firstIdx (fun t => !checkRep Com ℓ w t) (nOf w * mOf w) = nOf w * mOf w)))

/-- The repeated verdict is polynomial-time when `Com` is. -/
theorem verdictRepStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable fun w => [verdictRepStr Com ℓ w] := by
  have hwf : PolyTimeComputable fun w => [decide (argX w = (argX w).take (nOf w * nOf w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      (argX_poly.pairEncode (truncate_poly argX_poly (unaryMul_poly nOf_poly nOf_poly))))
      fun w => by simp
  have hN := unaryMul_poly nOf_poly mOf_poly
  have hfirst := polyTimeComputable_firstIdx (p := fun w t => !checkRep Com ℓ w t)
    (not_poly (checkRep_poly Com ℓ hCom)) hN
  exact polyTimeComputable_and hwf (or_poly (eqTest_poly mOf_poly (unaryConst_poly 0))
    (polyTimeComputable_and (leTest_poly (unaryConst_poly 2) nOf_poly) (eqTest_poly hfirst hN)))

/-- The verifier of the repeated protocol as a function of the layout. -/
noncomputable def verifierRepStr (w : List Bool) : List Bool :=
  let h := histLen (argM w)
  if h % 2 = 1 then (if h / 2 < nOf w * mOf w then List.replicate (eRep w (h / 2)) true else [])
  else if h = 2 * ((argX w).length * (argX w).length) then [verdictRepStr Com ℓ w]
  else []

/-- The verifier of the repeated protocol is polynomial-time when `Com` is. -/
theorem verifierRepStr_poly (hCom : PolyTimeComputable Com) :
    PolyTimeComputable (verifierRepStr Com ℓ) := by
  have hh := histLen_poly.comp argM_poly
  have ht : PolyTimeComputable fun w => List.replicate (histLen (argM w) / 2) true := by
    simpa only [divNum_eq] using divNum_poly hh (unaryConst_poly 2)
  have hpar : PolyTimeComputable fun w => [decide (histLen (argM w) % 2 = 1)] := by
    simpa only [modNum_eq] using eqTest_poly (modNum_poly hh (unaryConst_poly 2)) (unaryConst_poly 1)
  have hxl := unaryLength_poly argX_poly
  have hfull := eqTest_poly hh (unaryMul_poly (unaryConst_poly 2) (unaryMul_poly hxl hxl))
  have hchal := ptc_apply_unary (F := fun w t => List.replicate (eRep w t) true) eRep_poly ht
  have h := polyTimeComputable_ite hpar
    (polyTimeComputable_ite (ltTest_poly ht (unaryMul_poly nOf_poly mOf_poly)) hchal
      (polyTimeComputable_const []))
    (polyTimeComputable_ite hfull (verdictRepStr_poly Com ℓ hCom) (polyTimeComputable_const []))
  exact ptc_congr h fun w => by simp only [verifierRepStr, decide_eq_true_eq]

/-! ### The string functions on the interactive layout -/

section Layout

variable (x y z r : List Bool) (hist : List (List Bool))

/-- The vertex count read off a layout. -/
theorem nOf_ilayout : nOf (ilayout x z hist r) = (decGraph x).1 := by
  show Nat.sqrt (argX (ilayout x z hist r)).length = _
  rw [argX_ilayout]
  rfl

/-- The edge count read off a layout. -/
theorem mOf_ilayout : mOf (ilayout x z hist r) = edgeCount (decGraph x).2 := by
  show countTrue (argX (ilayout x z hist r)) (nOf (ilayout x z hist r) * nOf (ilayout x z hist r)) = _
  rw [argX_ilayout, nOf_ilayout, edgeCount_eq (decGraph x).2 x (decGraph_apply x)]

/-- The randomness length read off a layout. -/
theorem LOf_ilayout : LOf ℓ (ilayout x z hist r) = ℓ.eval (decGraph x).1 := by
  show ℓ.eval (nOf (ilayout x z hist r)) = _
  rw [nOf_ilayout]

/-- The verifier's challenge read off a layout is the edge sampler on its tape. -/
theorem eOf_ilayout :
    eOf (ilayout x z hist r) = sampleEdgeIdx (edgeCount (decGraph x).2) x.length r := by
  show sampleVal (NUPPT.inCoins (ilayout x z hist r)) (mOf (ilayout x z hist r))
    (Nat.size (mOf (ilayout x z hist r))) (argX (ilayout x z hist r)).length 0 = _
  rw [inCoins_ilayout, mOf_ilayout, argX_ilayout, sampleEdgeIdx, map_val_sampleIdx_getD]

/-- The challenge of iteration `t` of the repeated verifier read off a layout. -/
theorem eRep_ilayout (t : ℕ) : eRep (ilayout x z hist r) t =
    sampleEdgeIdx (edgeCount (decGraph x).2) x.length
      ((r.drop (t * (x.length + 1) ^ 2)).take ((x.length + 1) ^ 2)) := by
  show sampleVal (((NUPPT.inCoins (ilayout x z hist r)).drop
      (t * ((argX (ilayout x z hist r)).length + 1) ^ 2)).take
        (((argX (ilayout x z hist r)).length + 1) ^ 2))
    (mOf (ilayout x z hist r)) (Nat.size (mOf (ilayout x z hist r)))
    (argX (ilayout x z hist r)).length 0 = _
  rw [inCoins_ilayout, mOf_ilayout, argX_ilayout, sampleEdgeIdx, map_val_sampleIdx_getD]

/-- The permutation table read off a layout is the table of the sampled permutation. -/
theorem tblOf_ilayout :
    tblOf (ilayout x z hist r) = permTable (samplePerm3 x.length (r.take (3 * x.length))) := by
  show tableOfIdx (sampleVal ((NUPPT.inCoins (ilayout x z hist r)).take
    (3 * (argX (ilayout x z hist r)).length)) 6 3 (argX (ilayout x z hist r)).length 6) = _
  rw [inCoins_ilayout, argX_ilayout, permTable_samplePerm3]

/-- The permuted colour bits of vertex `i` read off a layout. -/
theorem colBits_ilayout (i : Fin (decGraph x).1) :
    colBits (ilayout x y hist r) i =
      encColor (samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i)) := by
  show colorFromTable (tblOf (ilayout x y hist r)) (colorVal (argZ (ilayout x y hist r)) i) = _
  rw [tblOf_ilayout, argZ_ilayout, ← decColoring_val, colorFromTable_permTable]

/-- The randomness block of vertex `i` read off a layout. -/
theorem blk_ilayout (i : Fin (decGraph x).1) :
    blk ℓ (ilayout x y hist r) i = List.ofFn (fun j : Fin (ℓ.eval (decGraph x).1) =>
      r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) := by
  show padTo (LOf ℓ (ilayout x y hist r)) ((NUPPT.inCoins (ilayout x y hist r)).drop
    (3 * (argX (ilayout x y hist r)).length + i * LOf ℓ (ilayout x y hist r))) = _
  rw [LOf_ilayout, inCoins_ilayout, argX_ilayout, ofFn_getD_add]

/-- The commitment of vertex `k` read off a layout. -/
theorem comAt_ilayout (k : ℕ) (hk : k < (decGraph x).1) :
    comAt Com ℓ (ilayout x y hist r) k = Com (pairEncode
      (List.ofFn (padColor (decGraph x).1 (samplePerm3 x.length (r.take (3 * x.length))
        (decColoring (decGraph x).1 y ⟨k, hk⟩))))
      (List.ofFn (fun j : Fin (ℓ.eval (decGraph x).1) =>
        r.getD (3 * x.length + k * ℓ.eval (decGraph x).1 + j) false))) := by
  show Com (pairEncode (padTo (nOf (ilayout x y hist r)) (colBits (ilayout x y hist r) k))
    (blk ℓ (ilayout x y hist r) k)) = _
  rw [nOf_ilayout,
    show colBits (ilayout x y hist r) k = colBits (ilayout x y hist r) ↑(⟨k, hk⟩ : Fin _) from rfl,
    colBits_ilayout,
    show blk ℓ (ilayout x y hist r) k = blk ℓ (ilayout x y hist r) ↑(⟨k, hk⟩ : Fin _) from rfl,
    blk_ilayout, padColor, ofFn_padFin]

/-- The prover's first message read off a layout is the commitment vector `multiCom`. -/
theorem commitStr_ilayout :
    commitStr Com ℓ (ilayout x y hist r) = multiCom Com
      (fun i => padColor (decGraph x).1 (samplePerm3 x.length (r.take (3 * x.length))
        (decColoring (decGraph x).1 y i)))
      (fun (i : Fin (decGraph x).1) (j : Fin (ℓ.eval (decGraph x).1)) =>
        r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) := by
  show (List.range (nOf (ilayout x y hist r))).flatMap
    (fun i => pairEncode (comAt Com ℓ (ilayout x y hist r) i) []) = _
  rw [nOf_ilayout, multiCom,
    encodeMsgs_ofFn_eq_flatMap _ (fun i => comAt Com ℓ (ilayout x y hist r) i)]
  intro k hk
  rw [comAt_ilayout Com ℓ x y r hist k hk]

/-- The prover's opening read off a layout (first received message `w`, at least one edge). -/
theorem openStr_ilayout (w : List Bool) (hm : 0 < edgeCount (decGraph x).2) :
    openStr ℓ (ilayout x y (w :: hist) r) =
      let p := edgeOf (decGraph x).2 ⟨w.length % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
      let c' := fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i)
      let rr := fun (i : Fin (decGraph x).1) (j : Fin (ℓ.eval (decGraph x).1)) =>
        r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false
      pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (rr p.1)))
        (pairEncode (encColor (c' p.2)) (List.ofFn (rr p.2))) := by
  obtain ⟨h1, h2⟩ := edgeOf_val (decGraph x).2 x (decGraph_apply x)
    ⟨w.length % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
  show pairEncode (pairEncode (colBits (ilayout x y (w :: hist) r) _)
      (blk ℓ (ilayout x y (w :: hist) r) _))
    (pairEncode (colBits (ilayout x y (w :: hist) r) _) (blk ℓ (ilayout x y (w :: hist) r) _)) = _
  simp only [argM_ilayout, Strategy.encodeMsgs_cons, pairFstD_pairEncode, mOf_ilayout, nOf_ilayout,
    argX_ilayout]
  rw [← h1, ← h2, colBits_ilayout, colBits_ilayout, blk_ilayout, blk_ilayout]

end Layout

end Parties

end TCSlib.Cryptography.ColMachines

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the protocol, completeness and soundness

The protocol of [PS10, Protocol 127.5] for the language `3COL` of `ThreeColoring/Language.lean`
(Def-124.f), built on a commitment scheme
`(Com, ℓ)` of `Commitment.lean`, and the completeness and soundness halves of
[PS10, Proposition 127.6]: one iteration (soundness error `1 - 1/|E|`) and the `n|E|`-fold
sequential repetition (soundness error `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`, Claim-125.a). The
zero-knowledge half is `ThreeColoring/Simulator.lean`; the machine infrastructure behind the
efficiency theorems (the parties as polynomial-time string functions of the interactive
layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`.

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours; the edges
are enumerated by `edgeList` and the verifier's challenge is the index of an edge in that
list, sent in unary. The prover commits to the colour `π (c i)` of every vertex, padded to an
`n`-bit value (`padColor`, DQ4), with `n` the number of vertices as the security parameter of
the commitment.

**Deviations** ([PS10, Protocol 127.5], source errors 41–43 of the plan):
* the verifier checks the two openings against the commitments (the text's "`V` accepts iff
  `c'_i ≠ c'_j`" is unsound without it) and the lengths of the opening randomness;
* if `E = ∅` the verifier accepts outright (every edgeless graph is 3-colourable; the text's
  "random edge" is undefined), and if `E ≠ ∅` but the graph has fewer than two vertices (so
  the edge is a loop and the graph is not colourable) it rejects outright, which is what makes
  the `n`-bit padding of the colours injective in every case that matters;
* colours are padded to `n` bits (DQ4; the text commits to 2-bit colours, i.e. at security
  parameter `2`);
* the witness is `c₁, …, c_n` (the text lists `c₀, …, c_m`), and the protocol is repeated
  `n|E|` times (the text's proof says `|E|²`);
* (D8, D10) the colour permutation `π ← S₃` and the edge `e ← E` are rejection-sampled from
  the parties' bit tapes with `|x|` trials, so the theorems carry the statistical terms
  `(1/4)^{|x|}` and `(1/2)^{|x|}`; the repeated protocol runs `4|x|²` fixed moves of which the
  first `4 n|E|` are the iterations and the rest are empty messages;
* (run-3 audit P11-3) `Graph n` is an arbitrary Boolean relation and `E` is the list of
  ordered pairs `(u, v)` with `G u v` (`edgeList`, loops included), so for the text's
  symmetric loopless graph `edgeCount G = 2|E|`: the per-iteration soundness error
  `1 - 1/edgeCount G` is `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|`
  times; the challenge is uniform over the ordered pairs, i.e. over the text's undirected
  edges, and `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. In this file `|E|` abbreviates
  `edgeCount G`.

## Main definitions

* `TCSlib.Cryptography.colCommit`,
  `TCSlib.Cryptography.colOpen`, `TCSlib.Cryptography.colVerify` — the commitment message,
  the opening message and the verifier's check of one iteration.
* `TCSlib.Cryptography.colProver`, `TCSlib.Cryptography.colVerifier`,
  `TCSlib.Cryptography.colProtocol` — one iteration of [PS10, Protocol 127.5];
  `TCSlib.Cryptography.colProverRep`, `TCSlib.Cryptography.colVerifierRep`,
  `TCSlib.Cryptography.colProtocolRep` — the `n|E|`-fold protocol (Prot-127.5).
* `TCSlib.Cryptography.committedColor` — the colour a commitment string can be opened to
  (Lem-127.f).

## Main results

* `TCSlib.Cryptography.colVerify_honest` — completeness of one iteration (Claim-127.e).
* `TCSlib.Cryptography.committedColor_eq_some`, `TCSlib.Cryptography.exists_bad_edge` — the
  committed colouring and its bad edge (Lem-127.f).
* `TCSlib.Cryptography.uprob_adaptive_escape` — adaptive sequential soundness with escape
  probability `1/m` (Lem-127.g); `TCSlib.Cryptography.uprob_col_cheat_le` — soundness of the
  `k`-fold protocol against adaptive provers (Claim-127.h).
* `TCSlib.Cryptography.col_efficientProverProofErr`,
  `TCSlib.Cryptography.colRep_efficientProverProof` — **[PS10, Proposition 127.6]**, the
  interactive-proof half (Prop-127.6).
* `TCSlib.Cryptography.R3COL_witnessRelation` — `R_3COL` is a witness relation for `3COL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring; Chapter 9, zero knowledge.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Messages of one iteration -/

/-- The `i`-th component of an encoded message list (`Strategy.encodeMsgs`): the first
projection after `i` second projections. -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- `msgAt` reads the `i`-th message of an encoded list. -/
theorem msgAt_encodeMsgs (l : List (List Bool)) (i : ℕ) (hi : i < l.length) :
    msgAt (Strategy.encodeMsgs l) i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a l ih =>
    cases i with
    | zero => simp [msgAt]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [msgAt, Function.iterate_succ_apply] using this

/-- The prover's first message of [PS10, Protocol 127.5]: the commitments to the (permuted)
colours `c' i`, padded to `n` bits, with randomness `r i ∈ {0,1}^{ℓ(n)}`, as one encoded list
(`multiCom`). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- The prover's opening message of [PS10, Protocol 127.5] for the edge `p = (i, j)`:
`⟨⟨c'_i, r_i⟩, ⟨c'_j, r_j⟩⟩`. -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- The verifier's check of one iteration of [PS10, Protocol 127.5] on the edge of index `e`,
the commitment message `com` and the opening `opn = ⟨⟨a, r_i⟩, ⟨b, r_j⟩⟩`: the randomness has
length `ℓ(n)`, both openings match the commitments, and `a ≠ b`.

**Deviation:** the opening check (the text's "`V` accepts iff `c'_i ≠ c'_j`"); `false` when
`E = ∅` (handled by the verifier before calling this check). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- **Completeness of one iteration** [PS10, proof of Proposition 127.6, "completeness follows
by inspection"] (Claim-127.e): for a proper colouring `c`, any colour permutation `π`, any
randomness `r` and any edge `p = edgeAt G e`, the honest commitment and opening pass the
verifier's check: the openings match by `msgAt_encodeMsgs`, and `π (c i) ≠ π (c j)` since
`c i ≠ c j` on the edge and `π` is injective. -/
theorem colVerify_honest (Com : List Bool → List Bool) {n ℓn : ℕ} {G : Graph n}
    {c : Fin n → Fin 3} (hc : ProperColoring G c) (π : Equiv.Perm (Fin 3))
    (r : Fin n → Fin ℓn → Bool) {e : ℕ} {p : Fin n × Fin n} (hp : edgeAt G e = some p) :
    colVerify Com ℓn G e (colCommit Com n ℓn (fun i => π (c i)) r)
      (colOpen (fun i => π (c i)) r p) = true := by
  have hadj := edgeAt_adj G hp
  unfold colVerify
  rw [hp]
  simp only [colOpen, pairFstD_pairEncode, pairSndD_pairEncode, decColor_encColor,
    List.length_ofFn, decide_eq_true_eq]
  refine ⟨trivial, trivial, ?_, ?_, fun h => hc _ _ hadj (π.injective h)⟩
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The committed colouring (Lem-127.f) -/

/-- The colour a commitment string `w` can be opened to at security parameter `n` with
randomness of length `ℓn` (Lem-127.f): `some a` if some `(a, r)` opens `w`, `none` otherwise.
By binding (`committedColor_eq_some`) the colour is unique. -/
noncomputable def committedColor (Com : List Bool → List Bool) (n ℓn : ℕ) (w : List Bool) :
    Option (Fin 3) := by
  classical
  exact if h : ∃ a : Fin 3, ∃ r : Fin ℓn → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w
    then some (Classical.choose h) else none

/-- A list of length `k` is the `ofFn` of its entries read with a default. -/
private theorem ofFn_getD_of_length {r : List Bool} {k : ℕ} (hr : r.length = k) :
    List.ofFn (fun i : Fin k => r.getD i false) = r := by
  subst hr
  exact List.ext_getElem (by simp) fun i _ h₂ => by
    simp [List.getD_eq_getElem?_getD]

/-- **The committed colouring is well defined** [PS10, proof of Proposition 127.6,
"soundness follows by the binding property"] (Lem-127.f): for a commitment scheme, `n ≥ 2`,
an opening `(a, r)` of `w` with `|r| = ℓ(n)` forces `committedColor w = some a` — any other
opening `(a', r')` would give `Com ⟨pad a', r'⟩ = Com ⟨pad a, r⟩` with `pad a' ≠ pad a`
(`padColor_injective`), contradicting `Commitment.binding_ofFn`. -/
theorem committedColor_eq_some {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {a : Fin 3} {r : List Bool}
    (hr : r.length = ℓ.eval n) {w : List Bool}
    (h : Com (pairEncode (List.ofFn (padColor n a)) r) = w) :
    committedColor Com n (ℓ.eval n) w = some a := by
  classical
  have hex : ∃ a : Fin 3, ∃ r : Fin (ℓ.eval n) → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w :=
    ⟨a, fun i => r.getD i false, by rwa [ofFn_getD_of_length hr]⟩
  unfold committedColor
  rw [dif_pos hex, Option.some.injEq]
  obtain ⟨r', hr'⟩ := Classical.choose_spec hex
  by_contra hne
  have hpad : padColor n (Classical.choose hex) ≠ padColor n a :=
    fun h' => hne (padColor_injective hn h')
  have := hC.binding_ofFn hpad r' (fun i => r.getD i false)
  rw [ofFn_getD_of_length hr, hr', h] at this
  exact this rfl

/-- **A non-colourable graph has a bad edge for every partial colouring**
[PS10, proof of Proposition 127.6, "for each coloring there exists at least one edge which
has the same colors on both endpoints"] (Lem-127.f): if `G` is not 3-colourable then for every
`ct : Fin n → Option (Fin 3)` some edge has an uncoloured endpoint or equal colours at both
endpoints — otherwise `i ↦ (ct i).getD 0` would be a proper colouring. -/
theorem exists_bad_edge {n : ℕ} {G : Graph n} (hG : ¬ ThreeColorable G)
    (ct : Fin n → Option (Fin 3)) :
    ∃ e : Fin (edgeCount G), ct (edgeOf G e).1 = none ∨ ct (edgeOf G e).2 = none ∨
      ct (edgeOf G e).1 = ct (edgeOf G e).2 := by
  by_contra hcon
  push_neg at hcon
  refine hG ⟨fun i => (ct i).getD 0, fun u v huv heq => ?_⟩
  obtain ⟨e, he⟩ := exists_edgeOf_eq G huv
  obtain ⟨h1, h2, h3⟩ := hcon e
  simp only [he] at h1 h2 h3
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 h2
  simp only [ha, hb] at h3 heq
  exact h3 (by simpa using heq)

/-! ### Adaptive sequential soundness (Lem-127.g, Claim-127.h) -/

/-- The strict prefix `e_0, …, e_{i-1}` of a challenge tuple (the history an adaptive prover
has seen before challenge `i`). -/
def challengesBefore {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin i → α :=
  fun j => e (Fin.castLE i.isLt.le j)

/-- The prefix `e_0, …, e_i` of a challenge tuple (the history including the current
challenge). -/
def challengesUpTo {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin (i + 1) → α :=
  fun j => e (Fin.castLE i.isLt j)

/-- A `(k+1)`-tuple of challenges with auxiliary data as a `k`-tuple, the data and the last
challenge (`Fin.snoc`): the splitting of the sequential-soundness induction. -/
private def snocEquivW (k m : ℕ) (W : Type*) :
    ((Fin k → Fin m) × W) × Fin m ≃ (Fin (k + 1) → Fin m) × W where
  toFun y := (Fin.snoc y.1.1 y.2, y.1.2)
  invFun z := ((Fin.init z.1, z.2), z.1 (Fin.last k))
  left_inv y := by
    rcases y with ⟨⟨e, w⟩, x⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    rcases z with ⟨e, w⟩
    simp [Fin.snoc_init_self]

/-- The history before a non-final challenge of `Fin.snoc e x` is the history before it in `e`. -/
private theorem challengesBefore_snoc_castSucc {k m : ℕ} (e : Fin k → Fin m) (x : Fin m)
    (i : Fin k) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.castSucc i) =
      challengesBefore e i := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (k + 1)) =
      Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- The history before the last challenge of `Fin.snoc e x` is `e`. -/
private theorem challengesBefore_snoc_last {k m : ℕ} (e : Fin k → Fin m) (x : Fin m) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.last k) = e := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.last k).isLt.le j : Fin (k + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- **Adaptive sequential soundness with escape probability `1/m`** [PS10, proof of
Proposition 127.6, "in each iteration a cheating prover is caught with probability `1/|E|`"]
(Lem-127.g): for `k` rounds with uniform challenges `e_i ∈ [m]` and, for every round, a
nonempty set `Bad i` of challenges (depending on the earlier challenges and on the prover's
coins `w`) on which the prover is caught, the probability that no challenge ever lands in its
bad set is at most `(1 - 1/m)^k`.

**Proof sketch.** Induction on `k`. Split the tuple as `Fin.snoc e' e_last` (the bijection
`(Fin (k+1) → Fin m) ≃ (Fin k → Fin m) × Fin m`, `Fin.snocEquiv`; `uprob_comp_equiv`); by
`uprob_prod` the probability is the average over `(e', w)` of the probability over `e_last`,
which is `0` if some earlier round is caught and at most `1 - |Bad k e' w| / m ≤ 1 - 1/m` otherwise
(`uprob_eq_card_filter`, `Finset.card_pos` from `hBad`); so the total is at most `(1 - 1/m)`
times the probability of the `k`-round event (`OneWay.uprob_and_le_mul`), and the induction
hypothesis applies to the latter. -/
theorem uprob_adaptive_escape (m k : ℕ) (hm : 0 < m) {W : Type*} [Fintype W]
    (Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m))
    (hBad : ∀ i h w, (Bad i h w).Nonempty) :
    uprob (fun z : (Fin k → Fin m) × W => ∀ i, z.1 i ∉ Bad i (challengesBefore z.1 i) z.2) ≤
      (1 - 1 / (m : ℝ)) ^ k := by
  induction k with
  | zero => simpa using uprob_le_one _
  | succ k ih =>
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hθ : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm']
      exact_mod_cast hm
    have hih := ih (fun i h w => Bad (Fin.castSucc i) h w) (fun i h w => hBad _ _ _)
    rw [← uprob_comp_equiv (snocEquivW k m W)]
    have hmono : uprob (fun y : ((Fin k → Fin m) × W) × Fin m => ∀ i,
          ((snocEquivW k m W) y).1 i ∉
            Bad i (challengesBefore ((snocEquivW k m W) y).1 i) ((snocEquivW k m W) y).2) ≤
        uprob (fun y : ((Fin k → Fin m) × W) × Fin m =>
          (∀ i, y.1.1 i ∉ Bad (Fin.castSucc i) (challengesBefore y.1.1 i) y.1.2) ∧
            y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2) := by
      apply uprob_mono
      rintro ⟨⟨e, w⟩, x⟩ h
      refine ⟨fun i => ?_, ?_⟩
      · have := h (Fin.castSucc i)
        simpa [snocEquivW, Fin.snoc_castSucc, challengesBefore_snoc_castSucc] using this
      · have := h (Fin.last k)
        simpa [snocEquivW, Fin.snoc_last, challengesBefore_snoc_last] using this
    have hbound := OneWay.uprob_and_le_mul
      (fun a : (Fin k → Fin m) × W => ∀ i, a.1 i ∉ Bad (Fin.castSucc i) (challengesBefore a.1 i) a.2)
      (fun y : ((Fin k → Fin m) × W) × Fin m => y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2)
      (θ := 1 - 1 / (m : ℝ)) (fun a _ => ?_)
    · calc _ ≤ _ := hmono
        _ ≤ _ := hbound
        _ ≤ (1 - 1 / (m : ℝ)) * (1 - 1 / (m : ℝ)) ^ k := mul_le_mul_of_nonneg_left hih hθ
        _ = (1 - 1 / (m : ℝ)) ^ (k + 1) := by ring
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      classical
      rw [uprob_not, uprob_eq_card_filter, Fintype.card_fin]
      have hcard : 1 ≤ (Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.card_pos.2 (hBad _ _ _)
      have : (1 : ℝ) / m ≤
          ((Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card : ℝ) / m := by
        gcongr
        exact_mod_cast hcard
      linarith

/-- **Soundness of the `k`-fold protocol against adaptive provers** [PS10, proof of
Proposition 127.6] (Claim-127.h, concrete): for a commitment scheme, a graph on `n ≥ 2`
vertices that is not 3-colourable, and a cheating prover whose `i`-th commitment message
`comF i` depends on the earlier challenges and its coins `w`, and whose `i`-th opening
`opnF i` also depends on the current challenge, the verifier accepts all `k` iterations with
probability at most `(1 - 1/|E|)^k` over the uniform challenges and `w` (`|E| = edgeCount G`,
the number of ordered edge pairs; run-3 audit P11-3).

**Proof sketch.** Apply `uprob_adaptive_escape` with
`Bad i h w := {e | the edge `edgeOf G e` is bad for the committed colouring
`k ↦ committedColor Com n ℓ(n) (msgAt (comF i h w) k)`}`, nonempty by `exists_bad_edge`
(`edgeCount_pos_of_not_threeColorable`). Acceptance in round `i` on the challenge `e_i`
means (`colVerify`, `edgeAt_eq_some_edgeOf`) that both openings `(a, r_i)`, `(b, r_j)` have
randomness of length `ℓ(n)` and match the commitments at the endpoints, so by
`committedColor_eq_some` the committed colours at the endpoints are `some a`, `some b` with
`a ≠ b`: the edge is not bad, i.e. `e_i ∉ Bad i …`. Hence the acceptance event is contained
in the escape event (`uprob_mono`). -/
theorem uprob_col_cheat_le {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G) (k : ℕ) {W : Type*} [Fintype W]
    (comF : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → List Bool)
    (opnF : (i : Fin k) → (Fin (i + 1) → Fin (edgeCount G)) → W → List Bool) :
    uprob (fun z : (Fin k → Fin (edgeCount G)) × W => ∀ i,
      colVerify Com (ℓ.eval n) G (z.1 i) (comF i (challengesBefore z.1 i) z.2)
        (opnF i (challengesUpTo z.1 i) z.2) = true) ≤
      (1 - 1 / (edgeCount G : ℝ)) ^ k := by
  classical
  have hm := edgeCount_pos_of_not_threeColorable hG
  let ct : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Fin n → Option (Fin 3) :=
    fun i h w v => committedColor Com n (ℓ.eval n) (msgAt (comF i h w) v)
  let Bad : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Finset (Fin (edgeCount G)) :=
    fun i h w => Finset.univ.filter fun e => ct i h w (edgeOf G e).1 = none ∨
      ct i h w (edgeOf G e).2 = none ∨ ct i h w (edgeOf G e).1 = ct i h w (edgeOf G e).2
  have hBad : ∀ i h w, (Bad i h w).Nonempty := by
    intro i h w
    obtain ⟨e, he⟩ := exists_bad_edge hG (ct i h w)
    exact ⟨e, by simpa [Bad] using he⟩
  refine le_trans (uprob_mono ?_) (uprob_adaptive_escape (edgeCount G) k hm Bad hBad)
  rintro ⟨es, w⟩ hacc i
  have h := hacc i
  simp only at h ⊢
  unfold colVerify at h
  rw [edgeAt_eq_some_edgeOf] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hri, hrj, hci, hcj, hab⟩ := h
  have h1 := committedColor_eq_some hC hn hri hci
  have h2 := committedColor_eq_some hC hn hrj hcj
  simp only [Bad, ct, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  rw [h1, h2]
  simp [hab]

/-! ### Protocol 127.5, one iteration (Prot-127.5) -/

/-- The well-formedness test of a common input: `x` is the encoding of the graph it decodes
to (i.e. `|x|` is a perfect square). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- An encoded graph is well formed. -/
theorem colWellFormed_encGraph {n : ℕ} (G : Graph n) : colWellFormed (encGraph G) = true := by
  unfold colWellFormed
  rw [decide_eq_true_eq]
  have h := decGraph_encGraph G
  rw [show encGraph (decGraph (encGraph G)).2 = encGraph (⟨n, G⟩ : Σ n, Graph n).2 by rw [h]]

/-- The honest prover of one iteration of [PS10, Protocol 127.5] (Prot-127.5): with common
input `x = encGraph G` (`n` vertices) and witness `y = encColoring c`, it samples `π ← S₃` from
the first `3|x|` bits of its tape and `r_i ∈ {0,1}^{ℓ(n)}` from the next `n ℓ(n)` bits; on the
empty history it sends the commitments to `π (c i)` (`colCommit`), and on the challenge `w`
it opens the two commitments of the edge `edgeAt G (edgeIdxOfMsg |E| w)` (`colOpen`), or
sends `[]` if `E = ∅`. Coins: `3|x| + |x| ℓ(|x|)` bits (an upper bound for every `n ≤ |x|`).

**Deviation (D10):** `π` by rejection sampling (identity on failure). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- The verifier of one iteration of [PS10, Protocol 127.5] (Prot-127.5): it samples the
edge index `e ← [|E|]` from its tape (`sampleEdgeIdx` with `|x|` trials); on the commitment
message it sends `1^e`; on the complete history `[com, opn]` it outputs `[true]` iff `x` is
well formed and either `E = ∅` or (`n ≥ 2` and `colVerify` accepts the openings on the edge
`e`). Coins: `(|x| + 1)²` bits.

**Deviation:** opening check, `E = ∅` accepted outright, `n < 2` with `E ≠ ∅` rejected outright,
well-formedness test (see the module docstring); `e` by rejection sampling (D10). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- One iteration of [PS10, Protocol 127.5] (Prot-127.5): three messages (commitments,
edge, openings), prover first; the verdict is the verifier's activation on `[com, opn]`. -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-! ### The `n|E|`-fold protocol (Prot-127.5, repeated) -/

/-- The `t`-th block of `c` bits of a tape (the coins of iteration `t` of the repeated
protocol). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- The number of iterations of the repeated protocol on `x`: `n |E|` [PS10, Protocol 127.5,
"repeat the procedure `n|E|` times"], with `|E| = edgeCount G` the number of ordered edge
pairs (for the text's simple graph `2n|E|` iterations; run-3 audit P11-3). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- The prover of the `n|E|`-fold protocol: iteration `t = hist.length / 2` (it has received
the challenges and the empty verifier messages of the earlier iterations) runs `colProver`
on the `t`-th block of `3|x| + |x| ℓ(|x|)` coins; after the `n|E|` iterations it sends `[]`. -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- The verifier of the `n|E|`-fold protocol: it has received `[com_0, opn_0, com_1, …]`; on
an odd history it sends the challenge of iteration `t = hist.length / 2` (from the `t`-th
block of `(|x|+1)²` coins); on the complete history (`2|x|²` received messages) it accepts iff
`x` is well formed and either `E = ∅` or `n ≥ 2` and every one of the `n|E|` iterations passes
`colVerify`; on every other even history it sends `[]`. -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of one iteration is a PPT strategy when `Com` is polynomial-time
[PS10, Proposition 127.6, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^N, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`): `n = Nat.sqrt |x|`
in unary by `polyTimeComputable_iterateFind` over `polyTimeComputable_lenLe` against unary
squares; `π` by `polyTimeComputable_iterateFind` over the `|x|` three-bit trials
(`pairTakePoly`/`pairDropPoly`); the `n` commitments by `polyTimeComputable_blockMap ℓ` on
the randomness blocks composed with `hCom` on `⟨pad (π (c i)), r_i⟩` (`PolyTimeComputable.pairEncode`,
the colour permutation as a table lookup, `polyTimeComputable_ite`) and
`polyTimeComputable_iterateEmit` for the `encodeMsgs` fold; the opening by the two projections
of the challenge's decoded index (`polyTimeComputable_lenLe` against the unary `|E|`, the edge
list scanned by `polyTimeComputable_iterateFind`); the case split on `msgs = []` by
`polyTimeComputable_lenEq`. The equation with `colProver.next` is
`NUPPT.runAtL_ofPolyTimeUniform` and `Strategy.pairFstD_encodeMsgs`. -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  ColProofs.colProver_efficient hCom ℓ

/-- The verifier of one iteration is a PPT strategy when `Com` is polynomial-time
[PS10, Definition 116.1 for Proposition 127.6] (Inf-4.2).

**Proof sketch.** As `colProver_efficient`: the edge index by `polyTimeComputable_iterateFind`
over the `|x|` trials of `Nat.size |E|` bits (`|E|` in unary by scanning the matrix with
`polyTimeComputable_iterateEmit`), the challenge `1^e` by `polyTimeComputable_unaryPoly`-style
emission, and the verdict by `polyTimeComputable_and` of the well-formedness test
(`polyTimeComputable_pairEq` on `x` and the re-encoded matrix), the two commitment checks
(`hCom` on the parsed openings, `msgAt` by `polyTimeComputable_iterate_pairFstD`-style
projections, `polyTimeComputable_pairEq`), the length tests (`polyTimeComputable_lenEq`) and
the colour comparison. -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  ColProofs.colVerifier_efficient hCom ℓ

/-- The prover of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): `colProver_efficient`
on the coin block `hist.length / 2` cut by `pairTakePoly`/`pairDropPoly`, with the parity and
iteration tests by `polyTimeComputable_lenLe` on unary counters. -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  ColProofs.colProverRep_efficient hCom ℓ

/-- The verifier of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): the challenge as in
`colVerifier_efficient` on the block `hist.length / 2`, and the verdict a loop over the
`n|E|` pairs of the history (`polyTimeComputable_iterate` with an accumulated conjunction of
`colVerify` checks). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  ColProofs.colVerifierRep_efficient hCom ℓ

/-! ### Proposition 127.6, interactive-proof half -/

section OneIteration

open ColMachines

/-! ### Unfolding the parties on a decoded instance -/

/-- The verifier's verdict on `[com, opn]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_two_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com opn : List Bool) :
    (colVerifier Com ℓ).next x z r [com, opn] =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length r) com opn = true)))] := by
  show [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
    colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
      (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) com opn = true)))] = _
  rw [hx]

/-- The verifier's challenge on `[com]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_one_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com : List Bool) :
    (colVerifier Com ℓ).next x z r [com] = edgeMsg (sampleEdgeIdx (edgeCount G) x.length r) := by
  show edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) = _
  rw [hx]

/-- The prover's commitments, on an input decoding to `⟨n, G⟩`. -/
private theorem colProver_next_nil_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) :
    (colProver Com ℓ).next x y r [] = colCommit Com n (ℓ.eval n)
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false) := by
  show colCommit Com (decGraph x).1 (ℓ.eval (decGraph x).1)
    (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i))
    (fun i j => r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) = _
  rw [hx]

/-- The prover's opening, on an input decoding to `⟨n, G⟩` with at least one edge. -/
private theorem colProver_next_cons_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List Bool)
    (h : List (List Bool)) :
    (colProver Com ℓ).next x y r (w :: h) = colOpen
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun (i : Fin n) (j : Fin (ℓ.eval n)) => r.getD (3 * x.length + i * ℓ.eval n + j) false)
      (edgeOf G ⟨edgeIdxOfMsg (edgeCount G) w % edgeCount G, Nat.mod_lt _ hm⟩) := by
  simp only [colProver]
  rw [hx]
  dsimp only
  rw [edgeAt_eq_some_of_pos G hm]

/-- The verdict of one iteration against any prover `P'`: the verifier's activation on the
two prover messages, the second being the reply to the challenge. -/
private theorem colProtocol_outV (Com : List Bool → List Bool) (ℓ : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (colProtocol Com ℓ).ExecCoins P' x) :
    (colProtocol Com ℓ).outV P' x y z r =
      (colVerifier Com ℓ).next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1)
            [(colVerifier Com ℓ).next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := rfl

/-! ### Completeness -/

/-- **The honest execution accepts** on every pair of random tapes: for a proper colouring the
verdict is `[true]`. -/
private theorem colProtocol_outV_honest {Com : List Bool → List Bool} {ℓ : PolyExpr} {n : ℕ}
    {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c) (z : List Bool)
    (r : (colProtocol Com ℓ).ExecCoins (colProtocol Com ℓ).P (encGraph G)) :
    (colProtocol Com ℓ).outV (colProtocol Com ℓ).P (encGraph G) (encColoring c) z r = [true] := by
  have hx : decGraph (encGraph G) = ⟨n, G⟩ := decGraph_encGraph G
  rw [colProtocol_outV]
  show (colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ [], (colProver Com ℓ).next _ _ _
    [(colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ []]]] = _
  rw [colVerifier_next_one_of Com ℓ hx, colProver_next_nil_of Com ℓ hx, colVerifier_next_two_of Com ℓ hx,
    colWellFormed_encGraph, decColoring_encColoring]
  by_cases hm : edgeCount G = 0
  · simp [hm]
  · have hpos := Nat.pos_of_ne_zero hm
    have he := sampleEdgeIdx_lt hpos (encGraph G).length (List.ofFn r.2)
    rw [colProver_next_cons_of Com ℓ hx hpos, decColoring_encColoring]
    simp only [edgeIdxOfMsg_edgeMsg he]
    rw [colVerify_honest Com hc _ _ (edgeAt_eq_some_of_pos G hpos _)]
    simp [ColProofs.two_le_of_edge hc hpos]

/-! ### Soundness -/

/-- **One-round soundness bound against a deterministic prover:** for a non-colourable graph
on `n ≥ 2` vertices, the verifier's check on a uniform edge index `e`, a fixed commitment
message and an opening depending on `e`, passes with probability at most `1 - 1/|E|`
(`uprob_col_cheat_le` at `k = 1`). -/
private theorem uprob_check_uniform_le {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G)
    (com : List Bool) (opn : ℕ → List Bool) :
    uprob (fun e : Fin (edgeCount G) => colVerify Com (ℓ.eval n) G e com (opn e) = true) ≤
      1 - 1 / (edgeCount G : ℝ) := by
  have h := uprob_col_cheat_le hC hn hG 1 (W := Unit) (fun _ _ _ => com)
    (fun i h _ => opn (h (Fin.last i)))
  rw [pow_one] at h
  refine le_trans ?_ h
  rw [← uprob_comp_equiv (ColProofs.finOneEquiv (edgeCount G))]
  apply uprob_mono
  intro e he i
  rw [Fin.fin_one_eq_zero i]
  exact he

/-- **Soundness of one iteration** [PS10, Proposition 127.6]: for `x ∉ 3COL` and any prover,
the verifier rejects with probability at least `1 - (1 - 1/|x| + (1/2)^{|x|})`. -/
private theorem colProtocol_sound {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    (x : List Bool) (hx : x ∉ L3COL) (P' : Strategy) (z : List Bool) :
    1 - (1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length) ≤
      uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
        (colProtocol Com ℓ).outV P' x [] z r = [false]) := by
  have hs0 : (0 : ℝ) ≤ 1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length := by
    have h1 : 1 / (x.length : ℝ) ≤ 1 := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h]; simp
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.length := by positivity
    linarith
  -- reduce to a bound on the acceptance probability
  suffices key : uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
      ¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ≤
        1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length by
    rw [uprob_not] at key
    linarith
  set n := (decGraph x).1 with hn_def
  set G := (decGraph x).2 with hG_def
  have hx' : decGraph x = ⟨n, G⟩ := rfl
  have hout : ∀ r : (colProtocol Com ℓ).ExecCoins P' x, (colProtocol Com ℓ).outV P' x [] z r =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
          (P'.next x [] (List.ofFn r.1) [])
          (P'.next x [] (List.ofFn r.1)
            [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true)))] := by
    intro r
    rw [colProtocol_outV, colVerifier_next_one_of Com ℓ hx', colVerifier_next_two_of Com ℓ hx']
  by_cases hwf : colWellFormed x = true
  · have hxG : x = encGraph G := of_decide_eq_true hwf
    have hnc : ¬ ThreeColorable G := fun h => hx (hxG ▸ (encGraph_mem_L3COL_iff G).2 h)
    have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hnc
    by_cases hn : 2 ≤ n
    · -- the acceptance event is the verifier's check
      have hacc : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          (¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ↔
            colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
              (P'.next x [] (List.ofFn r.1) [])
              (P'.next x [] (List.ofFn r.1)
                [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true := by
        intro r
        rw [hout r]
        simp [hwf, hm.ne', hn]
      -- fix the prover's coins
      obtain ⟨rP, hrP⟩ := (colProtocol Com ℓ).exists_proverCoins_le P' x [] z fun o => ¬ o = [false]
      refine hrP.trans ?_
      rw [OneWay.uprob_congr fun rV => hacc (rP, rV)]
      -- the sampled edge is close to uniform on the verifier's tape
      have hmx : edgeCount G ≤ x.length := by
        have h1 : x.length = n * n := by rw [hxG, length_encGraph]
        rw [edgeCount_eq G x (decGraph_apply x), h1]
        exact countTrue_le _ _
      have hle : x.length * Nat.size (edgeCount G) ≤ (colVerifier Com ℓ).coinLen x.length := by
        show x.length * Nat.size (edgeCount G) ≤ 1 * (x.length + 1) ^ 2
        have h1 : Nat.size (edgeCount G) ≤ x.length :=
          (Nat.size_le_size hmx).trans (Nat.size_le.2 Nat.lt_two_pow_self)
        calc x.length * Nat.size (edgeCount G) ≤ x.length * x.length := Nat.mul_le_mul_left _ h1
          _ ≤ 1 * (x.length + 1) ^ 2 := by nlinarith
      have hclose := (statClose_sampleEdgeIdx hm x.length).comp_pushesUniform
        (ColProofs.pushesUniform_castLE hle)
      have hbound := hclose.uprob_le_add fun e : Fin (edgeCount G) =>
        colVerify Com (ℓ.eval n) G e (P'.next x [] (List.ofFn rP) [])
          (P'.next x [] (List.ofFn rP) [edgeMsg e]) = true
      simp only [id] at hbound
      have hev : ∀ rV : (colVerifier Com ℓ).Coins x.length,
          (colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))
            (P'.next x [] (List.ofFn (rP, rV).1) [])
            (P'.next x [] (List.ofFn (rP, rV).1)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))]) = true) ↔
          (colVerify Com (ℓ.eval n) G
            (sampleEdgeIdx (edgeCount G) x.length (List.ofFn fun i => rV (Fin.castLE hle i)))
            (P'.next x [] (List.ofFn rP) [])
            (P'.next x [] (List.ofFn rP)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length
                (List.ofFn fun i => rV (Fin.castLE hle i)))]) = true) := by
        intro rV
        rw [← ColProofs.sampleEdgeIdx_ofFn_castLE hle rV]
      refine (le_of_eq (OneWay.uprob_congr hev)).trans (hbound.trans ?_)
      have hcheat := uprob_check_uniform_le hC hn hnc (P'.next x [] (List.ofFn rP) [])
        fun e => P'.next x [] (List.ofFn rP) [edgeMsg e]
      have hinv : 1 / (x.length : ℝ) ≤ 1 / (edgeCount G : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmx)
      linarith
    · -- fewer than two vertices with an edge: the verifier rejects outright
      have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
        intro r
        rw [hout r]
        simp [hm.ne', hn]
      rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
      rw [uprob_false]
      exact hs0
  · have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
        ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
      intro r
      rw [hout r]
      simp [hwf]
    rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
    rw [uprob_false]
    exact hs0

end OneIteration


/-- `R_3COL` is a witness relation for `3COL` [PS10, Definition 191.11 for Theorem 124.1]:
witnesses have length `2n ≤ 2|x|`, and the relation is decided in polynomial time by
re-encoding the decoded graph and colouring and checking every edge.

**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))`, correct by `decGraph_encGraph` and
`decColoring_encColoring`, and polynomial-time by `polyTimeComputable_pairEq` on the
re-encodings (`polyTimeComputable_blockMap`, `polyTimeComputable_iterateEmit`) and a scan of
the `n²` entries for the colouring test (`polyTimeComputable_iterate` with an accumulated
conjunction). -/
theorem R3COL_witnessRelation : WitnessRelation L3COL R3COL := by
  refine ⟨mem_L3COL_iff, ⟨.mul (.const 2) .var, ?_⟩, ?_⟩
  · rintro x y ⟨n, G, c, rfl, rfl, -⟩
    rw [length_encColoring, length_encGraph, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_var]
    nlinarith [Nat.zero_le n]
  · sorry

/-- **One iteration of [PS10, Protocol 127.5] is an interactive proof for `3COL` with
efficient prover and soundness error `1 - 1/|x| + (1/2)^{|x|}`** [PS10, Proposition 127.6,
one iteration: "a cheating prover is caught with probability `1/|E|`"] (Prop-127.6,
Claim-127.e, Claim-127.h).

**Deviation (D10):** the error `1 - 1/|E|` is stated through `|E| ≤ |x|`, plus the edge
sampler's failure term `(1/2)^{|x|}`; here `|E| = edgeCount G ≤ n² = |x|` counts ordered
pairs (run-3 audit P11-3), which is what makes `|E| ≤ |x|` immediate.

**Proof sketch.** Completeness for every witness: for `x = encGraph G`, `y = encColoring c`
with `c` proper, the transcript is `[com, opn]` with `com = colCommit (π ∘ c) r` and
`opn = colOpen (π ∘ c) r p` for `p = edgeAt G e` (`exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, `edgeIdxOfMsg_edgeMsg` with `sampleEdgeIdx_lt`), and the verdict is
`[true]` by `colWellFormed_encGraph`, `colVerify_honest` when `E ≠ ∅` (then `n ≥ 2`: a graph
with an edge and a proper colouring has two distinct vertices) and outright when `E = ∅`, for
every value of `π` and `e` (`HardcoreBit.uprob_eq_one_of_forall`). Completeness of
`InteractiveProofErr` is the witness of `mem_L3COL_iff`. Soundness: for `x ∉ 3COL` either
`colWellFormed x = false` (verdict `[false]` always) or `x = encGraph G` with `¬ ThreeColorable G`
(`encGraph_mem_L3COL_iff`), so `0 < |E|` (`edgeCount_pos_of_not_threeColorable`); if `n < 2`
the verdict is `[false]`; otherwise fix the prover's coins (`Protocol.exists_proverCoins_le`),
replace the sampled edge by a uniform one (`statClose_sampleEdgeIdx`,
`StatClose.abs_uprob_sub_le_prod`, cost `(1/2)^{|x|}`), and apply `uprob_col_cheat_le` with
`k = 1`, `comF :=` the prover's first message and `opnF :=` its reply to `1^e`, giving
`Pr[accept] ≤ 1 - 1/|E| + (1/2)^{|x|} ≤ 1 - 1/|x| + (1/2)^{|x|}` (`|E| ≤ n² = |x|`), i.e. the
`[false]` probability is at least `1 - s |x|` (`uprob_not`). Efficiency:
`colProver_efficient`, `colVerifier_efficient` from `hC.easy`. -/
theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
      (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) where
  efficientV := colVerifier_efficient hC.easy ℓ
  complete := by
    intro x hx
    obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
    exact ⟨encColoring c, fun z => HardcoreBit.uprob_eq_one_of_forall fun r =>
      colProtocol_outV_honest hc z r⟩
  sound := fun x hx P' z => colProtocol_sound hC x hx P' z
  efficientP := colProver_efficient hC.easy ℓ
  completeWitness := by
    rintro x y ⟨n, G, c, rfl, rfl, hc⟩ z
    exact HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r

/-- **The `n|E|`-fold [PS10, Protocol 127.5] is an interactive proof for `3COL` with efficient
prover** [PS10, Proposition 127.6, "the probability of successfully cheating in all rounds is
`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Prop-127.6, Claim-127.h, Claim-125.a).

**Deviation:** `n|E|` iterations inside `4|x|²` fixed moves (D8); the soundness error carries the
edge samplers' failure term `|x|² (1/2)^{|x|}` (D10); the text's "`|E|²` times" is the
protocol's `n|E|`.

**Proof sketch.** Completeness as in `col_efficientProverProofErr`, iteration by iteration
(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`; the empty
messages beyond `n|E|` iterations are ignored). Soundness with
`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): for `x = encGraph G`
not colourable with `n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers
being uniform (`statClose_sampleEdgeIdx` per block, `StatClose.prod` iterated,
`StatClose.abs_uprob_sub_le_prod`, union cost `n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply
`uprob_col_cheat_le` with `k = n|E|`, `comF i` the prover's commitment of iteration `i` (a
function of the earlier challenges through `exec`) and `opnF i` its opening: the acceptance
probability is at most `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`) with
`n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`). Negligibility:
`negligible_exp_neg_sqrt_div` with `C = 1`, `Negligible.mul_pow negligible_two_pow_neg 2`,
`negligible_two_pow_neg`, `Negligible.add`. Efficiency: `colProverRep_efficient`,
`colVerifierRep_efficient`. -/
theorem colRep_efficientProverProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL := by
  sorry

/-- The `n|E|`-fold protocol is an interactive proof for `3COL` [PS10, Proposition 127.6]. -/
theorem colRep_interactiveProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : InteractiveProof (colProtocolRep Com ℓ) L3COL :=
  (colRep_efficientProverProof hC).toInteractiveProof

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Parties
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: shadow strategies and proof infrastructure

Proof infrastructure for `ThreeColoring/Protocol.lean` ([PS10, Protocol 127.5, Proposition
127.6]). That file is at the file-size limit, so the identification of its strategies with the
polynomial-time string functions of `ThreeColoring/Parties.lean` lives here. An imported file
cannot refer to the main file's definitions, so this file restates them **verbatim** in the
inner namespace `TCSlib.Cryptography.ColProofs` (the *shadow* definitions, the device of
`GraphIsomorphism/Proofs.lean`): every shadow is definitionally equal to its original, and the
main file closes each efficiency theorem by `ColProofs.…`, which type-checks by `rfl`. The
shadows are proof devices, not public API; any divergence from the frozen definitions of the
main file makes the main file fail to type-check, so it cannot go unnoticed.

## Main results

* `TCSlib.Cryptography.ColProofs.colProver_next_eq`, `ColProofs.colVerifier_next_eq`,
  `ColProofs.colProverRep_next_eq`, `ColProofs.colVerifierRep_next_eq` — the next-message
  functions of the (shadow) parties are the string functions of `Parties.lean` on the layout.
* `TCSlib.Cryptography.ColProofs.colVerify_eq_checkStr` — the verifier's check is `checkStr`
  when the graph has an edge.
* `TCSlib.Cryptography.ColProofs.colProver_efficient`, `ColProofs.colVerifier_efficient`,
  `ColProofs.colProverRep_efficient`, `ColProofs.colVerifierRep_efficient` — the (shadow)
  parties are PPT strategies (Inf-4.2).
* `TCSlib.Cryptography.ColProofs.pushesUniform_castLE`, `ColProofs.sampleEdgeIdx_ofFn_castLE`,
  `ColProofs.finOneEquiv`, `ColProofs.two_le_of_edge` — helpers of the soundness proof of
  Proposition 127.6.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.ColProofs

open Complexity Turing ColMachines TCSlib.Cryptography.EncodingMachines

/-! ### Shadow definitions -/

/-- Shadow of `TCSlib.Cryptography.msgAt` (verbatim copy; see the module docstring). -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- Shadow of `TCSlib.Cryptography.colCommit` (verbatim copy; see the module docstring). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- Shadow of `TCSlib.Cryptography.colOpen` (verbatim copy; see the module docstring). -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- Shadow of `TCSlib.Cryptography.colVerify` (verbatim copy; see the module docstring). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- Shadow of `TCSlib.Cryptography.colWellFormed` (verbatim copy; see the module docstring). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- Shadow of `TCSlib.Cryptography.colProver` (verbatim copy; see the module docstring). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- Shadow of `TCSlib.Cryptography.colVerifier` (verbatim copy; see the module docstring). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.colProtocol` (verbatim copy; see the module docstring). -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-- Shadow of `TCSlib.Cryptography.colCoinSlice` (verbatim copy; see the module docstring). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- Shadow of `TCSlib.Cryptography.colIterations` (verbatim copy; see the module docstring). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- Shadow of `TCSlib.Cryptography.colProverRep` (verbatim copy; see the module docstring). -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- Shadow of `TCSlib.Cryptography.colVerifierRep` (verbatim copy; see the module docstring). -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- Shadow of `TCSlib.Cryptography.colProtocolRep` (verbatim copy; see the module docstring). -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### The parties as string functions of the layout -/

/-- The honest prover's message of one iteration is `proverStr` of the layout. -/
theorem colProver_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x y r : List Bool)
    (hist : List (List Bool)) :
    (colProver Com ℓ).next x y r hist = proverStr Com ℓ (ilayout x y hist r) := by
  cases hist with
  | nil =>
    rw [proverStr, if_pos (by rw [argM_ilayout]; rfl), commitStr_ilayout]
    rfl
  | cons w hist' =>
    rw [proverStr, if_neg (by
        rw [argM_ilayout, Strategy.encodeMsgs_cons]; exact Turing.pairEncode_ne_nil _ _),
      mOf_ilayout]
    by_cases hm : edgeCount (decGraph x).2 = 0
    · rw [if_pos hm]
      simp only [colProver]
      rw [(edgeAt_eq_none_iff _ _).2 hm]
    · rw [if_neg hm, openStr_ilayout ℓ x y r hist' w (Nat.pos_of_ne_zero hm)]
      simp only [colProver]
      rw [edgeAt_eq_some_of_pos _ (Nat.pos_of_ne_zero hm)]
      simp only [edgeIdxOfMsg, Nat.mod_mod]
      rfl

/-- When the graph has an edge, the verifier's check is `checkStr`. -/
theorem colVerify_eq_checkStr (Com : List Bool → List Bool) (L : ℕ) (x com opn : List Bool)
    (e : ℕ) (hm : 0 < edgeCount (decGraph x).2) :
    colVerify Com L (decGraph x).2 e com opn =
      checkStr Com L (decGraph x).1 (edgeCount (decGraph x).2) x com opn e := by
  obtain ⟨h1, h2⟩ := edgeOf_val (decGraph x).2 x (decGraph_apply x)
    ⟨e % edgeCount (decGraph x).2, Nat.mod_lt _ hm⟩
  unfold colVerify
  rw [edgeAt_eq_some_of_pos _ hm]
  unfold checkStr
  show decide _ = decide _
  rw [decide_eq_decide]
  simp only [msgAt, padColor, ofFn_padFin, encColor_eq_ofVal, decColor_val, h1, h2, ne_eq,
    Fin.ext_iff]

/-- The verifier's message of one iteration is `verifierStr` of the layout. -/
theorem colVerifier_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x z r : List Bool)
    (hist : List (List Bool)) :
    (colVerifier Com ℓ).next x z r hist = verifierStr Com ℓ (ilayout x z hist r) := by
  rcases hist with _ | ⟨com, _ | ⟨opn, _ | ⟨m3, t⟩⟩⟩
  · rw [verifierStr, if_pos (by rw [argM_ilayout]; rfl)]
    rfl
  · have c1 : argM (ilayout x z [com] r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z [com] r)) = [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode]
      rfl
    rw [verifierStr, if_neg c1, if_pos c2, eOf_ilayout]
    rfl
  · have c1 : argM (ilayout x z [com, opn] r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z [com, opn] r)) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    have c3 : pairSndD (pairSndD (argM (ilayout x z [com, opn] r))) = [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons,
        pairSndD_pairEncode]
      rfl
    rw [verifierStr, if_neg c1, if_neg c2, if_pos c3]
    show [decide _] = [verdictStr Com ℓ (ilayout x z [com, opn] r)]
    refine congrArg (fun b => [b]) ?_
    rw [verdictStr, nOf_ilayout, mOf_ilayout, LOf_ilayout, eOf_ilayout, argX_ilayout, argM_ilayout,
      Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairFstD_pairEncode,
      pairSndD_pairEncode, pairFstD_pairEncode, Bool.decide_and, Bool.decide_or, Bool.decide_and,
      Bool.decide_eq_true, Bool.decide_eq_true, colWellFormed, encGraph_decGraph_eq_take]
    by_cases hm : edgeCount (decGraph x).2 = 0
    · simp [hm]
    · rw [colVerify_eq_checkStr Com _ x com opn _ (Nat.pos_of_ne_zero hm)]
  · have c1 : argM (ilayout x z (com :: opn :: m3 :: t) r) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    have c2 : pairSndD (argM (ilayout x z (com :: opn :: m3 :: t) r)) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    have c3 : pairSndD (pairSndD (argM (ilayout x z (com :: opn :: m3 :: t) r))) ≠ [] := by
      rw [argM_ilayout, Strategy.encodeMsgs_cons, pairSndD_pairEncode, Strategy.encodeMsgs_cons,
        pairSndD_pairEncode, Strategy.encodeMsgs_cons]
      exact Turing.pairEncode_ne_nil _ _
    rw [verifierStr, if_neg c1, if_neg c2, if_neg c3]
    rfl

/-- The repeated prover's message is `proverRepStr` of the layout. -/
theorem colProverRep_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x y r : List Bool)
    (hist : List (List Bool)) :
    (colProverRep Com ℓ).next x y r hist = proverRepStr Com ℓ (ilayout x y hist r) := by
  have hlast : hist.getLastD [] =
      pairFstD (pairSndD^[hist.length - 1] (Strategy.encodeMsgs hist)) := by
    rw [getLastD_eq_getD, getD_eq_pairFstD_iterate]
  have hcoin : (colProver Com ℓ).coinLen x.length = proverCoinsOf ℓ x.length := by
    simp [Strategy.coinLen, colProver, proverCoinsOf]
  show (if hist.length / 2 < colIterations x then
      (colProver Com ℓ).next x y (colCoinSlice ((colProver Com ℓ).coinLen x.length) (hist.length / 2) r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []) = _
  rw [proverRepStr]
  simp only [argM_ilayout, histLen_encodeMsgs, nOf_ilayout, mOf_ilayout, argX_ilayout, argZ_ilayout,
    inCoins_ilayout]
  rw [hcoin]
  unfold colIterations colCoinSlice
  by_cases h1 : hist.length / 2 < (decGraph x).1 * edgeCount (decGraph x).2
  · rw [if_pos h1, if_pos h1, colProver_next_eq]
    unfold ilayout
    by_cases h2 : hist.length % 2 = 0
    · rw [if_pos h2, if_pos h2]
      rfl
    · rw [if_neg h2, if_neg h2, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, hlast]
  · rw [if_neg h1, if_neg h1]

/-- The repeated verifier's message is `verifierRepStr` of the layout. -/
theorem colVerifierRep_next_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (x z r : List Bool)
    (hist : List (List Bool)) :
    (colVerifierRep Com ℓ).next x z r hist = verifierRepStr Com ℓ (ilayout x z hist r) := by
  show (if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then
        edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length
          (colCoinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
        ∀ t : Fin (colIterations x), colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
          (sampleEdgeIdx (edgeCount (decGraph x).2) x.length (colCoinSlice ((x.length + 1) ^ 2) t r))
          (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []) = _
  rw [verifierRepStr]
  simp only [argM_ilayout, histLen_encodeMsgs, nOf_ilayout, mOf_ilayout, argX_ilayout]
  unfold colIterations colCoinSlice
  by_cases h1 : hist.length % 2 = 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : hist.length / 2 < (decGraph x).1 * edgeCount (decGraph x).2
    · rw [if_pos h2, if_pos h2, eRep_ilayout]
      rfl
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : hist.length = 2 * (x.length * x.length)
    · rw [if_pos h3, if_pos h3]
      refine congrArg (fun b => [b]) ?_
      rw [verdictRepStr, nOf_ilayout, mOf_ilayout, argX_ilayout, Bool.decide_and, Bool.decide_or,
        Bool.decide_and, Bool.decide_eq_true, colWellFormed, encGraph_decGraph_eq_take]
      by_cases hm : edgeCount (decGraph x).2 = 0
      · simp [hm]
      · refine congrArg (fun b => _ && (_ || (_ && b))) ?_
        rw [decide_eq_decide, firstIdx_eq_iff, Fin.forall_iff]
        refine forall_congr' fun t => forall_congr' fun ht => ?_
        rw [checkRep, eRep_ilayout, Bool.not_eq_false', LOf_ilayout, nOf_ilayout, mOf_ilayout,
          argX_ilayout, argM_ilayout, ← getD_eq_pairFstD_iterate, ← getD_eq_pairFstD_iterate,
          colVerify_eq_checkStr Com _ x _ _ _ (Nat.pos_of_ne_zero hm)]
    · rw [if_neg h3, if_neg h3]

/-! ### Efficiency of the (shadow) parties -/

/-- The honest prover of one iteration is a PPT strategy when `Com` is (shadow form). -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  efficient_of_polyTime _ (proverStr_poly Com ℓ hCom) (colProver_next_eq Com ℓ)

/-- The verifier of one iteration is a PPT strategy when `Com` is (shadow form). -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  efficient_of_polyTime _ (verifierStr_poly Com ℓ hCom) (colVerifier_next_eq Com ℓ)

/-- The prover of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  efficient_of_polyTime _ (proverRepStr_poly Com ℓ hCom) (colProverRep_next_eq Com ℓ)

/-- The verifier of the `n|E|`-fold protocol is a PPT strategy when `Com` is (shadow form). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  efficient_of_polyTime _ (verifierRepStr_poly Com ℓ hCom) (colVerifierRep_next_eq Com ℓ)

/-! ### Helpers of the soundness proof -/

/-- A graph with an edge and a proper colouring has at least two vertices. -/
theorem two_le_of_edge {n : ℕ} {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (hm : 0 < edgeCount G) : 2 ≤ n := by
  have hne : (edgeOf G ⟨0, hm⟩).1 ≠ (edgeOf G ⟨0, hm⟩).2 :=
    fun h => hc _ _ (edgeOf_adj G ⟨0, hm⟩) (by rw [h])
  have h1 := (edgeOf G ⟨0, hm⟩).1.isLt
  have h2 := (edgeOf G ⟨0, hm⟩).2.isLt
  by_contra hlt
  exact hne (Fin.ext (by omega))

/-- A prefix of a uniform tape is uniform (private copy of `GI.pushesUniform_castLE`). -/
theorem pushesUniform_castLE {m c : ℕ} (h : m ≤ c) :
    HardcoreBit.PushesUniform (fun t : Fin c → Bool => fun i : Fin m => t (Fin.castLE h i)) := by
  let e : (Fin c → Bool) ≃ (Fin m → Bool) × (Fin (c - m) → Bool) :=
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he : ∀ t : Fin c → Bool, (e t).1 = fun i : Fin m => t (Fin.castLE h i) := by
    intro t
    funext i
    simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, finCongr_symm,
      finCongr_apply, finSumFinEquiv_apply_left]
    congr 1
  have := (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
  simpa only [he] using this

/-- The bit `i < n` of `List.ofFn f` read with a default. -/
theorem ofFn_getD_lt {n : ℕ} (f : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]

/-- The edge sampler reads only the first `T · size m` bits of its tape. -/
theorem sampleEdgeIdx_ofFn_castLE {m T c : ℕ} (h : T * Nat.size m ≤ c) (t : Fin c → Bool) :
    sampleEdgeIdx m T (List.ofFn t) =
      sampleEdgeIdx m T (List.ofFn fun i : Fin (T * Nat.size m) => t (Fin.castLE h i)) := by
  unfold sampleEdgeIdx sampleIdx
  congr 3
  funext tr j
  have hlt : (tr : ℕ) * Nat.size m + j < T * Nat.size m := by
    have h1 := tr.isLt
    have h2 := j.isLt
    calc (tr : ℕ) * Nat.size m + j < (tr : ℕ) * Nat.size m + Nat.size m := by omega
      _ = ((tr : ℕ) + 1) * Nat.size m := by ring
      _ ≤ T * Nat.size m := Nat.mul_le_mul_right _ h1
  rw [ofFn_getD_lt t (lt_of_lt_of_le hlt h), ofFn_getD_lt _ hlt]
  rfl

/-- `Fin m` as single-round challenge tuples with trivial prover data. -/
def finOneEquiv (m : ℕ) : Fin m ≃ (Fin 1 → Fin m) × Unit where
  toFun e := (fun _ => e, ())
  invFun z := z.1 0
  left_inv _ := rfl
  right_inv z := by
    refine Prod.ext (funext fun i => ?_) rfl
    rw [Fin.fin_one_eq_zero i]

end TCSlib.Cryptography.ColProofs

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the simulator

The zero-knowledge half of [PS10, Proposition 127.6]: the simulator of [PS10, Algorithm 128.7]
for one iteration of [PS10, Protocol 127.5] (Alg-128.7), its efficiency (Claim-128.a), and
[PS10, Proposition 128.8] (Prop-128.8) through the hybrid chain of the text's proof,
corrected: the simulator `S` guesses an edge `e'` and a pair of distinct colours, commits to
them at the endpoints of `e'` and to the colour `0` elsewhere, runs `V*` and succeeds if `V*`
asks for `e'`; `S'` (Claim-129.a) uses the witness and a uniform colour permutation `π` at the
two endpoints instead of a uniform distinct pair — identically distributed by the bijection
`π ↦ (π a, π b)` between `S₃` and the distinct pairs (Lem-129.b); `S''` (Claim-129.c) commits
like the honest prover to `π (c k)` for **all** `k` but keeps the restart rule, so each attempt
succeeds with probability exactly `1/|E|` and, conditioned on success, outputs the honest view;
`S' ≈ S''` (Claim-129.d) by a hybrid over the `n|E|` attempts and the multi-value hiding of
the commitment (`Commitment.multiHiding`).

Two layers (D2): the *concrete* layer works over typed coins (`Fin |E|`, `Equiv.Perm (Fin 3)`,
the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → Bool`, and the coins
`ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.

**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT,
truncated at `n|E|` attempts and outputting `⊥ = []` on failure, which costs the statistical
term `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
`2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
`(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
all-zero colours and succeeds at once.

## Main definitions

* `TCSlib.Cryptography.ColorPair`, `TCSlib.Cryptography.colorPairEquiv` — the distinct colour
  pairs and the bijection `S₃ ≃ ColorPair` (Lem-129.b).
* `TCSlib.Cryptography.colRealView` — the view of `V*` in one honest iteration (typed).
* `TCSlib.Cryptography.colSimAttempt`, `TCSlib.Cryptography.colSimAttemptW`,
  `TCSlib.Cryptography.colSimAttemptH` — one attempt of `S`, `S'`, `S''`;
  `TCSlib.Cryptography.colSimTrunc`, `colSimTruncW`, `colSimTruncH` — their `N`-fold truncations;
  `TCSlib.Cryptography.colSimHyb`, `TCSlib.Cryptography.colSimAttemptPlanted`,
  `TCSlib.Cryptography.colSimRed` — the hybrids and the hiding reduction (Claim-129.d).
* `TCSlib.Cryptography.colSim`, `TCSlib.Cryptography.colSimCoins` — the string simulator
  [PS10, Algorithm 128.7] (Alg-128.7).

## Main results

* `TCSlib.Cryptography.uprob_colSimTruncW_eq` — `S ≡ S'` (Claim-129.a, proved).
* `TCSlib.Cryptography.uprob_colSimAttemptH_none`, `uprob_colSimAttemptH_some`,
  `TCSlib.Cryptography.statClose_colSimTruncH` — `S''` fails with probability `(1 - 1/|E|)^N`
  and is perfect given success (Claim-129.c).
* `TCSlib.Cryptography.exists_colSimRed_ge` — `S' ≈ S''` by hybrids (Claim-129.d).
* `TCSlib.Cryptography.exists_colSimulator` — the simulator is a uniform PPT (Claim-128.a).
* `TCSlib.Cryptography.col_zk` — **[PS10, Proposition 128.8]**: the protocol is
  zero-knowledge for `R_3COL`; `TCSlib.Cryptography.col_zeroKnowledgeProof` — **[PS10,
  Proposition 127.6]** assembled (Prop-127.6).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6, Algorithm 128.7, Proposition 128.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (hybrid arguments at the concrete layer).
-/

namespace TCSlib.Cryptography

open Complexity Turing ColSimLemmas

/-! ### Distinct colour pairs (Lem-129.b) -/

/-- The ordered pairs of distinct colours, the simulator's guess `(c'_{i'}, c'_{j'})` of
[PS10, Algorithm 128.7, step 1]. -/
abbrev ColorPair : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- There are six distinct colour pairs. -/
theorem card_colorPair : Fintype.card ColorPair = 6 := by decide

/-- A permutation of the three colours is determined by its values on two distinct colours. -/
theorem perm3_ext_of_ne : ∀ a b : Fin 3, a ≠ b → ∀ π σ : Equiv.Perm (Fin 3),
    π a = σ a → π b = σ b → π = σ := by
  decide

/-- **`π ↦ (π a, π b)` is a bijection from `S₃` to the distinct colour pairs** for `a ≠ b`
[PS10, proof of Proposition 128.8, "`S` and `S'` are identically distributed"] (Lem-129.b):
injective by `perm3_ext_of_ne`, bijective since both sides have six elements. -/
noncomputable def colorPairEquiv {a b : Fin 3} (hab : a ≠ b) : Equiv.Perm (Fin 3) ≃ ColorPair :=
  Equiv.ofBijective (fun π => ⟨(π a, π b), fun h => hab (π.injective h)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun π σ h => perm3_ext_of_ne a b hab π σ (congrArg (fun p : ColorPair => p.1.1) h)
        (congrArg (fun p : ColorPair => p.1.2) h),
        by rw [Fintype.card_perm, Fintype.card_fin, card_colorPair]; rfl⟩)

/-- Unfolding of `colorPairEquiv`. -/
@[simp] theorem colorPairEquiv_apply {a b : Fin 3} (hab : a ≠ b) (π : Equiv.Perm (Fin 3)) :
    (colorPairEquiv hab π : Fin 3 × Fin 3) = (π a, π b) := rfl

/-! ### The typed views of one iteration -/

/-- The simulator's colouring [PS10, Algorithm 128.7, step 1]: the guessed pair at the
endpoints of the guessed edge `p = (i', j')`, the colour `0` ("`1`" in the text) elsewhere. -/
def simColors {n : ℕ} (p : Fin n × Fin n) (ab : ColorPair) : Fin n → Fin 3 :=
  fun k => if k = p.1 then ab.1.1 else if k = p.2 then ab.1.2 else 0

/-- The colouring of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: the
witness colours permuted by `π` at the endpoints of `p`, the colour `0` elsewhere. -/
def simColorsW {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) (c : Fin n → Fin 3) :
    Fin n → Fin 3 :=
  fun k => if k = p.1 then π (c p.1) else if k = p.2 then π (c p.2) else 0

/-- `S'`'s colouring is `S`'s colouring at the pair `(π (c i'), π (c j'))`. -/
theorem simColorsW_eq {n : ℕ} (p : Fin n × Fin n) (π : Equiv.Perm (Fin 3)) {c : Fin n → Fin 3}
    (hp : c p.1 ≠ c p.2) : simColorsW p π c = simColors p (colorPairEquiv hp π) := rfl

/-- A typed view of `V*` in one iteration: its coins, the commitment message and the
prover's last message (the common input and `z` being fixed). -/
abbrev ColView (ρ : Type*) : Type _ := ρ × List Bool × List Bool

section Typed

variable (Com : List Bool → List Bool) {n : ℕ} (ℓn : ℕ) (G : Graph n) {ρ : Type*}

/-- The view of `V*` (reply function `V`, coins `ρ`) in one honest iteration of
[PS10, Protocol 127.5] with witness `c`, prover coins `(π, r)`: the commitments to `π (c i)`,
and the opening of the edge `V*` names (or `[]` if `E = ∅`). -/
def colRealView (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) : ColView ρ :=
  let c' : Fin n → Fin 3 := fun i => w.1.1 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  (w.2, com, match edgeAt G (edgeIdxOfMsg (edgeCount G) (V com w.2)) with
    | some p => colOpen c' w.1.2 p
    | none => [])

/-- One attempt of the simulator [PS10, Algorithm 128.7] (Alg-128.7, typed) on the coins
`((e', (a, b)), r, r_{V*})`: commit to `simColors (edgeOf G e') (a, b)`, run `V*`, and output
the view if `V*` names the edge `e'`, `none` otherwise. -/
def colSimAttempt (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) : Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColors p w.1.1.2
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S'` [PS10, proof of Proposition 128.8]: as
`colSimAttempt` with the colours `(π (c i'), π (c j'))` at the endpoints for a uniform `π`. -/
def colSimAttemptW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' := simColorsW p w.1.1.2 c
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- One attempt of the hybrid simulator `S''` [PS10, proof of Proposition 128.8]: commit to
`π (c k)` for every `k` (like the honest prover), but output the view only if `V*` names the
guessed edge `e'`. -/
def colSimAttemptH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G w.1.1.1
  let c' : Fin n → Fin 3 := fun i => w.1.1.2 (c i)
  let com := colCommit Com n ℓn c' w.1.2
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (w.1.1.1 : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The coin bijection of Claim-129.a: `((e', π), r, ρ) ↦ ((e', (π (c i'), π (c j'))), r, ρ)`
for a proper colouring `c` (`colorPairEquiv` fibrewise over `e'`). -/
noncomputable def simCoinsEquiv {c : Fin n → Fin 3} (hc : ProperColoring G c) :
    ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ ≃
      ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ :=
  Equiv.prodCongr (Equiv.prodCongr
    (Equiv.prodCongrRight fun e => colorPairEquiv (hc _ _ (edgeOf_adj G e))) (Equiv.refl _))
    (Equiv.refl ρ)

/-- **`S ≡ S'`, one attempt** [PS10, proof of Proposition 128.8, "it directly follows that
`S(x, z)` and `S'(x, z, y)` are identically distributed"] (Claim-129.a): for a proper colouring
`c` the attempts of `S'` and `S` have the same law — they agree pointwise along the coin
bijection `simCoinsEquiv` (`uprob_comp_equiv`). -/
theorem uprob_colSimAttemptW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimAttemptW Com ℓn G c V w)) =
      uprob (fun w => T (colSimAttempt Com ℓn G V w)) := by
  rw [← uprob_comp_equiv (simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-! ### The truncated simulators -/

/-- The first `some` among `N` optional values (the output of the first successful attempt). -/
def firstSome {α : Type*} {N : ℕ} (f : Fin N → Option α) : Option α :=
  (List.finRange N).findSome? f

/-- `firstSome` is `none` iff every attempt fails. -/
theorem firstSome_eq_none_iff {α : Type*} {N : ℕ} (f : Fin N → Option α) :
    firstSome f = none ↔ ∀ t, f t = none := by
  unfold firstSome
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The simulator truncated at `N` attempts with independent coins [PS10, Algorithm 128.7,
steps 4–5] (Alg-128.7, typed): the first successful attempt's view, `none` (`fail`) if all
`N` fail. -/
def colSimTrunc (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × ColorPair) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttempt Com ℓn G V (w t)

/-- `S'` truncated at `N` attempts. -/
def colSimTruncW (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptW Com ℓn G c V (w t)

/-- `S''` truncated at `N` attempts. -/
def colSimTruncH (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => colSimAttemptH Com ℓn G c V (w t)

/-- **`S ≡ S'`, `N` attempts** (Claim-129.a): the truncated `S'` and `S` have the same law
(`simCoinsEquiv` on every attempt, `Equiv.piCongrRight`). -/
theorem uprob_colSimTruncW_eq [Fintype ρ] {c : Fin n → Fin 3} (hc : ProperColoring G c)
    (V : List Bool → ρ → List Bool) (N : ℕ) (T : Option (ColView ρ) → Prop) :
    uprob (fun w => T (colSimTruncW Com ℓn G c V N w)) =
      uprob (fun w => T (colSimTrunc Com ℓn G V N w)) := by
  rw [← uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin N => simCoinsEquiv ℓn G (ρ := ρ) hc)]
  rfl

/-- **An attempt of `S''` fails with probability exactly `1 - 1/|E|`** [PS10, proof of
Proposition 128.8, "as `i, j` and `i', j'` are independently chosen"] (Claim-129.c (i)).

**Proof sketch.** The commitment message and `V*`'s reply do not depend on `e'`, so after
reindexing the coins as `Fin |E| × ((S₃ × randomness) × ρ)` (`Equiv.prodAssoc`,
`uprob_comp_equiv`) and conditioning on the second component (`uprob_prod`), the failure event
is `e' ≠ f(rest)` for a fixed index, of probability `1 - 1/|E|`
(`OneWay.uprob_eq_one_div_card`, `uprob_not`, `edgeIdxOfMsg_lt`). -/
theorem uprob_colSimAttemptH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) :
    uprob (fun w => colSimAttemptH Com ℓn G c V w = none) = 1 - 1 / (edgeCount G : ℝ) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = none ↔
        ¬ edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ)
        then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = none ↔ _
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h]
      exact ⟨fun h' => (Option.some_ne_none _ h').elim, fun h' => (h' h).elim⟩
    · rw [if_neg h]
      exact ⟨fun _ => h, fun _ => rfl⟩
  rw [OneWay.uprob_congr key]
  exact uprob_ne_idx hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _)

/-- **Conditioned on success, an attempt of `S''` is the honest view** [PS10, proof of
Proposition 128.8, "the following distributions are identical"] (Claim-129.c (ii)): for every
test set `T`, the probability that an attempt succeeds with a view in `T` is `1/|E|` times the
probability that the real view lies in `T`.

**Proof sketch.** On the coins `((e', π), r, ρ)` the attempt commits exactly as the honest
prover with `(π, r)`; it succeeds iff `V*`'s reply decodes to `e'` and then outputs
`colRealView (π, r, ρ)` (`edgeAt_eq_some_edgeOf` identifies the opened edge). Reindex as in
`uprob_colSimAttemptH_none` and condition on `(π, r, ρ)`: the inner probability over `e'` is
`1/|E|` if `T (colRealView …)` holds and `0` otherwise (`OneWay.uprob_eq_one_div_card`,
`uprob_false`); `uprob_prod` and `uexp` linearity give the product. -/
theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (T : ColView ρ → Prop) :
    uprob (fun w => ∃ v, colSimAttemptH Com ℓn G c V w = some v ∧ T v) =
      1 / (edgeCount G : ℝ) *
        uprob (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
          T (colRealView Com ℓn G c V w)) := by
  rw [← uprob_comp_equiv (attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm]
  have key : ∀ z : ((Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ) × Fin (edgeCount G),
      (∃ v, colSimAttemptH Com ℓn G c V
          ((attemptCoinsEquiv (edgeCount G) (Fin n → Fin ℓn → Bool) ρ).symm z) = some v ∧ T v) ↔
        (edgeIdxOfMsg (edgeCount G)
          (V (colCommit Com n ℓn (fun i => z.1.1.1 (c i)) z.1.1.2) z.1.2) = (z.2 : ℕ) ∧
          T (colRealView Com ℓn G c V z.1)) := by
    rintro ⟨⟨⟨π, r⟩, ρ₀⟩, e⟩
    show (∃ v, (if edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
        (e : ℕ) then some (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          colOpen (fun i => π (c i)) r (edgeOf G e)) else none) = some v ∧ T v) ↔
      (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) = (e : ℕ) ∧
        T (ρ₀, colCommit Com n ℓn (fun i => π (c i)) r,
          match edgeAt G (edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀))
            with
          | some p => colOpen (fun i => π (c i)) r p
          | none => []))
    by_cases h : edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => π (c i)) r) ρ₀) =
      (e : ℕ)
    · rw [if_pos h, h, edgeAt_eq_some_edgeOf]
      exact ⟨fun ⟨v, hv, hT⟩ => ⟨rfl, by rw [← Option.some.inj hv] at hT; exact hT⟩,
        fun ⟨_, hT⟩ => ⟨_, rfl, hT⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨v, hv, _⟩ => (Option.noConfusion hv), fun ⟨h', _⟩ => (h h').elim⟩
  rw [OneWay.uprob_congr key]
  exact uprob_eq_idx_and hm (fun a : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
    edgeIdxOfMsg (edgeCount G) (V (colCommit Com n ℓn (fun i => a.1.1 (c i)) a.1.2) a.2))
    (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))

/-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
128.8, "`S''` fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the attempts use
disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability `1 - 1/|E|`
(`uprob_colSimAttemptH_none`). -/
theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
  unfold colSimTruncH
  rw [OneWay.uprob_congr fun w => firstSome_eq_none_iff _,
    OneWay.uprob_pi_forall (ι := Fin N) (fun w => colSimAttemptH Com ℓn G c V w = none),
    uprob_colSimAttemptH_none Com ℓn G hm c V, Fintype.card_fin]

/-- **The truncated `S''` is statistically `(1 - 1/|E|)^N`-close to the honest view**
[PS10, proof of Proposition 128.8, "`view_{V*}` and `S''` can be distinguished with probability
at most `O(e^{-n})`"] (Claim-129.c): for every test set `T` of optional views,
`|Pr[T(S''_N)] - Pr[T(some view)]| ≤ (1 - 1/|E|)^N`.

**Proof sketch.** Decompose the event `T(S''_N)` by the index of the first successful attempt
(`firstSome`/`List.findSome?` on `List.finRange N`): the attempts have disjoint coins, so by
`uprob_prod`/`OneWay.uprob_update` the `t`-th term is `(1 - 1/|E|)^t · Pr[∃ v, attempt = some v ∧
T (some v)] = (1 - 1/|E|)^t (1/|E|) Pr[T (some view)]` (`uprob_colSimAttemptH_some`,
`uprob_colSimAttemptH_none`); the geometric sum gives
`Pr[T(S''_N)] = (1 - (1 - 1/|E|)^N) Pr[T (some view)] + (1 - 1/|E|)^N [T none]`
(`uprob_colSimTruncH_none`), within `(1 - 1/|E|)^N` of `Pr[T (some view)]`. -/
theorem statClose_colSimTruncH [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
    StatClose (colSimTruncH Com ℓn G c V N)
      (fun w : (Equiv.Perm (Fin 3) × (Fin n → Fin ℓn → Bool)) × ρ =>
        some (colRealView Com ℓn G c V w))
      ((1 - 1 / (edgeCount G : ℝ)) ^ N) := by
  have hθ : 0 ≤ 1 - 1 / (edgeCount G : ℝ) := by
    rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
    exact_mod_cast hm
  haveI : Nonempty (AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :=
    ⟨(((⟨0, hm⟩, 1), fun _ _ => false), Classical.arbitrary ρ)⟩
  exact statClose_truncAttempts (colSimAttemptH Com ℓn G c V) (colRealView Com ℓn G c V) hθ
    (uprob_colSimAttemptH_none Com ℓn G hm c V)
    (fun T => by rw [uprob_colSimAttemptH_some Com ℓn G hm c V T]; congr 1; ring) N

/-! ### The hybrids `S' ≈ S''` (Claim-129.d) -/

/-- The `k`-th hybrid simulator [PS10, proof of Proposition 128.8, "`S_k` proceeds as `S''` in
the first `k` iterations and like `S'` in the remaining ones"]: attempts `< k` are `S''`
attempts, the others `S'` attempts. -/
def colSimHyb (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N k : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  firstSome fun t => if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (w t)
    else colSimAttemptW Com ℓn G c V (w t)

/-- The zeroth hybrid is `S'`. -/
theorem colSimHyb_zero (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N 0 w = colSimTruncW Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncW]

/-- The `N`-th hybrid is `S''`. -/
theorem colSimHyb_self (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (w : Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    colSimHyb Com ℓn G c V N N w = colSimTruncH Com ℓn G c V N w := by
  simp [colSimHyb, colSimTruncH]

/-- The planted attempt of the hiding reduction: with the guessed edge `e₀` and permutation
`π₀` fixed, the commitments at the endpoints of `e₀` are made by the reduction itself (to
`π₀ (c i')`, `π₀ (c j')`, which `S'` and `S''` share) and all other commitments are read from
the challenger's vector `cv` (`msgAt`); the restart rule and the opening are as in the
attempts. -/
def colSimAttemptPlanted (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)) (cv : List Bool)
    (w : ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) :
    Option (ColView ρ) :=
  let p := edgeOf G e₀
  let c' : Fin n → Fin 3 := fun i => π₀ (c i)
  let com := Strategy.encodeMsgs (List.ofFn fun i =>
    if i = p.1 ∨ i = p.2 then Com (pairEncode (List.ofFn (padColor n (c' i))) (List.ofFn (w.1.2 i)))
    else msgAt cv i)
  if edgeIdxOfMsg (edgeCount G) (V com w.2) = (e₀ : ℕ) then
    some (w.2, com, colOpen c' w.1.2 p)
  else none

/-- The hiding reduction at hybrid index `k` with the worst `(e₀, π₀)` planted
[PS10, proof of Proposition 128.8, the reduction to the hiding property] (Claim-129.d): on a
challenge commitment vector `cv` it runs attempts `< k` as `S''`, attempt `k` as the planted
attempt on `cv`, the later attempts as `S'`, and hands the first success to `D`. -/
def colSimRed {ρ' : Type*} (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ)
    (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3))
    (D : Option (ColView ρ) → ρ' → Bool) :
    List Bool →
      (Fin N → ((Fin (edgeCount G) × Equiv.Perm (Fin 3)) × (Fin n → Fin ℓn → Bool)) × ρ) × ρ' →
        Bool :=
  fun cv z => D (firstSome fun t =>
    if (t : ℕ) < k then colSimAttemptH Com ℓn G c V (z.1 t)
    else if t = k then colSimAttemptPlanted Com ℓn G c V e₀ π₀ cv (z.1 t)
    else colSimAttemptW Com ℓn G c V (z.1 t)) z.2

/-- The `S'` colouring at an endpoint of `p` is the permuted witness colour. -/
private theorem simColorsW_of_mem {m : ℕ} (p : Fin m × Fin m) (π : Equiv.Perm (Fin 3))
    (c : Fin m → Fin 3) {i : Fin m} (hi : i = p.1 ∨ i = p.2) :
    simColorsW p π c i = π (c i) := by
  unfold simColorsW
  rcases hi with rfl | rfl
  · rw [if_pos rfl]
  · by_cases h : p.2 = p.1
    · rw [if_pos h, h]
    · rw [if_neg h, if_pos rfl]

/-- **The planted attempt on the `S'` commitment vector is an `S'` attempt** with the merged
randomness (the reduction's at the endpoints of the planted edge, the challenger's elsewhere)
and the planted `(e₀, π₀)`.

**Proof sketch.** The commitment messages agree position by position: at the endpoints both
commit to `π₀ (c i)` (`simColorsW_of_mem`) with the attempt's randomness, elsewhere the planted
attempt reads `Com ⟨pad (simColorsW … i), r' i⟩` off the challenge (`msgAt_multiCom`) and
`mergeAt` selects `r' i`; the openings agree since `mergeAt` is the attempt's randomness at the
endpoints (`mergeAt_fst`, `mergeAt_snd`); the success test and the output then coincide. -/
private theorem colSimAttemptPlanted_W (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r') w =
      colSimAttemptW Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i) =
      colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (simColorsW p ep.2 c i)))
        (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi, simColorsW_of_mem p ep.2 c hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd, simColorsW_of_mem p ep.2 c (Or.inl rfl),
      simColorsW_of_mem p ep.2 c (Or.inr rfl)]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (simColorsW p ep.2 c i)) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (simColorsW p ep.2 c) (mergeAt p w.1.2 r'),
        colOpen (simColorsW p ep.2 c) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **The planted attempt on the `S''` commitment vector is an `S''` attempt** with the merged
randomness and the planted `(e₀, π₀)`.

**Proof sketch.** As `colSimAttemptPlanted_W`: every position of the challenge commits to
`π₀ (c i)` (`msgAt_multiCom`), so the planted message is `colCommit (π₀ ∘ c)` with the merged
randomness, and the openings agree by `mergeAt_fst`, `mergeAt_snd`. -/
private theorem colSimAttemptPlanted_H (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool)
    (ep : Fin (edgeCount G) × Equiv.Perm (Fin 3)) (r' : Fin n → Fin ℓn → Bool)
    (w : AttemptCoins (edgeCount G) (Fin n → Fin ℓn → Bool) ρ) :
    colSimAttemptPlanted Com ℓn G c V ep.1 ep.2
        (multiCom Com (fun i => padColor n (ep.2 (c i))) r') w =
      colSimAttemptH Com ℓn G c V ((ep, mergeAt (edgeOf G ep.1) w.1.2 r'), w.2) := by
  set p := edgeOf G ep.1 with hp
  have hcom : Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i) =
      colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') := by
    show _ = Strategy.encodeMsgs (List.ofFn fun i =>
      Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (mergeAt p w.1.2 r' i))))
    congr 2
    funext i
    by_cases hi : i = p.1 ∨ i = p.2
    · rw [if_pos hi]
      simp only [mergeAt, hi, if_true]
    · rw [if_neg hi, msgAt_multiCom]
      simp only [mergeAt, hi, if_false]
  have hopen : colOpen (fun i => ep.2 (c i)) w.1.2 p =
      colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p := by
    unfold colOpen
    rw [mergeAt_fst, mergeAt_snd]
  show (if edgeIdxOfMsg (edgeCount G) (V (Strategy.encodeMsgs (List.ofFn fun i =>
      if i = p.1 ∨ i = p.2 then
        Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
      else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i)) w.2) =
        (ep.1 : ℕ) then
      some (w.2, Strategy.encodeMsgs (List.ofFn fun i =>
        if i = p.1 ∨ i = p.2 then
          Com (pairEncode (List.ofFn (padColor n (ep.2 (c i)))) (List.ofFn (w.1.2 i)))
        else msgAt (multiCom Com (fun i => padColor n (ep.2 (c i))) r') i),
        colOpen (fun i => ep.2 (c i)) w.1.2 p)
    else none) =
    (if edgeIdxOfMsg (edgeCount G)
        (V (colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r')) w.2) = (ep.1 : ℕ) then
      some (w.2, colCommit Com n ℓn (fun i => ep.2 (c i)) (mergeAt p w.1.2 r'),
        colOpen (fun i => ep.2 (c i)) (mergeAt p w.1.2 r') p)
    else none)
  rw [hcom, hopen]

/-- **`S' ≈ S''` by hybrids and multi-value hiding** [PS10, proof of Proposition 128.8,
"by the hybrid lemma … `D` distinguishes `S_k` and `S_{k+1}`"] (Claim-129.d, concrete): for
every distinguisher `D` of optional views there are a hybrid index `k < N`, an edge `e₀` and a
permutation `π₀` such that the advantage of `D` between the truncated `S'` and `S''`, divided
by `N`, is at most the advantage of the explicit reduction `colSimRed … k e₀ π₀ D` between the
commitment vectors (`multiCom`) to the `S'` colours `simColorsW (edgeOf G e₀) π₀ c` and to the
`S''` colours `π₀ ∘ c`.

**Deviation:** `N` hybrid steps (the text's `2n|E|`), the `6|E|` sub-hybrid replaced by the
non-uniform choice of `(e₀, π₀)`.

**Proof sketch.** `exists_hybrid_gap` on `k ↦ acceptProb (colSimHyb … N k) D`
(`colSimHyb_zero`, `colSimHyb_self` are the ends) gives `k` with gap `≥ distAdv / N`. The gap at
`k` is the average over attempt `k`'s `(e', π)` (`uprob_prod` on the `k`-th block,
`acceptProb_update`) of the difference between the planted attempt fed the `S'` vector and
fed the `S''` vector: on `cv = multiCom (pad ∘ simColorsW p π) r'` the planted attempt's
message is `colCommit (simColorsW p π) r''` for the randomness `r''` equal to `r'` off the
endpoints and to `w`'s randomness at the endpoints (`msgAt_encodeMsgs`, `List.getElem_ofFn`),
whose law is uniform (`OneWay.uprob_update` twice), so the acceptance probability is that of
hybrid `k`; likewise the `S''` vector gives hybrid `k + 1`. An average of absolute values
bounds the absolute value of the average, so some `(e₀, π₀)` attains at least the gap
(`Finset.exists_le_of_sum_le` / `uexp` averaging as in `Protocol.exists_proverCoins_le`). -/
theorem exists_colSimRed_ge [Fintype ρ] {ρ' : Type*} [Fintype ρ'] (hm : 0 < edgeCount G)
    (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) (hN : 0 < N)
    (D : Option (ColView ρ) → ρ' → Bool) :
    ∃ (k : Fin N) (e₀ : Fin (edgeCount G)) (π₀ : Equiv.Perm (Fin 3)),
      distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N ≤
        distAdv
          (fun r : Fin n → Fin ℓn → Bool =>
            multiCom Com (fun i => padColor n (simColorsW (edgeOf G e₀) π₀ c i)) r)
          (fun r : Fin n → Fin ℓn → Bool => multiCom Com (fun i => padColor n (π₀ (c i))) r)
          (colSimRed Com ℓn G c V N k e₀ π₀ D) := by
  obtain ⟨k, ep, h⟩ := exists_hybRed_ge hm hN (colSimAttemptH Com ℓn G c V)
    (colSimAttemptW Com ℓn G c V) D (edgeOf G)
    (fun ep cv => colSimAttemptPlanted Com ℓn G c V ep.1 ep.2 cv)
    (fun ep r => multiCom Com (fun i => padColor n (simColorsW (edgeOf G ep.1) ep.2 c i)) r)
    (fun ep r => multiCom Com (fun i => padColor n (ep.2 (c i))) r)
    (fun ep r' w => colSimAttemptPlanted_W Com ℓn G c V ep r' w)
    (fun ep r' w => colSimAttemptPlanted_H Com ℓn G c V ep r' w)
  refine ⟨k, ep.1, ep.2, ?_⟩
  have h0 : acceptProb (colSimTruncW Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0) D := by
    unfold acceptProb
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_zero Com ℓn G c V N z.1]; rfl)
  have hN' : acceptProb (colSimTruncH Com ℓn G c V N) D =
      acceptProb (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D := by
    unfold acceptProb
    exact congrArg uprob (funext fun z => by rw [← colSimHyb_self Com ℓn G c V N z.1]; rfl)
  calc distAdv (colSimTruncW Com ℓn G c V N) (colSimTruncH Com ℓn G c V N) D / N
      = distAdv (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N 0)
          (hybStd (colSimAttemptH Com ℓn G c V) (colSimAttemptW Com ℓn G c V) N N) D / N := by
        rw [distAdv, distAdv, h0, hN']
    _ ≤ _ := h

end Typed

/-! ### The string simulator [PS10, Algorithm 128.7] (Alg-128.7, Claim-128.a) -/

/-- The coin block of one attempt of the string simulator against `V'` at instance length
`N`: `(N+1)²` bits for the edge sampler, `3N` bits for the colour-pair sampler, `N ℓ(N)` bits
of commitment randomness and the tape of `V'`. -/
def colSimBlock (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .add (.add (.add (.normal 1 2) (.mul (.const 3) .var)) (.mul .var ℓ)) V'.coins

/-- The coin polynomial of the string simulator: `N²` blocks (at most `n|E| ≤ N²` attempts
are made). -/
def colSimCoins (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .mul (.mul .var .var) (colSimBlock ℓ V')

/-- The six distinct colour pairs enumerated by `Fin 6`. -/
noncomputable def pair6Equiv : Fin 6 ≃ ColorPair := (Fintype.equivFinOfCardEq card_colorPair).symm

/-- The simulator's distinct colour pair from `3T` tape bits: `T` rejection trials of three
bits, the pair `(0, 1)` on failure (D10). -/
noncomputable def sampleColorPair (T : ℕ) (r : List Bool) : ColorPair :=
  ((sampleIdx 6 3 T r).map pair6Equiv).getD ⟨(0, 1), by decide⟩

/-- One attempt of the string simulator [PS10, Algorithm 128.7, steps 1–4] on `(x, z)` with
the coin block `blk`: sample `e'` and the colour pair, commit to `simColors (edgeAt G e') (a, b)`
with the randomness read from the block, run `V'` on `[com]` with the rest of the block as its
tape, and output the encoded view `⟨⟨x, z⟩, ⟨r_{V'}, [com, opening]⟩⟩` if `V'` names `e'`;
if `E = ∅`, commit to all-zero colours and output the view with the empty opening. -/
noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  let n := (decGraph x).1
  let G : Graph n := (decGraph x).2
  let m := edgeCount G
  let N := x.length
  let e' := sampleEdgeIdx m N blk
  let ab := sampleColorPair N (blk.drop ((N + 1) ^ 2))
  let rr : Fin n → Fin (ℓ.eval n) → Bool :=
    fun i j => blk.getD ((N + 1) ^ 2 + 3 * N + i * ℓ.eval n + j) false
  let rV := blk.drop ((N + 1) ^ 2 + 3 * N + N * ℓ.eval N)
  match edgeAt G e' with
  | none => some (View.encode ⟨x, z, rV, [colCommit Com n (ℓ.eval n) (fun _ => 0) rr, []]⟩)
  | some p =>
    let c' := simColors p ab
    let com := colCommit Com n (ℓ.eval n) c' rr
    if edgeIdxOfMsg m (V'.next x z rV [com]) = e' then
      some (View.encode ⟨x, z, rV, [com, colOpen c' rr p]⟩)
    else none

/-- The string simulator [PS10, Algorithm 128.7] (Alg-128.7): up to `n|E|` attempts
(`colIterations x`, with `|E| = edgeCount G` counting ordered edge pairs; run-3 audit P11-3) on
the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
after `n|E|` failures; a single attempt if `E = ∅`.

**Deviation (D8):** truncated at `n|E|` attempts (strict PPT) instead of restarting until
success. -/
noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z r : List Bool) : List Bool :=
  let B := (colSimBlock ℓ V').eval x.length
  let att : ℕ → Option (List Bool) := fun t => colSimAttemptStr Com ℓ V' x z (colCoinSlice B t r)
  if edgeCount (decGraph x).2 = 0 then (att 0).getD []
  else ((List.range (colIterations x)).findSome? att).getD []

/-- **The simulator is a uniform PPT** [PS10, p. 128, "by construction it directly follows that
`S` is a p.p.t."] (Claim-128.a): for a polynomial-time `Com` and an efficient `V'` there is a
uniform `NUPPT` with coin polynomial `colSimCoins ℓ V'` whose activation on `⟨x, z⟩` at
parameter `|x|` is `colSim Com ℓ V' x z r`.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with
`V'.next x z rV [com] = A.runAtL |x| ⟨⟨x, z⟩, encodeMsgs [com]⟩ rV` (`Strategy.ofNUPPT_next`),
polynomial-time by `A.polyTimeComputable_output` and the pairing calculus. One attempt on the
raw layout is polynomial-time: the block is cut by `polyTimeComputable_pairTakePoly`/
`pairDropPoly` with the unary block length (`polyTimeComputable_unaryPoly`); the two samplers
by `polyTimeComputable_iterateFind` over the trials; the `n` commitments by
`polyTimeComputable_blockMap ℓ` composed with `hCom` and `polyTimeComputable_iterateEmit`
for the `encodeMsgs` fold (the colour at position `i` by `polyTimeComputable_ite` on the
comparison with the two endpoints); the comparison of `V'`'s reply with `e'` by
`polyTimeComputable_lenLe`-based modular arithmetic in unary; the view by
`PolyTimeComputable.pairEncode`. The loop over `t < n|E|` is
`Complexity.polyTimeComputable_iterateFind` with the attempt index in the state and the
accepting test "the attempt succeeded" (`R := mul var var`, `P :=` the layout length), the
`E = ∅` case by `polyTimeComputable_ite`; the result is packaged by `NUPPT.ofPolyTimeUniform`
with coins `colSimCoins ℓ V'` (`NUPPT.runAtL_ofPolyTimeUniform`,
`NUPPT.ofPolyTimeUniform_uniform`). -/
theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = colSimCoins ℓ V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = colSim Com ℓ V' x z (List.ofFn r) := by
  obtain ⟨S, hS, hc, hsim⟩ := ColSimMachine.exists_simulator hCom ℓ hV'
  exact ⟨S, hS, hc, fun x z r => (hsim x z r).trans rfl⟩

/-! ### Proposition 128.8 -/

/-- A negligible function of `√N` is negligible in `N` (the bookkeeping converting the
commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
Inf-4.4).

**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)` and `N ≥ max ((n₀ + 1)², 4^c · 4)`:
`n := Nat.sqrt N ≥ n₀` (`Nat.le_sqrt`) and `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`), so
`N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` once `n ≥ 4^c`, whence `|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
    Negligible fun N => μ (Nat.sqrt N) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := hμ (2 * c + 1)
  set K := max (max n₀ (4 ^ c)) 1 with hK
  refine ⟨K * K, fun N hN => ?_⟩
  set n := Nat.sqrt N with hn
  have hKn : K ≤ n := Nat.le_sqrt.2 hN
  have hn₀n : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hKn
  have h4n : 4 ^ c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hKn
  have h1n : 1 ≤ n := le_trans (le_max_right _ _) hKn
  have hNlt : N < (n + 1) * (n + 1) := Nat.lt_succ_sqrt N
  have hN2 : N ≤ 4 * (n * n) := by nlinarith
  have hNr : (N : ℝ) ≤ 4 * ((n : ℝ) * n) := by exact_mod_cast hN2
  have hμn : |μ n| < 1 / (n : ℝ) ^ (2 * c + 1) := hn₀ n hn₀n
  show |μ n| < 1 / (N : ℝ) ^ c
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1n
  have h4r : (4 : ℝ) ^ c ≤ n := by exact_mod_cast h4n
  have hNc : (N : ℝ) ^ c ≤ (n : ℝ) ^ (2 * c + 1) := by
    calc (N : ℝ) ^ c ≤ (4 * ((n : ℝ) * n)) ^ c := pow_le_pow_left₀ (Nat.cast_nonneg N) hNr c
      _ = 4 ^ c * (n : ℝ) ^ (2 * c) := by rw [_root_.mul_pow, pow_mul, sq]
      _ ≤ n * (n : ℝ) ^ (2 * c) := by gcongr
      _ = (n : ℝ) ^ (2 * c + 1) := by ring
  have hN1 : 1 ≤ N := by
    have hK1 : 1 ≤ K := le_max_right _ _
    have := Nat.mul_le_mul hK1 hK1
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  exact hμn.trans_le (one_div_le_one_div_of_le hNpos hNc)

/-- **One iteration of [PS10, Protocol 127.5] is zero-knowledge for `R_3COL`** [PS10,
Proposition 128.8 and Proposition 127.6, zero-knowledge half] (Prop-128.8, Prop-127.6 (b)):
for a commitment scheme `(Com, ℓ)`, for every efficient verifier `V'` there is a uniform PPT
simulator `S` such that for every auxiliary-input bound `Lz` and every non-uniform PPT `D`
there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| ≤ Lz(|x|)`, the
advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8, D10):** strict PPT simulator truncated at `n|E|` attempts, rejection-sampled
`π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
composition, [PS10, §7.2.1], out of scope).

**Proof sketch.** Fix `V'` efficient and take `S` from `exists_colSimulator hC.easy`. Fix
`Lz` and `D`. Let `B` be the hiding reduction machine of Claim-129.d (`colSimRed` at the
string level): at parameter `n` it carries in its advice the worst instance
`(x_n, y_n, z_n)` with `|x_n| = n²`, `|y_n| = 2n`, `|z_n| ≤ Lz(n²)` (`NUPPT.exists_withAdvice`
with the polynomial bound `add (add (mul var var) (mul (const 2) var)) (Lz.subst (mul var var))`),
the hybrid index `k_n`, `e₀`, `π₀` and `D.advice n²`; its coins are the other attempts' blocks
and `D`'s coins (`NUPPT.exists_split`); it runs `V'`'s machine and `D`'s machine
(`NUPPT.exists_seq`, `NUPPT.exists_comp`, `polyTimeComputable_iterateFind` for the attempts,
`polyTimeComputable_blockMap ℓ` with `hC.easy` for the commitments, `msgAt` projections by
`polyTimeComputable_iterate_pairFstD`). `hC.multiHiding var B` gives a negligible `ε_B` with
`distAdv (multiCom Com v ·) (multiCom Com v' ·) (B.distinguisherL n) ≤ ε_B n` for all `n`-vectors
`v, v'`. Put
`ε N := N · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N)) + 2 N² (1/4)^N + N² (1/2)^N + (1/4)^N`,
negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
(`C = 1`), `negligible_two_pow_neg` (with `(1/4)^N ≤ (1/2)^N`), `Negligible.add`,
`Negligible.const_mul`. Now fix `x = encGraph G`, `y = encColoring c` with `c` proper
(`R3COL`), `|z| ≤ Lz |x|`, `n` the vertex count, `m = |E|`. If `m = 0` the real view is
`⟨⟨x,z⟩,⟨r_V,[colCommit (π ∘ c) r, []]⟩⟩` and the simulated one has the all-zero colours, so
`D`'s advantage is at most `ε_B n` by `hC.multiHiding` applied to a machine `B'` built like
`B` (absorbed into `B` by a case split on `m` in its advice). Otherwise `n ≥ 2` and the chain is:
(1) the real view with `π = samplePerm3 |x| …` is within `(1/4)^{|x|}` of the view with a
uniform `π` (`statClose_samplePerm3`, `StatClose.prod` with `StatClose.refl` for the
randomness and `V'`'s tape, `StatClose.map` by the view encoding; `exec_succ` three times,
`decGraph_encGraph`, `decColoring_encColoring`, `colProver`/`colVerifier` unfold to
`colRealView` with `V com r_V := V'.next x z r_V [com]`); (2) `colSim` is `(Option.map enc
(colSimTrunc … (n m) w)).getD []` with the `t`-th attempt's coins read from the `t`-th block
(`colCoinSlice`, `colSimBlock`), within `n m ((1/2)^{|x|} + (1/4)^{|x|})` of the same with
uniform `(e'_t, (a_t, b_t))` (`statClose_sampleEdgeIdx`, the colour-pair analogue of
`statClose_samplePerm3`, `StatClose.prod` over the blocks); (3) `uprob_colSimTruncW_eq` makes
that the law of `colSimTruncW`; (4) `exists_colSimRed_ge` with `N := n m` gives `k, e₀, π₀`
with `distAdv (truncW) (truncH) D' ≤ n m · distAdv (X) (Y) (colSimRed …)`, and
`colSimRed … = B.distinguisherL n` up to the coin bijection (`acceptProb_comp_equiv`), so
`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`; (5) `statClose_colSimTruncH` and
`one_sub_inv_pow_mul_le_exp` give `distAdv (truncH) (some ∘ colRealView) D' ≤ e^{-n}`
(`distAdv_le_of_statClose`). The triangle inequality for `distAdv` (`abs_sub_le` on the
acceptance probabilities) sums the five terms, and `Nat.sqrt |x| = n` (`length_encGraph`,
`Nat.sqrt_eq`). -/
theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    ZK (colProtocol Com ℓ) R3COL := by
  sorry

/-- One iteration of [PS10, Protocol 127.5] is honest-verifier zero-knowledge for `R_3COL`
[PS10, Proposition 128.8 with the honest verifier] (`ZK.hvzk`, `colVerifier_efficient`). -/
theorem col_hvzk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
    HVZK (colProtocol Com ℓ) R3COL :=
  (col_zk hC).hvzk (colVerifier_efficient hC.easy ℓ)

/-- **[PS10, Proposition 127.6]: Protocol 127.5 is a zero-knowledge proof for `3COL`**
(Prop-127.6), assembled from its parts: one iteration is an interactive proof with efficient
prover and soundness error `1 - 1/|x| + (1/2)^{|x|}` (`col_efficientProverProofErr`) and is
zero-knowledge (`col_zk`), and the `n|E|`-fold repetition is an interactive proof with
efficient prover and negligible soundness error (`colRep_efficientProverProof`).

**Deviation (DQ5):** the zero-knowledge of the repeated protocol is sequential composition
[PS10, §7.2.1], outside Chapters 2–4, and is not claimed. -/
theorem col_zeroKnowledgeProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
        (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) ∧
      ZK (colProtocol Com ℓ) R3COL ∧
      EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL :=
  ⟨col_efficientProverProofErr hC, col_zk hC, colRep_efficientProverProof hC⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the 3-colouring simulator

The probability bookkeeping behind the zero-knowledge half of [PS10, Proposition 127.6]
(`ThreeColoring/Simulator.lean`): uniform indices hitting a fixed target, the first success of
a sequence of attempts, independent coordinates, and the two coin involutions of the hybrid
argument of [PS10, Proposition 128.8] — planting a fresh `(e', π)` into one attempt's coins
and merging a fresh randomness into one attempt's commitment randomness at the two endpoints
of an edge leave the coins uniform. None of these lemmas mentions the simulator itself; they
are stated for the coin layout `((e', π), r), ρ)` of one attempt (`ColSimLemmas.AttemptCoins`)
and for arbitrary events on tuples of attempts.

## Main definitions

* `TCSlib.Cryptography.ColSimLemmas.AttemptCoins` — the coin type of one attempt.
* `TCSlib.Cryptography.ColSimLemmas.mergeAt` — a randomness vector read from one source at
  the endpoints of an edge and from another elsewhere.
* `TCSlib.Cryptography.ColSimLemmas.plantEP`, `swapEP`, `swapR` — the planting map and the
  two coin involutions.

## Main results

* `TCSlib.Cryptography.ColSimLemmas.uprob_ne_idx`, `uprob_eq_idx_and` — a uniform index
  misses or hits a fixed in-range target with probability `1 - 1/m`, `1/m`.
* `TCSlib.Cryptography.ColSimLemmas.findSome?_finRange_cons_of_some`,
  `findSome?_finRange_cons_of_none` — the first success of `N + 1` attempts.
* `TCSlib.Cryptography.ColSimLemmas.uprob_and_add_uprob_not_and`, `uprob_prod_and` —
  splitting an event and independent coordinates.
* `TCSlib.Cryptography.ColSimLemmas.uprob_plantEP`, `uprob_mergeAt` — the two coin
  involutions preserve the uniform law.
* `TCSlib.Cryptography.ColSimLemmas.msgAt_multiCom` — the `i`-th message of a commitment
  vector.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Proposition 128.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (hybrid arguments at the concrete layer).
-/

namespace TCSlib.Cryptography.ColSimLemmas

open Complexity Turing Finset TCSlib.Cryptography

/-! ### Uniform indices -/

/-- A uniform index `b ∈ [m]` misses a fixed in-range target `f a` with probability `1 - 1/m`,
for every value of the independent coordinate `a` (`uprob_prod`, `uprob_not`,
`OneWay.uprob_eq_one_div_card`). -/
theorem uprob_ne_idx {m : ℕ} (hm : 0 < m) {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℕ) (hf : ∀ a, f a < m) :
    uprob (fun z : α × Fin m => ¬ f z.1 = (z.2 : ℕ)) = 1 - 1 / (m : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : Fin m => ¬ f a = (b : ℕ)) = 1 - 1 / (m : ℝ) := by
    intro a
    rw [uprob_not]
    have : (fun b : Fin m => f a = (b : ℕ)) = fun b : Fin m => b = ⟨f a, hf a⟩ := by
      funext b
      exact propext ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    rw [this, OneWay.uprob_eq_one_div_card, Fintype.card_fin]
  rw [show (fun a : α => uprob (fun b : Fin m => ¬ f a = (b : ℕ))) = fun _ => 1 - 1 / (m : ℝ)
    from funext h, OneWay.uexp_const]

/-- A uniform index `b ∈ [m]` hits the in-range target `f a` and the independent coordinate
`a` lies in `T` with probability `(1/m) · Pr[T]` (`uprob_prod`, `OneWay.uexp_indicator`). -/
theorem uprob_eq_idx_and {m : ℕ} (hm : 0 < m) {α : Type*} [Fintype α]
    (f : α → ℕ) (hf : ∀ a, f a < m) (T : α → Prop) :
    uprob (fun z : α × Fin m => f z.1 = (z.2 : ℕ) ∧ T z.1) = 1 / (m : ℝ) * uprob T := by
  classical
  have _ := hm
  rw [uprob_prod, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases hT : T a
  · simp only [hT, and_true, if_true]
    have : (fun b : Fin m => f a = (b : ℕ)) = fun b : Fin m => b = ⟨f a, hf a⟩ := by
      funext b
      exact propext ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    rw [this, OneWay.uprob_eq_one_div_card, Fintype.card_fin]
  · simp only [hT, and_false, if_false, uprob_false]

/-! ### The coins of one attempt -/

/-- The coins of one attempt of the simulators of [PS10, Algorithm 128.7]: the guessed edge
index, the colour permutation, the commitment randomness and the coins of `V*`. -/
abbrev AttemptCoins (m : ℕ) (R τ : Type*) : Type _ := ((Fin m × Equiv.Perm (Fin 3)) × R) × τ

/-- The coin reindexing `(((e', π), r), ρ) ↦ (((π, r), ρ), e')` of one attempt: the guessed
edge becomes the last, independent coordinate. -/
def attemptCoinsEquiv (m : ℕ) (R ρ : Type*) :
    AttemptCoins m R ρ ≃ ((Equiv.Perm (Fin 3) × R) × ρ) × Fin m where
  toFun w := (((w.1.1.2, w.1.2), w.2), w.1.1.1)
  invFun z := (((z.2, z.1.1.1), z.1.1.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The first success of a sequence of attempts -/

/-- `List.findSome?` over `List.finRange (N + 1)` on `Fin.cons a w` with a successful head
attempt returns its value (`List.finRange_succ`, `List.findSome?_cons_of_isSome`). -/
theorem findSome?_finRange_cons_of_some {α β : Type*} {N : ℕ} (F : β → Option α) {a : β}
    (w : Fin N → β) {v : α} (ha : F a = some v) :
    (List.finRange (N + 1)).findSome? (fun t => F ((Fin.cons a w : Fin (N + 1) → β) t)) =
      some v := by
  rw [List.finRange_succ, List.findSome?_cons_of_isSome]
  · simp [ha]
  · simp [ha]

/-- `List.findSome?` over `List.finRange (N + 1)` on `Fin.cons a w` with a failed head attempt
is the search over the tail (`List.findSome?_cons_of_isNone`, `List.findSome?_map`). -/
theorem findSome?_finRange_cons_of_none {α β : Type*} {N : ℕ} (F : β → Option α) {a : β}
    (w : Fin N → β) (ha : F a = none) :
    (List.finRange (N + 1)).findSome? (fun t => F ((Fin.cons a w : Fin (N + 1) → β) t)) =
      (List.finRange N).findSome? fun t => F (w t) := by
  rw [List.finRange_succ, List.findSome?_cons_of_isNone, List.findSome?_map]
  · simp only [Function.comp_def, Fin.cons_succ]
  · simp [ha]

/-- Splitting an event along a second event: `Pr[p ∧ q] + Pr[¬p ∧ q] = Pr[q]`. -/
theorem uprob_and_add_uprob_not_and {α : Type*} [Fintype α] (p q : α → Prop) :
    uprob (fun a => p a ∧ q a) + uprob (fun a => ¬ p a ∧ q a) = uprob q := by
  classical
  simp only [uprob_eq_card_filter]
  rw [← add_div]
  congr 1
  have h := filter_card_add_filter_neg_card_eq_card (s := univ.filter q) p
  rw [filter_filter, filter_filter] at h
  norm_cast
  rw [← h]
  congr 2 <;> ext a <;> simp [and_comm]

/-- Independent coordinates: `Pr[A(z.1) ∧ B(z.2)] = Pr[A] · Pr[B]` on a product
(`uprob_prod`, `OneWay.uexp_indicator`). -/
theorem uprob_prod_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop) :
    uprob (fun z : α × β => A z.1 ∧ B z.2) = uprob A * uprob B := by
  classical
  rw [uprob_prod, mul_comm, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases ha : A a
  · simp [ha]
  · simp [ha, uprob_false]

/-! ### Merged randomness -/

/-- The randomness `a` at the endpoints of `p`, `b` elsewhere (the randomness of the planted
attempt's commitment vector in the hybrid argument of [PS10, Proposition 128.8]: the
reduction's own at the endpoints of the guessed edge, the challenger's elsewhere). -/
def mergeAt {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    Fin m → Fin ℓ → Bool :=
  fun i => if i = p.1 ∨ i = p.2 then a i else b i

/-- `mergeAt` at the first endpoint. -/
theorem mergeAt_fst {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    mergeAt p a b p.1 = a p.1 := by
  simp [mergeAt]

/-- `mergeAt` at the second endpoint. -/
theorem mergeAt_snd {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    mergeAt p a b p.2 = a p.2 := by
  simp [mergeAt]

/-- Merging twice on the left. -/
theorem mergeAt_mergeAt_left {m ℓ : ℕ} (p : Fin m × Fin m) (a b c : Fin m → Fin ℓ → Bool) :
    mergeAt p (mergeAt p a b) c = mergeAt p a c := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- Merging twice on the right. -/
theorem mergeAt_mergeAt_right {m ℓ : ℕ} (p : Fin m × Fin m) (a b c : Fin m → Fin ℓ → Bool) :
    mergeAt p a (mergeAt p b c) = mergeAt p a c := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- Merging a function with itself. -/
theorem mergeAt_self {m ℓ : ℕ} (p : Fin m × Fin m) (a : Fin m → Fin ℓ → Bool) :
    mergeAt p a a = a := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- The `i`-th message of the commitment vector `multiCom Com v r` is `Com ⟨v i, r i⟩`
(`msgAt_encodeMsgs`, `List.getElem_ofFn`). -/
theorem msgAt_multiCom (Com : List Bool → List Bool) {q n ℓ : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin ℓ → Bool) (i : Fin q) :
    msgAt (multiCom Com v r) i = Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))) := by
  rw [multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The two coin involutions of the hybrid argument -/

section Involutions

variable {m : ℕ} {R τ : Type*}

/-- Replacing the `(e', π)` part of an attempt's coins. -/
def plantEP (ep : Fin m × Equiv.Perm (Fin 3)) (w : AttemptCoins m R τ) : AttemptCoins m R τ :=
  ((ep, w.1.2), w.2)

/-- The involution exchanging the external `(e', π)` with the one of attempt `k`. -/
def swapEP {N : ℕ} (k : Fin N) (ρ' : Type*) :
    (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') ≃
      (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') where
  toFun y := ((y.2.1 k).1.1, (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2))
  invFun y := ((y.2.1 k).1.1, (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2))
  left_inv y := by
    rcases y with ⟨ep, w, r⟩
    simp only [Function.update_self, plantEP, Function.update_idem, Prod.mk.eta,
      Function.update_eq_self]
  right_inv y := by
    rcases y with ⟨ep, w, r⟩
    simp only [Function.update_self, plantEP, Function.update_idem, Prod.mk.eta,
      Function.update_eq_self]

/-- **Planting a uniform `(e', π)` at attempt `k` leaves the coins uniform**: the law of the
tuple with attempt `k`'s `(e', π)` replaced by an independent uniform one is the law of the
tuple (`swapEP` is a bijection, `uprob_comp_equiv`, `uprob_fst`). -/
theorem uprob_plantEP (hm : 0 < m) [Fintype R] [Fintype τ] {N : ℕ} (k : Fin N) {ρ' : Type*}
    [Fintype ρ'] (P : (Fin N → AttemptCoins m R τ) × ρ' → Prop) :
    uprob (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2)) = uprob P := by
  haveI : Nonempty (Fin m × Equiv.Perm (Fin 3)) := ⟨(⟨0, hm⟩, 1)⟩
  have h := uprob_comp_equiv (swapEP (m := m) (R := R) (τ := τ) k ρ')
    (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') => P y.2)
  rw [show (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') =>
      P (swapEP (m := m) (R := R) (τ := τ) k ρ' y).2) = fun y =>
      P (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2) from rfl] at h
  rw [h, ← uprob_comp_equiv (Equiv.prodComm _ _)
    (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') => P y.2)]
  exact uprob_fst P

end Involutions

section MergeInvolution

variable {m n ℓ : ℕ} {τ : Type*}

/-- The involution exchanging the challenger's randomness with attempt `k`'s randomness off
the endpoints of `p`. -/
def swapR {N : ℕ} (k : Fin N) (p : Fin n × Fin n) (ρ' : Type*) :
    (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') ≃
      (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') where
  toFun y := (mergeAt p y.1 (y.2.1 k).1.2,
    (Function.update y.2.1 k (((y.2.1 k).1.1, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2))
  invFun y := (mergeAt p y.1 (y.2.1 k).1.2,
    (Function.update y.2.1 k (((y.2.1 k).1.1, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2))
  left_inv y := by
    rcases y with ⟨r', w, r⟩
    simp only [Function.update_self, Function.update_idem, mergeAt_mergeAt_left,
      mergeAt_mergeAt_right, mergeAt_self, Prod.mk.eta, Function.update_eq_self]
  right_inv y := by
    rcases y with ⟨r', w, r⟩
    simp only [Function.update_self, Function.update_idem, mergeAt_mergeAt_left,
      mergeAt_mergeAt_right, mergeAt_self, Prod.mk.eta, Function.update_eq_self]

/-- **Merging a fresh uniform randomness into attempt `k` leaves the coins uniform**: the law
of the tuple with attempt `k` replaced by `((ep, mergeAt p r_k r'), ρ_k)` for an independent
uniform `r'` is the law of the tuple with attempt `k` replaced by `((ep, r_k), ρ_k)`.

**Proof sketch.** Reindex the coins by the involution `swapR` (`uprob_comp_equiv`), which
exchanges `r'` and `r_k` off the endpoints of `p` and leaves the planted tuple invariant
(`Function.update_self`, `Function.update_idem`); the event then no longer depends on the
first coordinate, which `uprob_fst` removes. -/
theorem uprob_mergeAt [Fintype τ] {N : ℕ} (k : Fin N) (p : Fin n × Fin n)
    (ep : Fin m × Equiv.Perm (Fin 3)) {ρ' : Type*} [Fintype ρ']
    (P : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' → Prop) :
    uprob (fun y : (Fin n → Fin ℓ → Bool) ×
        ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
        P (Function.update y.2.1 k ((ep, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2)) =
      uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
        P (Function.update z.1 k (plantEP ep (z.1 k)), z.2)) := by
  have h := uprob_comp_equiv (swapR (m := m) (τ := τ) k p ρ')
    (fun y : (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP ep (y.2.1 k)), y.2.2))
  have hfun : (fun y : (Fin n → Fin ℓ → Bool) ×
      ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update (swapR (m := m) (τ := τ) k p ρ' y).2.1 k
        (plantEP ep ((swapR (m := m) (τ := τ) k p ρ' y).2.1 k)),
        (swapR (m := m) (τ := τ) k p ρ' y).2.2)) =
      fun y => P (Function.update y.2.1 k ((ep, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2),
        y.2.2) := by
    funext y
    rcases y with ⟨r', w, r⟩
    simp only [swapR, plantEP, Equiv.coe_fn_mk, Function.update_self, Function.update_idem]
  rw [hfun] at h
  rw [h, ← uprob_comp_equiv (Equiv.prodComm _ _)
    (fun y : (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP ep (y.2.1 k)), y.2.2))]
  exact uprob_fst (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
    P (Function.update z.1 k (plantEP ep (z.1 k)), z.2))

end MergeInvolution

/-! ### Truncated attempts: the first success of `N` independent attempts -/

section Truncation

variable {W U α : Type*} [Fintype W] [Fintype U]

/-- The first success among `N` independent attempts `att (w t)` (`none` if all fail): the
common shape of the truncated simulators `colSimTrunc`, `colSimTruncW`, `colSimTruncH`. -/
def truncAttempts (att : W → Option α) (N : ℕ) (w : Fin N → W) : Option α :=
  (List.finRange N).findSome? fun t => att (w t)

/-- One step of the recursion for the law of the truncated attempts: if one attempt fails with
probability `θ` and succeeds with a value in `T` with probability `(1 - θ) · Pr[T(view)]`, then
`Pr[T(S_{N+1})] = θ · Pr[T(S_N)] + (1 - θ) · Pr[T(some view)]`.

**Proof sketch.** Split the coins of the `N + 1` attempts as (first attempt, remaining
attempts) by `Fin.consEquiv` (`uprob_comp_equiv`) and the event along "the first attempt
fails" (`uprob_and_add_uprob_not_and`): when it fails, `S_{N+1}` is `S_N` on the remaining
coins (`findSome?_finRange_cons_of_none`), and the two factors are independent
(`uprob_prod_and`); when it succeeds the output is its value
(`findSome?_finRange_cons_of_some`), an event of the first coordinate alone (`uprob_fst`). -/
theorem uprob_truncAttempts_succ [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) (T : Option α → Prop) :
    uprob (fun w : Fin (N + 1) → W => T (truncAttempts att (N + 1) w)) =
      θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) +
        (1 - θ) * uprob (fun u => T (some (view u))) := by
  rw [← uprob_comp_equiv (Fin.consEquiv fun _ : Fin (N + 1) => W)]
  have hsplit := uprob_and_add_uprob_not_and
    (fun z : W × (Fin N → W) => att z.1 = none)
    (fun z => T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z)))
  have hA : uprob (fun z : W × (Fin N → W) => att z.1 = none ∧
        T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z))) =
      θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) := by
    rw [← hnone, ← uprob_prod_and (fun a : W => att a = none)
      (fun w : Fin N → W => T (truncAttempts att N w))]
    refine OneWay.uprob_congr fun z => and_congr_right fun hz => ?_
    rw [show (Fin.consEquiv fun _ : Fin (N + 1) => W) z = Fin.cons z.1 z.2 from rfl]
    unfold truncAttempts
    rw [findSome?_finRange_cons_of_none _ _ hz]
  have hB : uprob (fun z : W × (Fin N → W) => ¬ att z.1 = none ∧
        T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z))) =
      (1 - θ) * uprob (fun u => T (some (view u))) := by
    rw [← hsome (fun v => T (some v)),
      ← uprob_fst (β := Fin N → W) (fun a : W => ∃ v, att a = some v ∧ T (some v))]
    refine OneWay.uprob_congr fun z => ?_
    rw [show (Fin.consEquiv fun _ : Fin (N + 1) => W) z = Fin.cons z.1 z.2 from rfl]
    unfold truncAttempts
    constructor
    · rintro ⟨hne, hT⟩
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      exact ⟨v, hv, by rwa [findSome?_finRange_cons_of_some _ _ hv] at hT⟩
    · rintro ⟨v, hv, hT⟩
      exact ⟨by simp [hv], by rwa [findSome?_finRange_cons_of_some _ _ hv]⟩
  rw [← hsplit, hA, hB]

/-- The distance between the law of the truncated attempts and the law of `some view` shrinks
by the factor `θ` with every attempt: `|Pr[T(S_N)] - Pr[T(some view)]| ≤ θ^N`.

**Proof sketch.** Induction on `N`. For `N = 0` the output is `none` and both probabilities
lie in `[0, 1]`. The step is `uprob_truncAttempts_succ`:
`Pr[T(S_{N+1})] - p = θ (Pr[T(S_N)] - p)`. -/
theorem abs_uprob_truncAttempts_sub_le [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hθ : 0 ≤ θ) (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) (T : Option α → Prop) :
    |uprob (fun w : Fin N → W => T (truncAttempts att N w)) -
      uprob (fun u => T (some (view u)))| ≤ θ ^ N := by
  induction N with
  | zero =>
    have h0 : ∀ w : Fin 0 → W, truncAttempts att 0 w = none := fun w => by
      simp [truncAttempts]
    have hp0 := uprob_nonneg fun u => T (some (view u))
    have hp1 := uprob_le_one fun u => T (some (view u))
    simp only [h0, pow_zero]
    by_cases hT : T none
    · simp only [hT, uprob_true]
      rw [abs_le]
      constructor <;> linarith
    · simp only [hT, uprob_false]
      rw [abs_le]
      constructor <;> linarith
  | succ N ih =>
    rw [uprob_truncAttempts_succ att view hnone hsome N T]
    have h : θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) +
        (1 - θ) * uprob (fun u => T (some (view u))) - uprob (fun u => T (some (view u))) =
        θ * (uprob (fun w : Fin N → W => T (truncAttempts att N w)) -
          uprob (fun u => T (some (view u)))) := by ring
    rw [h, abs_mul, abs_of_nonneg hθ, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right ih hθ

/-- **Truncated attempts are statistically `θ^N`-close to the ideal output** when one attempt
fails with probability `θ` and, conditioned on success, has exactly the law of the ideal
output (`abs_uprob_truncAttempts_sub_le`). -/
theorem statClose_truncAttempts [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hθ : 0 ≤ θ) (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) :
    StatClose (truncAttempts att N) (fun u => some (view u)) (θ ^ N) :=
  fun T => abs_uprob_truncAttempts_sub_le att view hθ hnone hsome N T

end Truncation

/-! ### The hybrid argument over the attempts -/

section Hybrid

variable {W α ρ' : Type*}

/-- The `k`-th standard hybrid: attempts `< k` of type `H`, the others of type `Wa`
(the shape of `colSimHyb`). -/
def hybStd (H Wa : W → Option α) (N k : ℕ) (w : Fin N → W) : Option α :=
  (List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (w t) else Wa (w t)

/-- The hybrid with an arbitrary attempt `A` at position `k`: attempts `< k` are of type `H`,
attempt `k` is `A`, the later attempts are of type `Wa`; `D` judges the first success
(the shape of `colSimRed`, with `A` the planted attempt). -/
def hybGen (H Wa : W → Option α) {N : ℕ} (k : Fin N) (A : W → Option α)
    (D : Option α → ρ' → Bool) (z : (Fin N → W) × ρ') : Bool :=
  D ((List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (z.1 t)
    else if t = k then A (z.1 t) else Wa (z.1 t)) z.2

/-- Replacing attempt `k`'s coins and its attempt function consistently leaves the hybrid
unchanged. -/
theorem hybGen_update (H Wa : W → Option α) {N : ℕ} (k : Fin N) {A A' : W → Option α}
    (D : Option α → ρ' → Bool) {w : Fin N → W} {w' : W} (h : A (w k) = A' w') (r : ρ') :
    hybGen H Wa k A D (w, r) = hybGen H Wa k A' D (Function.update w k w', r) := by
  unfold hybGen
  congr 2
  funext t
  by_cases ht : t = k
  · subst ht
    simp only [Function.update_self, lt_irrefl, if_false, if_true, h]
  · simp only [Function.update_of_ne ht, ht, if_false]

/-- The `k`-th standard hybrid is the generic hybrid with a `Wa` attempt at `k`. -/
theorem hybGen_W (H Wa : W → Option α) {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    (w : Fin N → W) (r : ρ') :
    D (hybStd H Wa N k w) r = hybGen H Wa k Wa D (w, r) := by
  unfold hybGen hybStd
  congr 2
  funext t
  split_ifs <;> rfl

/-- The `(k+1)`-th standard hybrid is the generic hybrid with an `H` attempt at `k`. -/
theorem hybGen_H (H Wa : W → Option α) {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    (w : Fin N → W) (r : ρ') :
    D (hybStd H Wa N (k + 1) w) r = hybGen H Wa k H D (w, r) := by
  unfold hybGen hybStd
  congr 2
  funext t
  by_cases h1 : (t : ℕ) < k
  · rw [if_pos (Nat.lt_succ_of_lt h1), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : t = k
    · rw [if_pos h2, if_pos (by rw [h2]; exact Nat.lt_succ_self _)]
    · have h3 : ¬ (t : ℕ) < k + 1 := fun h => h2 (Fin.ext (by omega))
      rw [if_neg h2, if_neg h3]

end Hybrid

section HybridCoins

variable {m n ℓ : ℕ} {τ α ρ' : Type*} [Fintype τ] [Fintype ρ']

/-- The acceptance probability of `D` on the generic hybrid with attempt `k`'s `(e', π)` fixed
to `ep`. -/
noncomputable def hybAcc (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) {N : ℕ}
    (k : Fin N) (A : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    (D : Option α → ρ' → Bool) (ep : Fin m × Equiv.Perm (Fin 3)) : ℝ :=
  uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
    hybGen H Wa k A D (Function.update z.1 k (plantEP ep (z.1 k)), z.2) = true)

/-- The acceptance probability of `D` on a generic hybrid is the average over attempt `k`'s
`(e', π)` of the fixed-`(e', π)` acceptance probabilities (`uprob_plantEP`, `uprob_prod`). -/
theorem uprob_hybGen_eq_uexp (hm : 0 < m)
    (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) {N : ℕ} (k : Fin N)
    (A : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) (D : Option α → ρ' → Bool) :
    uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
        hybGen H Wa k A D z = true) =
      uexp (hybAcc H Wa k A D) := by
  rw [← uprob_plantEP hm k
    (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
      hybGen H Wa k A D z = true), uprob_prod]
  rfl

/-- A reduction that plants a challenge `cv` into attempt `k` accepts, on challenges that
make the planted attempt an `A'` attempt with merged randomness, with the fixed-`ep`
acceptance probability of the `A'` hybrid (`hybGen_update`, `uprob_mergeAt`). -/
theorem acceptProb_hybGen_planted (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    {Pl : List Bool → AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α}
    {X : (Fin n → Fin ℓ → Bool) → List Bool}
    {A' : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α} (p : Fin n × Fin n)
    (ep : Fin m × Equiv.Perm (Fin 3))
    (hPl : ∀ r' w, Pl (X r') w = A' ((ep, mergeAt p w.1.2 r'), w.2)) :
    acceptProb X (fun cv z => hybGen H Wa k (Pl cv) D z) = hybAcc H Wa k A' D ep := by
  unfold acceptProb hybAcc
  rw [← uprob_mergeAt k p ep
    (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
      hybGen H Wa k A' D z = true)]
  congr 1
  funext y
  show (hybGen H Wa k (Pl (X y.1)) D (y.2.1, y.2.2) = true) = _
  rw [hybGen_update H Wa k D (hPl y.1 (y.2.1 k)) y.2.2]

/-- **The hybrid argument over the attempts with a planted worst `(e₀, π₀)`** (the concrete
content of Claim-129.d): if the planted attempt on a challenge from `X ep` is a `Wa` attempt
and on a challenge from `Y ep` an `H` attempt (each with the planted `ep` and merged
randomness), then for every `D` some hybrid index `k` and some `ep` satisfy
`distAdv (H_0) (H_N) D / N ≤ distAdv (X ep) (Y ep) (reduction at k planting ep)`.

**Proof sketch.** `exists_hybrid_gap` on `k ↦ acceptProb (hybStd H Wa N k) D` gives `k` with
gap `≥ distAdv / N`; the gap at `k` is `|E_{ep} (hybAcc Wa ep - hybAcc H ep)|`
(`hybGen_W`, `hybGen_H`, `uprob_hybGen_eq_uexp`), bounded by its value at some `ep`
(`CommitmentLemmas.exists_abs_uexp_le`), which is the reduction's advantage
(`acceptProb_hybGen_planted` twice). -/
theorem exists_hybRed_ge (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) (D : Option α → ρ' → Bool)
    (p : Fin m → Fin n × Fin n)
    (Pl : Fin m × Equiv.Perm (Fin 3) → List Bool →
      AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    (X Y : Fin m × Equiv.Perm (Fin 3) → (Fin n → Fin ℓ → Bool) → List Bool)
    (hX : ∀ ep r' w, Pl ep (X ep r') w = Wa ((ep, mergeAt (p ep.1) w.1.2 r'), w.2))
    (hY : ∀ ep r' w, Pl ep (Y ep r') w = H ((ep, mergeAt (p ep.1) w.1.2 r'), w.2)) :
    ∃ (k : Fin N) (ep : Fin m × Equiv.Perm (Fin 3)),
      distAdv (hybStd H Wa N 0) (hybStd H Wa N N) D / N ≤
        distAdv (X ep) (Y ep) (fun cv z => hybGen H Wa k (Pl ep cv) D z) := by
  haveI : Nonempty (Fin m × Equiv.Perm (Fin 3)) := ⟨(⟨0, hm⟩, 1)⟩
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (hybStd H Wa N i) D) hN
  set kf : Fin N := ⟨k, hk⟩ with hkf
  have hPk : acceptProb (hybStd H Wa N k) D = uexp (hybAcc H Wa kf Wa D) := by
    rw [← uprob_hybGen_eq_uexp hm H Wa kf]
    unfold acceptProb
    congr 1
    funext z
    rw [← hybGen_W H Wa kf D z.1 z.2]
  have hPk1 : acceptProb (hybStd H Wa N (k + 1)) D = uexp (hybAcc H Wa kf H D) := by
    rw [← uprob_hybGen_eq_uexp hm H Wa kf]
    unfold acceptProb
    congr 1
    funext z
    rw [← hybGen_H H Wa kf D z.1 z.2]
  obtain ⟨ep₀, hep₀⟩ := CommitmentLemmas.exists_abs_uexp_le
    (fun ep => hybAcc H Wa kf Wa D ep - hybAcc H Wa kf H D ep)
  refine ⟨kf, ep₀, ?_⟩
  calc distAdv (hybStd H Wa N 0) (hybStd H Wa N N) D / N
      ≤ |acceptProb (hybStd H Wa N k) D - acceptProb (hybStd H Wa N (k + 1)) D| := hgap
    _ = |uexp (fun ep => hybAcc H Wa kf Wa D ep - hybAcc H Wa kf H D ep)| := by
        rw [hPk, hPk1, HardcoreBit.uexp_sub]
    _ ≤ |hybAcc H Wa kf Wa D ep₀ - hybAcc H Wa kf H D ep₀| := hep₀
    _ = _ := by
        rw [distAdv, acceptProb_hybGen_planted H Wa kf D (p ep₀.1) ep₀ (hX ep₀),
          acceptProb_hybGen_planted H Wa kf D (p ep₀.1) ep₀ (hY ep₀)]

end HybridCoins

end TCSlib.Cryptography.ColSimLemmas

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorNumeric
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3-colouring simulator as a polynomial-time machine

The machine behind Claim-128.a of `ThreeColoring/Simulator.lean` (`exists_colSimulator`): the
string-level simulator of [PS10, Algorithm 128.7], truncated at `n|E|` attempts (D8), is a
polynomial-time function of its machine layout `⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`, hence a uniform
`Complexity.NUPPT`. The shadows of the frozen string definitions and the numeric form
`attemptNum` of one attempt are in `ThreeColoring/SimulatorNumeric.lean`; this file proves each
ingredient of `attemptNum` polynomial-time in unary with the toolkit of
`EncodingMachines.lean` (bit counting, finite tables, the rejection sampler through
`EncodingPermutations.trialIdx_poly`, a loop emitting a computed number of chunks) and
assembles one attempt (`attemptAt_poly`) and the loop over the attempts (`sim_poly`, through
`EncodingMachines.polyTimeComputable_firstIdx`).

## Main definitions

* `TCSlib.Cryptography.ColSimMachine.simX`, `simZ`, `simR`, `attemptAt` — the projections of
  the simulator's layout and the attempt at a given index on it.

## Main results

* `TCSlib.Cryptography.ColSimMachine.countBits_poly`, `table_poly`, `sampleNum_poly`,
  `emitLoop_poly` — the generic machine helpers.
* `TCSlib.Cryptography.ColSimMachine.attemptNum_poly`, `attemptAt_poly` — one attempt is
  polynomial-time.
* `TCSlib.Cryptography.ColSimMachine.sim_poly` — the simulator is a polynomial-time function
  of its layout.
* `TCSlib.Cryptography.ColSimMachine.exists_simulator` — the simulator is a uniform PPT
  (Claim-128.a, shadow form).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7 Algorithm 128.7, p. 128.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColSimMachine

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Generic machine helpers -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- One more position adds the bit at that position to the count. -/
theorem countBits_succ (x : List Bool) (k : ℕ) :
    countBits x (k + 1) = countBits x k + (x.getD k false).toNat := by
  unfold countBits
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
  cases x.getD k false <;> simp

/-- The count of set bits is at most the number of positions. -/
theorem countBits_le (x : List Bool) (k : ℕ) : countBits x k ≤ k := by
  unfold countBits
  exact (List.length_filter_le _ _).trans (by simp)

/-- **Counting set bits is unary polynomial-time**: `z ↦ 1^{countBits (X z) (K z)}` for a
polynomial-time word `X` and a unary bound `K`.

**Proof sketch.** A counted loop (`EncodingMachines.polyTimeComputable_loopState`) of `K z`
rounds from `[]` whose round `i` appends a token iff bit `i` of `X z` is set
(`EncodingMachines.getBit_poly`), truncated to `K z` tokens so that every update is bounded; on
the genuine orbit the truncation is the identity (`countBits_le`, `countBits_succ`). -/
theorem countBits_poly {X : List Bool → List Bool} (hX : PolyTimeComputable X)
    {K : List Bool → ℕ} (hK : PolyTimeComputable fun z => List.replicate (K z) true) :
    PolyTimeComputable fun z => List.replicate (countBits (X z) (K z)) true := by
  let upd : List Bool → List Bool := fun w =>
    (pairSndD (pairSndD w) ++
      (if (X (pairFstD w)).getD (pairFstD (pairSndD w)).length false = true then [true] else [])).take
        (K (pairFstD w))
  have hbit : PolyTimeComputable fun w =>
      [(X (pairFstD w)).getD (pairFstD (pairSndD w)).length false] :=
    getBit_poly (hX.comp polyTimeComputable_pairFstD)
      (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  have hupd : PolyTimeComputable upd :=
    truncate_poly ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).append
      (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const [])))
      (unaryComp_poly hK polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hK.output_length_le
  have hKC : ∀ x, K x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd (polyTimeComputable_const []) hK
    (PolyExpr.normal C c) (fun x => by simp) (fun x s => by
      show ((_ : List Bool).take (K (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hKC x))
  convert hloop using 1
  funext z
  have key : ∀ i, i ≤ K z →
      loopState upd (fun _ => []) z i = List.replicate (countBits (X z) i) true := by
    intro i
    induction i with
    | zero => intro _; simp [countBits]
    | succ i ih =>
      intro hi
      rw [loopState_succ, ih (Nat.le_of_succ_le hi)]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      have hle : countBits (X z) i + ((X z).getD i false).toNat ≤ K z := by
        have := countBits_le (X z) (i + 1)
        rw [countBits_succ] at this
        omega
      have hrep : List.replicate (countBits (X z) i) true ++
          (if (X z).getD i false = true then [true] else []) =
          List.replicate (countBits (X z) i + ((X z).getD i false).toNat) true := by
        cases (X z).getD i false
        · simp
        · rw [if_pos rfl, ← List.replicate_succ', Bool.toNat_true]
      rw [hrep, List.take_replicate, min_eq_right hle, countBits_succ]
  exact (key (K z) le_rfl).symm

/-- **Finite table lookup**: for any `f : ℕ → List Bool` and bound `K`, `z ↦ f (min (V z) K)` is
polynomial-time for a unary `V` (induction on `K`, one `polyTimeComputable_ite` per entry). -/
theorem table_poly (f : ℕ → List Bool) {V : List Bool → ℕ}
    (hV : PolyTimeComputable fun z => List.replicate (V z) true) :
    ∀ K : ℕ, PolyTimeComputable fun z => f (min (V z) K)
  | 0 => by simpa using polyTimeComputable_const (f 0)
  | K + 1 => by
    have h := polyTimeComputable_ite (leTest_poly hV (unaryConst_poly K)) (table_poly f hV K)
      (polyTimeComputable_const (f (K + 1)))
    refine ptc_congr h fun z => ?_
    by_cases hz : V z ≤ K
    · simp [hz, min_eq_left (hz.trans (Nat.le_succ K))]
    · simp [hz, min_eq_right (Nat.succ_le_of_lt (not_le.1 hz))]

/-- **The rejection sampler is unary polynomial-time** (`EncodingPermutations.trialIdx_poly`
for the first accepted trial, `blockVal_poly` for its value, `polyTimeComputable_ite`). -/
theorem sampleNum_poly {M K T M' : List Bool → ℕ} {R : List Bool → List Bool}
    (hM : PolyTimeComputable fun z => List.replicate (M z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (T z) true) (hR : PolyTimeComputable R)
    (hM' : PolyTimeComputable fun z => List.replicate (M' z) true) (hKM : ∀ z, 2 ^ K z ≤ M' z) :
    PolyTimeComputable fun z => List.replicate (sampleNum (M z) (K z) (T z) (R z)) true := by
  have htr := trialIdx_poly hM hK hT hR (unaryConst_poly 0) hM' hKM
  have hbv := blockVal_poly hR (unaryMul_poly htr hK) hK hM' hKM
  refine ptc_congr (polyTimeComputable_ite (ltTest_poly htr hT) hbv hM) fun z => ?_
  unfold sampleNum
  by_cases h : trialIdx (M z) (K z) (T z) (R z) 0 < T z <;> simp [h]

/-- Concatenating the first `L` chunks of a longer range. -/
theorem flatMap_range_ite (f : ℕ → List Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then f i else []) =
      (List.range (min N L)).flatMap f
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite f L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, min_eq_left h.le, min_eq_left (Nat.succ_le_of_lt h), List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
    · rw [if_neg h, min_eq_right (not_lt.1 h), min_eq_right ((not_lt.1 h).trans (Nat.le_succ N)),
        List.append_nil]

/-- **A loop emitting `L z` chunks is polynomial-time** when the chunk `F z i` is polynomial-time
in `⟨1^i, z⟩`, the count `L` is unary and bounded by `|z| + 1`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` on the counter step
`EncodingMachines.cstep` from `⟨[], z⟩` (orbit `⟨1^i, z⟩`, `cstep_iterate`, bounded by
`cstep_horbit`) with the chunk `F z i` emitted while `i < L z` and nothing afterwards
(`polyTimeComputable_ite`, `ltTest_poly`); the `|z| + 3` emitted chunks concatenate to the
first `L z` ones (`flatMap_range_ite`). -/
theorem emitLoop_poly {F : List Bool → ℕ → List Bool}
    (hF : PolyTimeComputable fun w => F (pairSndD w) (pairFstD w).length)
    {L : List Bool → ℕ} (hL : PolyTimeComputable fun z => List.replicate (L z) true)
    (hLle : ∀ z, L z ≤ z.length + 1) :
    PolyTimeComputable fun z => (List.range (L z)).flatMap (F z) := by
  have hemit : PolyTimeComputable fun w =>
      if decide ((pairFstD w).length < L (pairSndD w)) = true then F (pairSndD w) (pairFstD w).length
      else [] :=
    polyTimeComputable_ite (ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD)
      (unaryComp_poly hL polyTimeComputable_pairSndD)) hF (polyTimeComputable_const [])
  have hE := polyTimeComputable_iterateEmit cstep_poly hemit .var (cbound .var) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  refine ptc_congr (hE.comp hpre) fun z => ?_
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : L z ≤ PolyExpr.var.eval (pairEncode [] z).length + 1 := by
    rw [PolyExpr.eval_var, length_pairEncode]
    have := hLle z
    simp only [List.length_nil]
    omega
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite, min_eq_right hN]


/-! ### The simulator's machine layout -/

/-- The common input of the simulator's machine input `⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`. -/
def simX (w : List Bool) : List Bool := pairFstD (NUPPT.inArg w)

/-- The auxiliary input of the simulator's machine input. -/
def simZ (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The coins of the simulator's machine input. -/
def simR (w : List Bool) : List Bool := NUPPT.inCoins w

/-- The common-input projection is polynomial-time. -/
theorem simX_poly : PolyTimeComputable simX :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg

/-- The auxiliary-input projection is polynomial-time. -/
theorem simZ_poly : PolyTimeComputable simZ :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-- The coin projection is polynomial-time. -/
theorem simR_poly : PolyTimeComputable simR := NUPPT.polyTimeComputable_inCoins

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length :=
  le_trans (Nat.le_add_left _ _) (length_pairFstD_add_pairSndD_le z)

/-- The common input is no longer than the machine input. -/
theorem length_simX_le (w : List Bool) : (simX w).length ≤ w.length :=
  (length_pairFstD_le _).trans ((length_pairSndD_le _).trans
    ((length_pairFstD_le _).trans (length_pairFstD_le _)))

/-! ### The components of one attempt as machines -/

section Components

variable {X Z R : List Bool → List Bool} {T : List Bool → ℕ}

/-- The coin block of attempt `T w` is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`
at the unary offset `T · B`, `EncodingMachines.truncate_poly` at the unary block length). -/
theorem blk_poly (ℓ : PolyExpr) (V' : Strategy) (hX : PolyTimeComputable X)
    (hT : PolyTimeComputable fun w => List.replicate (T w) true) (hR : PolyTimeComputable R) :
    PolyTimeComputable fun w =>
      colCoinSlice ((blockPoly ℓ V').eval (X w).length) (T w) (R w) := by
  have hB : PolyTimeComputable fun w =>
      List.replicate ((blockPoly ℓ V').eval (X w).length) true :=
    unaryPolyOf_poly (blockPoly ℓ V') (unaryLength_poly hX)
  have hdrop : PolyTimeComputable fun w =>
      (R w).drop (T w * (blockPoly ℓ V').eval (X w).length) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryMul_poly hT hB).pairEncode hR)) fun w => ?_
    simp
  exact truncate_poly hdrop hB

/-- The vertex count is unary polynomial-time (`EncodingMachines.unarySqrt_poly`). -/
theorem nV_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (nV (X w)) true :=
  unarySqrt_poly (unaryLength_poly hX)

/-- The edge count is unary polynomial-time (`countBits_poly`). -/
theorem mE_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (mE (X w)) true :=
  countBits_poly hX (unaryMul_poly (nV_poly hX) (nV_poly hX))

/-- The offset `baseR` of the commitment randomness is unary polynomial-time. -/
theorem baseR_poly (hX : PolyTimeComputable X) :
    PolyTimeComputable fun w => List.replicate (baseR (X w)) true :=
  unaryAdd_poly (unaryPolyOf_poly (.pow (.add .var (.const 1)) 2) (unaryLength_poly hX))
    (unaryMul_poly (unaryConst_poly 3) (unaryLength_poly hX))

/-- The sampled edge index is unary polynomial-time (`sampleNum_poly` with `Nat.size |E|` bits
and the bound `2^{size |E|} ≤ 2|E| + 1`, `sampleEdgeIdx_eq`). -/
theorem eIdx_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (eIdx (X w) (B w)) true := by
  have hm := mE_poly hX
  have hs := sampleNum_poly hm (unarySize_poly hm) (unaryLength_poly hX) hB
    (unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) hm) (unaryConst_poly 1))
    (fun w => two_pow_size_le_two_mul_succ (mE (X w)))
  refine ptc_congr (polyTimeComputable_ite (ltTest_poly hs hm) hs (unaryConst_poly 0)) fun w => ?_
  unfold eIdx
  rw [sampleEdgeIdx_eq]
  by_cases h : sampleNum (mE (X w)) (Nat.size (mE (X w))) (X w).length (B w) < mE (X w) <;>
    simp [h]

/-- The numeric colour-pair sample is unary polynomial-time (`sampleNum_poly` with `3` bits). -/
theorem vIdx_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (vIdx (X w) (B w)) true := by
  have hdrop : PolyTimeComputable fun w => (B w).drop (((X w).length + 1) ^ 2) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryPolyOf_poly (.pow (.add .var (.const 1)) 2) (unaryLength_poly hX)).pairEncode hB))
      fun w => ?_
    simp [PolyExpr.eval]
  exact sampleNum_poly (unaryConst_poly 6) (unaryConst_poly 3) (unaryLength_poly hX) hdrop
    (unaryConst_poly 8) (fun _ => by norm_num)

/-- The position of the sampled edge is unary polynomial-time
(`EncodingMachines.polyTimeComputable_firstIdx` with the test "set bit with `e'` set bits
before it", `getBit_poly`, `countBits_poly`, `eqTest_poly`). -/
theorem kPos_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w)) true := by
  have hp : PolyTimeComputable fun w' =>
      [(X (pairSndD w')).getD (pairFstD w').length false &&
        decide (countBits (X (pairSndD w')) (pairFstD w').length =
          eIdx (X (pairSndD w')) (B (pairSndD w')))] :=
    polyTimeComputable_and
      (getBit_poly (hX.comp polyTimeComputable_pairSndD)
        (unaryLength_poly polyTimeComputable_pairFstD))
      (eqTest_poly (countBits_poly (hX.comp polyTimeComputable_pairSndD)
        (unaryLength_poly polyTimeComputable_pairFstD))
        (unaryComp_poly (eIdx_poly hX hB) polyTimeComputable_pairSndD))
  exact polyTimeComputable_firstIdx
    (p := fun w k => (X w).getD k false && decide (countBits (X w) k = eIdx (X w) (B w))) hp
    (unaryMul_poly (nV_poly hX) (nV_poly hX))

/-- The first endpoint of the sampled edge is unary polynomial-time (`divNum_poly`). -/
theorem p1_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w) / nV (X w)) true := by
  refine ptc_congr (divNum_poly (kPos_poly hX hB) (nV_poly hX)) fun w => ?_
  rw [divNum_eq]

/-- The second endpoint of the sampled edge is unary polynomial-time (`modNum_poly`). -/
theorem p2_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => List.replicate (kPos (X w) (B w) % nV (X w)) true := by
  refine ptc_congr (modNum_poly (kPos_poly hX hB) (nV_poly hX)) fun w => ?_
  rw [modNum_eq]

/-- The encoding of the first sampled colour is polynomial-time (a six-entry table,
`table_poly`). -/
theorem colA_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => encColor (colorA (vIdx (X w) (B w))) := by
  refine ptc_congr (table_poly (fun j => encColor (colorA j)) (vIdx_poly hX hB) 6) fun w => ?_
  congr 1
  unfold colorA
  by_cases h : vIdx (X w) (B w) < 6
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.1 h), dif_neg h, dif_neg (lt_irrefl 6)]

/-- The encoding of the second sampled colour is polynomial-time (`table_poly`). -/
theorem colB_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => encColor (colorB (vIdx (X w) (B w))) := by
  refine ptc_congr (table_poly (fun j => encColor (colorB j)) (vIdx_poly hX hB) 6) fun w => ?_
  congr 1
  unfold colorB
  by_cases h : vIdx (X w) (B w) < 6
  · rw [min_eq_left h.le]
  · rw [min_eq_right (not_lt.1 h), dif_neg h, dif_neg (lt_irrefl 6)]

/-- The encoded simulated colour of vertex `I w` is polynomial-time (two comparisons with the
endpoints, `polyTimeComputable_ite`). -/
theorem colorStr_poly (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true) :
    PolyTimeComputable fun w => encColor (colorNum (X w) (B w) (I w)) := by
  have h := polyTimeComputable_ite (eqTest_poly hI (p1_poly hX hB)) (colA_poly hX hB)
    (polyTimeComputable_ite (eqTest_poly hI (p2_poly hX hB)) (colB_poly hX hB)
      (polyTimeComputable_const (encColor 0)))
  refine ptc_congr h fun w => ?_
  unfold colorNum
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- The commitment randomness of vertex `I w` is polynomial-time
(`EnsembleLemmas.polyTimeComputable_padL` after the unary offset). -/
theorem rrStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true) :
    PolyTimeComputable fun w => rrStr ℓ (X w) (B w) (I w) := by
  have hℓn : PolyTimeComputable fun w => List.replicate (ℓ.eval (nV (X w))) true :=
    unaryPolyOf_poly ℓ (nV_poly hX)
  have hdrop : PolyTimeComputable fun w =>
      (B w).drop (baseR (X w) + I w * ℓ.eval (nV (X w))) := by
    refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp
      ((unaryAdd_poly (baseR_poly hX) (unaryMul_poly hI hℓn)).pairEncode hB)) fun w => ?_
    simp
  refine ptc_congr (EnsembleLemmas.polyTimeComputable_padL ℓ (nV_poly hX) hdrop) fun w => ?_
  simp [rrStr]

/-- One encoded commitment of the vector is polynomial-time (`hCom` on the padded colour and
the randomness). -/
theorem chunk_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) {B : List Bool → List Bool} (hB : PolyTimeComputable B)
    {c : List Bool → ℕ → Fin 3} {I : List Bool → ℕ}
    (hI : PolyTimeComputable fun w => List.replicate (I w) true)
    (hc : PolyTimeComputable fun w => encColor (c w (I w))) :
    PolyTimeComputable fun w => chunk Com ℓ (X w) (B w) (c w) (I w) := by
  have hpad : PolyTimeComputable fun w => EnsembleLemmas.padL (nV (X w)) (encColor (c w (I w))) := by
    refine ptc_congr (EnsembleLemmas.polyTimeComputable_padL .var (nV_poly hX) hc) fun w => ?_
    simp
  exact (hCom.comp (hpad.pairEncode (rrStr_poly ℓ hX hB hI))).pairEncode
    (polyTimeComputable_const [])

/-- The simulated commitment message is polynomial-time (`emitLoop_poly` over the vertices). -/
theorem comStr_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) (hXle : ∀ w, (X w).length ≤ w.length)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => comStr Com ℓ (X w) (B w) (colorNum (X w) (B w)) := by
  have hF := chunk_poly hCom ℓ (hX.comp polyTimeComputable_pairSndD)
    (hB.comp polyTimeComputable_pairSndD)
    (c := fun w' => colorNum (X (pairSndD w')) (B (pairSndD w')))
    (unaryLength_poly polyTimeComputable_pairFstD)
    (colorStr_poly (hX.comp polyTimeComputable_pairSndD) (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD))
  exact emitLoop_poly (F := fun w i => chunk Com ℓ (X w) (B w) (colorNum (X w) (B w)) i) hF
    (nV_poly hX) (fun w => (Nat.sqrt_le_self _).trans ((hXle w).trans (Nat.le_succ _)))

/-- The all-zero commitment message is polynomial-time (`emitLoop_poly`). -/
theorem comStr0_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    (hX : PolyTimeComputable X) (hXle : ∀ w, (X w).length ≤ w.length)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => comStr Com ℓ (X w) (B w) (fun _ => 0) := by
  have hF := chunk_poly hCom ℓ (hX.comp polyTimeComputable_pairSndD)
    (hB.comp polyTimeComputable_pairSndD) (c := fun _ _ => 0)
    (unaryLength_poly polyTimeComputable_pairFstD) (polyTimeComputable_const (encColor 0))
  exact emitLoop_poly (F := fun w i => chunk Com ℓ (X w) (B w) (fun _ => 0) i) hF
    (nV_poly hX) (fun w => (Nat.sqrt_le_self _).trans ((hXle w).trans (Nat.le_succ _)))

/-- The tape handed to `V'` is polynomial-time. -/
theorem rVStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => rVStr ℓ (X w) (B w) := by
  have hN := unaryLength_poly hX
  have hlen : PolyTimeComputable fun w =>
      List.replicate (baseR (X w) + (X w).length * ℓ.eval (X w).length) true :=
    unaryAdd_poly (baseR_poly hX) (unaryMul_poly hN (unaryPolyOf_poly ℓ hN))
  refine ptc_congr ((polyTimeComputable_pairDropPoly .var).comp (hlen.pairEncode hB)) fun w => ?_
  simp [rVStr]

/-- The reply of an efficient `V'` to the commitment message is polynomial-time: one activation
of its machine on the layout `⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, ⟨com, []⟩⟩⟩, []⟩, r_V⟩`
(`Strategy.ofNUPPT_next`, `NUPPT.runAtL_eq_output_layout`, `NUPPT.polyTimeComputable_layout`). -/
theorem reply_poly (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) (hX : PolyTimeComputable X)
    (hZ : PolyTimeComputable Z) {B : List Bool → List Bool} (hB : PolyTimeComputable B)
    {C : List Bool → List Bool} (hC : PolyTimeComputable C) :
    PolyTimeComputable fun w => V'.next (X w) (Z w) (rVStr ℓ (X w) (B w)) [C w] := by
  obtain ⟨A, hA, -, hnext⟩ := hV'
  have hlay := NUPPT.polyTimeComputable_layout (polyTimeComputable_unary.comp hX)
    ((hX.pairEncode hZ).pairEncode (hC.pairEncode (polyTimeComputable_const [])))
    (polyTimeComputable_const []) (rVStr_poly ℓ hX hB)
  refine ptc_congr (A.polyTimeComputable_output.comp hlay) fun w => ?_
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq]
  rfl

/-- The opening message is polynomial-time. -/
theorem opnStr_poly (ℓ : PolyExpr) (hX : PolyTimeComputable X) {B : List Bool → List Bool}
    (hB : PolyTimeComputable B) :
    PolyTimeComputable fun w => opnStr ℓ (X w) (B w) :=
  ((colorStr_poly hX hB (p1_poly hX hB)).pairEncode (rrStr_poly ℓ hX hB (p1_poly hX hB))).pairEncode
    ((colorStr_poly hX hB (p2_poly hX hB)).pairEncode (rrStr_poly ℓ hX hB (p2_poly hX hB)))

/-- An encoded two-message view is polynomial-time in its components. -/
theorem view_poly (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    {Rv C O : List Bool → List Bool} (hRv : PolyTimeComputable Rv) (hC : PolyTimeComputable C)
    (hO : PolyTimeComputable O) :
    PolyTimeComputable fun w => View.encode ⟨X w, Z w, Rv w, [C w, O w]⟩ :=
  (hX.pairEncode hZ).pairEncode
    (hRv.pairEncode (hC.pairEncode (hO.pairEncode (polyTimeComputable_const []))))

/-- **One attempt is polynomial-time**: both the success test and the (defaulted) view of
`attemptNum` on polynomial-time inputs `X, Z, B`.

**Proof sketch.** Assemble the components: the edge count (`mE_poly`), the commitment messages
(`comStr_poly`, `comStr0_poly`), the tape (`rVStr_poly`), `V'`'s reply (`reply_poly`), the
test `|reply| % |E| = e'` (`modNum_poly`, `eqTest_poly`), the opening (`opnStr_poly`) and the
views (`view_poly`); the success test is `|E| = 0 ∨ test` and the output a two-way
`polyTimeComputable_ite`. -/
theorem attemptNum_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) (hX : PolyTimeComputable X)
    (hXle : ∀ w, (X w).length ≤ w.length) (hZ : PolyTimeComputable Z)
    {B : List Bool → List Bool} (hB : PolyTimeComputable B) :
    PolyTimeComputable (fun w => [(attemptNum Com ℓ V' (X w) (Z w) (B w)).isSome]) ∧
    PolyTimeComputable (fun w => (attemptNum Com ℓ V' (X w) (Z w) (B w)).getD []) := by
  have hm := mE_poly hX
  have hcom := comStr_poly hCom ℓ hX hXle hB
  have hcom0 := comStr0_poly hCom ℓ hX hXle hB
  have hrV := rVStr_poly ℓ hX hB
  have hreply := reply_poly ℓ hV' hX hZ hB hcom
  have htest : PolyTimeComputable fun w =>
      [decide ((V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
        [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
          eIdx (X w) (B w))] := by
    refine ptc_congr (eqTest_poly (modNum_poly (unaryLength_poly hreply) hm) (eIdx_poly hX hB))
      fun w => ?_
    rw [modNum_eq]
  have hzero : PolyTimeComputable fun w => [decide (mE (X w) = 0)] :=
    eqTest_poly hm (unaryConst_poly 0)
  have hview := view_poly hX hZ hrV hcom (opnStr_poly ℓ hX hB)
  have hview0 := view_poly hX hZ hrV hcom0 (polyTimeComputable_const [])
  refine ⟨?_, ?_⟩
  · refine ptc_congr (or_poly hzero htest) fun w => ?_
    unfold attemptNum
    by_cases h0 : mE (X w) = 0
    · simp [h0]
    · by_cases ht : (V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
          [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
            eIdx (X w) (B w) <;> simp [h0, ht]
  · refine ptc_congr (polyTimeComputable_ite hzero hview0
      (polyTimeComputable_ite htest hview (polyTimeComputable_const []))) fun w => ?_
    unfold attemptNum
    by_cases h0 : mE (X w) = 0
    · simp [h0]
    · by_cases ht : (V'.next (X w) (Z w) (rVStr ℓ (X w) (B w))
          [comStr Com ℓ (X w) (B w) (colorNum (X w) (B w))]).length % mE (X w) =
            eIdx (X w) (B w) <;> simp [h0, ht]

end Components

/-! ### The attempts on the layout and the loop over them -/

/-- The attempt of the simulator at index `t` on the layout `w`, in numeric form. -/
noncomputable def attemptAt (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (w : List Bool) (t : ℕ) : Option (List Bool) :=
  attemptNum Com ℓ V' (simX w) (simZ w)
    (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) t (simR w))

/-- **One attempt on the indexed layout `⟨1^t, w⟩` is polynomial-time** (`attemptNum_poly` on
the projections of the layout, the block cut by `blk_poly`). -/
theorem attemptAt_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) :
    PolyTimeComputable (fun u => [(attemptAt Com ℓ V' (pairSndD u) (pairFstD u).length).isSome]) ∧
    PolyTimeComputable (fun u => (attemptAt Com ℓ V' (pairSndD u) (pairFstD u).length).getD []) :=
  attemptNum_poly hCom ℓ hV' (X := fun u => simX (pairSndD u))
    (simX_poly.comp polyTimeComputable_pairSndD)
    (fun u => (length_simX_le _).trans (length_pairSndD_le u))
    (Z := fun u => simZ (pairSndD u)) (simZ_poly.comp polyTimeComputable_pairSndD)
    (B := fun u => colCoinSlice ((blockPoly ℓ V').eval (simX (pairSndD u)).length)
      (pairFstD u).length (simR (pairSndD u)))
    (blk_poly ℓ V' (simX_poly.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD) (simR_poly.comp polyTimeComputable_pairSndD))

/-- The simulator on its layout, through the first accepted attempt.

**Proof sketch.** Every attempt is its numeric form (`attemptStr_eq_attemptNum`), the edge
count is `mE` (`edgeCount_eq_countBits`) and the iteration count `n|E|` is `nV · mE`; the
search `List.findSome?` over the attempts is the attempt at the first accepted index
(`findSome?_range_eq`). -/
theorem sim_eq (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy) (w : List Bool) :
    sim Com ℓ V' (simX w) (simZ w) (simR w) =
      if mE (simX w) = 0 then (attemptAt Com ℓ V' w 0).getD []
      else if firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)) <
          nV (simX w) * mE (simX w) then
        (attemptAt Com ℓ V' w
          (firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)))).getD []
      else [] := by
  have hm : edgeCount (decGraph (simX w)).2 = mE (simX w) := edgeCount_eq_countBits _
  have hit : colIterations (simX w) = nV (simX w) * mE (simX w) := by
    unfold colIterations
    rw [hm]
    rfl
  have hatt : (fun t => attemptStr Com ℓ V' (simX w) (simZ w)
      (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) t (simR w))) = attemptAt Com ℓ V' w := by
    funext t
    exact attemptStr_eq_attemptNum Com ℓ V' _ _ _
  have hatt0 : attemptStr Com ℓ V' (simX w) (simZ w)
      (colCoinSlice ((blockPoly ℓ V').eval (simX w).length) 0 (simR w)) = attemptAt Com ℓ V' w 0 :=
    attemptStr_eq_attemptNum Com ℓ V' _ _ _
  unfold sim
  simp only [hm, hit, hatt, hatt0]
  rw [findSome?_range_eq]
  by_cases h0 : mE (simX w) = 0
  · simp [h0]
  · by_cases hlt : firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome)
        (nV (simX w) * mE (simX w)) < nV (simX w) * mE (simX w) <;> simp [h0, hlt]

/-- **The simulator is polynomial-time** as a function of its machine layout.

**Proof sketch.** The first accepted attempt index is
`EncodingMachines.polyTimeComputable_firstIdx` with the success test of `attemptAt_poly` and
the unary bound `nV · mE`; the output is that attempt's view (`attemptAt_poly` on
`⟨1^{index}, w⟩`) or `[]`, and the single attempt `0` when `E = ∅`; `sim_eq` identifies the
cases. -/
theorem sim_poly {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com) (ℓ : PolyExpr)
    {V' : Strategy} (hV' : V'.Efficient) :
    PolyTimeComputable fun w => sim Com ℓ V' (simX w) (simZ w) (simR w) := by
  obtain ⟨hp, hout⟩ := attemptAt_poly hCom ℓ hV'
  have hm : PolyTimeComputable fun w => List.replicate (mE (simX w)) true := mE_poly simX_poly
  have hlen : PolyTimeComputable fun w => List.replicate (nV (simX w) * mE (simX w)) true :=
    unaryMul_poly (nV_poly simX_poly) hm
  have hidx := polyTimeComputable_firstIdx (p := fun w t => (attemptAt Com ℓ V' w t).isSome) hp hlen
  have hsel : PolyTimeComputable fun w => (attemptAt Com ℓ V' w
      (firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome) (nV (simX w) * mE (simX w)))).getD [] := by
    refine ptc_congr (hout.comp (hidx.pairEncode polyTimeComputable_id)) fun w => ?_
    simp
  have h0 : PolyTimeComputable fun w => (attemptAt Com ℓ V' w 0).getD [] := by
    refine ptc_congr (hout.comp ((polyTimeComputable_const []).pairEncode polyTimeComputable_id))
      fun w => ?_
    simp
  refine ptc_congr (polyTimeComputable_ite (eqTest_poly hm (unaryConst_poly 0)) h0
    (polyTimeComputable_ite (ltTest_poly hidx hlen) hsel (polyTimeComputable_const []))) fun w => ?_
  rw [sim_eq]
  by_cases hz : mE (simX w) = 0
  · simp [hz]
  · by_cases hlt : firstIdx (fun t => (attemptAt Com ℓ V' w t).isSome)
        (nV (simX w) * mE (simX w)) < nV (simX w) * mE (simX w) <;> simp [hz, hlt]

/-- **The simulator is a uniform PPT** (Claim-128.a, shadow form): `NUPPT.ofPolyTimeUniform`
of `sim_poly` with the coin polynomial `simCoins ℓ V'` computes `sim Com ℓ V' x z r` on
`⟨x, z⟩` at parameter `|x|` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_simulator {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) {V' : Strategy} (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = simCoins ℓ V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = sim Com ℓ V' x z (List.ofFn r) := by
  have hF := sim_poly hCom ℓ hV'
  refine ⟨NUPPT.ofPolyTimeUniform hF (simCoins ℓ V'), NUPPT.ofPolyTimeUniform_uniform _ _, rfl, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [simX, simZ, simR, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

end TCSlib.Cryptography.ColSimMachine

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
import TCSlib.Cryptography.ZeroKnowledge.EncodingPermutations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3-colouring simulator: shadows and numeric models

The first half of the machine infrastructure behind Claim-128.a of
`ThreeColoring/Simulator.lean` (`exists_colSimulator`). The frozen string definitions of the
main file (`colSimBlock`, `colSimCoins`, `pair6Equiv`, `sampleColorPair`, `colSimAttemptStr`,
`colSim`, together with the typed `ColorPair` and `simColors` they use) are *shadowed* here by
`ColSimMachine.blockPoly`, `simCoins`, `pair6Equiv`, `sampleColorPair`, `attemptStr`, `sim`,
`ColorPair`, `simColors` with identical bodies, so that the machine can be built before the
main file; the main file identifies each shadow with its original by `rfl`.

The *numeric* layer identifies every typed ingredient of one attempt of
[PS10, Algorithm 128.7] with a number or a string computed from the tape: the rejection
samplers of the edge index and of the colour pair are the first accepted trial of
`EncodingPermutations.trialIdx` and its block value (`sampleNum`, `sampleIdx_eq`); the edge
list of the decoded graph is the list of set bits of the adjacency word in row-major order
(`edgeList_eq_map`), so `|E|` is a bit count (`edgeCount_eq_countBits`) and the `e`-th edge is
the position of the `(e+1)`-th set bit (`edgeOf_val_eq`); one attempt is its numeric form
`attemptNum` (`attemptStr_eq_attemptNum`). The machines themselves are in
`ThreeColoring/SimulatorMachine.lean`.

## Main definitions

* `TCSlib.Cryptography.ColSimMachine.blockPoly`, `simCoins`, `attemptStr`, `sim` — shadows of
  the string simulator of the main file.
* `TCSlib.Cryptography.ColSimMachine.sampleNum`, `countBits`, `edgePos` — the numeric models
  of the rejection sampler, of `|E|` and of the `e`-th edge.
* `TCSlib.Cryptography.ColSimMachine.attemptNum` — one attempt in numeric form, with its
  ingredients `nV`, `mE`, `eIdx`, `vIdx`, `kPos`, `colorNum`, `rrStr`, `comStr`, `rVStr`,
  `opnStr`.

## Main results

* `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq`, `edgeCount_eq_countBits`,
  `edgeOf_val_eq` — the numeric models agree with the typed definitions.
* `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` — one attempt of the string
  simulator is its numeric form.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7 Algorithm 128.7, p. 128.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColSimMachine

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Shadows of the typed colour pairs and of the string simulator -/

/-- Shadow of `ColorPair`: the ordered pairs of distinct colours. -/
abbrev ColorPair : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- There are six distinct colour pairs. -/
theorem card_colorPair : Fintype.card ColorPair = 6 := by decide

/-- Shadow of `simColors`: the guessed pair at the endpoints of `p`, the colour `0` elsewhere. -/
def simColors {n : ℕ} (p : Fin n × Fin n) (ab : ColorPair) : Fin n → Fin 3 :=
  fun k => if k = p.1 then ab.1.1 else if k = p.2 then ab.1.2 else 0

/-- Shadow of `colSimBlock`: the coin block of one attempt against `V'` at instance length
`N` has `(N+1)²` edge-sampling bits, `3N` colour-pair bits, `N ℓ(N)` commitment bits and the
tape of `V'`. -/
def blockPoly (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .add (.add (.add (.normal 1 2) (.mul (.const 3) .var)) (.mul .var ℓ)) V'.coins

/-- Shadow of `colSimCoins`: `N²` blocks. -/
def simCoins (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .mul (.mul .var .var) (blockPoly ℓ V')

/-- Shadow of `pair6Equiv`: the six distinct colour pairs enumerated by `Fin 6`. -/
noncomputable def pair6Equiv : Fin 6 ≃ ColorPair := (Fintype.equivFinOfCardEq card_colorPair).symm

/-- Shadow of `sampleColorPair`: `T` rejection trials of three bits, the pair `(0, 1)` on
failure. -/
noncomputable def sampleColorPair (T : ℕ) (r : List Bool) : ColorPair :=
  ((sampleIdx 6 3 T r).map pair6Equiv).getD ⟨(0, 1), by decide⟩

/-- Shadow of `colSimAttemptStr`: one attempt of [PS10, Algorithm 128.7] on the coin block
`blk`. -/
noncomputable def attemptStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  let n := (decGraph x).1
  let G : Graph n := (decGraph x).2
  let m := edgeCount G
  let N := x.length
  let e' := sampleEdgeIdx m N blk
  let ab := sampleColorPair N (blk.drop ((N + 1) ^ 2))
  let rr : Fin n → Fin (ℓ.eval n) → Bool :=
    fun i j => blk.getD ((N + 1) ^ 2 + 3 * N + i * ℓ.eval n + j) false
  let rV := blk.drop ((N + 1) ^ 2 + 3 * N + N * ℓ.eval N)
  match edgeAt G e' with
  | none => some (View.encode ⟨x, z, rV, [colCommit Com n (ℓ.eval n) (fun _ => 0) rr, []]⟩)
  | some p =>
    let c' := simColors p ab
    let com := colCommit Com n (ℓ.eval n) c' rr
    if edgeIdxOfMsg m (V'.next x z rV [com]) = e' then
      some (View.encode ⟨x, z, rV, [com, colOpen c' rr p]⟩)
    else none

/-- Shadow of `colSim`: up to `n|E|` attempts on consecutive coin blocks, the first successful
view, or `[]`; a single attempt if `E = ∅`. -/
noncomputable def sim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z r : List Bool) : List Bool :=
  let B := (blockPoly ℓ V').eval x.length
  let att : ℕ → Option (List Bool) := fun t => attemptStr Com ℓ V' x z (colCoinSlice B t r)
  if edgeCount (decGraph x).2 = 0 then (att 0).getD []
  else ((List.range (colIterations x)).findSome? att).getD []

/-! ### The numeric model of the rejection samplers -/

/-- The `k` bits of the tape from position `base` read as a number: `bitsToNat` of the block
is `EncodingMachines.blockVal` (induction on `k`, `List.ofFn_succ'`, `blockVal_succ`). -/
theorem bitsToNat_getD_eq_blockVal (r : List Bool) (base : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => r.getD (base + j) false) = blockVal r base k
  | 0 => by simp [bitsToNat]
  | k + 1 => by
    rw [blockVal_succ, ← bitsToNat_getD_eq_blockVal r base k]
    unfold bitsToNat
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [show (r.getD (base + k) false).toNat = cond (r.getD (base + k) false) 1 0 from rfl,
      Bool.cond_eq_ite]

/-- `List.findSome?` over `List.range T` is the value at the first index with a `some`, if any
(`EncodingMachines.firstIdx` on the `isSome` test).

**Proof sketch.** Induction on `T` through `List.range_succ` and `List.findSome?_append`: if
the search over `range T` succeeds, appending `T` changes neither the search index
(`firstIdx_eq_of`, `firstIdx_min`) nor the result; otherwise every `t < T` is rejected
(`firstIdx_eq_iff`), the result is `g T`, and the search index over `T + 1` is `T` or `T + 1`
according to `(g T).isSome`. -/
theorem findSome?_range_eq {α : Type*} (g : ℕ → Option α) (T : ℕ) :
    (List.range T).findSome? g =
      if firstIdx (fun t => (g t).isSome) T < T then g (firstIdx (fun t => (g t).isSome) T)
      else none := by
  induction T with
  | zero => simp [firstIdx]
  | succ T ih =>
    rw [List.range_succ, List.findSome?_append, ih, List.findSome?_singleton]
    by_cases h : firstIdx (fun t => (g t).isSome) T < T
    · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = firstIdx (fun t => (g t).isSome) T :=
        firstIdx_eq_of (Nat.lt_succ_of_lt h) (q_firstIdx h) fun i hi => firstIdx_min hi
      rw [if_pos h, heq, if_pos (Nat.lt_succ_of_lt h)]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (q_firstIdx h)
      rw [hv]
      rfl
    · rw [if_neg h, Option.none_or]
      have hall : ∀ i < T, (g i).isSome = false :=
        firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
      by_cases hT : (g T).isSome = true
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T :=
          firstIdx_eq_of (Nat.lt_succ_self T) hT hall
        rw [heq, if_pos (Nat.lt_succ_self T)]
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T + 1 :=
          firstIdx_eq_of_forall fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact hall i hi
            · simpa using hT
        rw [heq, if_neg (lt_irrefl _)]
        cases hg : g T with
        | none => rfl
        | some v => simp [hg] at hT

/-- The numeric model of the rejection sampler `sampleIdx m k T r`: the block value of the
first accepted trial (the first `t < T` whose `k`-bit block reads below `m`), and `m` itself
(an out-of-range marker) if every trial is rejected. -/
noncomputable def sampleNum (m k T : ℕ) (r : List Bool) : ℕ :=
  if trialIdx m k T r 0 < T then blockVal r (trialIdx m k T r 0 * k) k else m

/-- **The rejection sampler is its numeric model**: `sampleIdx m k T r` is `some` of the
numeric sample when it is below `m` and `none` otherwise.

**Proof sketch.** `sampleIdx` is `List.findSome?` over `List.finRange T` of the trials, i.e.
over `List.range T` (`List.map_coe_finRange`, `List.findSome?_map`); each trial is `some` of
its block value iff that value is below `m` (`uniformFromBits`, `bitsToNat_getD_eq_blockVal`);
`findSome?_range_eq` turns the search into `trialIdx m k T r 0` (`firstIdx_congr`). -/
theorem sampleIdx_eq (m k T : ℕ) (r : List Bool) :
    sampleIdx m k T r =
      if h : sampleNum m k T r < m then some ⟨sampleNum m k T r, h⟩ else none := by
  set g : ℕ → Option (Fin m) := fun t =>
    if h : blockVal r (t * k) k < m then some ⟨blockVal r (t * k) k, h⟩ else none with hg
  have h1 : sampleIdx m k T r = (List.range T).findSome? g := by
    show (List.finRange T).findSome? (fun t : Fin T =>
      uniformFromBits m k (fun j : Fin k => r.getD ((t : ℕ) * k + j) false)) = _
    rw [← List.map_coe_finRange, List.findSome?_map]
    congr 1
    funext t
    simp only [Function.comp, uniformFromBits, hg, bitsToNat_getD_eq_blockVal]
  have h2 : ∀ t, (g t).isSome = decide (blockVal r ((0 * T + t) * k) k < m - 0) := by
    intro t
    simp only [hg, zero_mul, zero_add, Nat.sub_zero]
    split_ifs <;> simp_all
  rw [h1, findSome?_range_eq, firstIdx_congr (fun t _ => h2 t)]
  show (if trialIdx m k T r 0 < T then g (trialIdx m k T r 0) else none) = _
  unfold sampleNum
  by_cases ht : trialIdx m k T r 0 < T
  · rw [if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, dif_neg (lt_irrefl m)]

/-- The sampled edge index is the numeric sample when it is in range, `0` otherwise. -/
theorem sampleEdgeIdx_eq (m T : ℕ) (r : List Bool) :
    sampleEdgeIdx m T r =
      if sampleNum m (Nat.size m) T r < m then sampleNum m (Nat.size m) T r else 0 := by
  unfold sampleEdgeIdx
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-- The first colour of the sampled pair as a function of the numeric sample (`0`, the first
colour of the default pair, when the sample is out of range). -/
noncomputable def colorA (v : ℕ) : Fin 3 := if h : v < 6 then (pair6Equiv ⟨v, h⟩).1.1 else 0

/-- The second colour of the sampled pair as a function of the numeric sample (`1` when the
sample is out of range). -/
noncomputable def colorB (v : ℕ) : Fin 3 := if h : v < 6 then (pair6Equiv ⟨v, h⟩).1.2 else 1

/-- The first colour of the sampled pair is `colorA` of the numeric sample. -/
theorem sampleColorPair_fst (T : ℕ) (r : List Bool) :
    (sampleColorPair T r).1.1 = colorA (sampleNum 6 3 T r) := by
  unfold sampleColorPair colorA
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-- The second colour of the sampled pair is `colorB` of the numeric sample. -/
theorem sampleColorPair_snd (T : ℕ) (r : List Bool) :
    (sampleColorPair T r).1.2 = colorB (sampleNum 6 3 T r) := by
  unfold sampleColorPair colorB
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-! ### The numeric model of the edge list -/

/-- Indexing a product list: `(l₁ ×ˢ l₂)[k] = (l₁[k / |l₂|], l₂[k % |l₂|])`.

**Proof sketch.** Induction on `l₁`: `(a :: l₁) ×ˢ l₂` is `l₂.map (a, ·) ++ l₁ ×ˢ l₂`
(`List.product_cons`); an index `k < |l₂|` falls in the first block (`k / |l₂| = 0`,
`k % |l₂| = k`), a larger one in the tail with index `k - |l₂|`, where `k / |l₂|` and
`k % |l₂|` are those of `k - |l₂|` shifted (`Nat.div_eq_sub_div`, `Nat.mod_eq_sub_mod`). -/
theorem getElem_product {α β : Type*} (l₁ : List α) (l₂ : List β) :
    ∀ (k : ℕ) (hk : k < (l₁ ×ˢ l₂).length) (h₁ : k / l₂.length < l₁.length)
      (h₂ : k % l₂.length < l₂.length),
      (l₁ ×ˢ l₂)[k] = (l₁[k / l₂.length], l₂[k % l₂.length]) := by
  induction l₁ with
  | nil => intro k hk; simp at hk
  | cons a l₁ ih =>
    intro k hk h₁ h₂
    show (List.map (fun b => (a, b)) l₂ ++ l₁ ×ˢ l₂)[k] = _
    by_cases hlt : k < l₂.length
    · rw [List.getElem_append_left (by simpa using hlt), List.getElem_map]
      have hdiv : k / l₂.length = 0 := Nat.div_eq_of_lt hlt
      have hmod : k % l₂.length = k := Nat.mod_eq_of_lt hlt
      simp only [hdiv, hmod, List.getElem_cons_zero]
    · have hle : l₂.length ≤ k := not_lt.1 hlt
      have hpos : 0 < l₂.length := by
        rcases Nat.eq_zero_or_pos l₂.length with h0 | h0
        · exfalso
          rw [List.length_product, h0, Nat.mul_zero] at hk
          exact Nat.not_lt_zero _ hk
        · exact h0
      have hdiv : k / l₂.length = (k - l₂.length) / l₂.length + 1 := Nat.div_eq_sub_div hpos hle
      have hmod : k % l₂.length = (k - l₂.length) % l₂.length := Nat.mod_eq_sub_mod hle
      have hk' : k - l₂.length < (l₁ ×ˢ l₂).length := by
        rw [List.length_product] at hk ⊢
        rw [List.length_cons] at hk
        have : (l₁.length + 1) * l₂.length = l₁.length * l₂.length + l₂.length := by ring
        omega
      have h₁' : (k - l₂.length) / l₂.length < l₁.length := by
        rw [hdiv, List.length_cons] at h₁
        omega
      have h₂' : (k - l₂.length) % l₂.length < l₂.length := hmod ▸ h₂
      have hih := ih (k - l₂.length) hk' h₁' h₂'
      rw [List.getElem_append_right (by simpa using hle)]
      simp only [List.length_map]
      rw [hih]
      simp only [hdiv, hmod, List.getElem_cons_succ]

/-- The square `List.finRange n ×ˢ List.finRange n` is `List.finRange (n * n)` read through
`finProdFinEquiv.symm` (row-major order). -/
theorem finRange_product_eq (n : ℕ) :
    List.finRange n ×ˢ List.finRange n = (List.finRange (n * n)).map finProdFinEquiv.symm := by
  apply List.ext_getElem
  · simp [List.length_product]
  · intro k h₁ h₂
    have hk : k < n * n := by simpa using h₂
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
    rw [getElem_product (List.finRange n) (List.finRange n) k h₁
      (by rw [List.length_finRange]; exact (Nat.div_lt_iff_lt_mul hn).2 hk)
      (by rw [List.length_finRange]; exact Nat.mod_lt _ hn)]
    rw [List.getElem_map, List.getElem_finRange, List.getElem_finRange, List.getElem_finRange,
      finProdFinEquiv_symm_apply]
    simp [Fin.divNat, Fin.modNat]

/-- The number of set bits among the first `k` positions of a word (`|E|` of the decoded graph
for `k = n²`). -/
def countBits (x : List Bool) (k : ℕ) : ℕ := ((List.range k).filter fun j => x.getD j false).length

/-- The edge list of the decoded graph is the list of set-bit positions of the adjacency
word, read as pairs through `finProdFinEquiv.symm` (`finRange_product_eq`,
`List.filter_map`). -/
theorem edgeList_eq_map (x : List Bool) :
    edgeList (decGraph x).2 =
      (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map
          finProdFinEquiv.symm) := by
  unfold edgeList
  rw [finRange_product_eq, List.filter_map]
  congr 1
  apply List.filter_congr
  intro k _
  show x.getD (finProdFinEquiv (finProdFinEquiv.symm k)) false = x.getD k false
  rw [Equiv.apply_symm_apply]

/-- The filter of `List.finRange M` by a test on values, mapped to values, is the filter of
`List.range M`. -/
theorem map_val_filter_finRange (Q : ℕ → Bool) (M : ℕ) :
    (((List.finRange M).filter fun k : Fin M => Q k).map Fin.val) = (List.range M).filter Q := by
  rw [← List.map_coe_finRange, List.filter_map]
  rfl

/-- `|E|` of the decoded graph is the number of set bits of the adjacency word. -/
theorem edgeCount_eq_countBits (x : List Bool) :
    edgeCount (decGraph x).2 = countBits x ((decGraph x).1 * (decGraph x).1) := by
  show (edgeList (decGraph x).2).length = _
  rw [edgeList_eq_map, List.length_map, countBits, ← map_val_filter_finRange, List.length_map]

/-- The number of set bits is monotone, and strictly so across a set position. -/
theorem countBits_lt_of_lt (x : List Bool) {k k' : ℕ} (hk : k < k') (hQ : x.getD k false = true) :
    countBits x k < countBits x k' := by
  unfold countBits
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + 1 + d := ⟨k' - (k + 1), by omega⟩
  rw [List.range_add, List.filter_append, List.length_append, List.range_succ,
    List.filter_append, List.length_append]
  simp only [List.filter_singleton, hQ, cond_true, List.length_singleton]
  omega

/-- The `e`-th element of the filtered range `(List.range M).filter Q` is a set position `< M`
with exactly `e` set positions before it.

**Proof sketch.** Induction on `M`: `(range (M+1)).filter Q` is `(range M).filter Q ++ [M].filter Q`
(`List.range_succ`, `List.filter_append`); an index below the length of the first part is
covered by the induction hypothesis (`List.getElem_append_left`), otherwise `Q M` holds, the
index equals the length of the first part and the element is `M`. -/
theorem getElem_filter_range_spec (Q : ℕ → Bool) :
    ∀ (M e : ℕ) (he : e < ((List.range M).filter Q).length),
      Q ((List.range M).filter Q)[e] = true ∧ ((List.range M).filter Q)[e] < M ∧
        ((List.range ((List.range M).filter Q)[e]).filter Q).length = e := by
  intro M
  induction M with
  | zero => intro e he; simp at he
  | succ M ih =>
    intro e he
    have hsplit : (List.range (M + 1)).filter Q = (List.range M).filter Q ++ [M].filter Q := by
      rw [List.range_succ, List.filter_append]
    by_cases hlt : e < ((List.range M).filter Q).length
    · have hget : ((List.range (M + 1)).filter Q)[e] = ((List.range M).filter Q)[e] := by
        simp only [hsplit]
        rw [List.getElem_append_left hlt]
      obtain ⟨h1, h2, h3⟩ := ih e hlt
      rw [hget]
      exact ⟨h1, Nat.lt_succ_of_lt h2, h3⟩
    · have hlen : e < ((List.range M).filter Q).length + ([M].filter Q).length := by
        rw [hsplit, List.length_append] at he
        exact he
      have hQM : Q M = true := by
        by_contra hQ
        rw [Bool.not_eq_true] at hQ
        rw [List.filter_singleton] at hlen
        simp [hQ] at hlen
        omega
      have hone : [M].filter Q = [M] := by
        rw [List.filter_singleton]
        simp [hQM]
      have heq : e = ((List.range M).filter Q).length := by
        rw [hone, List.length_singleton] at hlen
        omega
      have hsplit' : (List.range (M + 1)).filter Q = (List.range M).filter Q ++ [M] := by
        rw [hsplit, hone]
      have hget : ((List.range (M + 1)).filter Q)[e] = M := by
        simp only [hsplit']
        rw [List.getElem_append_right (not_lt.1 hlt)]
        simp [heq]
      rw [hget]
      exact ⟨hQM, Nat.lt_succ_self M, heq.symm⟩

/-- The position of the `(e+1)`-th set bit of a word below `n²`: the first `k < n²` that is set
and has exactly `e` set positions before it (`n²` if there is none). -/
noncomputable def edgePos (n : ℕ) (x : List Bool) (e : ℕ) : ℕ :=
  firstIdx (fun k => x.getD k false && decide (countBits x k = e)) (n * n)

/-- The `e`-th set position of a word is `edgePos` (`getElem_filter_range_spec`,
`countBits_lt_of_lt`, `firstIdx_eq_of`). -/
theorem getElem_filter_range_eq_edgePos (n : ℕ) (x : List Bool) (e : ℕ)
    (he : e < ((List.range (n * n)).filter fun j => x.getD j false).length) :
    ((List.range (n * n)).filter fun j => x.getD j false)[e] = edgePos n x e := by
  obtain ⟨h1, h2, h3⟩ := getElem_filter_range_spec (fun j => x.getD j false) (n * n) e he
  set k₀ := ((List.range (n * n)).filter fun j => x.getD j false)[e] with hk₀
  symm
  apply firstIdx_eq_of h2
  · rw [h1, Bool.true_and, decide_eq_true_eq]
    exact h3
  · intro k hk
    by_cases hQ : x.getD k false = true
    · rw [hQ, Bool.true_and, decide_eq_false_iff_not]
      have := countBits_lt_of_lt x hk hQ
      unfold countBits at this ⊢
      omega
    · rw [Bool.not_eq_true] at hQ
      rw [hQ, Bool.false_and]

/-- **The `e`-th edge of the decoded graph is the `(e+1)`-th set bit** of the adjacency word:
its endpoints are `edgePos n x e / n` and `edgePos n x e % n`.

**Proof sketch.** `edgeOf G e` is the `e`-th element of the edge list, which is the filtered
`List.finRange (n²)` read through `finProdFinEquiv.symm` (`edgeList_eq_map`,
`List.getElem_map`); its value is the `e`-th element of the filtered `List.range (n²)`
(`map_val_filter_finRange`, `List.getElem_of_eq`), i.e. `edgePos n x e`
(`getElem_filter_range_eq_edgePos`), and `finProdFinEquiv.symm` splits it into quotient and
remainder (`finProdFinEquiv_symm_apply`). -/
theorem edgeOf_val_eq (x : List Bool) (e : Fin (edgeCount (decGraph x).2)) :
    ((edgeOf (decGraph x).2 e).1 : ℕ) = edgePos (decGraph x).1 x e / (decGraph x).1 ∧
      ((edgeOf (decGraph x).2 e).2 : ℕ) = edgePos (decGraph x).1 x e % (decGraph x).1 := by
  have hlen : (e : ℕ) < (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map
        finProdFinEquiv.symm).length := by
    rw [← edgeList_eq_map x]
    exact e.isLt
  have hLe : (e : ℕ) < ((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).length := by
    simpa using hlen
  have hget : edgeOf (decGraph x).2 e = finProdFinEquiv.symm
      (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false)[e.val]'hLe) := by
    unfold edgeOf
    rw [List.get_eq_getElem, List.getElem_of_eq (edgeList_eq_map x), List.getElem_map]
  have hval : (((((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false)[e.val]'hLe) :
        Fin ((decGraph x).1 * (decGraph x).1)) : ℕ) = edgePos (decGraph x).1 x e := by
    have h1 : (e : ℕ) < (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map Fin.val).length := by
      simpa using hLe
    have h2 := List.getElem_of_eq
      (map_val_filter_finRange (fun j => x.getD j false) ((decGraph x).1 * (decGraph x).1)) h1
    rw [List.getElem_map] at h2
    rw [h2]
    exact getElem_filter_range_eq_edgePos (decGraph x).1 x e _
  rw [hget, finProdFinEquiv_symm_apply]
  simp only [Fin.divNat, Fin.modNat]
  rw [hval]
  exact ⟨rfl, rfl⟩


/-! ### The numeric form of one attempt -/

/-- The encoding of a message list is the concatenation of the self-delimiting encodings of
its messages (`pairEncode m []` is `dbl m ++ [false, true]`). -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih]
    simp [pairEncode, List.append_assoc]

/-- The encoding of a message list given by a function on `Fin n` is the concatenation over
`List.range n` of the encodings of a numeric form of the function. -/
theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (F : Fin n → List Bool) (F' : ℕ → List Bool)
    (hF : ∀ i : Fin n, F i = F' i) :
    Strategy.encodeMsgs (List.ofFn F) = (List.range n).flatMap fun i => pairEncode (F' i) [] := by
  rw [encodeMsgs_eq_flatMap, List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map,
    List.flatMap_map]
  congr 1
  funext i
  simp [hF]

/-- The `ℓ`-bit randomness read from position `s` of a tape, as a string: `List.ofFn` of the
`getD` reading is `padL` of the dropped tape. -/
theorem ofFn_getD_eq_padL (blk : List Bool) (s ℓ : ℕ) :
    List.ofFn (fun j : Fin ℓ => blk.getD (s + j) false) = EnsembleLemmas.padL ℓ (blk.drop s) := by
  unfold EnsembleLemmas.padL
  congr 1
  funext j
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The vertex count read off an adjacency word. -/
def nV (x : List Bool) : ℕ := Nat.sqrt x.length

/-- The edge count read off an adjacency word: the number of set bits among its first `n²`
positions. -/
def mE (x : List Bool) : ℕ := countBits x (nV x * nV x)

/-- The sampled edge index of an attempt. -/
noncomputable def eIdx (x blk : List Bool) : ℕ := sampleEdgeIdx (mE x) x.length blk

/-- The numeric colour-pair sample of an attempt. -/
noncomputable def vIdx (x blk : List Bool) : ℕ :=
  sampleNum 6 3 x.length (blk.drop ((x.length + 1) ^ 2))

/-- The position of the sampled edge in the adjacency word. -/
noncomputable def kPos (x blk : List Bool) : ℕ := edgePos (nV x) x (eIdx x blk)

/-- The start of the commitment randomness in a coin block. -/
def baseR (x : List Bool) : ℕ := (x.length + 1) ^ 2 + 3 * x.length

/-- The commitment randomness of vertex `i` as a string. -/
noncomputable def rrStr (ℓ : PolyExpr) (x blk : List Bool) (i : ℕ) : List Bool :=
  EnsembleLemmas.padL (ℓ.eval (nV x)) (blk.drop (baseR x + i * ℓ.eval (nV x)))

/-- The simulator's colour of vertex `i` in numeric form: the sampled pair at the endpoints of
the sampled edge, `0` elsewhere. -/
noncomputable def colorNum (x blk : List Bool) (i : ℕ) : Fin 3 :=
  if i = kPos x blk / nV x then colorA (vIdx x blk)
  else if i = kPos x blk % nV x then colorB (vIdx x blk) else 0

/-- The encoded commitment of vertex `i` to the colour `c i`. -/
noncomputable def chunk (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c : ℕ → Fin 3) (i : ℕ) : List Bool :=
  pairEncode (Com (pairEncode (EnsembleLemmas.padL (nV x) (encColor (c i))) (rrStr ℓ x blk i))) []

/-- The commitment message to the colouring `c` in numeric form. -/
noncomputable def comStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c : ℕ → Fin 3) : List Bool :=
  (List.range (nV x)).flatMap (chunk Com ℓ x blk c)

/-- The tape handed to `V'`. -/
def rVStr (ℓ : PolyExpr) (x blk : List Bool) : List Bool :=
  blk.drop (baseR x + x.length * ℓ.eval x.length)

/-- The opening message in numeric form. -/
noncomputable def opnStr (ℓ : PolyExpr) (x blk : List Bool) : List Bool :=
  pairEncode
    (pairEncode (encColor (colorNum x blk (kPos x blk / nV x))) (rrStr ℓ x blk (kPos x blk / nV x)))
    (pairEncode (encColor (colorNum x blk (kPos x blk % nV x))) (rrStr ℓ x blk (kPos x blk % nV x)))

/-- One attempt in numeric form: if the graph has no edge, the view with the all-zero
commitments and the empty opening; otherwise the view with the simulated commitments and the
opening of the sampled edge if `V'` names that edge, `none` otherwise. -/
noncomputable def attemptNum (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  if mE x = 0 then
    some (View.encode ⟨x, z, rVStr ℓ x blk, [comStr Com ℓ x blk (fun _ => 0), []]⟩)
  else if (V'.next x z (rVStr ℓ x blk) [comStr Com ℓ x blk (colorNum x blk)]).length % mE x =
      eIdx x blk then
    some (View.encode ⟨x, z, rVStr ℓ x blk, [comStr Com ℓ x blk (colorNum x blk), opnStr ℓ x blk]⟩)
  else none

/-- The commitment message of the typed attempt is the numeric commitment message. -/
theorem colCommit_eq_comStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c' : Fin (nV x) → Fin 3) (c : ℕ → Fin 3) (hc : ∀ i : Fin (nV x), c' i = c i) :
    colCommit Com (nV x) (ℓ.eval (nV x)) c'
        (fun i j => blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false) =
      comStr Com ℓ x blk c := by
  unfold colCommit multiCom comStr
  apply encodeMsgs_ofFn_eq_flatMap
  intro i
  simp only [rrStr, hc i, ← ofFn_getD_eq_padL]
  rfl

/-- **One attempt of the string simulator is its numeric form** (the content of the machine's
correctness).

**Proof sketch.** The vertex count is `nV x` by definition of `decGraph`, the edge count is
`mE x` (`edgeCount_eq_countBits`). If `E = ∅` the attempt takes the `none` branch of `edgeAt`
(`edgeAt_eq_none_iff`) and its commitments are `comStr` to the all-zero colouring
(`colCommit_eq_comStr`). Otherwise the sampled index is in range (`sampleEdgeIdx_lt`), `edgeAt`
is the `e'`-th edge (`edgeAt_eq_some_edgeOf`), whose endpoints are `kPos / nV` and `kPos % nV`
(`edgeOf_val_eq`); the typed colours are `colorNum` (`sampleColorPair_fst/snd`), the
commitments are `comStr` and the opening is `opnStr`. -/
theorem attemptStr_eq_attemptNum (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : attemptStr Com ℓ V' x z blk = attemptNum Com ℓ V' x z blk := by
  have hm : edgeCount (decGraph x).2 = mE x := edgeCount_eq_countBits x
  have hn : (decGraph x).1 = nV x := rfl
  unfold attemptStr attemptNum
  simp only []
  by_cases hm0 : mE x = 0
  · rw [if_pos hm0]
    have hnone : edgeAt (decGraph x).2 (sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk) =
        none := (edgeAt_eq_none_iff _ _).2 (hm.trans hm0)
    rw [hnone]
    show some (View.encode ⟨x, z,
      blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length),
      [colCommit Com (nV x) (ℓ.eval (nV x)) (fun _ => 0)
        (fun i j => blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false),
        []]⟩) = _
    rw [colCommit_eq_comStr Com ℓ x blk (fun _ => 0) (fun _ => 0) (fun _ => rfl)]
    rfl
  · rw [if_neg hm0]
    have hmpos : 0 < edgeCount (decGraph x).2 := by rw [hm]; exact Nat.pos_of_ne_zero hm0
    have he : sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk < edgeCount (decGraph x).2 :=
      sampleEdgeIdx_lt hmpos _ _
    set ef : Fin (edgeCount (decGraph x).2) := ⟨_, he⟩ with hef
    have hsome : edgeAt (decGraph x).2 (sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk) =
        some (edgeOf (decGraph x).2 ef) := edgeAt_eq_some_edgeOf (decGraph x).2 ef
    rw [hsome]
    obtain ⟨hp1, hp2⟩ := edgeOf_val_eq x ef
    have heI : (ef : ℕ) = eIdx x blk := by
      show sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk = eIdx x blk
      rw [hm]
      rfl
    have hkPos : edgePos (decGraph x).1 x ef = kPos x blk := by
      rw [heI]
      rfl
    rw [hkPos] at hp1 hp2
    have hcol : ∀ i : Fin (nV x),
        simColors (edgeOf (decGraph x).2 ef) (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))) i =
          colorNum x blk i := by
      intro i
      unfold simColors colorNum
      simp only [sampleColorPair_fst, sampleColorPair_snd, Fin.ext_iff, hp1, hp2]
      rfl
    have hcom := colCommit_eq_comStr Com ℓ x blk _ _ hcol
    have hopn : colOpen
        (simColors (edgeOf (decGraph x).2 ef) (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
        (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
          blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)
        (edgeOf (decGraph x).2 ef) = opnStr ℓ x blk := by
      unfold colOpen opnStr
      simp only [hcol]
      rw [hp1, hp2]
      unfold rrStr
      rw [← ofFn_getD_eq_padL, ← ofFn_getD_eq_padL]
      rfl
    show (if edgeIdxOfMsg (edgeCount (decGraph x).2)
        (V'.next x z (blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length))
          [colCommit Com (nV x) (ℓ.eval (nV x))
            (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)])
          = (ef : ℕ) then
        some (View.encode ⟨x, z,
          blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length),
          [colCommit Com (nV x) (ℓ.eval (nV x))
            (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false),
           colOpen (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)
            (edgeOf (decGraph x).2 ef)]⟩)
      else none) = _
    simp only [hcom, hopn, heI, hm]
    rfl

end TCSlib.Cryptography.ColSimMachine

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring

The zero-knowledge proof for the language of 3-colourable graphs [PS10, §4.7.2]: the
language and its witness relation (Def-124.f), the protocol of [PS10, Protocol 127.5] built on
a commitment scheme of `ZeroKnowledge/Commitment.lean`, its completeness and soundness
[PS10, Proposition 127.6], and the simulator of [PS10, Algorithm 128.7] with
[PS10, Proposition 128.8]. The protocol is the step 1 of [PS10, Theorem 124.1]; step 2 (every
language with a Levin reduction to `3COL`) is `ZeroKnowledge/NP.lean`.

## Contents

* `Language` — 3-colourings, the language `3COL` and its witness relation `R_3COL`, the edge
  enumeration, the bound `(1 - 1/m)^{nm} ≤ e^{-n}` (Claim-125.a), colours as `n`-bit committed
  values and the rejection samplers of the honest parties (Def-124.f, Claim-125.a, DQ4, D10).
* `Protocol` — the commitment, challenge and opening messages, the verifier's check, one
  iteration and the `n|E|`-fold protocol (Prot-127.5), completeness (Claim-127.e), the
  committed colouring and its bad edge (Lem-127.f), adaptive sequential soundness
  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]
  (Prop-127.6).
* `Simulator` — the distinct colour pairs and `S₃ ≃ ColorPair` (Lem-129.b), the typed views
  and the attempts of `S`, `S'`, `S''` (Alg-128.7, Claim-129.a, Claim-129.c), the hybrid
  reduction to multi-value hiding (Claim-129.d), the string simulator and its efficiency
  (Claim-128.a), and [PS10, Proposition 128.8] with the assembled [PS10, Proposition 127.6]
  (Prop-128.8, Prop-127.6).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.2, pp. 127–129.)
-/
