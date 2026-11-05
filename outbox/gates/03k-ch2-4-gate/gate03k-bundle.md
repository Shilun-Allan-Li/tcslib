## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03k-pack.md =====

# Gate 03k ([PS10] ch. 2–4, graph isomorphism ZK and encodings): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/k/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the graph isomorphism and non-isomorphism protocols and their proofs (Prots 118.3, 120.6; Props 118.4, 120.7; Thm 122.3, ZK for GI), with their efficiency and soundness repetitions, the simulators, the string encodings of graphs and permutations, the commitment lemmas, and the NP lemmas.
- **This is a "rest" pack.** Its files mostly hold the proofs of headline theorems stated in
  earlier packs, so its trusted surface is their **auxiliary statements**, definitions and
  sketches. A wrong auxiliary statement can make a proof hold for the wrong reason, or hide a
  weaker result behind a headline.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03k-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.5–§4.7 (book pp. 116–127).

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
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{GraphIsomorphism, GraphIsomorphismZK}.lean`, `ZeroKnowledge/GraphIsomorphism/{Concrete, Efficiency, EfficiencyRep, EfficiencyRepGI, Proofs, Soundness, SoundnessRep, SoundnessRepGI}.lean`, `ZeroKnowledge/GraphIsomorphismZK/{Closeness, Simulator}.lean`, `ZeroKnowledge/{Encoding, EncodingMachines, EncodingPermutations, CommitmentLemmas, NPLemmas}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` |
| Context, not under audit | pack 03e's files (interaction, ZK definitions, commitments, NP) |
| Design record | `briefs/pass-shelat/DESIGN.md` |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-117.e, Def-118.a, Claim-118.b, Claim-118.c, Prot-118.3, Lems 119.a–d, Prop-118.4, Prot-120.6, Lems 120.a–d, Prop-120.7, Thm-122.3 (with .hv, .trunc), the GI simulator rows, Inf-4.1, Inf-4.2 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/k/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 358 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 23 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 23 use only the standard axioms, and
   0 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 17 files.

Pack-specific notes (as drafted): elaboration (a fresh replay of the closure); the axiom prints of
the headlines whose proofs live here; admissions (none in these files); lint.

## Specific questions

1. **GI and GNI protocols.** Are completeness and soundness stated with the source's error
   bounds, and the repetitions' error bounds?
2. **ZK for GI (Thm 122.3).** Are the honest-verifier and the truncated forms (D8) stated as
   declared? Is the simulator's success probability per attempt `1/2`, and is the truncation
   error stated?
3. **Encodings.** Are the graph and permutation encodings injective and polynomial-time, as
   their uses need (Inf-4.1, Inf-4.2)?

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/k/replay.log =====

# closure of pack 03k's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 358 modules, extracted from g03-replay.log
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
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 15s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 7s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0
TCSlib/Programs/Compat rc=0 3s errors=0 sorry=0
TCSlib/Programs/Util/List rc=0 9s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/k/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03k's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.pushesUniform_coinTable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.polyTimeComputable_encPermGraph: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.polyTimeComputable_encPermMulInv: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.polyTimeComputable_encPermFromCoins: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Riso_witnessRelation: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_gi_cheat_le_half: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_gi_rep_cheat_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_gni_rep_cheat: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gni_interactiveProofErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gni_interactiveProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_efficientProverProofErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_rep_efficientProverProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_rep_interactiveProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_sim_H_dist: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_sim_half: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_giSimTrunc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_giSimulator: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_statZK: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.gi_hvzk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_samplePerm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_mul_permFailBound: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_adaptive_guess: propext, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/k/admissions.txt =====

# declarations with `sorry` in pack 03k's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/k/lint.log =====

# scripts/style_lint.py on pack 03k's files, at a3c5fa8b72e50939822f22364647dc844a3914a0


















0 findings in 17 files

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph non-isomorphism and graph isomorphism protocols

The two graph protocols of [PS10, §4.5]: the interactive proof for graph non-isomorphism
[PS10, Protocol 118.3, Proposition 118.4] (unbounded prover, verifier first) and the
interactive proof with efficient prover for graph isomorphism [PS10, Protocol 120.6,
Proposition 120.7] (prover first). Graphs are the Boolean adjacency relations `Graph n` of
`Encoding.lean`, isomorphism is `Isomorphic G₀ G₁ := ∃ σ, σ(G₀) = G₁` (Def-117.e), the string
languages `Liso`, `Lniso` and the witness relation `Riso` are stated on the encoded instance
`⟨encGraph G₀, encGraph G₁⟩` (Def-118.a). Every protocol is given once for a single iteration
and once repeated `|x|` times (the text's "repeat `|G₁|` times"); the concrete probability
lemmas (Lem-119.a–d, Lem-120.a–d) are stated over typed coins with ideal uniform
permutations, and the string-level propositions carry the statistical term of the
rejection-sampled permutations (D10).

**Deviation (D10, Inf-4.2):** the honest parties sample `σ, π ← S_n` by `samplePerm`
(`permFromCoins` at the campaign parameters of `Asymptotic/Permutations.lean`:
`permBits n = Nat.size n` bits per trial and `permTrials n = 2n²` trials per position,
identity on failure), which fails with probability at most `permFailBound n = n · 2^{-n}`;
the single-iteration graph non-isomorphism proof has soundness error `1/2 + permFailBound n`
and the repeated protocols' soundness errors carry the same term. The frozen scratch's
`permFromCoins n n n` (`n` bits per trial) accepts a trial with probability `(n - i) / 2^n`
and would make the prover's permutation the identity almost surely — under which
Theorem 122.3 fails (the third message would reveal `σ⁻¹`).

**Repair (run-3 audit P2-1):** `samplePerm`, `permCoinLen` and `permFailBound` are stated in
terms of the shared `permBits`/`permTrials`, `permFailBound n = n · 2^{-n}` is the closed
form `uprob_permFromCoins_none_le_two_pow`, `statClose_samplePerm` and
`negligible_mul_permFailBound` are proved from the shared lemmas, and the run-2
`permFailBound_le_exp` (bound `n e^{-n/2}` for the local parameters) was removed.
(Run-3 audit P10-3, which reported the private `polyTimeComputable_encSamplePerm` as a
diverged copy of the shared sampler lemma with `n²` trials, is resolved by the same repair:
the string form of the sampler is `GI.sampleStr_poly` of `GraphIsomorphism/Efficiency.lean`,
a derivation of `polyTimeComputable_encPermFromCoins` at the one set of parameters
`permBits`/`permTrials`, and DESIGN.md §2.15 records them.)

**Proof layout (run 4).** This file is at the file-size limit, so the proofs of its theorems
live in the sibling files `GraphIsomorphism/Proofs.lean` (verbatim shadow copies of the
definitions below in the inner namespace `GI`, definitionally equal to them, with the generic
infrastructure), `GraphIsomorphism/Efficiency.lean` (the machines of the honest parties and the
decider of `Riso`) and `GraphIsomorphism/Soundness.lean` (completeness and soundness); each
target below is closed by `exact GI.…`, which type-checks by `rfl`.

**Repair (run-3 audit P10-1, P10-2):** the exact-probability lemmas `uprob_adaptive_guess`
(Lem-119.c) and `uprob_gni_rep_cheat` (Lem-119.b) assume the auxiliary coin type nonempty
(`[Nonempty W]`, `[Nonempty ρ]`): `uprob` on an empty type is `0`, so the run-2 statements
read `0 = 1` at `m = 0` over `Empty`. Every consumer instantiates the coin type with a tape
`Fin k → Bool` (nonempty), so no downstream statement changes; `uprob_gi_rep_cheat_le`
(an inequality, true for empty coins) is reproved by a case split on `ρ`. Both corrected
lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the change of
variables `gniShear`), which certifies the repaired statements.

**Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).

**Deviation (well-formedness):** the verifiers reject common inputs that are not the
encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
malformed `x ∉ L` could decode to a pair of isomorphic graphs and soundness would fail.

## Contents

* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs` — shadow copies of the
  definitions of this file (namespace `GI`) and the generic proof infrastructure.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency` — the machines of the honest
  parties of the single iterations and the decider of `Riso`.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep` — the loop infrastructure
  of the `|x|`-fold parties and the machine of the `|x|`-fold graph non-isomorphism verifier.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI` — the machines of the
  parties of the `|x|`-fold graph isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness` — completeness and soundness of
  the single iterations.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete` — shadow copies of the concrete
  repetition lemmas (Lem-119.b, Lem-119.c, Lem-120.d) for the sibling proofs.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep` — completeness and soundness
  of the `|x|`-fold graph non-isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI` — completeness and
  soundness of the `|x|`-fold graph isomorphism protocol.

## Main definitions

* `TCSlib.Cryptography.Isomorphic` — `∃ σ, σ(G₀) = G₁` [PS10, §4.5] (Def-117.e).
* `TCSlib.Cryptography.Liso`, `TCSlib.Cryptography.Lniso`, `TCSlib.Cryptography.Riso` —
  the languages of isomorphic / non-isomorphic encoded pairs and the witness relation
  (Def-118.a); `encInstance`, `wellFormedInstance`, `instanceVertices`.
* `TCSlib.Cryptography.samplePerm`, `TCSlib.Cryptography.permFailBound` — the honest parties'
  permutation sampler and its failure bound (D10).
* `TCSlib.Cryptography.gniProtocol`, `TCSlib.Cryptography.gniProtocolRep` — the graph
  non-isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 118.3]
  (Prot-118.3).
* `TCSlib.Cryptography.giProtocol`, `TCSlib.Cryptography.giProtocolRep` — the graph
  isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 120.6]
  (Prot-120.6).

## Main results

* `TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic` — uniformly permuted isomorphic
  graphs are identically distributed (Lem-119.a, proved).
* `TCSlib.Cryptography.uprob_adaptive_guess` — the adaptive guessing lemma `2^{-m}`
  (Lem-119.c, proved); `TCSlib.Cryptography.uprob_gni_rep_cheat` — `n`-fold GNI soundness
  (Lem-119.b, proved); `TCSlib.Cryptography.gni_honest_reply` — GNI completeness (Lem-119.d,
  proved).
* `TCSlib.Cryptography.gi_honest_reply_eq` (Lem-120.a, proved),
  `TCSlib.Cryptography.not_isomorphic_both` (Lem-120.b, proved),
  `TCSlib.Cryptography.uprob_gi_cheat_le_half` (Lem-120.c, proved),
  `TCSlib.Cryptography.uprob_gi_rep_cheat_le` (Lem-120.d, proved from Lem-119.c).
* `TCSlib.Cryptography.gni_interactiveProofErr`, `TCSlib.Cryptography.gni_interactiveProof`
  — [PS10, Proposition 118.4]; `TCSlib.Cryptography.gi_efficientProverProofErr`,
  `TCSlib.Cryptography.gi_rep_efficientProverProof` — [PS10, Proposition 120.7].
* `TCSlib.Cryptography.Riso_witnessRelation` — `Riso` is a witness relation for `Liso`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, the graph non-isomorphism protocol.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Isomorphism of graphs (Def-117.e) -/

/-- Two graphs on `Fin n` are isomorphic when some relabelling `σ` maps the first onto the
second, `σ(G₀) = G₁` [PS10, §4.5] (Def-117.e). The "same number of vertices" condition of
the text is the common type `Graph n`. -/
def Isomorphic {n : ℕ} (G₀ G₁ : Graph n) : Prop := ∃ σ : Equiv.Perm (Fin n), permGraph G₀ σ = G₁

/-- Isomorphism is decidable (finitely many permutations). -/
instance {n : ℕ} (G₀ G₁ : Graph n) : Decidable (Isomorphic G₀ G₁) := by
  unfold Isomorphic
  infer_instance

/-- Every graph is isomorphic to itself (via the identity). -/
theorem Isomorphic.refl {n : ℕ} (G : Graph n) : Isomorphic G G := ⟨1, permGraph_one G⟩

/-- Isomorphism is symmetric (via the inverse permutation). -/
theorem Isomorphic.symm {n : ℕ} {G₀ G₁ : Graph n} (h : Isomorphic G₀ G₁) : Isomorphic G₁ G₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, permGraph_permGraph_inv]⟩

/-- Isomorphism is transitive (via the product of the permutations). -/
theorem Isomorphic.trans {n : ℕ} {G₀ G₁ G₂ : Graph n} (h₁ : Isomorphic G₀ G₁)
    (h₂ : Isomorphic G₁ G₂) : Isomorphic G₀ G₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [← permGraph_mul, hσ, hτ]⟩

/-- A graph is isomorphic to each of its relabellings. -/
theorem isomorphic_permGraph {n : ℕ} (G : Graph n) (σ : Equiv.Perm (Fin n)) :
    Isomorphic G (permGraph G σ) := ⟨σ, rfl⟩

/-- Relabelling by a fixed permutation is injective on graphs. -/
theorem permGraph_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective fun G : Graph n => permGraph G σ := by
  intro G G' h
  have := congrArg (fun K => permGraph K σ⁻¹) h
  simpa only [permGraph_permGraph_inv] using this

/-- A graph is isomorphic to at most one of two non-isomorphic graphs [PS10, proof of
Proposition 120.7, "`H` can be isomorphic to at most one of them"] (Lem-120.b): by symmetry
and transitivity of `Isomorphic`. -/
theorem not_isomorphic_both {n : ℕ} {G₀ G₁ H : Graph n} (h : ¬ Isomorphic G₀ G₁) :
    ¬ (Isomorphic G₀ H ∧ Isomorphic G₁ H) := fun ⟨h₀, h₁⟩ => h (h₀.trans h₁.symm)

/-- The honest prover's third message is accepted whatever the challenge [PS10, proof of
Proposition 120.7, corrected: `π(G₀) = H` and `(π σ⁻¹)(G₁) = H`] (Lem-120.a): if
`σ(G₀) = G₁` then `γ(G_b) = π(G₀)` for `γ = if b then π σ⁻¹ else π`. -/
theorem gi_honest_reply_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) (b : Bool) :
    permGraph (cond b G₁ G₀) (if b then π * σ⁻¹ else π) = permGraph G₀ π := by
  cases b
  · rfl
  · exact permGraph_mul_inv_of_eq hσ π

/-! ### Encoded instances and the languages (Def-118.a) -/

/-- The total decoding of a graph on a *given* vertex count `n` (entries read with default
`false`): the second component of `decGraph` at `n`, used to read the other party's graph
message on the vertex set of the common input. -/
def decGraphAt (n : ℕ) (w : List Bool) : Graph n := fun u v => w.getD (finProdFinEquiv (u, v)) false

/-- Decoding an encoded graph on its own vertex count gives the graph back. -/
@[simp] theorem decGraphAt_encGraph {n : ℕ} (G : Graph n) : decGraphAt n (encGraph G) = G :=
  funext fun u => funext fun v => encGraph_getD G u v

/-- The second component of `decGraph` is `decGraphAt` at the decoded vertex count. -/
theorem decGraph_snd (w : List Bool) : (decGraph w).2 = decGraphAt (decGraph w).1 w := rfl

/-- The encoded instance `x = ⟨encGraph G₀, encGraph G₁⟩` of the graph protocols
[PS10, Protocols 118.3 and 120.6, "`x = (G₀, G₁)`"]. -/
def encInstance {n : ℕ} (G₀ G₁ : Graph n) : List Bool := pairEncode (encGraph G₀) (encGraph G₁)

/-- An encoded instance on `n` vertices has `3n² + 2` bits. -/
theorem length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : (encInstance G₀ G₁).length = 3 * (n * n) + 2 := by
  simp only [encInstance, length_pairEncode, length_encGraph]
  ring

/-- The vertex count read from a common input: `Nat.sqrt` of the length of the first
component (the `n` of `decGraph`). -/
def instanceVertexCount (x : List Bool) : ℕ := Nat.sqrt (pairFstD x).length

/-- The first graph of a common input, on the decoded vertex set. -/
def instanceG₀ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairFstD x)

/-- The second graph of a common input, on the vertex set of the first. -/
def instanceG₁ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairSndD x)

/-- A common input is well formed when it is a pair whose two components are adjacency
matrices of the same size `n²` (the "same number of vertices" of [PS10, §4.5]). -/
def wellFormedInstance (x : List Bool) : Bool :=
  decide ((pairDecode x).isSome ∧ (pairFstD x).length = instanceVertexCount x * instanceVertexCount x ∧
    (pairSndD x).length = instanceVertexCount x * instanceVertexCount x)

/-- The vertex count of an encoded instance from its length: `n = √((|x| - 2) / 3)`. -/
def instanceVertices (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 3)

/-- `instanceVertices` recovers `n` from the length of an encoded instance on `n` vertices. -/
theorem instanceVertices_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertices (encInstance G₀ G₁).length = n := by
  rw [instanceVertices, length_encInstance, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.sqrt_eq]

/-- The vertex count decoded from an encoded instance is `n`. -/
theorem instanceVertexCount_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertexCount (encInstance G₀ G₁) = n := by
  simp [instanceVertexCount, encInstance, Nat.sqrt_eq]

/-- The language of pairs of isomorphic graphs, `L_iso` [PS10, §4.5] (Def-118.a): the encoded
instances `⟨encGraph G₀, encGraph G₁⟩` with `σ(G₀) = G₁` for some `σ`. -/
def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

/-- The language of pairs of non-isomorphic graphs with the same number of vertices,
`L_niso` [PS10, §4.5] (Def-118.a); malformed strings are not in `L_niso`. -/
def Lniso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n), x = pairEncode (encGraph G₀) (encGraph G₁) ∧ ¬ Isomorphic G₀ G₁}

/-- The witness relation of `L_iso` [PS10, Theorem 122.3, "some canonical witness relation"]
(Def-118.a): the witness of `⟨encGraph G₀, encGraph G₁⟩` is the encoding of a permutation `σ`
with `σ(G₀) = G₁`. -/
def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

/-- Equal encodings come from the same vertex count and the same graph (as a `Sigma`). -/
private theorem sigma_eq_of_encGraph_eq {n n' : ℕ} {G : Graph n} {G' : Graph n'}
    (h : encGraph G = encGraph G') : (⟨n, G⟩ : Σ m, Graph m) = ⟨n', G'⟩ := by
  rw [← decGraph_encGraph G, ← decGraph_encGraph G', h]

/-- An encoded instance is in `L_iso` exactly when its graphs are isomorphic. -/
theorem encInstance_mem_Liso_iff {n : ℕ} (G₀ G₁ : Graph n) : encInstance G₀ G₁ ∈ Liso ↔ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', σ, hx, hσ⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨n, G₀, G₁, σ, rfl, hσ⟩

/-- An encoded instance is in `L_niso` exactly when its graphs are not isomorphic. -/
theorem encInstance_mem_Lniso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Lniso ↔ ¬ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', hx, hni⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact hni
  · intro h
    exact ⟨n, G₀, G₁, rfl, h⟩

/-- The languages `L_iso` and `L_niso` are disjoint. -/
theorem not_mem_Lniso_of_mem_Liso {x : List Bool} (h : x ∈ Liso) : x ∉ Lniso := by
  obtain ⟨n, G₀, G₁, σ, rfl, hσ⟩ := h
  rw [show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
    encInstance_mem_Lniso_iff]
  exact fun hni => hni ⟨σ, hσ⟩

/-- `Riso` is a witness relation for `L_iso` [PS10, Definition 191.11 for Theorem 122.3]
(Def-118.a).

**Proof sketch.** `mem_iff`: both sides unfold to the same existential (the witness of
`⟨encGraph G₀, encGraph G₁⟩` is `encPerm σ`). `bounded` with `p := var`: `|encPerm σ| = n² ≤
3n² + 2 = |x|` (`length_encPerm`, `length_encInstance`). `decidable`: the predicate
`T z := wellFormedInstance x && decide (encPerm (decPerm n y) = y) &&
decide (encGraph (permGraph G₀ (decPerm n y)) = pairSndD x)` with `x := pairFstD z`,
`y := pairSndD z`, `n := instanceVertexCount x`; it is polynomial-time by
`Complexity.polyTimeComputable_and`, `polyTimeComputable_pairEq`, `polyTimeComputable_lenEq`
and `polyTimeComputable_encPermGraph` composed with the pairing projections (the identity
`encPerm ∘ decPerm` test is a scan of the `n²` bits with the row/column uniqueness check of
`decPerm`'s sketch); on well-formed inputs `T ⟨x, y⟩ = true ↔ Riso x y` by
`decGraph_encGraph`, `decPerm_encPerm`, `encGraph_injective`, `encPerm_injective` and the
well-formedness characterization of `wellFormedInstance`. -/
theorem Riso_witnessRelation : WitnessRelation Liso Riso := by
  refine ⟨fun x => ?_, ⟨.var, ?_⟩, ?_⟩
  · constructor
    · rintro ⟨n, G₀, G₁, σ, hx, hσ⟩
      exact ⟨encPerm σ, n, G₀, G₁, σ, hx, rfl, hσ⟩
    · rintro ⟨y, n, G₀, G₁, σ, hx, -, hσ⟩
      exact ⟨n, G₀, G₁, σ, hx, hσ⟩
  · rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, -⟩
    rw [PolyExpr.eval_var, length_encPerm, show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
      length_encInstance]
    omega
  · exact GI.Riso_decidable

/-! ### The permutation sampler of the honest parties (D10) -/

/-- The honest parties' permutation sampler: `permFromCoins` at the campaign parameters
(`permBits n = Nat.size n` bits per trial, so that `n ≤ 2^k ≤ 2n`, and `permTrials n = 2n²`
trials per position), read from the tape by `coinTable`; the identity on failure
[PS10, Protocols 118.3 and 120.6, "`σ ← S_n`", "`π ← S_n`"] (D10).

**Repair (run-3 audit P2-1):** parameters taken from `Asymptotic/Permutations.lean`
(the run-2 file used `Nat.size n` bits and `n²` trials locally). -/
noncomputable def samplePerm (n : ℕ) (r : List Bool) : Equiv.Perm (Fin n) :=
  (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1

/-- The number of tape bits consumed by `samplePerm n`: `n · permTrials n · permBits n`
(`= 2n³ · Nat.size n`).

**Repair (run-3 audit P2-1):** stated in terms of `permTrials`/`permBits`. -/
def permCoinLen (n : ℕ) : ℕ := n * permTrials n * permBits n

/-- The failure bound of the permutation sampler at the campaign parameters, `n · 2^{-n}`
(`uprob_permFromCoins_none_le_two_pow`).

**Repair (run-3 audit P2-1):** the run-2 bound `n (1 - 2^{-size n})^{n²}` had no closed form;
the closed form `n · 2^{-n}` is owned by `Asymptotic/Permutations.lean`. -/
noncomputable def permFailBound (n : ℕ) : ℝ := n * (2 : ℝ)⁻¹ ^ n

/-- The sampler consumes at most `(N + 1)²` tape bits whenever `2n² ≤ N` (every encoded
instance on `n` vertices has length `3n² + 2`, `length_encInstance`), so the coin polynomial
`normal 1 2` of the parties suffices: `n · 2n² · permBits n ≤ 2n⁴ ≤ N² ≤ (N + 1)²`.

**Repair (run-3 audit P2-1):** hypothesis strengthened from `n² ≤ N` to `2n² ≤ N` to absorb
the factor `2` of `permTrials` (satisfied by every encoded instance). -/
theorem permCoinLen_le {n N : ℕ} (h : 2 * (n * n) ≤ N) : permCoinLen n ≤ (N + 1) ^ 2 := by
  have hnn : n * n ≤ N := le_trans (Nat.le_mul_of_pos_left (n * n) two_pos) h
  calc permCoinLen n = n * (2 * n * n) * permBits n := rfl
    _ ≤ n * (2 * n * n) * n := Nat.mul_le_mul_left _ (permBits_le n)
    _ = (2 * (n * n)) * (n * n) := by ring
    _ ≤ N * N := Nat.mul_le_mul h hnn
    _ ≤ (N + 1) ^ 2 := by nlinarith

/-- The permutation sampler is within `permFailBound n = n · 2^{-n}` of a uniform permutation
(D10): `pushesUniform_coinTable` identifies the tape with a uniform coin table
(`StatClose.comp_pushesUniform`) and `statClose_permFromCoins_two_pow` is the closeness of
`permFromCoins` at the campaign parameters.

**Repair (run-3 audit P2-1):** proved from the shared lemmas of
`Asymptotic/Permutations.lean` (previously sorried with the argument restated). -/
theorem statClose_samplePerm (n : ℕ) :
    StatClose (fun r : Fin (permCoinLen n) → Bool => samplePerm n (List.ofFn r))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) :=
  (statClose_permFromCoins_two_pow n 1).comp_pushesUniform
    (pushesUniform_coinTable n (permTrials n) (permBits n))

/-- The sampling error of the repeated protocols, `|x| · permFailBound n` with
`n = instanceVertices |x|`, is negligible in `|x|` (Inf-4.4): for `N ≥ 8`,
`√(N/4) ≤ instanceVertices N ≤ N`, so the term is at most `N² · 2^{-√(N/4)}`
(`negligible_two_pow_neg_sqrt_div`, `Negligible.mul_pow`, `Negligible.mono`).

**Repair (run-3 audit P2-1):** proved (the run-2 sketch went through `permFailBound_le_exp`,
removed). -/
theorem negligible_mul_permFailBound :
    Negligible fun N : ℕ => (N : ℝ) * permFailBound (instanceVertices N) := by
  refine ((negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mul_pow 2).mono
    ⟨8, fun N hN => ?_⟩
  have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
  have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
  have hpow : (2 : ℝ)⁻¹ ^ instanceVertices N ≤ (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have hv' : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
  unfold permFailBound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (N : ℝ) * (instanceVertices N * (2 : ℝ)⁻¹ ^ instanceVertices N)
      ≤ N * (N * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4)) := by gcongr
    _ = (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) := by ring

/-- The `i`-th block of `c` bits of a tape (the coins of iteration `i` of a repeated
protocol). -/
def coinSlice (c i : ℕ) (r : List Bool) : List Bool := (r.drop (i * c)).take c

/-! ### The graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3) -/

/-- The honest (unbounded) prover of the graph non-isomorphism protocol [PS10, Protocol
118.3]: on the latest received graph `H` it answers `b' = 0` if `H ≅ G₀` and `b' = 1`
otherwise (so `b' = b` whenever `G₀ ≇ G₁`); no coins, no auxiliary input. The text's
"exponential time" is the search over all permutations in the `Decidable` instance. -/
def gniProver : Strategy where
  coins := .const 0
  next x _ _ hist :=
    [decide (¬ Isomorphic (instanceG₀ x) (decGraphAt (instanceVertexCount x) (hist.getLastD [])))]

/-- The verifier of one iteration of the graph non-isomorphism protocol [PS10, Protocol
118.3]: with random tape `b :: r`, it first sends `H = σ(G_b)` for `σ := samplePerm n r`, and
on the reply `b'` outputs `[decide (x well formed ∧ b' = b)]`.

**Deviation:** `σ` by rejection sampling (D10); well-formedness check on `x`. -/
noncomputable def gniVerifier : Strategy where
  coins := .add (.const 1) (.normal 1 2)
  next x _ r hist :=
    let b := r.headD false
    match hist with
    | [] => encGraph (permGraph (if b then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (r.drop 1)))
    | [b'] => [decide (wellFormedInstance x = true ∧ b'.headD false = b)]
    | _ => [false]

/-- One iteration of the graph non-isomorphism protocol [PS10, Protocol 118.3]
(Prot-118.3): verifier first, two messages (`H`, then `b'`); the verdict is the verifier's
third activation. -/
noncomputable def gniProtocol : Protocol where
  P := gniProver
  V := gniVerifier
  rounds := .const 2
  verifierFirst := true

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3,
"repeat the procedure `|G₁|` times"]: iteration `i` uses the coin block
`coinSlice (1 + (|x|+1)²) i r` (bit `b_i`, then the permutation coins); after `i < |x|`
replies it sends `H_i`, and on the complete history of `|x|` replies it accepts iff `x` is
well formed and every reply `b'_i` equals `b_i`.

**Deviation:** `|x|` iterations instead of `n`; rejection-sampled `σ_i` (D10). -/
noncomputable def gniVerifierRep : Strategy where
  coins := .mul .var (.add (.const 1) (.normal 1 2))
  next x _ r hist :=
    let c := 1 + (x.length + 1) ^ 2
    if hist.length < x.length then
      let ri := coinSlice c hist.length r
      encGraph (permGraph (if ri.headD false then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (ri.drop 1)))
    else
      [decide (wellFormedInstance x = true ∧
        ∀ j : Fin x.length, (hist.getD j []).headD false = (coinSlice c j r).headD false)]

/-- The `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3):
verifier first, `2|x|` messages; the honest prover answers each `H_i` as in one iteration. -/
noncomputable def gniProtocolRep : Protocol where
  P := gniProver
  V := gniVerifierRep
  rounds := .mul (.const 2) .var
  verifierFirst := true

/-! ### The graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6) -/

/-- The prover of the graph isomorphism protocol [PS10, Protocol 120.6]: with witness
`y = encPerm σ` it samples `π ← S_n` from its tape, sends `H = π(G₀)`, and on the challenge
`b` sends `γ = if b then π σ⁻¹ else π` (so that `γ(G_b) = H`, `gi_honest_reply_eq`).

**Deviation (D10):** `π` by `samplePerm` (rejection sampling, identity on failure). -/
noncomputable def giProver : Strategy where
  coins := .normal 1 2
  next x y r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let σ := decPerm n y
    let π := samplePerm n r
    match hist with
    | [] => encGraph (permGraph G₀ π)
    | _ :: _ => encPerm (if (hist.headD []).headD false then π * σ⁻¹ else π)

/-- The verifier of the graph isomorphism protocol [PS10, Protocol 120.6]: with the single
coin `b` it answers the first message `H` with `[b]`, and on `[H, γ]` outputs
`[decide (x well formed ∧ γ(G_b) = H)]`.

**Deviation:** well-formedness check on `x` (needed for soundness on malformed inputs). -/
noncomputable def giVerifier : Strategy where
  coins := .const 1
  next x _ r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let G₁ : Graph n := fun u v => (pairSndD x).getD (finProdFinEquiv (u, v)) false
    let b := r.headD false
    match hist with
    | [H, γ] => [decide (wellFormedInstance x = true ∧
        encGraph (permGraph (if b then G₁ else G₀) (decPerm n γ)) = H)]
    | [_] => [b]
    | _ => [false]

/-- One iteration of the graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6):
three messages (`H`, `b`, `γ`), prover first; the verdict is the verifier's activation on
the complete history `[H, γ]`. -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

/-- The prover of the `|x|`-fold graph isomorphism protocol: iteration `i` (the prover has
received `2i` or `2i + 1` messages: the challenges and the verifier's empty fourth messages)
uses `π_i := samplePerm n (coinSlice (|x|+1)² i r)`; on an even history it sends `H_i`, on an
odd one `γ_i` for the latest challenge. -/
noncomputable def giProverRep : Strategy where
  coins := .mul .var (.normal 1 2)
  next x y r hist :=
    let n := instanceVertexCount x
    let σ := decPerm n y
    let π := samplePerm n (coinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)
    if hist.length % 2 = 0 then encGraph (permGraph (instanceG₀ x) π)
    else encPerm (if (hist.getLastD []).headD false then π * σ⁻¹ else π)

/-- The verifier of the `|x|`-fold graph isomorphism protocol: it has received
`[H_0, γ_0, H_1, γ_1, …]`; on an odd history it sends the challenge `b_i = r_i`, on an even
incomplete history the empty message, and on the complete history it accepts iff `x` is
well formed and `γ_j(G_{b_j}) = H_j` for every `j < |x|`. -/
noncomputable def giVerifierRep : Strategy where
  coins := .var
  next x _ r hist :=
    let n := instanceVertexCount x
    if hist.length % 2 = 1 then [r.getD (hist.length / 2) false]
    else if hist.length < 2 * x.length then []
    else [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
      encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm n (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])]

/-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
`|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
noncomputable def giProtocolRep : Protocol where
  P := giProverRep
  V := giVerifierRep
  rounds := .mul (.const 4) .var
  verifierFirst := false

/-! ### Concrete probability lemmas (ideal uniform permutations) -/

/-- Uniformly permuted isomorphic graphs are identically distributed, jointly with
independent auxiliary coins [PS10, proof of Lemma 123.5 and of Proposition 118.4,
"`H` is independent of the bit `b`"] (Lem-119.a): if `σ₀(G₀) = G₁` then
`σ(G₁) = (σ σ₀)(G₀)` and `σ ↦ σ σ₀` is a bijection of `S_n` (`Equiv.mulRight`). -/
theorem uprob_permGraph_eq_of_isomorphic {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → ρ → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₁ z.1) z.2) =
      uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2) := by
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.mulRight σ₀) (Equiv.refl ρ))
    (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2)]
  congr 1
  funext z
  simp [← hσ, permGraph_mul]

/-- The one-coordinate form of Lem-119.a: `σ(G₁)` and `σ(G₀)` have the same law. -/
theorem uprob_permGraph_eq_of_isomorphic' {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → Prop) :
    uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₁ σ)) =
      uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ)) := by
  rw [← uprob_comp_equiv (Equiv.mulRight σ₀) (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ))]
  congr 1
  funext σ
  simp [← hσ, permGraph_mul]

/-- The strict prefix `b_0, …, b_{i-1}` of a bit tuple (the history an adaptive prover has
seen before challenge `i`). -/
def prefixLT {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin i → α :=
  fun j => b (Fin.castLE i.isLt.le j)

/-- The prefix `b_0, …, b_i` of a tuple (the history including the current challenge). -/
def prefixLE {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin (i + 1) → α :=
  fun j => b (Fin.castLE i.isLt j)

/-- The adaptive guess map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` of Lem-119.c: triangular with
identity diagonal, hence a bijection of `Fin m → Bool` for every `w` (`adaptiveXorEquiv`); it
carries the event "`b_i = g_i(b_{<i}, w)` for every `i`" to "`b = 0`". -/
private def adaptiveXor {m : ℕ} {W : Type*} (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W)
    (b : Fin m → Bool) : Fin m → Bool :=
  fun i => xor (b i) (g i (prefixLT b i) w)

/-- `adaptiveXor g w` is injective.

**Proof sketch.** If the images agree then `b_i = b'_i` for every `i`, by induction on a bound
`k > i`: the prefixes `b_{<i}`, `b'_{<i}` agree by the induction hypothesis, so the guesses
`g_i(b_{<i}, w)`, `g_i(b'_{<i}, w)` agree and `xor` cancels (`Bool.xor_left_inj`). -/
private theorem adaptiveXor_injective {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) :
    Function.Injective (adaptiveXor g w) := by
  intro b b' h
  have key : ∀ k, ∀ i : Fin m, i.val < k → b i = b' i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hpre : prefixLT b i = prefixLT b' i := by
          funext j
          have hj := j.isLt
          exact ih _ (by simp only [Fin.coe_castLE]; omega)
        have hi' := congrFun h i
        simp only [adaptiveXor, hpre] at hi'
        exact Bool.xor_left_inj.mp hi'
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The bijection `adaptiveXor g w` of `Fin m → Bool` (an injection of a finite type into
itself, `Finite.injective_iff_bijective`). -/
private noncomputable def adaptiveXorEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.ofBijective (adaptiveXor g w)
    (Finite.injective_iff_bijective.mp (adaptiveXor_injective g w))

/-- The coin bijection `(b, w) ↦ (adaptiveXor g w b, w)` of `(Fin m → Bool) × W`. -/
private noncomputable def adaptiveEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) : (Fin m → Bool) × W ≃ (Fin m → Bool) × W where
  toFun z := (adaptiveXorEquiv g z.2 z.1, z.2)
  invFun z := ((adaptiveXorEquiv g z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The adaptive guessing lemma [PS10, proof of Proposition 118.4, "each iteration is
independent of all prior iterations"] (Lem-119.c): for every finite nonempty `W` and every
family of guesses `g i` depending on the earlier bits and on `w`, the probability that a
uniform tuple `b` satisfies `b_i = g_i(b_{<i}, w)` for every `i` is exactly `2^{-m}`. The
engine of every `2^{-n}` soundness bound against adaptive provers.

**Deviation:** `W` nonempty (`uprob` on an empty type is `0`, so the equality fails for
`W = Empty`; every consumer uses a tape type `Fin k → Bool`).

**Repair (run-3 audit P10-1):** hypothesis `[Nonempty W]` added (the run-2 statement
specialised to `W := Empty`, `m := 0` reads `0 = 1`).

**Proof sketch.** For each `w` the map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` is a bijection of
`Fin m → Bool` (`adaptiveXorEquiv`: triangular with identity diagonal, injective by strong
induction on `i`, hence bijective on a finite type) carrying the event to `{b = 0}`; so
`uprob_comp_equiv` with the coin bijection `adaptiveEquiv`, `uprob_fst` (here `W ≠ ∅` is
used) and `OneWay.uprob_eq_one_div_card` give `1 / 2^m` (`Fintype.card_fun`). Equivalently,
exactly one `b` per `w` satisfies all the constraints (`|W|` elements out of `2^m |W|`). -/
theorem uprob_adaptive_guess (m : ℕ) {W : Type*} [Fintype W] [Nonempty W]
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) :
    uprob (fun z : (Fin m → Bool) × W => ∀ i, z.1 i = g i (prefixLT z.1 i) z.2) =
      (2 : ℝ)⁻¹ ^ m := by
  have hev : ∀ z : (Fin m → Bool) × W,
      (∀ i, z.1 i = g i (prefixLT z.1 i) z.2) ↔ (adaptiveEquiv g z).1 = fun _ => false := by
    intro z
    simp only [adaptiveEquiv, adaptiveXorEquiv, Equiv.coe_fn_mk, Equiv.ofBijective_apply,
      adaptiveXor, funext_iff]
    exact forall_congr' fun i => by cases z.1 i <;> cases g i (prefixLT z.1 i) z.2 <;> simp
  rw [OneWay.uprob_congr hev,
    uprob_comp_equiv (adaptiveEquiv g) (fun z : (Fin m → Bool) × W => z.1 = fun _ => false),
    uprob_fst (β := W) (fun b : Fin m → Bool => b = fun _ => false),
    OneWay.uprob_eq_one_div_card (fun _ : Fin m => false), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow]

/-- Soundness of one iteration of the graph isomorphism protocol against an arbitrary
prover [PS10, proof of Proposition 120.7] (Lem-120.c): if `G₀ ≇ G₁` then, for a prover
whose first message is `H(r)` and whose reply to the challenge `b` is `γ(b, r)`, the verifier
accepts with probability at most `1/2` over the uniform `b` and the prover's coins `r`.

**Proof sketch.** `uprob_bool_prod`; for each `r` at most one `b` can be accepted
(`not_isomorphic_both`), so the `b = false` event is contained in the complement of the
`b = true` event (`uprob_mono`, `uprob_not`). -/
theorem uprob_gi_cheat_le_half {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : ρ → Graph n) (γ : Bool → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : Bool × ρ => permGraph (cond z.1 G₁ G₀) (γ z.1 z.2) = H z.2) ≤ 1 / 2 := by
  rw [uprob_bool_prod]
  have hsub : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) ≤
      uprob (fun r : ρ => ¬ permGraph (cond true G₁ G₀) (γ true r) = H r) := by
    refine uprob_mono fun r h0 h1 => ?_
    exact not_isomorphic_both h ⟨⟨γ false r, h0⟩, ⟨γ true r, h1⟩⟩
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    have h1 : uprob (fun r : ρ => permGraph (cond true G₁ G₀) (γ true r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0, h1]
    norm_num
  · rw [uprob_not] at hsub
    linarith

/-- Soundness of the `m`-fold graph isomorphism protocol against adaptive provers
[PS10, Proposition 120.7, "repeated … to drive the error as low as desired"] (Lem-120.d):
if `G₀ ≇ G₁` then for a prover whose `i`-th graph `H_i` depends on the earlier challenges and
its coins and whose `i`-th reply `γ_i` also depends on the current challenge, the verifier
accepts all `m` iterations with probability at most `2^{-m}`.

**Proof sketch.** For empty `ρ` the probability is `0`. Otherwise acceptance in iteration `i` forces
`b_i = g_i(b_{<i}, r)` for the guess `g_i := decide (G₁ ≅ H_i)` (`not_isomorphic_both`), so
`uprob_mono` reduces to `uprob_adaptive_guess`.

**Repair (run-3 audit P10-1):** statement unchanged (an inequality, true for empty coins);
the proof splits on `ρ` empty since `uprob_adaptive_guess` now assumes `Nonempty`. -/
theorem uprob_gi_rep_cheat_le {n m : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : (i : Fin m) → (Fin i → Bool) → ρ → Graph n)
    (γ : (i : Fin m) → (Fin (i + 1) → Bool) → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
      permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) ≤
      (2 : ℝ)⁻¹ ^ m := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
        permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) = 0 := by
      classical
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0]
    positivity
  · rw [← uprob_adaptive_guess m fun i p r => decide (Isomorphic G₁ (H i p r))]
    refine uprob_mono fun z hz i => ?_
    have hi := hz i
    cases hb : z.1 i
    · rw [hb] at hi
      have h0 : Isomorphic G₀ (H i (prefixLT z.1 i) z.2) := ⟨_, hi⟩
      exact (decide_eq_false fun h1 => not_isomorphic_both h ⟨h0, h1⟩).symm
    · rw [hb] at hi
      exact (decide_eq_true ⟨_, hi⟩).symm

/-- The change of variables of Lem-119.b, `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, with the
coins regrouped as `(b, (σ, w))` (inverse: multiply by `σ₀` instead). -/
private def gniShear {n m : ℕ} (ρ : Type*) (σ₀ : Equiv.Perm (Fin n)) :
    (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ) ≃
      ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ where
  toFun z := ((z.1, fun i => if z.1 i then z.2.1 i * σ₀⁻¹ else z.2.1 i), z.2.2)
  invFun z := (z.1.1, (fun i => if z.1.1 i then z.1.2 i * σ₀ else z.1.2 i, z.2))
  left_inv z := by
    rcases z with ⟨b, σ, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp
  right_inv z := by
    rcases z with ⟨⟨b, σ⟩, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp

/-- Under `gniShear` every graph `H_j = σ'_j(G₀)` is independent of `b`
(`permGraph_mul_inv_of_eq`), so the event "every reply equals the verifier's bit" is the
adaptive guessing event of `uprob_adaptive_guess` with guesses ignoring the earlier bits. -/
private theorem gniShear_event_iff {n m : ℕ} {ρ : Type*} {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    ∀ z : (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ),
      (∀ i, g i (prefixLE (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ z).1.1 j) G₁ G₀)
          ((gniShear (m := m) ρ σ₀ z).1.2 j)) i) (gniShear (m := m) ρ σ₀ z).2 =
            (gniShear (m := m) ρ σ₀ z).1.1 i) ↔
      (∀ i, z.1 i = g i (prefixLE (fun j => permGraph G₀ (z.2.1 j)) i) z.2.2) := by
  rintro ⟨b, σ, w⟩
  have hH : (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.1 j) G₁ G₀)
      ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.2 j)) = fun j => permGraph G₀ (σ j) := by
    funext j
    show permGraph (cond (b j) G₁ G₀) (if b j then σ j * σ₀⁻¹ else σ j) = permGraph G₀ (σ j)
    cases b j
    · rfl
    · exact permGraph_mul_inv_of_eq hσ (σ j)
  rw [hH]
  exact forall_congr' fun i => eq_comm

/-- Soundness of the `m`-fold graph non-isomorphism protocol against adaptive provers
[PS10, proof of Proposition 118.4] (Lem-119.b): if `σ₀(G₀) = G₁`, then for every prover
whose `i`-th reply `g_i` depends on the graphs `H_0, …, H_i` received so far and on its
(nonempty type of) coins `w`, the probability (over the verifier's bits `b`, permutations `σ`
and `w`) that every reply equals the verifier's bit is exactly `2^{-m}`.

**Deviation:** `ρ` nonempty (`uprob` on an empty type is `0`; the consumer
`gni_interactiveProof` uses `ρ := P'.Coins |x|`, a tape type).

**Repair (run-3 audit P10-2):** hypothesis `[Nonempty ρ]` added (the run-2 statement
specialised to `ρ := Empty`, `n = m = 0`, `σ₀ = 1` reads `0 = 1`).

**Proof sketch.** Change variables `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, a bijection of the
coins fixing `b` and `w` (`gniShear`, with `uprob_comp_equiv`); then every `H_i = σ'_i(G₀)`
(`permGraph_mul_inv_of_eq`, `hσ`) is a function of `σ'` alone, the event is
`∀ i, b_i = g'_i(b_{<i}, (σ', w))` with `g'_i` ignoring `b_{<i}` (`gniShear_event_iff`), and
`uprob_adaptive_guess` with `W := (Fin m → S_n) × ρ` (nonempty since `ρ` is) gives
`2^{-m}`. -/
theorem uprob_gni_rep_cheat {n m : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    uprob (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i) =
      (2 : ℝ)⁻¹ ^ m := by
  have h1 := uprob_comp_equiv (gniShear (m := m) ρ σ₀)
    (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i)
  have h2 := uprob_adaptive_guess m
    fun i (_ : Fin i → Bool) (w : (Fin m → Equiv.Perm (Fin n)) × ρ) =>
      g i (prefixLE (fun j => permGraph G₀ (w.1 j)) i) w.2
  rw [← h1, ← h2]
  exact OneWay.uprob_congr (gniShear_event_iff hσ g)

/-- Completeness of the graph non-isomorphism protocol [PS10, proof of Proposition 118.4,
"the prover will always succeed in finding `b'` such that `b' = b`"] (Lem-119.d): if
`G₀ ≇ G₁` then for every `b` and `σ` the honest reply `decide (¬ G₀ ≅ σ(G_b))` is `b`. -/
theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (b : Bool)
    (σ : Equiv.Perm (Fin n)) :
    decide (¬ Isomorphic G₀ (permGraph (cond b G₁ G₀) σ)) = b := by
  cases b
  · exact decide_eq_false (not_not.2 (isomorphic_permGraph G₀ σ))
  · exact decide_eq_true fun h' => h (h'.trans (isomorphic_permGraph G₁ σ).symm)

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of the graph isomorphism protocol is a PPT strategy
[PS10, Proposition 120.7, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^n, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`,
`polyTimeComputable_inArg`): `encPerm π` by `polyTimeComputable_encSamplePerm` on
`⟨x, r⟩`; message 1 by `polyTimeComputable_encPermGraph` on `⟨pairFstD x, encPerm π⟩`;
message 3 by `polyTimeComputable_encPermMulInv` on `⟨encPerm π, y⟩` (branch on the challenge
bit `pairFstD msgs` with `polyTimeComputable_ite`; the `γ = π` branch outputs `encPerm π`),
the case split on `msgs = []` by `polyTimeComputable_lenEq`; the equation with `giProver.next`
by `NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`, `decPerm_encPerm`. -/
theorem giProver_efficient : giProver.Efficient := GI.giProver_efficient

/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
for Proposition 120.7] (Inf-4.2).

**Proof sketch.** As `giProver_efficient`: the challenge is the first coin
(`polyTimeComputable_pairFstD`-style projection of one bit), the verdict compares
`polyTimeComputable_encPermGraph` on `⟨G_b, γ⟩` with `H` by `polyTimeComputable_pairEq`,
conjoined (`polyTimeComputable_and`) with the well-formedness test (`polyTimeComputable_lenEq`
against the squared vertex count in unary and `computesFunInTime_pairValid`). -/
theorem giVerifier_efficient : giVerifier.Efficient := GI.giVerifier_efficient

/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
[PS10, Proposition 118.4] (Inf-4.2): as `giVerifier_efficient`, with the first message
`polyTimeComputable_encPermGraph` on `⟨G_b, encPerm σ⟩` for `σ` from
`polyTimeComputable_encSamplePerm` and the verdict a one-bit comparison. -/
theorem gniVerifier_efficient : gniVerifier.Efficient := GI.gniVerifier_efficient

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy
(Inf-4.2): the coin block of iteration `hist.length` is cut by `pairTakePoly`/`pairDropPoly`
with the unary block length, the message as in `gniVerifier_efficient`, and the verdict is a
loop over the `|x|` replies (`polyTimeComputable_iterate` with an accumulated conjunction). -/
theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := GI.gniVerifierRep_efficient

/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2): as
`giProver_efficient` with the coin block of iteration `hist.length / 2` cut by
`pairTakePoly`/`pairDropPoly` and the parity test of the history length. -/
theorem giProverRep_efficient : giProverRep.Efficient := GI.giProverRep_efficient

/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2):
the challenge is coin `hist.length / 2`, and the verdict is a loop over the `|x|` pairs
`(H_j, γ_j)` of the history (`polyTimeComputable_iterate` over `polyTimeComputable_encPermGraph`
and `polyTimeComputable_pairEq`). -/
theorem giVerifierRep_efficient : giVerifierRep.Efficient := GI.giVerifierRep_efficient

/-! ### The propositions [PS10, Propositions 118.4 and 120.7] -/

/-- One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n` [PS10, Proposition 118.4, one
iteration] (Prop-118.4).

**Deviation (D10):** the verifier's `σ` is rejection-sampled; on a sampling failure `H = G_b`
may reveal `b`, whence the additional term `permFailBound n` with `n = instanceVertices |x|`.

**Proof sketch.** Completeness: for `x = encInstance G₀ G₁ ∈ L_niso` the verifier's message
decodes to `σ(G_b)` (`decGraphAt_encGraph`, `instanceVertexCount_encInstance`), the honest
reply is `b` by `gni_honest_reply`, and `wellFormedInstance x = true`, so the verdict is
`[true]` on every coin pair (`HardcoreBit.uprob_eq_one_of_forall`). Soundness: for
`x ∉ L_niso`, either `wellFormedInstance x = false` (verdict `[false]` always) or
`x = encInstance G₀ G₁` with `σ₀(G₀) = G₁` (`encInstance_mem_Lniso_iff`); fix the prover's
coins (`Protocol.exists_proverCoins_le`), split the verifier's tape into `b` and the sampler
bits (`uprob_prod` through the bijection `Fin (1 + c) → Bool ≃ Bool × (Fin c → Bool)`), and
bound `Pr[b' = b] ≤ Pr[b' = b ∧ sampler succeeds] + Pr[fail]`; on success the permutation is
uniform (`statClose_samplePerm`, `StatClose.abs_uprob_sub_le_prod`) and
`uprob_permGraph_eq_of_isomorphic` makes `H` independent of `b`, so the first term is
`≤ 1/2` (`uprob_bool_prod`); the second is `≤ permFailBound n` with
`n = instanceVertices |x|` (`instanceVertices_length_encInstance`). Efficiency:
`gniVerifier_efficient`. -/
theorem gni_interactiveProofErr :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) :=
  GI.gni_interactiveProofErr gniVerifier_efficient

/-- The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso`
[PS10, Proposition 118.4] (Prop-118.4).

**Deviation:** `|x|` iterations (soundness `2^{-|x|}`) plus the sampling term
`|x| · permFailBound n` (D10).

**Proof sketch.** Completeness as in `gni_interactiveProofErr`, iteration by iteration
(the history has exactly `|x|` replies, `exec_length`). Soundness with
`ε N := 2⁻¹ ^ N + N · permFailBound (instanceVertices N) + 2⁻¹ ^ N` (strict clause): fix the
prover's coins, condition on all `|x|` samplers succeeding (union bound `uprob_exists_le`
over the iterations, `statClose_samplePerm` per block via `pushesUniform_coinTable`), and
apply `uprob_gni_rep_cheat` (with `ρ := P'.Coins |x|`, a nonempty tape type) with `g_i := `
the prover's reply after the graphs `H_0, …, H_i` (the prover's `i`-th activation reads
exactly the graphs received so far, `exec_succ`).
Negligibility: `negligible_two_pow_neg`, `negligible_mul_permFailBound`, `Negligible.add`.
Efficiency: `gniVerifierRep_efficient`. -/
theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
  GI.gni_interactiveProof gniVerifierRep_efficient

/-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`
[PS10, Proposition 120.7, corrected: for `L_iso`, not `L_niso`] (Prop-120.7).

**Proof sketch.** Completeness for every witness: for `x = encInstance G₀ G₁`,
`y = encPerm σ` with `σ(G₀) = G₁`, the transcript is `[H, γ]` with `H = encGraph (π(G₀))` and
`γ = encPerm (if b then π σ⁻¹ else π)` (`exec_succ`, `decPerm_encPerm`), and the verdict is
`[true]` by `gi_honest_reply_eq`, `decGraph_encGraph`, `wellFormedInstance` on every coin
pair (`HardcoreBit.uprob_eq_one_of_forall`) — for every value of `π`, so the sampler's
failures are harmless. Completeness of `InteractiveProofErr` is the witness
`encPerm σ` of `Liso`. Soundness: for `x ∉ L_iso` either `x` is malformed (verdict `[false]`)
or `x = encInstance G₀ G₁` with `G₀ ≇ G₁` (`encInstance_mem_Liso_iff`); the verifier's tape is
one bit (`Fin 1 → Bool ≃ Bool`), so after `Protocol.exists_proverCoins_le`,
`uprob_gi_cheat_le_half` with `H r :=` the prover's first message decoded and
`γ b r :=` its reply to `[b]` decoded gives `Pr[accept] ≤ 1/2`, i.e. `1/2 ≤ Pr[out = [false]]`
(`uprob_not`). Efficiency: `giProver_efficient`, `giVerifier_efficient`. -/
theorem gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) :=
  GI.gi_efficientProverProofErr giProver_efficient giVerifier_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
efficient prover with respect to `R_iso` [PS10, Proposition 120.7, repeated] (Prop-120.7,
Lem-120.d).

**Deviation:** `|x|` iterations of four moves each (D8 fixed alternation).

**Proof sketch.** Completeness as in `gi_efficientProverProofErr` for each of the `|x|`
iterations (the verifier's history is `[H_0, γ_0, …]`, `exec_succ`, parity bookkeeping of
`giProverRep`/`giVerifierRep`). Soundness with `ε N := 2⁻¹ ^ N + 2⁻¹ ^ N` (strict clause): fix
the prover's coins; the verifier's tape is the challenge tuple `Fin |x| → Bool` (`List.ofFn`),
and `uprob_gi_rep_cheat_le` with `H_i` the decoded `i`-th graph message and `γ_i` the decoded
`i`-th reply (functions of the earlier challenges through `exec`) gives
`Pr[accept] ≤ 2^{-|x|}`; `negligible_two_pow_neg`. Efficiency: `giProverRep_efficient`,
`giVerifierRep_efficient`. -/
theorem gi_rep_efficientProverProof : EfficientProverProof giProtocolRep Liso Riso :=
  GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso`
[PS10, Proposition 120.7]. -/
theorem gi_rep_interactiveProof : InteractiveProof giProtocolRep Liso :=
  gi_rep_efficientProverProof.toInteractiveProof

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Closeness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge of the graph isomorphism protocol

[PS10, Theorem 122.3]: one iteration of the graph isomorphism protocol
(`giProtocol`, [PS10, Protocol 120.6]) is a zero-knowledge interactive proof for `L_iso` with
the witness relation `R_iso`. The simulator is [PS10, Algorithm 123.4]: guess the challenge
`b'`, send `H = π(G_{b'})`, run `V*` on `H` with fresh coins, and output the view if `V*`'s
challenge is `b'`; [PS10, Lemma 123.5] says that `H` is distributed as `π(G₀)` independently
of `b'` and that each attempt succeeds with probability exactly `1/2`.

The chapter's mathematics is stated first at the *concrete* layer over typed coins (a
cheating verifier is any function `V* : Graph n → ρ → Bool` of the first message and its
coins): the honest-verifier simulator by reindexing (Thm-122.3.hv, proved), Lemma 123.5
(proved), perfect simulation conditioned on success (Claim-123.b, proved by the coin
bijection `(π', b') ↦ π`), and the truncated simulator with `N` attempts, which fails with
probability `2^{-N}` and is otherwise exact (Thm-122.3.trunc). The string-level simulator
`giSim` (Alg-123.4) runs `n` attempts, each with a rejection-sampled permutation, a guessed
bit and a fresh tape for `V*`; its machine form is Claim-123.d and the statistical
zero-knowledge theorem is `gi_statZK` (Thm-122.3). The machine behind Claim-123.d and the
coin-tape bookkeeping behind Thm-122.3 live in the sibling files
`GraphIsomorphismZK/Simulator.lean` and `GraphIsomorphismZK/Closeness.lean` (namespace
`TCSlib.Cryptography.GIZK`), which shadow the definitions of this file with definitionally
equal copies; the targets here are closed by instantiating their results.

**Deviation (D8, D10):** strict PPT simulator truncated at `n` attempts, so the theorem is
*statistical* zero-knowledge with error `2^{-n} + (n + 1) · permFailBound n` (the text claims
perfect zero-knowledge with an expected polynomial-time simulator); only one iteration is
treated (the text defers the `n`-fold protocol to its §7.2.1); the Goldreich abort form
`PerfectZKAbort` holds for the one-attempt simulator at the concrete layer
(`giSimAttempt_perfectAbort`) but is not claimed for `giProtocol` itself, whose honest
prover's rejection-sampled `π` is not exactly uniform.

## Contents

* `GraphIsomorphismZK/Simulator.lean` — the string simulator as a polynomial-time machine
  (Claim-123.d, shadow form `GIZK.exists_simulator`).
* `GraphIsomorphismZK/Closeness.lean` — coin-tape bijections, `N`-fold products of close
  samplers, the real view from `exec`, and the closeness assembly `GIZK.statClose_real_sim`.

## Main definitions

* `TCSlib.Cryptography.giHonestView`, `TCSlib.Cryptography.giHVSim` — the honest verifier's
  view and its simulator by reindexing (Thm-122.3.hv).
* `TCSlib.Cryptography.giRealView`, `TCSlib.Cryptography.giSimAttempt`,
  `TCSlib.Cryptography.giSimTrunc` — the view of a cheating verifier, one attempt of
  [PS10, Algorithm 123.4], and the simulator truncated at `N` attempts (Alg-123.4, typed).
* `TCSlib.Cryptography.giSim`, `TCSlib.Cryptography.giSimCoins` — the string-level simulator
  of [PS10, Algorithm 123.4] and its coin polynomial.

## Main results

* `TCSlib.Cryptography.statClose_giHonestView` — honest-verifier perfect zero-knowledge of one
  iteration by reindexing (Thm-122.3.hv, proved).
* `TCSlib.Cryptography.gi_sim_H_dist`, `TCSlib.Cryptography.gi_sim_half` —
  [PS10, Lemma 123.5] (Lem-123.5, proved).
* `TCSlib.Cryptography.uprob_giSimAttempt_some` — perfect simulation conditioned on success
  (Claim-123.b, proved); `TCSlib.Cryptography.giSimAttempt_perfectAbort` — the abort form.
* `TCSlib.Cryptography.uprob_giSimTrunc_none` (proved),
  `TCSlib.Cryptography.statClose_giSimTrunc` — the truncated simulator (Thm-122.3.trunc).
* `TCSlib.Cryptography.exists_giSimulator` — the simulator is a uniform PPT (Claim-123.d).
* `TCSlib.Cryptography.gi_statZK`, `TCSlib.Cryptography.gi_zk`, `TCSlib.Cryptography.gi_hvzk`
  — [PS10, Theorem 122.3] (Thm-122.3).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, pp. 122–124.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
  Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Honest-verifier zero-knowledge by reindexing (Thm-122.3.hv) -/

/-- The honest verifier's view of one iteration of [PS10, Protocol 120.6] on the prover's
coins `π` and the verifier's coin `b`: `(b, π(G₀), γ)` with `γ = if b then π σ⁻¹ else π`. -/
def giHonestView {n : ℕ} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (w : Equiv.Perm (Fin n) × Bool) :
    Bool × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if w.2 then w.1 * σ⁻¹ else w.1)

/-- The honest-verifier simulator: draw `γ` and `b` uniformly and output `(b, γ(G_b), γ)`
[PS10, Theorem 122.3, honest-verifier case]. -/
def giHVSim {n : ℕ} (G₀ G₁ : Graph n) (w : Equiv.Perm (Fin n) × Bool) :
    Bool × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph (cond w.2 G₁ G₀) w.1, w.1)

/-- The reindexing `(π, b) ↦ (if b then π σ⁻¹ else π, b)` of the prover's coins, a bijection
with inverse `(γ, b) ↦ (if b then γ σ else γ, b)`. -/
def giReindex {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) × Bool ≃ Equiv.Perm (Fin n) × Bool where
  toFun w := (if w.2 then w.1 * σ⁻¹ else w.1, w.2)
  invFun w := (if w.2 then w.1 * σ else w.1, w.2)
  left_inv w := by
    rcases w with ⟨π, b⟩
    cases b <;> simp
  right_inv w := by
    rcases w with ⟨π, b⟩
    cases b <;> simp

/-- The simulator on the reindexed coins is the honest view (`gi_honest_reply_eq`). -/
theorem giHVSim_giReindex {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁)
    (w : Equiv.Perm (Fin n) × Bool) : giHVSim G₀ G₁ (giReindex σ w) = giHonestView G₀ σ w := by
  rcases w with ⟨π, b⟩
  cases b <;> simp [giHVSim, giHonestView, giReindex, permGraph_mul_inv_of_eq hσ]

/-- Honest-verifier perfect zero-knowledge of one iteration of the graph isomorphism
protocol [PS10, Theorem 122.3, honest verifier] (Thm-122.3.hv): for `σ(G₀) = G₁` the honest
view and the simulator's output have the same law, since the honest view is the simulator
composed with the bijection `giReindex σ` (`uprob_comp_equiv`). -/
theorem uprob_giHonestView_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (T : Bool × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun w : Equiv.Perm (Fin n) × Bool => T (giHonestView G₀ σ w)) =
      uprob (fun w : Equiv.Perm (Fin n) × Bool => T (giHVSim G₀ G₁ w)) := by
  rw [← uprob_comp_equiv (giReindex σ) (fun w => T (giHVSim G₀ G₁ w))]
  congr 1
  funext w
  rw [giHVSim_giReindex hσ]

/-- The honest view is statistically `0`-close to the honest-verifier simulator
(Thm-122.3.hv in the `StatClose` form consumed by `StatZK`). -/
theorem statClose_giHonestView {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) : StatClose (giHonestView G₀ σ) (giHVSim G₀ G₁) 0 := fun T => by
  rw [uprob_giHonestView_eq hσ T, sub_self, abs_zero]

/-! ### Lemma 123.5 -/

/-- The coin bijection `(b, (π, r)) ↦ ((π, b), r)` between the simulator's coin layouts. -/
private def coinAssoc (α β γ : Type*) : α × (β × γ) ≃ (β × α) × γ where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- [PS10, Lemma 123.5], first half (exact, uniform permutation): in the simulator the graph
`H = π(G_{b'})` has the law of `π(G₀)`, independently of the guessed bit `b'`.

**Proof.** Condition on `b'` (`uprob_bool_prod` after swapping the coordinates); for `b' = 1`
the law of `π(G₁)` is that of `π(G₀)` by `uprob_permGraph_eq_of_isomorphic'` (Lem-119.a). -/
theorem gi_sim_H_dist {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁)
    (p : Graph n → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × Bool => p (permGraph (cond z.2 G₁ G₀) z.1)) =
      uprob (fun π : Equiv.Perm (Fin n) => p (permGraph G₀ π)) := by
  rw [← uprob_comp_equiv (Equiv.prodComm Bool (Equiv.Perm (Fin n))), uprob_bool_prod]
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic' hσ p]
  ring

/-- [PS10, Lemma 123.5], second half: for every cheating verifier `V*` (any function of the
graph `H` and of its coins `r`), the guessed bit equals `V*`'s challenge with probability
exactly `1/2`.

**Deviation:** `ρ` is assumed nonempty (for `ρ` empty every `uprob` is `0`; the frozen
statement omits the hypothesis).

**Proof.** Condition on `b'` (`uprob_bool_prod`); for `b' = 1` replace `π(G₁)` by `π(G₀)`
(`uprob_permGraph_eq_of_isomorphic`); the two conditional probabilities are those of an
event and of its complement (`uprob_not`), so they sum to `1`. -/
theorem gi_sim_half {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] (G₀ G₁ : Graph n)
    (σ : Equiv.Perm (Fin n)) (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun z : (Equiv.Perm (Fin n) × Bool) × ρ =>
      V (permGraph (cond z.1.2 G₁ G₀) z.1.1) z.2 = z.1.2) = 1 / 2 := by
  rw [← uprob_comp_equiv (coinAssoc Bool (Equiv.Perm (Fin n)) ρ), uprob_bool_prod]
  simp only [coinAssoc, Equiv.coe_fn_mk, cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic hσ (fun H r => V H r = true)]
  have h : uprob (fun w : Equiv.Perm (Fin n) × ρ => V (permGraph G₀ w.1) w.2 = false) =
      uprob (fun w : Equiv.Perm (Fin n) × ρ => ¬ V (permGraph G₀ w.1) w.2 = true) := by
    congr 1
    funext w
    simp
  rw [h, uprob_not]
  ring

/-! ### One attempt of the simulator and perfect simulation given success -/

/-- The view of a cheating verifier `V*` in one real iteration of [PS10, Protocol 120.6] on
the prover's coins `π` and `V*`'s coins `r`: `(r, H, γ)` with `H = π(G₀)`, `b = V*(H, r)` and
`γ = if b then π σ⁻¹ else π`. -/
def giRealView {n : ℕ} {ρ : Type*} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (V : Graph n → ρ → Bool)
    (w : Equiv.Perm (Fin n) × ρ) : ρ × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if V (permGraph G₀ w.1) w.2 then w.1 * σ⁻¹ else w.1)

/-- One attempt of the simulator [PS10, Algorithm 123.4] on the coins `((π', b'), r)`: send
`H = π'(G_{b'})`, run `V*` on `H` with coins `r`, and output the view `(r, H, π')` if `V*`'s
challenge is `b'`, `none` otherwise (Alg-123.4, typed). -/
def giSimAttempt {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  if V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 then
    some (c.2, permGraph (cond c.1.2 G₁ G₀) c.1.1, c.1.1)
  else none

/-- An attempt fails exactly when `V*`'s challenge differs from the guessed bit. -/
theorem giSimAttempt_eq_none_iff {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) :
    giSimAttempt G₀ G₁ V c = none ↔ ¬ V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 := by
  unfold giSimAttempt
  split_ifs with h <;> simp [h]

/-- One attempt fails with probability exactly `1/2` [PS10, Lemma 123.5] (`gi_sim_half`,
`uprob_not`). -/
theorem uprob_giSimAttempt_none {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c = none) = 1 / 2 := by
  rw [OneWay.uprob_congr (giSimAttempt_eq_none_iff G₀ G₁ V), uprob_not, gi_sim_half G₀ G₁ σ hσ V]
  norm_num

/-- The coin bijection of Claim-123.b: `((π, b'), r) ↦ ((if b' then π σ⁻¹ else π, b'), r)`,
mapping the prover's coins to the simulator's coins (inverse: multiply by `σ`). -/
private def simReindex {n : ℕ} (ρ : Type*) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm (Fin n) × Bool) × ρ ≃ (Equiv.Perm (Fin n) × Bool) × ρ where
  toFun c := ((if c.1.2 then c.1.1 * σ⁻¹ else c.1.1, c.1.2), c.2)
  invFun c := ((if c.1.2 then c.1.1 * σ else c.1.1, c.1.2), c.2)
  left_inv c := by
    rcases c with ⟨⟨π, b⟩, r⟩
    cases b <;> simp
  right_inv c := by
    rcases c with ⟨⟨π, b⟩, r⟩
    cases b <;> simp

/-- Splitting an event along a second event: `Pr[p ∧ q] + Pr[¬p ∧ q] = Pr[q]`. -/
private theorem uprob_and_add_uprob_not_and {α : Type*} [Fintype α] (p q : α → Prop) :
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

/-- Perfect simulation conditioned on success [PS10, proof of Theorem 122.3, "since `H` is
independent from `b'`, this does not change the output distribution"] (Claim-123.b): for
every test set `T` of views, the probability that an attempt succeeds with a view in `T` is
exactly half the probability that the real view of `V*` lies in `T`.

**Proof sketch.** Reindex the attempt's coins by `simReindex`: on `((π, b'), r)` the attempt sends
`H = π(G₀)` in both cases (`permGraph_mul_inv_of_eq`), succeeds iff `V*(π(G₀), r) = b'`, and
then outputs exactly `giRealView (π, r)`. Condition on `b'` (`uprob_bool_prod`) and add the
two halves (`uprob_and_add_uprob_not_and`). -/
theorem uprob_giSimAttempt_some {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (T : ρ × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => ∃ v, giSimAttempt G₀ G₁ V c = some v ∧ T v) =
      1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (giRealView G₀ σ V w)) := by
  rw [← uprob_comp_equiv (simReindex ρ σ)]
  have key : ∀ c : (Equiv.Perm (Fin n) × Bool) × ρ,
      (∃ v, giSimAttempt G₀ G₁ V (simReindex ρ σ c) = some v ∧ T v) ↔
        (V (permGraph G₀ c.1.1) c.2 = c.1.2 ∧ T (giRealView G₀ σ V (c.1.1, c.2))) := by
    rintro ⟨⟨π, b⟩, r⟩
    cases b <;> cases hV : V (permGraph G₀ π) r <;>
      simp [simReindex, giSimAttempt, giRealView, hV, permGraph_mul_inv_of_eq hσ]
  rw [OneWay.uprob_congr key, ← uprob_comp_equiv (coinAssoc Bool (Equiv.Perm (Fin n)) ρ),
    uprob_bool_prod]
  simp only [coinAssoc, Equiv.coe_fn_mk]
  have h := uprob_and_add_uprob_not_and (fun w : Equiv.Perm (Fin n) × ρ => V (permGraph G₀ w.1) w.2 = true)
    (fun w => T (giRealView G₀ σ V w))
  have hf : uprob (fun w : Equiv.Perm (Fin n) × ρ =>
      V (permGraph G₀ w.1) w.2 = false ∧ T (giRealView G₀ σ V (w.1, w.2))) =
      uprob (fun w : Equiv.Perm (Fin n) × ρ => ¬ V (permGraph G₀ w.1) w.2 = true ∧ T (giRealView G₀ σ V w)) := by
    congr 1
    funext w
    simp
  rw [hf]
  linarith

/-- The abort form of perfect zero-knowledge for one attempt of the simulator
[Goldreich, Definition 4.3.1; PS10, Algorithm 123.4] (Claim-123.b, `PerfectZKAbort` shape at
the concrete layer): the attempt aborts with probability at most `1/2`, and for every test
set `T`, `Pr[T(view)] · Pr[attempt ≠ ⊥] = Pr[attempt ≠ ⊥ ∧ T(attempt)]`. -/
theorem giSimAttempt_perfectAbort {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (T : ρ × Graph n × Equiv.Perm (Fin n) → Prop) :
    uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c = none) ≤ 1 / 2 ∧
    uprob (fun w : Equiv.Perm (Fin n) × ρ => T (giRealView G₀ σ V w)) *
        uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V c ≠ none) =
      uprob (fun c : (Equiv.Perm (Fin n) × Bool) × ρ =>
        ∃ v, giSimAttempt G₀ G₁ V c = some v ∧ T v) := by
  refine ⟨(uprob_giSimAttempt_none hσ V).le, ?_⟩
  rw [uprob_not, uprob_giSimAttempt_none hσ V, uprob_giSimAttempt_some hσ V T]
  ring

/-! ### The truncated simulator (Thm-122.3.trunc) -/

/-- The simulator truncated at `N` attempts with independent coins: the output of the first
successful attempt, `none` (`⊥`) if all `N` fail (Alg-123.4, typed; the strict-PPT
truncation of D8). -/
def giSimTrunc {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  (List.finRange N).findSome? fun t => giSimAttempt G₀ G₁ V (c t)

/-- The truncated simulator fails exactly when every attempt fails. -/
theorem giSimTrunc_eq_none_iff {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) :
    giSimTrunc G₀ G₁ V N c = none ↔ ∀ t, giSimAttempt G₀ G₁ V (c t) = none := by
  unfold giSimTrunc
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The truncated simulator outputs `⊥` with probability exactly `2^{-N}`
[PS10, proof of Theorem 122.3, "`S` has probability `1/2` of succeeding in each trial"]
(Thm-122.3.trunc, failure probability): the attempts use disjoint coins
(`OneWay.uprob_pi_forall`) and each fails with probability `1/2`
(`uprob_giSimAttempt_none`). -/
theorem uprob_giSimTrunc_none {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ) :
    uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => giSimTrunc G₀ G₁ V N c = none) =
      (2 : ℝ)⁻¹ ^ N := by
  rw [OneWay.uprob_congr (giSimTrunc_eq_none_iff G₀ G₁ V N),
    OneWay.uprob_pi_forall (ι := Fin N) (fun c => giSimAttempt G₀ G₁ V c = none),
    uprob_giSimAttempt_none hσ V, Fintype.card_fin]
  norm_num

/-- With one more attempt whose first attempt succeeds, the truncated simulator outputs that
attempt's view (`List.finRange_succ`, `List.findSome?_cons_of_isSome`). -/
private theorem giSimTrunc_cons_of_some {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (N : ℕ) {a : (Equiv.Perm (Fin n) × Bool) × ρ} (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
    {v : ρ × Graph n × Equiv.Perm (Fin n)} (ha : giSimAttempt G₀ G₁ V a = some v) :
    giSimTrunc G₀ G₁ V (N + 1) (Fin.cons a c) = some v := by
  unfold giSimTrunc
  rw [List.finRange_succ, List.findSome?_cons_of_isSome]
  · simp [ha]
  · simp [ha]

/-- With one more attempt whose first attempt fails, the truncated simulator is the truncated
simulator on the remaining attempts (`List.findSome?_cons_of_isNone`, `List.findSome?_map`). -/
private theorem giSimTrunc_cons_of_none {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (N : ℕ) {a : (Equiv.Perm (Fin n) × Bool) × ρ} (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
    (ha : giSimAttempt G₀ G₁ V a = none) :
    giSimTrunc G₀ G₁ V (N + 1) (Fin.cons a c) = giSimTrunc G₀ G₁ V N c := by
  unfold giSimTrunc
  rw [List.finRange_succ, List.findSome?_cons_of_isNone, List.findSome?_map]
  · simp only [Function.comp_def, Fin.cons_succ]
  · simp [ha]

/-- Independent coordinates: `Pr[A(z.1) ∧ B(z.2)] = Pr[A] · Pr[B]` on a product
(`uprob_prod`, `OneWay.uexp_indicator`). -/
private theorem uprob_prod_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop) :
    uprob (fun z : α × β => A z.1 ∧ B z.2) = uprob A * uprob B := by
  classical
  rw [uprob_prod, mul_comm, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases ha : A a
  · simp [ha]
  · simp [ha, uprob_false]

/-- One step of the recursion for the law of the truncated simulator: with one more attempt,
`Pr[T(S_{N+1})] = 1/2 · Pr[T(S_N)] + 1/2 · Pr[T(some view)]`.

**Proof sketch.** Split the coins of the `N + 1` attempts as (first attempt, remaining
attempts) by `Fin.consEquiv` (`uprob_comp_equiv`) and the event along "the first attempt
fails" (`uprob_and_add_uprob_not_and`): when it fails, `S_{N+1}` is `S_N` on the remaining
coins (`giSimTrunc_cons_of_none`), and the two factors are independent
(`uprob_prod_and`, `uprob_giSimAttempt_none`); when it succeeds the output is its view
(`giSimTrunc_cons_of_some`), an event of the first coordinate alone (`uprob_fst`) of
probability `1/2 · Pr[T(some view)]` (`uprob_giSimAttempt_some`). -/
private theorem uprob_giSimTrunc_succ {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ)
    (T : Option (ρ × Graph n × Equiv.Perm (Fin n)) → Prop) :
    uprob (fun c : Fin (N + 1) → (Equiv.Perm (Fin n) × Bool) × ρ =>
        T (giSimTrunc G₀ G₁ V (N + 1) c)) =
      1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) +
        1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) := by
  rw [← uprob_comp_equiv (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ)]
  have hsplit := uprob_and_add_uprob_not_and
    (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      giSimAttempt G₀ G₁ V z.1 = none)
    (fun z => T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z)))
  have hA : uprob (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      giSimAttempt G₀ G₁ V z.1 = none ∧
        T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z))) =
      1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) := by
    rw [← uprob_giSimAttempt_none hσ V,
      ← uprob_prod_and (fun a : (Equiv.Perm (Fin n) × Bool) × ρ => giSimAttempt G₀ G₁ V a = none)
        (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c))]
    refine OneWay.uprob_congr fun z => and_congr_right fun hz => ?_
    rw [show (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ) z = Fin.cons z.1 z.2 from rfl,
      giSimTrunc_cons_of_none G₀ G₁ V N z.2 hz]
  have hB : uprob (fun z : ((Equiv.Perm (Fin n) × Bool) × ρ) × (Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) =>
      ¬ giSimAttempt G₀ G₁ V z.1 = none ∧
        T (giSimTrunc G₀ G₁ V (N + 1) ((Fin.consEquiv fun _ => _) z))) =
      1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) := by
    rw [← uprob_giSimAttempt_some hσ V (fun v => T (some v)),
      ← uprob_fst (β := Fin N → (Equiv.Perm (Fin n) × Bool) × ρ)
        (fun a : (Equiv.Perm (Fin n) × Bool) × ρ => ∃ v, giSimAttempt G₀ G₁ V a = some v ∧ T (some v))]
    refine OneWay.uprob_congr fun z => ?_
    rw [show (Fin.consEquiv fun _ => (Equiv.Perm (Fin n) × Bool) × ρ) z = Fin.cons z.1 z.2 from rfl]
    constructor
    · rintro ⟨hne, hT⟩
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      exact ⟨v, hv, by rwa [giSimTrunc_cons_of_some G₀ G₁ V N z.2 hv] at hT⟩
    · rintro ⟨v, hv, hT⟩
      exact ⟨by simp [hv], by rwa [giSimTrunc_cons_of_some G₀ G₁ V N z.2 hv]⟩
  rw [← hsplit, hA, hB]

/-- The distance between the law of the truncated simulator and the law of the real view
halves with every attempt: `|Pr[T(S_N)] - Pr[T(some view)]| ≤ 2^{-N}`.

**Proof sketch.** Induction on `N`. For `N = 0` the simulator outputs `none`
(`List.finRange_zero`) and both probabilities lie in `[0, 1]`. The step is
`uprob_giSimTrunc_succ`: `Pr[T(S_{N+1})] - p = 1/2 (Pr[T(S_N)] - p)`. -/
private theorem abs_uprob_giSimTrunc_sub_le {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool)
    (N : ℕ) (T : Option (ρ × Graph n × Equiv.Perm (Fin n)) → Prop) :
    |uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
      uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))| ≤ (2 : ℝ)⁻¹ ^ N := by
  induction N with
  | zero =>
    have h0 : ∀ c : Fin 0 → (Equiv.Perm (Fin n) × Bool) × ρ, giSimTrunc G₀ G₁ V 0 c = none :=
      fun c => by simp [giSimTrunc]
    have hp0 := uprob_nonneg fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))
    have hp1 := uprob_le_one fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))
    simp only [h0, pow_zero]
    by_cases hT : T none
    · simp only [hT, uprob_true]
      rw [abs_le]
      constructor <;> linarith
    · simp only [hT, uprob_false]
      rw [abs_le]
      constructor <;> linarith
  | succ N ih =>
    rw [uprob_giSimTrunc_succ hσ V N T]
    have h : 1 / 2 * uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) +
        1 / 2 * uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) -
        uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w))) =
        1 / 2 * (uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
          uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))) := by ring
    rw [h, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), pow_succ]
    calc 1 / 2 * |uprob (fun c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ => T (giSimTrunc G₀ G₁ V N c)) -
          uprob (fun w : Equiv.Perm (Fin n) × ρ => T (some (giRealView G₀ σ V w)))|
        ≤ 1 / 2 * (2 : ℝ)⁻¹ ^ N := by gcongr
      _ = (2 : ℝ)⁻¹ ^ N * 2⁻¹ := by ring

/-- The truncated simulator is statistically `2^{-N}`-close to the real view
[PS10, Theorem 122.3, truncated form] (Thm-122.3.trunc): for every test set `T` of optional
views, `|Pr[T(S_N)] - Pr[T(some view)]| ≤ 2^{-N}`.

**Proof sketch.** Decompose the event `T(S_N)` by the index of the first successful attempt
(`List.findSome?` on `List.finRange N`: `giSimTrunc = some v` iff some `t` has
`giSimAttempt (c t) = some v` and all earlier attempts fail): the attempts have disjoint
coins, so by `uprob_prod` / `OneWay.uprob_update` the `t`-th term is
`(1/2)^t · Pr[∃ v, attempt = some v ∧ T (some v)] = (1/2)^{t+1} · Pr[T (some view)]`
(`uprob_giSimAttempt_some`, `uprob_giSimAttempt_none`); summing the geometric series,
`Pr[T(S_N)] = (1 - 2^{-N}) Pr[T (some view)] + 2^{-N} [T none]`
(`uprob_giSimTrunc_none`), whose distance from `Pr[T (some view)]` is at most `2^{-N}`. -/
theorem statClose_giSimTrunc {n : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ = G₁) (V : Graph n → ρ → Bool) (N : ℕ) :
    StatClose (giSimTrunc G₀ G₁ V N)
      (fun w : Equiv.Perm (Fin n) × ρ => some (giRealView G₀ σ V w)) ((2 : ℝ)⁻¹ ^ N) :=
  fun T => abs_uprob_giSimTrunc_sub_le hσ V N T

/-! ### The string-level simulator [PS10, Algorithm 123.4] (Alg-123.4, Claim-123.d) -/

/-- The length of the coin block of one attempt of the string simulator against `V'` at
instance length `N`: one guessed bit, `(N + 1)²` permutation-sampling bits, and `V'`'s tape. -/
def giSimBlockLen (V' : Strategy) (N : ℕ) : ℕ := 1 + (N + 1) ^ 2 + V'.coinLen N

/-- The coin polynomial of the string simulator: `|x|` blocks (at most `|x|` attempts are
made, the actual number being the vertex count `n ≤ |x|`). -/
def giSimCoins (V' : Strategy) : PolyExpr :=
  .mul .var (.add (.add (.const 1) (.normal 1 2)) V'.coins)

/-- The coin polynomial evaluates to `|x|` blocks of `giSimBlockLen V' |x|` bits. -/
theorem giSimCoins_eval (V' : Strategy) (N : ℕ) : (giSimCoins V').eval N = N * giSimBlockLen V' N := by
  simp [giSimCoins, giSimBlockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- One attempt of the string simulator [PS10, Algorithm 123.4] on `(x, z)` with the coin
block `c = b' :: (permutation coins ++ V'`'s tape)`: `H := π(G_{b'})` for `π := samplePerm n`,
`b :=` the bit of `V'.next x z rV [H]`, and the encoded view `⟨⟨x, z⟩, ⟨rV, [H, encPerm π]⟩⟩`
if `b = b'`, `none` otherwise. -/
noncomputable def giSimAttemptStr (V' : Strategy) (x z c : List Bool) : Option (List Bool) :=
  let n := instanceVertexCount x
  let b' := c.headD false
  let π := samplePerm n ((c.drop 1).take ((x.length + 1) ^ 2))
  let rV := c.drop (1 + (x.length + 1) ^ 2)
  let H := encGraph (permGraph (if b' then instanceG₁ x else instanceG₀ x) π)
  if (V'.next x z rV [H]).headD false = b' then some (View.encode ⟨x, z, rV, [H, encPerm π]⟩)
  else none

/-- The string simulator [PS10, Algorithm 123.4] (Alg-123.4): up to `n = instanceVertexCount x`
attempts on the consecutive coin blocks of the tape `r`; the first successful attempt's view,
or `⊥ = []` after `n` failures.

**Deviation (D8):** truncated at `n` attempts (strict PPT) instead of restarting until
success. -/
noncomputable def giSim (V' : Strategy) (x z r : List Bool) : List Bool :=
  ((List.range (instanceVertexCount x)).findSome? fun t =>
    giSimAttemptStr V' x z (coinSlice (giSimBlockLen V' x.length) t r)).getD []

/-- The string simulator is a uniform PPT [PS10, proof of Theorem 122.3, "`S` runs in
(expected) polynomial time"] (Claim-123.d): for every efficient `V'` there is a uniform
`NUPPT` with coin polynomial `giSimCoins V'` whose activation on `⟨x, z⟩` at parameter `|x|`
is `giSim V' x z r`.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with `V'.next x z rV [H] =
A.runAtL |x| ⟨⟨x, z⟩, encodeMsgs [H]⟩ rV` (`Strategy.ofNUPPT_next`), polynomial-time by
`A.polyTimeComputable_output` and the pairing calculus. One attempt on the raw layout is
polynomial-time: the block is cut by `polyTimeComputable_pairTakePoly`/`pairDropPoly` with
the unary block length (`polyTimeComputable_unaryPoly`), `encPerm π` by
`polyTimeComputable_encSamplePerm`-style sampling, `H` by `polyTimeComputable_encPermGraph`,
the comparison by `polyTimeComputable_pairEq`, the view by `PolyTimeComputable.pairEncode`.
The loop over `t < n` is `Complexity.polyTimeComputable_iterateFind` with the attempt index in
the state and the accepting test "the attempt succeeded" (`R := var`, `P :=` the layout
length); the result is packaged by `NUPPT.ofPolyTimeUniform` with coins `giSimCoins V'`
(`NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.ofPolyTimeUniform_uniform`). -/
theorem exists_giSimulator (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = giSimCoins V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = giSim V' x z (List.ofFn r) :=
  GIZK.exists_simulator V' hV'

/-! ### Theorem 122.3 -/

/-- [PS10, Theorem 122.3], one iteration, statistical form (D8): the graph isomorphism
protocol is statistical zero-knowledge for `R_iso` with a negligible error.

**Deviation (D8, D10):** statistical instead of perfect zero-knowledge (strict PPT simulator
truncated at `n` attempts; rejection-sampled permutations); one iteration (the text's
`n`-fold protocol relies on its §7.2.1).

**Proof sketch.** Take `δ N := 2⁻¹ ^ instanceVertices N + (instanceVertices N + 1) ·
permFailBound (instanceVertices N)`, negligible by `negligible_two_pow_neg_sqrt_div` (with
`instanceVertices N ≥ √(N / 4)` for `N ≥ 8`), `negligible_mul_permFailBound` and
`Negligible.add`. For an efficient `V'` take the simulator of `exists_giSimulator`. For
`Riso x y`, i.e. `x = encInstance G₀ G₁`, `y = encPerm σ`, `σ(G₀) = G₁`, let
`V* H r := (V'.next x z r [encGraph H]).headD false` on `ρ := V'.Coins |x|` (nonempty) and
`enc (r, H, γ) := View.encode ⟨x, z, List.ofFn r, [encGraph H, encPerm γ]⟩`. The real view
`((giProtocol.withV V').viewV x y z (r₁, r₂)).encode` is `enc (giRealView G₀ σ V* (π, r₂))`
with `π = samplePerm n (List.ofFn r₁)` (`exec_succ` three times, `decPerm_encPerm`,
`decGraph_encGraph`), and `giSim V' x z (List.ofFn r)` is `(Option.map enc (giSimTrunc G₀ G₁
V* n c)).getD []` with the `t`-th attempt's coins `c t = ((samplePerm n …, b'_t), rV_t)` read
from the `t`-th block (`giSimCoins_eval`, `coinSlice`). Chain of `StatClose` steps:
(1) real view with sampled `π` ≈ real view with uniform `π` within `permFailBound n`
(`statClose_samplePerm`, `StatClose.prod` with `StatClose.refl` for `r₂`, `StatClose.map`);
(2) `statClose_giSimTrunc` within `2^{-n}`, mapped by `v ↦ (Option.map enc v).getD []`
(`StatClose.map`); (3) the simulator with uniform `π'_t` ≈ with sampled `π'_t` within
`n · permFailBound n` (`StatClose.prod` iterated over the `n` blocks, `StatClose.map`);
`StatClose.trans`, `StatClose.symm`, `StatClose.mono` with
`instanceVertices_length_encInstance`. -/
theorem gi_statZK : ∃ δ : ℕ → ℝ, Negligible δ ∧ StatZK giProtocol Riso δ := by
  refine ⟨fun N => (2 : ℝ)⁻¹ ^ instanceVertices N +
    ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N), GIZK.negligible_delta, ?_⟩
  intro V' hV'
  obtain ⟨S, hS, hc, hsim⟩ := exists_giSimulator V' hV'
  refine ⟨S, hS, ?_⟩
  rintro x y z ⟨n, G₀, G₁, σ, hx, hy, hσ⟩
  rw [show x = encInstance G₀ G₁ from hx, hy]
  have hm : S.coinLen (encInstance G₀ G₁).length =
      (encInstance G₀ G₁).length * GIZK.blockLen V' (encInstance G₀ G₁).length := by
    rw [NUPPT.coinLen, hc, giSimCoins_eval]
    rfl
  have key := GIZK.statClose_real_sim V' G₀ G₁ σ z
    (statClose_giSimTrunc hσ (GIZK.vstar V' (encInstance G₀ G₁) z) n) _ hm
  have hsim' : S.simulate (encInstance G₀ G₁) z =
      fun r => giSim V' (encInstance G₀ G₁) z (List.ofFn r) :=
    funext (hsim _ z)
  dsimp only
  rw [hsim', instanceVertices_length_encInstance]
  exact key

/-- [PS10, Theorem 122.3]: the graph isomorphism protocol is zero-knowledge for `R_iso`
(`StatZK.zk`). -/
theorem gi_zk : ZK giProtocol Riso := by
  obtain ⟨δ, hδ, h⟩ := gi_statZK
  exact h.zk hδ

/-- [PS10, Theorem 122.3, honest verifier]: the graph isomorphism protocol is honest-verifier
zero-knowledge for `R_iso` (`StatZK.hvzk` with `giVerifier_efficient`). -/
theorem gi_hvzk : HVZK giProtocol Riso := by
  obtain ⟨δ, hδ, h⟩ := gi_statZK
  exact h.hvzk hδ giVerifier_efficient

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: shadow copies of the concrete repetition lemmas

Shadow copies (namespace `TCSlib.Cryptography.GI`, for the proofs of the `|x|`-fold protocols
in `GraphIsomorphism/SoundnessRep.lean`) of the concrete probability lemmas of the main file
`ZeroKnowledge/GraphIsomorphism.lean` that are stated with the main file's definitions
`prefixLT`, `prefixLE` and `Isomorphic`: the adaptive guessing lemma (Lem-119.c), the `n`-fold
soundness of the graph non-isomorphism protocol against adaptive provers (Lem-119.b), the
`m`-fold soundness of the graph isomorphism protocol (Lem-120.d), and the negligibility of the
sampling term (Inf-4.4). The statements and proofs are those of the main file verbatim (with
`GI.prefixLT`, `GI.prefixLE`, `GI.Isomorphic`, `GI.permFailBound`, `GI.instanceVertices`, all
definitionally equal to the originals); the main file cannot be imported here, and its
proofs cannot be moved out without moving the public statements.

## Main definitions

* `TCSlib.Cryptography.GI.prefixLT`, `GI.prefixLE` — shadows of the prefix maps of a bit tuple.

## Main results

* `TCSlib.Cryptography.GI.uprob_adaptive_guess` — the adaptive guessing lemma `2^{-m}`
  (Lem-119.c).
* `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` — `m`-fold GI soundness (Lem-120.d).
* `TCSlib.Cryptography.GI.uprob_gni_rep_cheat` — `n`-fold GNI soundness (Lem-119.b).
* `TCSlib.Cryptography.GI.negligible_mul_permFailBound` — the sampling term is negligible.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-- The sampling error of the repeated protocols, `|x| · permFailBound n` with
`n = instanceVertices |x|`, is negligible in `|x|` (Inf-4.4): for `N ≥ 8`,
`√(N/4) ≤ instanceVertices N ≤ N`, so the term is at most `N² · 2^{-√(N/4)}`
(`negligible_two_pow_neg_sqrt_div`, `Negligible.mul_pow`, `Negligible.mono`).

**Repair (run-3 audit P2-1):** proved (the run-2 sketch went through `permFailBound_le_exp`,
removed). -/
theorem negligible_mul_permFailBound :
    Negligible fun N : ℕ => (N : ℝ) * permFailBound (instanceVertices N) := by
  refine ((negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mul_pow 2).mono
    ⟨8, fun N hN => ?_⟩
  have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
  have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
  have hpow : (2 : ℝ)⁻¹ ^ instanceVertices N ≤ (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have hv' : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
  unfold permFailBound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (N : ℝ) * (instanceVertices N * (2 : ℝ)⁻¹ ^ instanceVertices N)
      ≤ N * (N * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4)) := by gcongr
    _ = (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) := by ring

/-- The strict prefix `b_0, …, b_{i-1}` of a bit tuple (the history an adaptive prover has
seen before challenge `i`). -/
def prefixLT {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin i → α :=
  fun j => b (Fin.castLE i.isLt.le j)

/-- The prefix `b_0, …, b_i` of a tuple (the history including the current challenge). -/
def prefixLE {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin (i + 1) → α :=
  fun j => b (Fin.castLE i.isLt j)

/-- The adaptive guess map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` of Lem-119.c: triangular with
identity diagonal, hence a bijection of `Fin m → Bool` for every `w` (`adaptiveXorEquiv`); it
carries the event "`b_i = g_i(b_{<i}, w)` for every `i`" to "`b = 0`". -/
private def adaptiveXor {m : ℕ} {W : Type*} (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W)
    (b : Fin m → Bool) : Fin m → Bool :=
  fun i => xor (b i) (g i (prefixLT b i) w)

/-- `adaptiveXor g w` is injective.

**Proof sketch.** If the images agree then `b_i = b'_i` for every `i`, by induction on a bound
`k > i`: the prefixes `b_{<i}`, `b'_{<i}` agree by the induction hypothesis, so the guesses
`g_i(b_{<i}, w)`, `g_i(b'_{<i}, w)` agree and `xor` cancels (`Bool.xor_left_inj`). -/
private theorem adaptiveXor_injective {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) :
    Function.Injective (adaptiveXor g w) := by
  intro b b' h
  have key : ∀ k, ∀ i : Fin m, i.val < k → b i = b' i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hpre : prefixLT b i = prefixLT b' i := by
          funext j
          have hj := j.isLt
          exact ih _ (by simp only [Fin.coe_castLE]; omega)
        have hi' := congrFun h i
        simp only [adaptiveXor, hpre] at hi'
        exact Bool.xor_left_inj.mp hi'
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The bijection `adaptiveXor g w` of `Fin m → Bool` (an injection of a finite type into
itself, `Finite.injective_iff_bijective`). -/
private noncomputable def adaptiveXorEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.ofBijective (adaptiveXor g w)
    (Finite.injective_iff_bijective.mp (adaptiveXor_injective g w))

/-- The coin bijection `(b, w) ↦ (adaptiveXor g w b, w)` of `(Fin m → Bool) × W`. -/
private noncomputable def adaptiveEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) : (Fin m → Bool) × W ≃ (Fin m → Bool) × W where
  toFun z := (adaptiveXorEquiv g z.2 z.1, z.2)
  invFun z := ((adaptiveXorEquiv g z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The adaptive guessing lemma [PS10, proof of Proposition 118.4, "each iteration is
independent of all prior iterations"] (Lem-119.c): for every finite nonempty `W` and every
family of guesses `g i` depending on the earlier bits and on `w`, the probability that a
uniform tuple `b` satisfies `b_i = g_i(b_{<i}, w)` for every `i` is exactly `2^{-m}`. The
engine of every `2^{-n}` soundness bound against adaptive provers.

**Deviation:** `W` nonempty (`uprob` on an empty type is `0`, so the equality fails for
`W = Empty`; every consumer uses a tape type `Fin k → Bool`).

**Repair (run-3 audit P10-1):** hypothesis `[Nonempty W]` added (the run-2 statement
specialised to `W := Empty`, `m := 0` reads `0 = 1`).

**Proof sketch.** For each `w` the map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` is a bijection of
`Fin m → Bool` (`adaptiveXorEquiv`: triangular with identity diagonal, injective by strong
induction on `i`, hence bijective on a finite type) carrying the event to `{b = 0}`; so
`uprob_comp_equiv` with the coin bijection `adaptiveEquiv`, `uprob_fst` (here `W ≠ ∅` is
used) and `OneWay.uprob_eq_one_div_card` give `1 / 2^m` (`Fintype.card_fun`). Equivalently,
exactly one `b` per `w` satisfies all the constraints (`|W|` elements out of `2^m |W|`). -/
theorem uprob_adaptive_guess (m : ℕ) {W : Type*} [Fintype W] [Nonempty W]
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) :
    uprob (fun z : (Fin m → Bool) × W => ∀ i, z.1 i = g i (prefixLT z.1 i) z.2) =
      (2 : ℝ)⁻¹ ^ m := by
  have hev : ∀ z : (Fin m → Bool) × W,
      (∀ i, z.1 i = g i (prefixLT z.1 i) z.2) ↔ (adaptiveEquiv g z).1 = fun _ => false := by
    intro z
    simp only [adaptiveEquiv, adaptiveXorEquiv, Equiv.coe_fn_mk, Equiv.ofBijective_apply,
      adaptiveXor, funext_iff]
    exact forall_congr' fun i => by cases z.1 i <;> cases g i (prefixLT z.1 i) z.2 <;> simp
  rw [OneWay.uprob_congr hev,
    uprob_comp_equiv (adaptiveEquiv g) (fun z : (Fin m → Bool) × W => z.1 = fun _ => false),
    uprob_fst (β := W) (fun b : Fin m → Bool => b = fun _ => false),
    OneWay.uprob_eq_one_div_card (fun _ : Fin m => false), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow]

/-- Soundness of the `m`-fold graph isomorphism protocol against adaptive provers
[PS10, Proposition 120.7, "repeated … to drive the error as low as desired"] (Lem-120.d):
if `G₀ ≇ G₁` then for a prover whose `i`-th graph `H_i` depends on the earlier challenges and
its coins and whose `i`-th reply `γ_i` also depends on the current challenge, the verifier
accepts all `m` iterations with probability at most `2^{-m}`.

**Proof sketch.** For empty `ρ` the probability is `0`. Otherwise acceptance in iteration `i` forces
`b_i = g_i(b_{<i}, r)` for the guess `g_i := decide (G₁ ≅ H_i)` (`not_isomorphic_both`), so
`uprob_mono` reduces to `uprob_adaptive_guess`.

**Repair (run-3 audit P10-1):** statement unchanged (an inequality, true for empty coins);
the proof splits on `ρ` empty since `uprob_adaptive_guess` now assumes `Nonempty`. -/
theorem uprob_gi_rep_cheat_le {n m : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : (i : Fin m) → (Fin i → Bool) → ρ → Graph n)
    (γ : (i : Fin m) → (Fin (i + 1) → Bool) → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
      permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) ≤
      (2 : ℝ)⁻¹ ^ m := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
        permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) = 0 := by
      classical
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0]
    positivity
  · rw [← uprob_adaptive_guess m fun i p r => decide (Isomorphic G₁ (H i p r))]
    refine uprob_mono fun z hz i => ?_
    have hi := hz i
    cases hb : z.1 i
    · rw [hb] at hi
      have h0 : Isomorphic G₀ (H i (prefixLT z.1 i) z.2) := ⟨_, hi⟩
      exact (decide_eq_false fun h1 => not_isomorphic_both h ⟨h0, h1⟩).symm
    · rw [hb] at hi
      exact (decide_eq_true ⟨_, hi⟩).symm

/-- The change of variables of Lem-119.b, `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, with the
coins regrouped as `(b, (σ, w))` (inverse: multiply by `σ₀` instead). -/
private def gniShear {n m : ℕ} (ρ : Type*) (σ₀ : Equiv.Perm (Fin n)) :
    (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ) ≃
      ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ where
  toFun z := ((z.1, fun i => if z.1 i then z.2.1 i * σ₀⁻¹ else z.2.1 i), z.2.2)
  invFun z := (z.1.1, (fun i => if z.1.1 i then z.1.2 i * σ₀ else z.1.2 i, z.2))
  left_inv z := by
    rcases z with ⟨b, σ, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp
  right_inv z := by
    rcases z with ⟨⟨b, σ⟩, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp

/-- Under `gniShear` every graph `H_j = σ'_j(G₀)` is independent of `b`
(`permGraph_mul_inv_of_eq`), so the event "every reply equals the verifier's bit" is the
adaptive guessing event of `uprob_adaptive_guess` with guesses ignoring the earlier bits. -/
private theorem gniShear_event_iff {n m : ℕ} {ρ : Type*} {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    ∀ z : (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ),
      (∀ i, g i (prefixLE (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ z).1.1 j) G₁ G₀)
          ((gniShear (m := m) ρ σ₀ z).1.2 j)) i) (gniShear (m := m) ρ σ₀ z).2 =
            (gniShear (m := m) ρ σ₀ z).1.1 i) ↔
      (∀ i, z.1 i = g i (prefixLE (fun j => permGraph G₀ (z.2.1 j)) i) z.2.2) := by
  rintro ⟨b, σ, w⟩
  have hH : (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.1 j) G₁ G₀)
      ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.2 j)) = fun j => permGraph G₀ (σ j) := by
    funext j
    show permGraph (cond (b j) G₁ G₀) (if b j then σ j * σ₀⁻¹ else σ j) = permGraph G₀ (σ j)
    cases b j
    · rfl
    · exact permGraph_mul_inv_of_eq hσ (σ j)
  rw [hH]
  exact forall_congr' fun i => eq_comm

/-- Soundness of the `m`-fold graph non-isomorphism protocol against adaptive provers
[PS10, proof of Proposition 118.4] (Lem-119.b): if `σ₀(G₀) = G₁`, then for every prover
whose `i`-th reply `g_i` depends on the graphs `H_0, …, H_i` received so far and on its
(nonempty type of) coins `w`, the probability (over the verifier's bits `b`, permutations `σ`
and `w`) that every reply equals the verifier's bit is exactly `2^{-m}`.

**Deviation:** `ρ` nonempty (`uprob` on an empty type is `0`; the consumer
`gni_interactiveProof` uses `ρ := P'.Coins |x|`, a tape type).

**Repair (run-3 audit P10-2):** hypothesis `[Nonempty ρ]` added (the run-2 statement
specialised to `ρ := Empty`, `n = m = 0`, `σ₀ = 1` reads `0 = 1`).

**Proof sketch.** Change variables `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, a bijection of the
coins fixing `b` and `w` (`gniShear`, with `uprob_comp_equiv`); then every `H_i = σ'_i(G₀)`
(`permGraph_mul_inv_of_eq`, `hσ`) is a function of `σ'` alone, the event is
`∀ i, b_i = g'_i(b_{<i}, (σ', w))` with `g'_i` ignoring `b_{<i}` (`gniShear_event_iff`), and
`uprob_adaptive_guess` with `W := (Fin m → S_n) × ρ` (nonempty since `ρ` is) gives
`2^{-m}`. -/
theorem uprob_gni_rep_cheat {n m : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    uprob (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i) =
      (2 : ℝ)⁻¹ ^ m := by
  have h1 := uprob_comp_equiv (gniShear (m := m) ρ σ₀)
    (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i)
  have h2 := uprob_adaptive_guess m
    fun i (_ : Fin i → Bool) (w : (Fin m → Equiv.Perm (Fin n)) × ρ) =>
      g i (prefixLE (fun j => permGraph G₀ (w.1 j)) i) w.2
  rw [← h1, ← h2]
  exact OneWay.uprob_congr (gniShear_event_iff hσ g)


end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: efficiency of the honest parties

The polynomial-time machines behind the honest parties of [PS10, Protocols 118.3 and 120.6]
(inventory item Inf-4.2) and the decider of the witness relation `R_iso`, proved for the
shadow strategies of `GraphIsomorphism/Proofs.lean` (the main file
`ZeroKnowledge/GraphIsomorphism.lean` closes its targets by `exact GI.…`).

Every strategy is exhibited as a polynomial-time function of the interactive machine layout
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`GI.efficient_of_polyTime`), assembled from the FP
calculus of `TCSlib.Complexity.ClassNP.PolyTimePairing`, the state-loop toolkit of
`TCSlib.Complexity.Randomized.Build.StateLoop`, the typed coin cuts of
`TCSlib.Complexity.Randomized.Primitives`, and the three string operations of
`ZeroKnowledge/Encoding.lean` (`polyTimeComputable_encPermGraph`,
`polyTimeComputable_encPermMulInv`, `polyTimeComputable_encPermFromCoins`), used as black
boxes. The two new devices are the **unary square root** `w ↦ 1^{√|w|}` (a state loop
counting up to the first `i` with `|w| < (i+1)²`), which reads the vertex count off the common
input, and the **padding** `padSq n w` of a graph word to length `n²`, which lets the
`encPermGraph` machine (whose vertex count is `√` of the length of the graph word) relabel a
graph decoded on a *given* vertex count (`decGraphAt n w`, as the verifiers do on possibly
malformed inputs).

## Main definitions

* `TCSlib.Cryptography.GI.padSq` — a graph word padded to length `n²`.
* `TCSlib.Cryptography.GI.relabelAt`, `GI.sampleStr`, `GI.mulInvStr` — the three string
  operations of the honest parties as functions of words (vertex count passed in unary).
* `TCSlib.Cryptography.GI.argX`, `GI.argZ`, `GI.argM`, `GI.vcount` — the projections of the
  interactive layout.
* `TCSlib.Cryptography.GI.risoTest` — the decider of `R_iso`.

## Main results

* `TCSlib.Cryptography.GI.stateFind` — the state-loop form of the repetition lemma (copy of the
  private `polyTimeComputable_stateFind` of `Randomized/Repetition.lean`).
* `TCSlib.Cryptography.GI.unarySqrt_poly` — `w ↦ 1^{√|w|}` is polynomial-time.
* `TCSlib.Cryptography.GI.wellFormed_poly` — the well-formedness test is polynomial-time.
* `TCSlib.Cryptography.GI.encPermGraphAt_poly` — relabelling a graph decoded on a given vertex
  count is polynomial-time.
* `TCSlib.Cryptography.GI.Riso_decidable` — the decider clause of `Riso_witnessRelation`.
* `TCSlib.Cryptography.GI.giProver_efficient`, `GI.giVerifier_efficient`,
  `GI.gniVerifier_efficient` — the single-iteration parties are PPT strategies.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### An FP toolkit -/

/-- Polynomial-time computability transfers along pointwise equality. -/
theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- The pair-validity test `x ↦ [(pairDecode x).isSome]` is polynomial-time
(`Turing.FinTM.computesFunInTime_pairValid`). -/
theorem pairValid_poly : PolyTimeComputable fun x => [(pairDecode x).isSome] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_pairValid
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- State loops (copy of `polyTimeComputable_stateFind` of
`TCSlib.Complexity.Randomized.Repetition`, which is private there): a state word `⟨x, s⟩`
evolving from `start x` by `step`, a test `acc` first true at round `N x ≤ R|x|`, states of
length `≤ B|x|` up to that round; then `x ↦ out ⟨x, orbit x (N x)⟩` is polynomial-time.

**Proof sketch.** `Complexity.polyTimeComputable_iterateFind` on the guarded step
`StateLoop.gstep step B` (orbit bound `StateLoop.length_gstep_iterate_le` for every word),
pre-composed with `x ↦ ⟨x, start x⟩`; on the genuine orbit the guard never fires
(`StateLoop.gstep_iterate_eq`) and `List.find?` returns `N x` (`StateLoop.find?_range_eq_some`). -/
theorem stateFind {start step : List Bool → List Bool}
    {acc : List Bool → Bool} {out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
    (R B : PolyExpr) (N : List Bool → ℕ) (hN : ∀ x, N x ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ N x → (orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ x i, i < N x → acc (pairEncode x (orbit start step x i)) = false)
    (hlast : ∀ x, acc (pairEncode x (orbit start step x (N x))) = true) :
    PolyTimeComputable fun x => out (pairEncode x (orbit start step x (N x))) := by
  have hF := polyTimeComputable_iterateFind (gstep_poly hstep B) hacc hout R (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  convert hF.comp hpre using 1
  funext x
  simp only [Function.comp_apply]
  have horb := gstep_iterate_eq start step B x (N x) (hbound x)
  have hle : N x ≤ R.eval (pairEncode x (start x)).length :=
    (hN x).trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((gstep step B)^[i] (pairEncode x (start x)))) = some (N x) := by
    apply find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst x i hi
    · rw [horb (N x) le_rfl]
      exact hlast x
  rw [hfind]
  exact (congrArg out (horb (N x) le_rfl)).symm

/-! ### The unary square root -/

namespace SqrtLoop

/-- The initial state: the empty counter. -/
def start (_w : List Bool) : List Bool := []

/-- The step on the state word `⟨w, 1^i⟩`: the counter `1^{i+1}`. -/
def step (st : List Bool) : List Bool := true :: pairSndD st

/-- The test on `⟨w, 1^i⟩`: `|w| < (i + 1)²`, first true at `i = √|w|`. -/
def acc (st : List Bool) : Bool := decide ((pairFstD st).length < ((pairSndD st).length + 1) ^ 2)

/-- The output on `⟨w, 1^i⟩`: the counter. -/
def out (st : List Bool) : List Bool := pairSndD st

/-- The closed form of the orbit: the counter `1^i` after `i` rounds. -/
theorem orbit_eq (w : List Bool) (i : ℕ) : orbit start step w i = List.replicate i true := by
  induction i with
  | zero => rfl
  | succ i ih => simp [step, ih, List.replicate_succ]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start := polyTimeComputable_const []

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step := (cons_poly true).comp polyTimeComputable_pairSndD

/-- The test is polynomial-time: the negated length comparison of `w` with `1^{(i+1)²}`. -/
theorem acc_poly : PolyTimeComputable fun st => [acc st] := by
  have h := not_poly (lenLe_comp polyTimeComputable_pairFstD
    (unaryPoly_comp (.normal 1 2) polyTimeComputable_pairSndD))
  refine ptc_congr h fun st => ?_
  simp only [acc, List.length_replicate, PolyExpr.eval_normal, one_mul]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := polyTimeComputable_pairSndD

end SqrtLoop

/-- **The unary square root is polynomial-time:** `w ↦ 1^{√|w|}` (the vertex count of an
encoded graph read off its length). A state loop counting up to the first `i` with
`|w| < (i + 1)²` (`Nat.le_sqrt'`, `Nat.lt_succ_sqrt'`), at most `|w|` rounds. -/
theorem unarySqrt_poly : PolyTimeComputable fun w => List.replicate (Nat.sqrt w.length) true := by
  have h := stateFind SqrtLoop.start_poly SqrtLoop.step_poly SqrtLoop.acc_poly SqrtLoop.out_poly
    .var .var (fun w => Nat.sqrt w.length) (fun w => Nat.sqrt_le_self _)
    (fun w i hi => by
      rw [SqrtLoop.orbit_eq, List.length_replicate]
      exact hi.trans (Nat.sqrt_le_self _))
    (fun w i hi => by
      simp only [SqrtLoop.acc, SqrtLoop.orbit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, decide_eq_false_iff_not, not_lt]
      exact Nat.le_sqrt'.1 hi)
    (fun w => by
      simp only [SqrtLoop.acc, SqrtLoop.orbit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, decide_eq_true_eq]
      exact Nat.lt_succ_sqrt' _)
  refine ptc_congr h fun w => ?_
  simp [SqrtLoop.out, SqrtLoop.orbit_eq]

/-! ### Well-formedness of an instance -/

/-- The well-formedness test of a common input is polynomial-time: the pair-validity test and
two length comparisons against `1^{n²}` for `n = √|fst x|` in unary (`unarySqrt_poly`,
`polyTimeComputable_unaryPoly`, `polyTimeComputable_lenEq`). -/
theorem wellFormed_poly : PolyTimeComputable fun x => [wellFormedInstance x] := by
  have hsq : PolyTimeComputable fun x => List.replicate
      ((PolyExpr.mul .var .var).eval (List.replicate (Nat.sqrt (pairFstD x).length) true).length) true :=
    unaryPoly_comp (.mul .var .var) (unarySqrt_poly.comp polyTimeComputable_pairFstD)
  have h1 := polyTimeComputable_lenEq.comp (polyTimeComputable_pairFstD.pairEncode hsq)
  have h2 := polyTimeComputable_lenEq.comp (polyTimeComputable_pairSndD.pairEncode hsq)
  have h := polyTimeComputable_and pairValid_poly (polyTimeComputable_and h1 h2)
  refine ptc_congr h fun x => ?_
  simp only [wellFormedInstance, instanceVertexCount, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_var, Bool.decide_and, Bool.decide_eq_true]

/-! ### Padding a graph word to a given vertex count -/

/-- The graph word `w` padded with `false` (or cut) to length `n²`: it decodes on `n` vertices
to the same graph as `w` (`decGraphAt_padSq`) and its length determines `n`. -/
def padSq (n : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate (n * n) false).take (n * n)

/-- The padded word has length `n²`. -/
theorem length_padSq (n : ℕ) (w : List Bool) : (padSq n w).length = n * n := by
  simp [padSq, List.length_take, List.length_append]

/-- The vertex count read off the padded word is `n`. -/
theorem sqrt_length_padSq (n : ℕ) (w : List Bool) : Nat.sqrt (padSq n w).length = n := by
  rw [length_padSq, Nat.sqrt_eq]

/-- Below `n²` the padded word reads as `w` with default `false`. -/
theorem getD_padSq (n : ℕ) (w : List Bool) {k : ℕ} (hk : k < n * n) :
    (padSq n w).getD k false = w.getD k false := by
  simp only [padSq, List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_replicate, if_pos (by omega), Option.getD_some,
      List.getElem?_eq_none (by omega)]
    rfl

/-- Padding does not change the decoded graph on `n` vertices. -/
theorem decGraphAt_padSq (n : ℕ) (w : List Bool) : decGraphAt n (padSq n w) = decGraphAt n w :=
  funext fun u => funext fun v => getD_padSq n w (finProdFinEquiv (u, v)).isLt

/-- `w ↦ 0^{|w|}` is polynomial-time (`polyTimeComputable_pairXor` on `⟨w, w⟩`). -/
theorem zeros_poly : PolyTimeComputable fun w => List.replicate w.length false :=
  ptc_congr (polyTimeComputable_pairXor.comp (polyTimeComputable_id.pairEncode polyTimeComputable_id))
    fun w => by simp

/-- Padding to the square of a unary count is polynomial-time: on `⟨u, w⟩`, `padSq |u| w`
(`polyTimeComputable_pairTakePoly` at `n²` on `⟨u, w ++ 0^{|u|²}⟩`). -/
theorem padSq_poly : PolyTimeComputable fun z => padSq (pairFstD z).length (pairSndD z) := by
  have hsq : PolyTimeComputable fun z =>
      List.replicate ((PolyExpr.mul .var .var).eval (pairFstD z).length) true :=
    unaryPoly_comp (.mul .var .var) polyTimeComputable_pairFstD
  have hz := zeros_poly.comp hsq
  have hcat := polyTimeComputable_pairSndD.append hz
  have h := (polyTimeComputable_pairTakePoly (.mul .var .var)).comp
    (polyTimeComputable_pairFstD.pairEncode hcat)
  refine ptc_congr h fun z => ?_
  simp [padSq, PolyExpr.eval_mul]

/-! ### The three string operations of the honest parties, as functions of words -/

/-- `encGraph (π(G))` for the graph `G` decoded from `w` on `|u|` vertices and the permutation
`π` decoded from `p` on `|u|` points (the vertex count is passed in unary so that it is an
ordinary argument, not read off `w`). -/
noncomputable def relabelAt (u w p : List Bool) : List Bool :=
  encGraph (permGraph (decGraphAt u.length w) (decPerm u.length p))

/-- `relabelAt` with the vertex count `1^n`. -/
theorem relabelAt_replicate (n : ℕ) (w p : List Bool) :
    relabelAt (List.replicate n true) w p = encGraph (permGraph (decGraphAt n w) (decPerm n p)) := by
  unfold relabelAt
  rw [List.length_replicate]

/-- The permutation sampled from the tape `r` on the vertex count of the graph word `w`, as a
string (`samplePerm` at `√|w|`). -/
noncomputable def sampleStr (w r : List Bool) : List Bool := encPerm (samplePerm (Nat.sqrt w.length) r)

/-- The product `π σ⁻¹` of the permutations decoded from `p` and `y` on `√|p|` points, as a
string (the function of `polyTimeComputable_encPermMulInv`). -/
noncomputable def mulInvStr (p y : List Bool) : List Bool :=
  encPerm (decPerm (Nat.sqrt p.length) p * (decPerm (Nat.sqrt p.length) y)⁻¹)

/-- The product machine on `⟨encPerm π, y⟩` returns `encPerm (π σ⁻¹)` for `σ = decPerm n y`
(`length_encPerm`, `Nat.sqrt_eq`, `decPerm_encPerm`). -/
theorem mulInvStr_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) (y : List Bool) :
    mulInvStr (encPerm π) y = encPerm (π * (decPerm n y)⁻¹) := by
  have h : Nat.sqrt (encPerm π).length = n := by rw [length_encPerm, Nat.sqrt_eq]
  unfold mulInvStr
  rw [h, decPerm_encPerm]

/-- Sampling the vertex permutation of a graph word from a tape is polynomial-time
(the shared `polyTimeComputable_encPermFromCoins` of `ZeroKnowledge/Encoding.lean`, whose
vertex count `(decGraph w).1` is `√|w|`). -/
theorem sampleStr_poly : PolyTimeComputable fun z => sampleStr (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPermFromCoins

/-- The permutation product is polynomial-time (`polyTimeComputable_encPermMulInv`). -/
theorem mulInvStr_poly : PolyTimeComputable fun z => mulInvStr (pairFstD z) (pairSndD z) :=
  polyTimeComputable_encPermMulInv

/-- **Relabelling a graph decoded on a given vertex count is polynomial-time:** on
`⟨u, ⟨w, p⟩⟩`, `relabelAt u w p` (`polyTimeComputable_encPermGraph` on the padded word
`padSq |u| w`, whose decoding is `⟨|u|, decGraphAt |u| w⟩`). -/
theorem relabelAt_poly :
    PolyTimeComputable fun z => relabelAt (pairFstD z) (pairFstD (pairSndD z)) (pairSndD (pairSndD z)) := by
  have hpad : PolyTimeComputable fun z => padSq (pairFstD z).length (pairFstD (pairSndD z)) :=
    ptc_congr (padSq_poly.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))) fun z => by simp
  have h := polyTimeComputable_encPermGraph.comp
    (hpad.pairEncode (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  refine ptc_congr h fun z => ?_
  simp only [Function.comp_apply]
  rw [pairFstD_pairEncode, pairSndD_pairEncode, decGraph_eq_of_sqrt (sqrt_length_padSq _ _)]
  simp only [relabelAt, decGraphAt_padSq]

/-! ### The interactive layout and its projections -/

/-- The common-input slot of the interactive layout. -/
def argX (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inArg w))

/-- The auxiliary-input slot of the interactive layout. -/
def argZ (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg w))

/-- The encoded-messages slot of the interactive layout. -/
def argM (w : List Bool) : List Bool := pairSndD (NUPPT.inArg w)

/-- The vertex count of the common input of the layout. -/
def vcount (w : List Bool) : ℕ := Nat.sqrt (pairFstD (argX w)).length

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

/-- The unary parameter of a layout. -/
@[simp] theorem inParam_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    NUPPT.inParam (ilayout x z hist r) = List.replicate x.length true := by
  simp [ilayout]

/-- The vertex count of a layout. -/
@[simp] theorem vcount_ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) :
    vcount (ilayout x z hist r) = Nat.sqrt (pairFstD x).length := by
  simp [vcount]

/-- The common-input projection is polynomial-time. -/
theorem argX_poly : PolyTimeComputable argX :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The auxiliary-input projection is polynomial-time. -/
theorem argZ_poly : PolyTimeComputable argZ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- The messages projection is polynomial-time. -/
theorem argM_poly : PolyTimeComputable argM :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg

/-- The first graph word of the common input. -/
theorem w₀_poly : PolyTimeComputable fun w => pairFstD (argX w) := polyTimeComputable_pairFstD.comp argX_poly

/-- The second graph word of the common input. -/
theorem w₁_poly : PolyTimeComputable fun w => pairSndD (argX w) := polyTimeComputable_pairSndD.comp argX_poly

/-- The vertex count in unary. -/
theorem vcount_poly : PolyTimeComputable fun w => List.replicate (vcount w) true :=
  unarySqrt_poly.comp w₀_poly

/-- The first bit of the coins (the challenge of the verifiers). -/
theorem coinBit_poly : PolyTimeComputable fun w => [(NUPPT.inCoins w).headD false] :=
  headBit_poly.comp NUPPT.polyTimeComputable_inCoins

/-- The graph word selected by the first coin, `G_b`. -/
theorem selGraph_poly : PolyTimeComputable fun w =>
    if (NUPPT.inCoins w).headD false then pairSndD (argX w) else pairFstD (argX w) :=
  polyTimeComputable_ite coinBit_poly w₁_poly w₀_poly

/-- Relabelling the graph word `g w` on `vcount w` vertices by the permutation word `p w`. -/
theorem relabel_poly {g p : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hp : PolyTimeComputable p) :
    PolyTimeComputable fun w => relabelAt (List.replicate (vcount w) true) (g w) (p w) :=
  ptc_congr (relabelAt_poly.comp (vcount_poly.pairEncode (hg.pairEncode hp))) fun w => by simp

/-- The sampled permutation of a party as a string, from the common input and the coins. -/
theorem piStr_poly : PolyTimeComputable fun w => sampleStr (pairFstD (argX w)) (NUPPT.inCoins w) :=
  ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode NUPPT.polyTimeComputable_inCoins)) fun w => by simp

/-! ### The witness relation `R_iso` -/

/-- The test "`y` is a genuine permutation encoding": `encPerm (decPerm n y) = y`, computed by the
product machine against the identity `decPerm n [] = 1`. -/
noncomputable def permTest (y : List Bool) : Bool := decide (mulInvStr y [] = y)

/-- The test `encGraph (σ(G₀)) = w₁` for `G₀` decoded from `w₀` and `σ` from `y`. -/
noncomputable def graphTest (w₀ w₁ y : List Bool) : Bool :=
  decide (relabelAt (List.replicate (Nat.sqrt w₀.length) true) w₀ y = w₁)

/-- A permutation encoding passes `permTest`. -/
theorem permTest_encPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : permTest (encPerm σ) = true := by
  simp [permTest, mulInvStr_encPerm, decPerm_nil]

/-- A word of length `n²` passing `permTest` is the encoding of its decoded permutation. -/
theorem eq_encPerm_of_permTest {n : ℕ} {y : List Bool} (hlen : y.length = n * n)
    (h : permTest y = true) : y = encPerm (decPerm n y) := by
  have hn : Nat.sqrt y.length = n := by rw [hlen, Nat.sqrt_eq]
  simp only [permTest, mulInvStr, decide_eq_true_eq] at h
  rw [hn, decPerm_nil, inv_one, mul_one] at h
  exact h.symm

/-- `graphTest` on an encoded graph. -/
theorem graphTest_encGraph {n : ℕ} (G₀ : Graph n) (w₁ y : List Bool) :
    graphTest (encGraph G₀) w₁ y = decide (encGraph (permGraph G₀ (decPerm n y)) = w₁) := by
  unfold graphTest
  rw [length_encGraph, Nat.sqrt_eq, relabelAt_replicate, decGraphAt_encGraph]

/-- The decider of `R_iso` on `⟨x, y⟩`: `x` well formed, `|y| = |fst x|`, `y` a genuine
permutation encoding, and `encGraph (σ(G₀)) = snd x`. -/
noncomputable def risoTest (z : List Bool) : Bool :=
  wellFormedInstance (pairFstD z) &&
    (decide ((pairSndD z).length = (pairFstD (pairFstD z)).length) &&
      (permTest (pairSndD z) && graphTest (pairFstD (pairFstD z)) (pairSndD (pairFstD z)) (pairSndD z)))

/-- The decider of `R_iso` is polynomial-time (`wellFormed_poly`, `polyTimeComputable_lenEq`,
`mulInvStr_poly`, `relabelAt_poly`, `polyTimeComputable_pairEq`). -/
theorem risoTest_poly : PolyTimeComputable fun z => [risoTest z] := by
  have hw0 : PolyTimeComputable fun z => pairFstD (pairFstD z) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hw1 : PolyTimeComputable fun z => pairSndD (pairFstD z) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have h1 : PolyTimeComputable fun z => [wellFormedInstance (pairFstD z)] :=
    wellFormed_poly.comp polyTimeComputable_pairFstD
  have h2 : PolyTimeComputable fun z => [decide ((pairSndD z).length = (pairFstD (pairFstD z)).length)] :=
    ptc_congr (polyTimeComputable_lenEq.comp (polyTimeComputable_pairSndD.pairEncode hw0))
      fun z => by simp
  have h3 : PolyTimeComputable fun z => [permTest (pairSndD z)] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((mulInvStr_poly.comp
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))).pairEncode
        polyTimeComputable_pairSndD)) fun z => by simp [permTest]
  have h4 : PolyTimeComputable fun z => [graphTest (pairFstD (pairFstD z)) (pairSndD (pairFstD z)) (pairSndD z)] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabelAt_poly.comp
      ((unarySqrt_poly.comp hw0).pairEncode (hw0.pairEncode polyTimeComputable_pairSndD))).pairEncode hw1))
      fun z => by simp [graphTest]
  exact polyTimeComputable_and h1 (polyTimeComputable_and h2 (polyTimeComputable_and h3 h4))

/-- The decider of `R_iso` is correct: `risoTest ⟨x, y⟩ = true ↔ Riso x y`.

**Proof sketch.** (→) A well-formed `x` is `encInstance G₀ G₁` (`eq_encInstance_of_wellFormed`);
`|y| = n²` and `permTest` give `y = encPerm σ` for `σ := decPerm n y` (`eq_encPerm_of_permTest`),
and the graph test reads `encGraph (σ(G₀)) = encGraph G₁`, i.e. `σ(G₀) = G₁`
(`graphTest_encGraph`, `encGraph_injective`). (←) Unfold the witnesses and evaluate
(`wellFormedInstance_encInstance`, `length_encPerm`, `permTest_encPerm`, `decPerm_encPerm`). -/
theorem risoTest_iff (x y : List Bool) : risoTest (pairEncode x y) = true ↔ Riso x y := by
  simp only [risoTest, pairFstD_pairEncode, pairSndD_pairEncode, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hwf, hlen, hperm, hgraph⟩
    obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
    have h0 : pairFstD (encInstance G₀ G₁) = encGraph G₀ := pairFstD_pairEncode _ _
    have h1 : pairSndD (encInstance G₀ G₁) = encGraph G₁ := pairSndD_pairEncode _ _
    rw [h0, length_encGraph] at hlen
    rw [h0, h1, graphTest_encGraph, decide_eq_true_eq] at hgraph
    exact ⟨n, G₀, G₁, decPerm n y, rfl, eq_encPerm_of_permTest hlen hperm, encGraph_injective n hgraph⟩
  · rintro ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩
    refine ⟨wellFormedInstance_encInstance G₀ G₁, by simp, permTest_encPerm σ, ?_⟩
    rw [pairFstD_pairEncode, pairSndD_pairEncode, graphTest_encGraph, decPerm_encPerm, hσ]
    exact decide_eq_true rfl

/-- The decider clause of `Riso_witnessRelation` (Def-191.11 for `R_iso`). -/
theorem Riso_decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ Riso x y :=
  ⟨risoTest, risoTest_poly, risoTest_iff⟩

/-! ### Efficiency of the single-iteration parties -/

/-- The honest prover of the graph isomorphism protocol is a PPT strategy
[PS10, Proposition 120.7] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime` with the layout function: message `1` is
`relabel_poly` of `G₀` by the sampled permutation (`piStr_poly`), message `3` is
`mulInvStr_poly` on `⟨encPerm π, y⟩` or `encPerm π` according to the challenge bit
(`polyTimeComputable_ite`), the case split on `msgs = []` by `isNil_poly`. The equation with
`giProver.next` is checked on the two shapes of the history (`giProver_next_nil'`,
`giProver_next_cons'`) with `relabelAt_replicate`, `decPerm_encPerm`, `mulInvStr_encPerm`. -/
theorem giProver_efficient : giProver.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hbit : PolyTimeComputable fun w => [(pairFstD (argM w)).headD false] :=
    headBit_poly.comp (polyTimeComputable_pairFstD.comp argM_poly)
  have hF₁ := relabel_poly w₀_poly piStr_poly
  have hmul : PolyTimeComputable fun w =>
      mulInvStr (sampleStr (pairFstD (argX w)) (NUPPT.inCoins w)) (argZ w) :=
    ptc_congr (mulInvStr_poly.comp (piStr_poly.pairEncode argZ_poly)) fun w => by simp
  have hF₃ : PolyTimeComputable fun w => if (pairFstD (argM w)).headD false then
      mulInvStr (sampleStr (pairFstD (argX w)) (NUPPT.inCoins w)) (argZ w)
    else sampleStr (pairFstD (argX w)) (NUPPT.inCoins w) := polyTimeComputable_ite hbit hmul piStr_poly
  refine efficient_of_polyTime giProver (polyTimeComputable_ite hnil hF₁ hF₃) ?_
  intro x z r hist
  cases hist with
  | nil =>
    rw [giProver_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true, vcount_ilayout,
      argX_ilayout, inCoins_ilayout]
    rw [relabelAt_replicate, sampleStr, decPerm_encPerm]
    rfl
  | cons m h =>
    rw [giProver_next_cons']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Turing.pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairFstD_pairEncode, argX_ilayout, inCoins_ilayout, argZ_ilayout]
    rw [sampleStr, mulInvStr_encPerm]
    split_ifs <;> rfl

/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
for Proposition 120.7] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the challenge is the first coin (`coinBit_poly`),
the verdict conjoins the well-formedness test (`wellFormed_poly`) with `relabel_poly` of `G_b`
by `γ` compared with `H` (`polyTimeComputable_pairEq`); the number of messages is read off the
nesting of `msgs` by `isNil_poly` tests. The equation with `giVerifier.next` is checked on the
four shapes of the history (`giVerifier_next_nil'`, `giVerifier_next_one`,
`giVerifier_next_two'`, `giVerifier_next_long'`). -/
theorem giVerifier_efficient : giVerifier.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hnil₂ : PolyTimeComputable fun w => [decide (pairSndD (argM w) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hnil₃ : PolyTimeComputable fun w => [decide (pairSndD (pairSndD (argM w)) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp argM_poly))
  have hH : PolyTimeComputable fun w => pairFstD (argM w) := polyTimeComputable_pairFstD.comp argM_poly
  have hγ : PolyTimeComputable fun w => pairFstD (pairSndD (argM w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hcheck : PolyTimeComputable fun w => [decide (relabelAt (List.replicate (vcount w) true)
      (if (NUPPT.inCoins w).headD false then pairSndD (argX w) else pairFstD (argX w))
      (pairFstD (pairSndD (argM w))) = pairFstD (argM w))] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabel_poly selGraph_poly hγ).pairEncode hH))
      fun w => by simp
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf hcheck
  have hF := polyTimeComputable_ite hnil (polyTimeComputable_const [false])
    (polyTimeComputable_ite hnil₂ coinBit_poly
      (polyTimeComputable_ite hnil₃ hverdict (polyTimeComputable_const [false])))
  refine efficient_of_polyTime giVerifier hF ?_
  intro x z r hist
  rcases hist with _ | ⟨H, _ | ⟨γ, _ | ⟨m, t⟩⟩⟩
  · rw [giVerifier_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true]
  · rw [giVerifier_next_one]
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      Turing.pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, decide_true, if_true,
      inCoins_ilayout]
  · rw [giVerifier_next_two']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      Turing.pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, pairFstD_pairEncode,
      decide_true, if_true, vcount_ilayout, argX_ilayout, inCoins_ilayout,
      Bool.decide_and, Bool.decide_eq_true]
    rw [relabelAt_replicate]
    split_ifs <;> rfl
  · rw [giVerifier_next_long']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Turing.pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairSndD_pairEncode]

/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
[PS10, Proposition 118.4] (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the first message is `relabel_poly` of `G_b` by
the permutation sampled from the coins after the first (`sampleStr_poly` on
`⟨fst x, tail r⟩`), the verdict compares the reply's bit with the first coin
(`polyTimeComputable_pairEq` on one-bit words) under the well-formedness test
(`wellFormed_poly`). The equation with `gniVerifier.next` is checked on the three shapes of
the history (`gniVerifier_next_nil'`, `gniVerifier_next_one`, `gniVerifier_next_long'`). -/
theorem gniVerifier_efficient : gniVerifier.Efficient := by
  have hnil : PolyTimeComputable fun w => [decide (argM w = [])] := isNil_poly.comp argM_poly
  have hnil₂ : PolyTimeComputable fun w => [decide (pairSndD (argM w) = [])] :=
    isNil_poly.comp (polyTimeComputable_pairSndD.comp argM_poly)
  have hσ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w)) (NUPPT.inCoins w).tail :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode (tail_poly.comp NUPPT.polyTimeComputable_inCoins)))
      fun w => by simp
  have hF₀ := relabel_poly selGraph_poly hσ
  have hbit : PolyTimeComputable fun w =>
      [decide ([(pairFstD (argM w)).headD false] = [(NUPPT.inCoins w).headD false])] :=
    ptc_congr (polyTimeComputable_pairEq.comp
      ((headBit_poly.comp (polyTimeComputable_pairFstD.comp argM_poly)).pairEncode coinBit_poly))
      fun w => by simp
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf hbit
  have hF := polyTimeComputable_ite hnil hF₀
    (polyTimeComputable_ite hnil₂ hverdict (polyTimeComputable_const [false]))
  refine efficient_of_polyTime gniVerifier hF ?_
  intro x z r hist
  rcases hist with _ | ⟨b', _ | ⟨m, t⟩⟩
  · rw [gniVerifier_next_nil']
    simp only [argM_ilayout, Strategy.encodeMsgs_nil, decide_true, if_true,
      vcount_ilayout, argX_ilayout, inCoins_ilayout, List.drop_one]
    rw [relabelAt_replicate, sampleStr, decPerm_encPerm]
    split_ifs <;> rfl
  · rw [gniVerifier_next_one]
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      Turing.pairEncode_ne_nil,
      decide_false, Bool.false_eq_true, if_false, pairSndD_pairEncode, pairFstD_pairEncode,
      decide_true, if_true, argX_ilayout, inCoins_ilayout, Bool.decide_and,
      Bool.decide_eq_true, List.cons.injEq, and_true]
  · rw [gniVerifier_next_long']
    simp only [argM_ilayout, Strategy.encodeMsgs_cons, Turing.pairEncode_ne_nil, decide_false,
      Bool.false_eq_true, if_false, pairSndD_pairEncode]

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: efficiency of the repeated parties

The loop infrastructure for the polynomial-time machines behind the `|x|`-fold parties of
[PS10, Protocols 118.3 and 120.6] (inventory item Inf-4.2), and the machine of the
`|x|`-fold graph non-isomorphism verifier `gniVerifierRep`, proved for the shadow strategies
of `GraphIsomorphism/Proofs.lean` (the `|x|`-fold graph isomorphism parties are in
`GraphIsomorphism/EfficiencyRepGI.lean`). The repeated parties read the
*number* of messages received (to select the coin block of the current iteration and to
decide whether the protocol is over), the parity of that number and the last message
received, and the verifiers' verdicts scan the `|x|` iterations. All of these are **peeling
loops** over the nested-pair encoding `encodeMsgs hist = ⟨m₀, ⟨m₁, …⟩⟩` of the history
(`peelLoop_poly`: iterate a shrinking map until a test holds, counting the rounds in unary)
and one **unary-count loop** (`iterUnary_poly`: iterate a step `|u|` times for a unary count
`u` read from the input), both instances of the state-loop lemma `GI.stateFind`.

## Main definitions

* `TCSlib.Cryptography.GI.peelSteps` — the rounds of a peeling loop (with fuel).
* `TCSlib.Cryptography.GI.msgCount`, `GI.halfCount`, `GI.lastSteps` — the number of messages,
  half of it, and the rounds to the last message of an encoded history.

## Main results

* `TCSlib.Cryptography.GI.peelLoop_poly`, `GI.iterUnary_poly` — the two loop schemes.
* `TCSlib.Cryptography.GI.msgCount_poly`, `GI.halfLoop_poly`, `GI.lastMsg_poly` — the
  number of messages in unary, the half count with the remainder (parity), the last message.
* `TCSlib.Cryptography.GI.unaryMul_poly`, `GI.coinSlice_poly` — unary multiplication and the
  coin block of a given iteration.
* `TCSlib.Cryptography.GI.gniVerifierRep_efficient` — the `|x|`-fold graph non-isomorphism
  verifier is a PPT strategy.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### Peeling the nested-pair encoding -/

/-- The second component of a nonempty word is shorter than the word. -/
theorem length_pairSndD_lt {w : List Bool} (h : w ≠ []) : (pairSndD w).length < w.length := by
  cases hw : pairDecode w with
  | none =>
    simp only [pairSndD, hw, Option.map_none, Option.getD_none, List.length_nil]
    exact List.length_pos_of_ne_nil h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode w a b hw
    subst hz
    rw [pairSndD_pairEncode, length_pairEncode]
    omega

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (w : List Bool) : (pairSndD w).length ≤ w.length := by
  rcases eq_or_ne w [] with rfl | h
  · rfl
  · exact (length_pairSndD_lt h).le

/-- Iterating a length-non-increasing map never lengthens. -/
theorem length_iterate_le {f : List Bool → List Bool} (hle : ∀ w, (f w).length ≤ w.length)
    (w : List Bool) : ∀ k, (f^[k] w).length ≤ w.length
  | 0 => le_rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (hle _).trans (length_iterate_le hle w k)

/-- Peeling the empty word gives the empty word. -/
theorem iterate_pairSndD_nil : ∀ k : ℕ, pairSndD^[k] [] = []
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply]; exact iterate_pairSndD_nil k

/-- Peeling the encoding of a history drops its first message. -/
theorem pairSndD_encodeMsgs (hist : List (List Bool)) :
    pairSndD (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop 1) := by
  cases hist with
  | nil => rfl
  | cons m h => rw [Strategy.encodeMsgs_cons, pairSndD_pairEncode, List.drop_succ_cons, List.drop_zero]

/-- Peeling the encoding of a history `k` times leaves the encoding of the history without its
first `k` messages. -/
theorem iterate_pairSndD_encodeMsgs : ∀ (k : ℕ) (hist : List (List Bool)),
    pairSndD^[k] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop k)
  | 0, _ => rfl
  | k + 1, hist => by
    rw [Function.iterate_succ_apply, pairSndD_encodeMsgs, iterate_pairSndD_encodeMsgs k, List.drop_drop]
    congr 2
    omega

/-- The encoding of a history is empty exactly when the history is. -/
theorem encodeMsgs_eq_nil_iff (hist : List (List Bool)) : Strategy.encodeMsgs hist = [] ↔ hist = [] := by
  cases hist with
  | nil => simp
  | cons m h => simp [Turing.pairEncode_ne_nil]

/-- The rounds of a peeling loop, with fuel: `0` once `stop` holds, else one more than from
`f w`. -/
def peelStepsAux (f : List Bool → List Bool) (stop : List Bool → Bool) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, w => if stop w then 0 else peelStepsAux f stop n (f w) + 1

/-- The rounds of a peeling loop from `w` (fuel `|w| + 1`): the first round at which `stop`
holds along the orbit of `f`, provided `f` shortens every word that is not stopped. -/
def peelSteps (f : List Bool → List Bool) (stop : List Bool → Bool) (w : List Bool) : ℕ :=
  peelStepsAux f stop (w.length + 1) w

/-- With enough fuel the round count is the first round at which `stop` holds, and it is at
most `|w|`.

**Proof sketch.** Induction on the fuel: if `stop w` holds the count is `0`; otherwise `f w` is
shorter than `w` (`hdec`), the induction hypothesis applies to it, and the three clauses shift
by one round (`Function.iterate_succ_apply`). -/
theorem peelStepsAux_spec (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) :
    ∀ n w, w.length < n →
      (∀ k < peelStepsAux f stop n w, stop (f^[k] w) = false) ∧
        stop (f^[peelStepsAux f stop n w] w) = true ∧ peelStepsAux f stop n w ≤ w.length := by
  intro n
  induction n with
  | zero => intro w hw; omega
  | succ n ih =>
    intro w hw
    by_cases hs : stop w = true
    · simp only [peelStepsAux, hs, if_true]
      exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), by simpa using hs, Nat.zero_le _⟩
    · have hs' : stop w = false := by simpa using hs
      have hlt := hdec w hs'
      obtain ⟨h1, h2, h3⟩ := ih (f w) (by omega)
      simp only [peelStepsAux, hs', Bool.false_eq_true, if_false]
      refine ⟨fun k hk => ?_, ?_, by omega⟩
      · cases k with
        | zero => simpa using hs'
        | succ k => rw [Function.iterate_succ_apply]; exact h1 k (by omega)
      · rw [Function.iterate_succ_apply]; exact h2

/-- The specification of `peelSteps`. -/
theorem peelSteps_spec (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) (w : List Bool) :
    (∀ k < peelSteps f stop w, stop (f^[k] w) = false) ∧
      stop (f^[peelSteps f stop w] w) = true ∧ peelSteps f stop w ≤ w.length :=
  peelStepsAux_spec f stop hdec _ w (Nat.lt_succ_self _)

/-- `peelSteps` is the first round at which `stop` holds. -/
theorem peelSteps_eq (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) {w : List Bool} {k : ℕ}
    (hk : ∀ j < k, stop (f^[j] w) = false) (hk' : stop (f^[k] w) = true) :
    peelSteps f stop w = k := by
  obtain ⟨h1, h2, -⟩ := peelSteps_spec f stop hdec w
  rcases lt_trichotomy (peelSteps f stop w) k with h | h | h
  · have := hk _ h
    rw [h2] at this
    exact absurd this (by decide)
  · exact h
  · have := h1 _ h
    rw [hk'] at this
    exact absurd this (by decide)

/-- **Peeling loop:** iterate a length-non-increasing polynomial-time map `f` from `w` until
the polynomial-time test `stop` holds (within `|w|` rounds, as `f` shortens unstopped words),
returning the final word paired with the round count in unary.

**Proof sketch.** `stateFind` on the state `⟨rem, 1^k⟩` from `⟨w, []⟩` with the step
`⟨f rem, 1^{k+1}⟩`, the test `stop rem` and the output `⟨rem, 1^k⟩`; the orbit is
`⟨f^[k] w, 1^k⟩`, of length at most `3|w| + 2`, and `peelSteps_spec` gives the first round. -/
theorem peelLoop_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hle : ∀ w, (f w).length ≤ w.length) {stop : List Bool → Bool}
    (hstop : PolyTimeComputable fun w => [stop w])
    (hdec : ∀ w, stop w = false → (f w).length < w.length) :
    PolyTimeComputable fun w =>
      pairEncode (f^[peelSteps f stop w] w) (List.replicate (peelSteps f stop w) true) := by
  have horbit : ∀ (w : List Bool) (k : ℕ),
      orbit (fun w => pairEncode w [])
        (fun st => pairEncode (f (pairFstD (pairSndD st))) (true :: pairSndD (pairSndD st))) w k =
        pairEncode (f^[k] w) (List.replicate k true) := by
    intro w k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [orbit_succ, ih, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
        Function.iterate_succ_apply', List.replicate_succ]
  have hstart : PolyTimeComputable fun w => pairEncode w [] :=
    polyTimeComputable_id.pairEncode (polyTimeComputable_const [])
  have hstep : PolyTimeComputable fun st =>
      pairEncode (f (pairFstD (pairSndD st))) (true :: pairSndD (pairSndD st)) :=
    (hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hacc : PolyTimeComputable fun st => [stop (pairFstD (pairSndD st))] :=
    hstop.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := stateFind hstart hstep hacc
    polyTimeComputable_pairSndD .var (.add (.mul (.const 3) .var) (.const 2)) (peelSteps f stop)
    (fun w => (peelSteps_spec f stop hdec w).2.2)
    (fun w k hk => by
      rw [horbit, length_pairEncode, List.length_replicate]
      have h1 := length_iterate_le hle w k
      have h2 := (peelSteps_spec f stop hdec w).2.2
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega)
    (fun w k hk => by
      show stop (pairFstD (pairSndD (pairEncode w _))) = false
      rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]
      exact (peelSteps_spec f stop hdec w).1 k hk)
    (fun w => by
      show stop (pairFstD (pairSndD (pairEncode w _))) = true
      rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]
      exact (peelSteps_spec f stop hdec w).2.1)
  refine ptc_congr h fun w => ?_
  rw [horbit, pairSndD_pairEncode]

/-! ### The number of messages, its half and parity, the last message -/

/-- Peeling `pairSndD` until the word is empty shortens every unstopped word. -/
theorem dec_sndD_nil : ∀ w : List Bool, decide (w = []) = false → (pairSndD w).length < w.length :=
  fun w hw => length_pairSndD_lt (by simpa using hw)

/-- The number of messages of an encoded history: the rounds of peeling until empty. -/
def msgCount (w : List Bool) : ℕ := peelSteps pairSndD (fun v => decide (v = [])) w

/-- The number of messages of `encodeMsgs hist` is `|hist|`. -/
theorem msgCount_encodeMsgs (hist : List (List Bool)) : msgCount (Strategy.encodeMsgs hist) = hist.length := by
  apply peelSteps_eq _ _ dec_sndD_nil
  · intro j hj
    rw [iterate_pairSndD_encodeMsgs]
    simp [encodeMsgs_eq_nil_iff, List.drop_eq_nil_iff, hj]
  · rw [iterate_pairSndD_encodeMsgs]
    simp

/-- The number of messages in unary is polynomial-time (`peelLoop_poly`). -/
theorem msgCount_poly : PolyTimeComputable fun w => List.replicate (msgCount w) true :=
  ptc_congr (polyTimeComputable_pairSndD.comp
    (peelLoop_poly polyTimeComputable_pairSndD length_pairSndD_le isNil_poly dec_sndD_nil))
    fun w => by simp [msgCount]

/-- Peeling two messages at a time until at most one is left shortens every unstopped word. -/
theorem dec_sndD_two : ∀ w : List Bool, (decide (w = []) || decide (pairSndD w = [])) = false →
    (pairSndD (pairSndD w)).length < w.length := by
  intro w hw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hw
  exact (length_pairSndD_lt hw.2).trans (length_pairSndD_lt hw.1)

/-- Half the number of messages of an encoded history: the rounds of peeling two messages at a
time until at most one is left. -/
def halfCount (w : List Bool) : ℕ :=
  peelSteps (fun v => pairSndD (pairSndD v)) (fun v => decide (v = []) || decide (pairSndD v = [])) w

/-- Peeling two messages `k` times drops `2k` messages. -/
theorem iterate_sndD_two_encodeMsgs (k : ℕ) (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[k] (Strategy.encodeMsgs hist) =
      Strategy.encodeMsgs (hist.drop (2 * k)) := by
  induction k generalizing hist with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    show (fun v => pairSndD (pairSndD v))^[k] (pairSndD^[2] (Strategy.encodeMsgs hist)) = _
    rw [iterate_pairSndD_encodeMsgs, ih, List.drop_drop]
    congr 2
    ring

/-- The half count of `encodeMsgs hist` is `|hist| / 2`. -/
theorem halfCount_encodeMsgs (hist : List (List Bool)) :
    halfCount (Strategy.encodeMsgs hist) = hist.length / 2 := by
  apply peelSteps_eq _ _ dec_sndD_two
  · intro j hj
    rw [iterate_sndD_two_encodeMsgs]
    have h1 : ¬ hist.drop (2 * j) = [] := by
      rw [List.drop_eq_nil_iff]; omega
    have h2 : ¬ (hist.drop (2 * j)).drop 1 = [] := by
      rw [List.drop_drop, List.drop_eq_nil_iff]; omega
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, encodeMsgs_eq_nil_iff, h1,
      not_false_eq_true, true_and, pairSndD_encodeMsgs]
    exact h2
  · rw [iterate_sndD_two_encodeMsgs]
    simp only [Bool.or_eq_true, decide_eq_true_eq, encodeMsgs_eq_nil_iff, pairSndD_encodeMsgs,
      List.drop_drop, List.drop_eq_nil_iff]
    omega

/-- The remainder after the half loop on `encodeMsgs hist`: the history without its first
`2 (|hist| / 2)` messages (empty exactly when `|hist|` is even). -/
theorem halfRem_encodeMsgs (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[halfCount (Strategy.encodeMsgs hist)] (Strategy.encodeMsgs hist) =
      Strategy.encodeMsgs (hist.drop (2 * (hist.length / 2))) := by
  rw [halfCount_encodeMsgs, iterate_sndD_two_encodeMsgs]

/-- The half loop (remainder paired with the half count in unary) is polynomial-time. -/
theorem halfLoop_poly : PolyTimeComputable fun w =>
    pairEncode ((fun v => pairSndD (pairSndD v))^[halfCount w] w) (List.replicate (halfCount w) true) :=
  peelLoop_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
    (fun w => (length_pairSndD_le _).trans (length_pairSndD_le w))
    (or_poly isNil_poly (isNil_poly.comp polyTimeComputable_pairSndD)) dec_sndD_two

/-- Peeling until the second component is empty shortens every unstopped word. -/
theorem dec_sndD_last : ∀ w : List Bool, decide (pairSndD w = []) = false → (pairSndD w).length < w.length := by
  intro w hw
  apply length_pairSndD_lt
  rintro rfl
  exact (by simpa using hw : ¬ pairSndD ([] : List Bool) = []) rfl

/-- The rounds to the last message of an encoded history. -/
def lastSteps (w : List Bool) : ℕ := peelSteps pairSndD (fun v => decide (pairSndD v = [])) w

/-- The rounds to the last message of `encodeMsgs hist` are `|hist| - 1`. -/
theorem lastSteps_encodeMsgs (hist : List (List Bool)) :
    lastSteps (Strategy.encodeMsgs hist) = hist.length - 1 := by
  apply peelSteps_eq _ _ dec_sndD_last
  · intro j hj
    rw [iterate_pairSndD_encodeMsgs, pairSndD_encodeMsgs]
    simp only [decide_eq_false_iff_not, encodeMsgs_eq_nil_iff, List.drop_drop, List.drop_eq_nil_iff]
    omega
  · rw [iterate_pairSndD_encodeMsgs, pairSndD_encodeMsgs]
    simp only [decide_eq_true_eq, encodeMsgs_eq_nil_iff, List.drop_drop, List.drop_eq_nil_iff]
    omega

/-- The first component of the remainder after `lastSteps` rounds is the last message. -/
theorem lastMsg_encodeMsgs (hist : List (List Bool)) :
    pairFstD (pairSndD^[lastSteps (Strategy.encodeMsgs hist)] (Strategy.encodeMsgs hist)) =
      hist.getLastD [] := by
  rw [lastSteps_encodeMsgs, iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs,
    List.headD_eq_head?, List.head?_drop, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]

/-- The last message of an encoded history is polynomial-time (`peelLoop_poly`). -/
theorem lastMsg_poly : PolyTimeComputable fun w => pairFstD (pairSndD^[lastSteps w] w) :=
  ptc_congr (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
    (peelLoop_poly polyTimeComputable_pairSndD length_pairSndD_le (isNil_poly.comp polyTimeComputable_pairSndD)
      dec_sndD_last))) fun w => by simp [lastSteps]

/-! ### Unary multiplication and coin blocks -/

/-- Unary multiplication `⟨u, v⟩ ↦ 1^{|u| · |v|}` is polynomial-time
(`Turing.FinTM.computesFunInTime_unaryMul`). -/
theorem unaryMul_poly : PolyTimeComputable fun z => match pairDecode z with
    | some (u, v) => List.replicate (u.length * v.length) true
    | none => [] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  exact ⟨M, c, 2, hM⟩

/-- The product of two unary counts given by polynomial-time maps. -/
theorem unaryMul_comp {f g : List Bool → ℕ} (hf : PolyTimeComputable fun w => List.replicate (f w) true)
    (hg : PolyTimeComputable fun w => List.replicate (g w) true) :
    PolyTimeComputable fun w => List.replicate (f w * g w) true :=
  ptc_congr (unaryMul_poly.comp (hf.pairEncode hg)) fun w => by simp [pairDecode_pairEncode]

/-- The coin block `coinSlice c i r` for a block length `c = p(|u|)` and an index `i` given in
unary by polynomial-time maps (`polyTimeComputable_pairDropPoly`, `polyTimeComputable_pairTakePoly`). -/
theorem coinSlice_poly (p : PolyExpr) {u i r : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hi : PolyTimeComputable i) (hr : PolyTimeComputable r) :
    PolyTimeComputable fun w => coinSlice (p.eval (u w).length) (i w).length (r w) := by
  have hic : PolyTimeComputable fun w => List.replicate ((i w).length * p.eval (u w).length) true :=
    unaryMul_comp (ptc_congr (polyTimeComputable_unary.comp hi) fun w => rfl) (unaryPoly_comp p hu)
  have hdrop : PolyTimeComputable fun w => (r w).drop ((i w).length * p.eval (u w).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp (hic.pairEncode hr)) fun w => by simp
  refine ptc_congr ((polyTimeComputable_pairTakePoly p).comp (hu.pairEncode hdrop)) fun w => ?_
  simp [coinSlice]

/-! ### Iterating a step a unary number of times -/

/-- **Unary-count loop:** on `x₀ = ⟨u, s₀⟩`, iterate `s ↦ step ⟨x₀, s⟩` exactly `|u|` times from
`s₀` (the step may read `x₀`), provided the orbit stays within the bound `B|x₀|`.

**Proof sketch.** `stateFind` on the state `⟨s, 1^k⟩` from `⟨x₀, ⟨s₀, []⟩⟩` with the test
`|u| ≤ |1^k|`, which fires first at round `|u| ≤ |x₀|`. -/
theorem iterUnary_poly {step : List Bool → List Bool} (hstep : PolyTimeComputable step) (B : PolyExpr)
    (hbound : ∀ x₀ k, k ≤ (pairFstD x₀).length →
      ((fun s => step (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤ B.eval x₀.length) :
    PolyTimeComputable fun x₀ => (fun s => step (pairEncode x₀ s))^[(pairFstD x₀).length] (pairSndD x₀) := by
  have horbit : ∀ (x₀ : List Bool) (k : ℕ),
      orbit (fun x₀ => pairEncode (pairSndD x₀) [])
        (fun st => pairEncode (step (pairEncode (pairFstD st) (pairFstD (pairSndD st))))
          (true :: pairSndD (pairSndD st))) x₀ k =
        pairEncode ((fun s => step (pairEncode x₀ s))^[k] (pairSndD x₀)) (List.replicate k true) := by
    intro x₀ k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [orbit_succ, ih, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
        pairSndD_pairEncode, Function.iterate_succ_apply', List.replicate_succ]
  have hstart : PolyTimeComputable fun x₀ => pairEncode (pairSndD x₀) [] :=
    polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])
  have hstep' : PolyTimeComputable fun st =>
      pairEncode (step (pairEncode (pairFstD st) (pairFstD (pairSndD st)))) (true :: pairSndD (pairSndD st)) :=
    (hstep.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hacc : PolyTimeComputable fun st =>
      [decide ((pairFstD (pairFstD st)).length ≤ (pairSndD (pairSndD st)).length)] :=
    lenLe_comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hout : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have h := stateFind hstart hstep' hacc hout .var
    (.add (.mul (.const 2) B) (.add (.const 2) .var)) (fun x₀ => (pairFstD x₀).length)
    (fun x₀ => length_pairFstD_le x₀)
    (fun x₀ k hk => by
      rw [horbit, length_pairEncode, List.length_replicate]
      have hk' : k ≤ (pairFstD x₀).length := hk
      have h1 := hbound x₀ k hk'
      have h2 := length_pairFstD_le x₀
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega)
    (fun x₀ k hk => by
      show decide ((pairFstD (pairFstD (pairEncode x₀ _))).length ≤
        (pairSndD (pairSndD (pairEncode x₀ _))).length) = false
      rw [horbit, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      simpa using hk)
    (fun x₀ => by
      show decide ((pairFstD (pairFstD (pairEncode x₀ _))).length ≤
        (pairSndD (pairSndD (pairEncode x₀ _))).length) = true
      rw [horbit, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      simp)
  refine ptc_congr h fun x₀ => ?_
  rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]

/-! ### The verifier of the `|x|`-fold graph non-isomorphism protocol -/

/-- The number of messages of the layout's history, in unary. -/
theorem cnt_poly : PolyTimeComputable fun w => List.replicate (msgCount (argM w)) true :=
  msgCount_poly.comp argM_poly

/-- The test `|hist| < |x|` (the protocol is not over), as the negated length comparison of
`1^{|x|}` with the message count. -/
theorem ltLen_poly : PolyTimeComputable fun w => [decide (msgCount (argM w) < (NUPPT.inParam w).length)] := by
  refine ptc_congr (not_poly (lenLe_comp cnt_poly NUPPT.polyTimeComputable_inParam)) fun w => ?_
  simp only [List.length_replicate]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The coin polynomial of one iteration of the graph non-isomorphism protocol,
`1 + (N + 1)²`. -/
def gniBlock : PolyExpr := .add (.const 1) (.normal 1 2)

/-- The block length evaluates to `1 + (N + 1)²`. -/
theorem gniBlock_eval (N : ℕ) : gniBlock.eval N = 1 + (N + 1) ^ 2 := by
  simp [gniBlock, PolyExpr.eval_normal]

/-- The coin block of the current iteration of the `|x|`-fold graph non-isomorphism verifier:
`coinSlice (1 + (|x|+1)²) |hist| r`. -/
theorem gniSlice_poly : PolyTimeComputable fun w =>
    coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w) :=
  ptc_congr (coinSlice_poly gniBlock NUPPT.polyTimeComputable_inParam cnt_poly
    NUPPT.polyTimeComputable_inCoins) fun w => by simp

/-- One round of the verdict scan of the `|x|`-fold graph non-isomorphism verifier, on the
state word `⟨x₀, ⟨remMsgs, ⟨remCoins, [bit]⟩⟩⟩` (with `x₀ = ⟨1^{|x|}, …⟩`): peel one message,
drop one coin block, and conjoin the comparison of the message's first bit with the block's
first bit. -/
def gniStep (st : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD (pairSndD st)))
    (pairEncode ((pairFstD (pairSndD (pairSndD st))).drop (gniBlock.eval (pairFstD (pairFstD st)).length))
      [(pairSndD (pairSndD (pairSndD st))).headD false &&
        decide ((pairFstD (pairFstD (pairSndD st))).headD false =
          (pairFstD (pairSndD (pairSndD st))).headD false)])

/-- The scan round is polynomial-time. -/
theorem gniStep_poly : PolyTimeComputable gniStep := by
  have hM : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hR : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hB : PolyTimeComputable fun st => pairSndD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hu : PolyTimeComputable fun st => pairFstD (pairFstD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun st =>
      (pairFstD (pairSndD (pairSndD st))).drop (gniBlock.eval (pairFstD (pairFstD st)).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly gniBlock).comp (hu.pairEncode hR)) fun st => by simp
  have hbit : PolyTimeComputable fun st => [(pairSndD (pairSndD (pairSndD st))).headD false &&
      decide ((pairFstD (pairFstD (pairSndD st))).headD false = (pairFstD (pairSndD (pairSndD st))).headD false)] :=
    polyTimeComputable_and (headBit_poly.comp hB)
      (ptc_congr (polyTimeComputable_pairEq.comp
        ((headBit_poly.comp (polyTimeComputable_pairFstD.comp hM)).pairEncode (headBit_poly.comp hR)))
        fun st => by simp)
  exact (polyTimeComputable_pairSndD.comp hM).pairEncode (hdrop.pairEncode hbit)

/-- The scan after `k` rounds from the input `⟨u, ⟨M, ⟨R, [b]⟩⟩⟩` (with `c = 1 + (|u|+1)²`):
the remaining messages, the remaining coins and the conjunction of the first `k` comparisons
with the initial bit `b`. -/
theorem gniIter_eq (u M R : List Bool) (b : Bool) (k : ℕ) :
    (fun s => gniStep (pairEncode (pairEncode u (pairEncode M (pairEncode R [b]))) s))^[k]
        (pairSndD (pairEncode u (pairEncode M (pairEncode R [b])))) =
      pairEncode (pairSndD^[k] M) (pairEncode (R.drop (k * gniBlock.eval u.length))
        [b && decide (∀ j < k, (pairFstD (pairSndD^[j] M)).headD false =
          (R.drop (j * gniBlock.eval u.length)).headD false)]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [gniStep, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, List.drop_drop,
      Function.iterate_succ_apply', Nat.forall_lt_succ_right, Bool.decide_and, Bool.and_assoc, Nat.succ_mul]

/-- The scan from an arbitrary input has, after at least one round, the shape of `gniIter_eq`
with the components read off the input (the bit being unspecified). -/
theorem gniIter_shape (x₀ : List Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : Bool, (fun s => gniStep (pairEncode x₀ s))^[k] (pairSndD x₀) =
      pairEncode (pairSndD^[k] (pairFstD (pairSndD x₀)))
        (pairEncode ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)) [b]) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨(pairSndD (pairSndD (pairSndD x₀))).headD false &&
        decide ((pairFstD (pairFstD (pairSndD x₀))).headD false = (pairFstD (pairSndD (pairSndD x₀))).headD false),
        by simp only [Nat.zero_add, Function.iterate_one, gniStep, pairFstD_pairEncode, pairSndD_pairEncode,
          Nat.one_mul]⟩
    · obtain ⟨b, hb⟩ := ih hpos
      refine ⟨b && decide ((pairFstD (pairSndD^[k] (pairFstD (pairSndD x₀)))).headD false =
        ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)).headD false), ?_⟩
      rw [Function.iterate_succ_apply', hb]
      simp only [gniStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop,
        Function.iterate_succ_apply', Nat.succ_mul, List.headD_cons]

/-- The scan states are bounded by `4|x₀| + 5`. -/
theorem gniIter_bound (x₀ : List Bool) (k : ℕ) :
    ((fun s => gniStep (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤
      (PolyExpr.add (.mul (.const 4) .var) (.const 5)).eval x₀.length := by
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := length_pairSndD_le x₀
    simp only [Function.iterate_zero, id]
    omega
  · obtain ⟨b, hb⟩ := gniIter_shape x₀ k hk
    rw [hb, length_pairEncode, length_pairEncode, List.length_singleton]
    have h1 := length_iterate_le length_pairSndD_le (pairFstD (pairSndD x₀)) k
    have h2 : (pairFstD (pairSndD x₀)).length ≤ x₀.length :=
      (length_pairFstD_le _).trans (length_pairSndD_le _)
    have h3 : ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)).length ≤
        x₀.length := by
      rw [List.length_drop]
      exact (Nat.sub_le _ _).trans
        ((length_pairFstD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _)))
    omega

/-- The verdict scan of the `|x|`-fold graph non-isomorphism verifier is polynomial-time: the
one-bit word `[decide (∀ j < |x|, bit of message j = bit of coin block j)]`
(`iterUnary_poly` on `gniStep` from `⟨1^{|x|}, ⟨msgs, ⟨r, [true]⟩⟩⟩`, closed form `gniIter_eq`). -/
theorem gniScan_poly : PolyTimeComputable fun w =>
    [decide (∀ j < (NUPPT.inParam w).length, (pairFstD (pairSndD^[j] (argM w))).headD false =
      ((NUPPT.inCoins w).drop (j * gniBlock.eval (NUPPT.inParam w).length)).headD false)] := by
  have hx₀ : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inParam w) (pairEncode (argM w) (pairEncode (NUPPT.inCoins w) [true])) :=
    NUPPT.polyTimeComputable_inParam.pairEncode (argM_poly.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const [true])))
  have h := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
    ((iterUnary_poly gniStep_poly _ (fun x₀ k _ => gniIter_bound x₀ k)).comp hx₀)
  refine ptc_congr h fun w => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode]
  rw [gniIter_eq, pairSndD_pairEncode, pairSndD_pairEncode, Bool.true_and]

/-- The first bit of a nonempty prefix is the first bit of the word. -/
theorem headD_take {c : ℕ} (hc : 0 < c) (l : List Bool) : (l.take c).headD false = l.headD false := by
  cases l with
  | nil => simp
  | cons a l =>
    cases c with
    | zero => omega
    | succ c => simp

/-- An entry of a list with default is the first entry of the corresponding suffix. -/
theorem getD_eq_headD_drop {α : Type*} (l : List α) (j : ℕ) (d : α) : l.getD j d = (l.drop j).headD d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The verdict condition of the `|x|`-fold graph non-isomorphism verifier, read through the
scan: message `j` is `pairFstD (pairSndD^[j] msgs)` and the first bit of coin block `j` is the
first bit of `r.drop (j c)`. -/
theorem gni_verdict_iff (hist : List (List Bool)) (r : List Bool) (N c : ℕ) (hc : 0 < c) :
    (∀ j : Fin N, (hist.getD j []).headD false = (coinSlice c j r).headD false) ↔
      ∀ j < N, (pairFstD (pairSndD^[j] (Strategy.encodeMsgs hist))).headD false =
        (r.drop (j * c)).headD false := by
  rw [Fin.forall_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, coinSlice, headD_take hc, Fin.val_mk,
    getD_eq_headD_drop]

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the message count `1^{|hist|}` (`cnt_poly`), the
test `|hist| < |x|` (`ltLen_poly`), the coin block of the current iteration (`gniSlice_poly`)
and the message `relabel_poly` of `G_b` by the sampled permutation on the one hand, the
well-formedness test conjoined with the verdict scan (`gniScan_poly`) on the other; the
equation with `gniVerifierRep.next` is `msgCount_encodeMsgs`, `gniBlock_eval` and
`gni_verdict_iff`. -/
theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := by
  have hri := gniSlice_poly
  have hsel : PolyTimeComputable fun w =>
      if (coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w)).headD false
        then pairSndD (argX w) else pairFstD (argX w) :=
    polyTimeComputable_ite (headBit_poly.comp hri) w₁_poly w₀_poly
  have hσ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w))
      (coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w)).tail :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode (tail_poly.comp hri))) fun w => by simp
  have hmsg := relabel_poly hsel hσ
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf gniScan_poly
  refine efficient_of_polyTime gniVerifierRep (polyTimeComputable_ite ltLen_poly hmsg hverdict) ?_
  intro x z r hist
  show (if hist.length < x.length then _ else _) = _
  simp only [argM_ilayout, msgCount_encodeMsgs, inParam_ilayout, List.length_replicate, inCoins_ilayout,
    argX_ilayout, vcount_ilayout, gniBlock_eval, decide_eq_true_eq]
  by_cases hlt : hist.length < x.length
  · rw [if_pos hlt, if_pos hlt, relabelAt_replicate, sampleStr, decPerm_encPerm, List.drop_one]
    split_ifs <;> rfl
  · rw [if_neg hlt, if_neg hlt, Bool.decide_and, Bool.decide_eq_true]
    congr 2
    exact decide_eq_decide.2 (gni_verdict_iff hist r x.length _ (by positivity))

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph isomorphism protocol: efficiency of the parties

The polynomial-time machines behind the parties of the `|x|`-fold graph isomorphism protocol
[PS10, Protocol 120.6, repeated] (`giProverRep`, `giVerifierRep`; inventory item Inf-4.2),
proved for the shadow strategies of `GraphIsomorphism/Proofs.lean` with the loop
infrastructure of `GraphIsomorphism/EfficiencyRep.lean`: the half count and parity of the
history (`halfLoop_poly`), the last message received (`lastMsg_poly`), the coin block of the
current iteration (`coinSlice_poly`), and the verdict scan over the `|x|` iterations
(`iterUnary_poly` on `giStep`).

## Main definitions

* `TCSlib.Cryptography.GI.giBlock` — the coin polynomial `(N + 1)²` of one iteration.
* `TCSlib.Cryptography.GI.giStep` — one round of the verifier's verdict scan.

## Main results

* `TCSlib.Cryptography.GI.giProverRep_efficient`, `GI.giVerifierRep_efficient` — the parties of
  the `|x|`-fold graph isomorphism protocol are PPT strategies.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### The prover of the `|x|`-fold graph isomorphism protocol -/

/-- The coin polynomial of one iteration of the graph isomorphism protocol, `(N + 1)²`. -/
def giBlock : PolyExpr := .normal 1 2

/-- The block length evaluates to `(N + 1)²`. -/
theorem giBlock_eval (N : ℕ) : giBlock.eval N = (N + 1) ^ 2 := by
  simp [giBlock, PolyExpr.eval_normal]

/-- The half count of the layout's history, in unary. -/
theorem halfCnt_poly : PolyTimeComputable fun w => List.replicate (halfCount (argM w)) true :=
  ptc_congr (polyTimeComputable_pairSndD.comp (halfLoop_poly.comp argM_poly)) fun w => by simp

/-- The remainder of the half loop on the layout's history (empty exactly for an even number of
messages). -/
theorem halfRem_poly : PolyTimeComputable fun w =>
    (fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) :=
  ptc_congr (polyTimeComputable_pairFstD.comp (halfLoop_poly.comp argM_poly)) fun w => by simp

/-- The parity test "an even number of messages" of the layout. -/
theorem even_poly : PolyTimeComputable fun w =>
    [decide ((fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) = [])] :=
  isNil_poly.comp halfRem_poly

/-- The parity test "an odd number of messages" of the layout. -/
theorem odd_poly : PolyTimeComputable fun w =>
    [decide (¬ (fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) = [])] :=
  ptc_congr (not_poly even_poly) fun w => by simp only [decide_not]

/-- The remainder of the half loop on `encodeMsgs hist` (after `|hist| / 2` rounds) is empty iff
`|hist|` is even. -/
theorem halfRem_nil_iff (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[hist.length / 2] (Strategy.encodeMsgs hist) = [] ↔
      hist.length % 2 = 0 := by
  rw [iterate_sndD_two_encodeMsgs, encodeMsgs_eq_nil_iff, List.drop_eq_nil_iff]
  omega

/-- The remainder of the half loop on `encodeMsgs hist` is nonempty iff `|hist|` is odd. -/
theorem halfRem_ne_nil_iff (hist : List (List Bool)) :
    (¬ (fun v => pairSndD (pairSndD v))^[hist.length / 2] (Strategy.encodeMsgs hist) = []) ↔
      hist.length % 2 = 1 := by
  rw [halfRem_nil_iff]
  omega

/-- The coin block of the current iteration of the `|x|`-fold graph isomorphism prover:
`coinSlice ((|x|+1)²) (|hist| / 2) r`. -/
theorem giSlice_poly : PolyTimeComputable fun w =>
    coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w) :=
  ptc_congr (coinSlice_poly giBlock NUPPT.polyTimeComputable_inParam halfCnt_poly
    NUPPT.polyTimeComputable_inCoins) fun w => by simp

/-- The first bit of the last message of the layout's history. -/
theorem lastBit_poly : PolyTimeComputable fun w =>
    [(pairFstD (pairSndD^[lastSteps (argM w)] (argM w))).headD false] :=
  headBit_poly.comp (lastMsg_poly.comp argM_poly)

/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the half count `|hist| / 2` and the parity by the
half loop (`halfLoop_poly`), the coin block of the current iteration (`giSlice_poly`), the
sampled permutation (`sampleStr_poly`), the graph message by `relabel_poly` and the reply by
`mulInvStr_poly` or the identity according to the first bit of the last message
(`lastMsg_poly`); the equation with `giProverRep.next` is `halfCount_encodeMsgs`,
`halfRem_nil_iff` and `lastMsg_encodeMsgs`. -/
theorem giProverRep_efficient : giProverRep.Efficient := by
  have hπ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w))
      (coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w)) :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode giSlice_poly)) fun w => by simp
  have heven := relabel_poly w₀_poly hπ
  have hmul : PolyTimeComputable fun w => mulInvStr (sampleStr (pairFstD (argX w))
      (coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w))) (argZ w) :=
    ptc_congr (mulInvStr_poly.comp (hπ.pairEncode argZ_poly)) fun w => by simp
  have hodd := polyTimeComputable_ite lastBit_poly hmul hπ
  refine efficient_of_polyTime giProverRep (polyTimeComputable_ite even_poly heven hodd) ?_
  intro x z r hist
  show (if hist.length % 2 = 0 then _ else _) = _
  simp only [argM_ilayout, halfCount_encodeMsgs, halfRem_nil_iff, inParam_ilayout, List.length_replicate,
    inCoins_ilayout, argX_ilayout, argZ_ilayout, vcount_ilayout, giBlock_eval, decide_eq_true_eq,
    lastMsg_encodeMsgs]
  by_cases hev : hist.length % 2 = 0
  · rw [if_pos hev, if_pos hev, relabelAt_replicate, sampleStr, decPerm_encPerm]
    rfl
  · rw [if_neg hev, if_neg hev, sampleStr, mulInvStr_encPerm]
    split_ifs <;> rfl

/-! ### The verifier of the `|x|`-fold graph isomorphism protocol -/

/-- The test `|hist| < 2|x|` (the iterations are not over). -/
theorem ltLen2_poly : PolyTimeComputable fun w =>
    [decide (msgCount (argM w) < (PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam w).length)] := by
  refine ptc_congr (not_poly (lenLe_comp cnt_poly
    (unaryPoly_comp (.mul (.const 2) .var) NUPPT.polyTimeComputable_inParam))) fun w => ?_
  simp only [List.length_replicate]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The challenge of the `|x|`-fold graph isomorphism verifier: coin `|hist| / 2`. -/
theorem challenge_poly : PolyTimeComputable fun w =>
    [((NUPPT.inCoins w).drop (halfCount (argM w))).headD false] :=
  ptc_congr (headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp
    (halfCnt_poly.pairEncode NUPPT.polyTimeComputable_inCoins))) fun w => by simp

/-- One round of the verdict scan of the `|x|`-fold graph isomorphism verifier, on the state
word `⟨x₀, ⟨S, ⟨remMsgs, ⟨remCoins, [bit]⟩⟩⟩⟩` with the static data `S = ⟨1^n, x⟩`: peel two
messages `H, γ`, drop one coin `b`, and conjoin the check `γ(G_b) = H`. -/
noncomputable def giStep (st : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD st))
    (pairEncode (pairSndD (pairSndD (pairFstD (pairSndD (pairSndD st)))))
      (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD st)))).tail
        [(pairSndD (pairSndD (pairSndD (pairSndD st)))).headD false &&
          decide (relabelAt (pairFstD (pairFstD (pairSndD st)))
            (if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
              pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))))
            (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD st))))) =
              pairFstD (pairFstD (pairSndD (pairSndD st))))]))

/-- The scan round is polynomial-time.

**Proof sketch.** Projections of the state word, `relabelAt_poly` on `⟨1^n, ⟨G_b, γ⟩⟩` with
`G_b` selected by `polyTimeComputable_ite` on the first coin, the comparison with `H` by
`polyTimeComputable_pairEq`, and the conjunction with the carried bit
(`polyTimeComputable_and`). -/
theorem giStep_poly : PolyTimeComputable giStep := by
  have hS : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hM : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hC : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD (pairSndD st))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hB : PolyTimeComputable fun st => pairSndD (pairSndD (pairSndD (pairSndD st))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hsel : PolyTimeComputable fun st =>
      if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
        pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))) :=
    polyTimeComputable_ite (headBit_poly.comp hC)
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hS))
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hS))
  have hcheck : PolyTimeComputable fun st => [decide (relabelAt (pairFstD (pairFstD (pairSndD st)))
      (if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
        pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))))
      (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD st))))) = pairFstD (pairFstD (pairSndD (pairSndD st))))] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabelAt_poly.comp
      ((polyTimeComputable_pairFstD.comp hS).pairEncode
        (hsel.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hM))))).pairEncode
      (polyTimeComputable_pairFstD.comp hM))) fun st => by simp
  exact hS.pairEncode ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM)).pairEncode
    ((tail_poly.comp hC).pairEncode (polyTimeComputable_and (headBit_poly.comp hB) hcheck)))

/-- The scan after `k` rounds from the input `⟨u, ⟨S, ⟨M, ⟨R, [b]⟩⟩⟩⟩`: the static data, the
remaining messages (two peeled per round), the remaining coins and the conjunction of the first
`k` checks with the initial bit `b`. -/
theorem giIter_eq (u S M R : List Bool) (b : Bool) (k : ℕ) :
    (fun s => giStep (pairEncode (pairEncode u (pairEncode S (pairEncode M (pairEncode R [b])))) s))^[k]
        (pairSndD (pairEncode u (pairEncode S (pairEncode M (pairEncode R [b]))))) =
      pairEncode S (pairEncode ((fun v => pairSndD (pairSndD v))^[k] M) (pairEncode (R.drop k)
        [b && decide (∀ j < k, relabelAt (pairFstD S)
          (if (R.drop j).headD false then pairSndD (pairSndD S) else pairFstD (pairSndD S))
          (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] M))) =
            pairFstD ((fun v => pairSndD (pairSndD v))^[j] M))])) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [giStep, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, List.tail_drop,
      Function.iterate_succ_apply', Nat.forall_lt_succ_right, Bool.decide_and, Bool.and_assoc]

/-- The scan from an arbitrary input has, after at least one round, the shape of `giIter_eq`
with the components read off the input (the bit being unspecified).

**Proof sketch.** Induction on the number of rounds: the first round reads the components off
the input word; every later round peels two messages, drops one coin and keeps the static
data (`List.tail_drop`, `Function.iterate_succ_apply'`). -/
theorem giIter_shape (x₀ : List Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : Bool, (fun s => giStep (pairEncode x₀ s))^[k] (pairSndD x₀) =
      pairEncode (pairFstD (pairSndD x₀))
        (pairEncode ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀))))
          (pairEncode ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k) [b])) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨(pairSndD (pairSndD (pairSndD (pairSndD x₀)))).headD false &&
        decide (relabelAt (pairFstD (pairFstD (pairSndD x₀)))
          (if (pairFstD (pairSndD (pairSndD (pairSndD x₀)))).headD false then
            pairSndD (pairSndD (pairFstD (pairSndD x₀))) else pairFstD (pairSndD (pairFstD (pairSndD x₀))))
          (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD x₀))))) = pairFstD (pairFstD (pairSndD (pairSndD x₀)))),
        by simp only [Nat.zero_add, Function.iterate_one, giStep, pairSndD_pairEncode, List.drop_one]⟩
    · obtain ⟨b, hb⟩ := ih hpos
      refine ⟨b && decide (relabelAt (pairFstD (pairFstD (pairSndD x₀)))
        (if ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k).headD false then
          pairSndD (pairSndD (pairFstD (pairSndD x₀))) else pairFstD (pairSndD (pairFstD (pairSndD x₀))))
        (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀)))))) =
          pairFstD ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀))))), ?_⟩
      rw [Function.iterate_succ_apply', hb]
      simp only [giStep, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
        Function.iterate_succ_apply', List.headD_cons]

/-- The scan states are bounded by `6|x₀| + 7`.

**Proof sketch.** Round `0` is `pairSndD x₀`; afterwards the shape `giIter_shape` has three
components (`static`, remaining messages, remaining coins), each no longer than `x₀`
(`length_pairFstD_le`, `length_pairSndD_le`, `List.length_drop`), and one bit. -/
theorem giIter_bound (x₀ : List Bool) (k : ℕ) :
    ((fun s => giStep (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤
      (PolyExpr.add (.mul (.const 6) .var) (.const 7)).eval x₀.length := by
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := length_pairSndD_le x₀
    simp only [Function.iterate_zero, id]
    omega
  · obtain ⟨b, hb⟩ := giIter_shape x₀ k hk
    rw [hb, length_pairEncode, length_pairEncode, length_pairEncode, List.length_singleton]
    have h0 : (pairFstD (pairSndD x₀)).length ≤ x₀.length :=
      (length_pairFstD_le _).trans (length_pairSndD_le _)
    have h1 := length_iterate_le (fun w => (length_pairSndD_le _).trans (length_pairSndD_le w))
      (pairFstD (pairSndD (pairSndD x₀))) k
    have h2 : (pairFstD (pairSndD (pairSndD x₀))).length ≤ x₀.length :=
      (length_pairFstD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _))
    have h3 : ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k).length ≤ x₀.length := by
      rw [List.length_drop]
      exact (Nat.sub_le _ _).trans ((length_pairFstD_le _).trans
        ((length_pairSndD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _))))
    omega

/-- The verdict scan of the `|x|`-fold graph isomorphism verifier is polynomial-time: the
one-bit word `[decide (∀ j < |x|, γ_j(G_{b_j}) = H_j)]` (`iterUnary_poly` on `giStep` from
`⟨1^{|x|}, ⟨⟨1^n, x⟩, ⟨msgs, ⟨r, [true]⟩⟩⟩⟩`, closed form `giIter_eq`). -/
theorem giScan_poly : PolyTimeComputable fun w =>
    [decide (∀ j < (NUPPT.inParam w).length, relabelAt (List.replicate (vcount w) true)
      (if ((NUPPT.inCoins w).drop j).headD false then pairSndD (argX w) else pairFstD (argX w))
      (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] (argM w)))) =
        pairFstD ((fun v => pairSndD (pairSndD v))^[j] (argM w)))] := by
  have hx₀ : PolyTimeComputable fun w => pairEncode (NUPPT.inParam w)
      (pairEncode (pairEncode (List.replicate (vcount w) true) (argX w))
        (pairEncode (argM w) (pairEncode (NUPPT.inCoins w) [true]))) :=
    NUPPT.polyTimeComputable_inParam.pairEncode ((vcount_poly.pairEncode argX_poly).pairEncode
      (argM_poly.pairEncode (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const [true]))))
  have h := (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)).comp
    ((iterUnary_poly giStep_poly _ (fun x₀ k _ => giIter_bound x₀ k)).comp hx₀)
  refine ptc_congr h fun w => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode]
  rw [giIter_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, Bool.true_and,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- The verdict condition of the `|x|`-fold graph isomorphism verifier, read through the scan:
messages `2j` and `2j+1` are the two components of `(pairSndD ∘ pairSndD)^[j] msgs`, coin `j` is
the first bit of `r.drop j`, and `relabelAt` is `encGraph (γ(G_b))`. -/
theorem gi_verdict_iff (x : List Bool) (hist : List (List Bool)) (r : List Bool) (N : ℕ) :
    (∀ j : Fin N, encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm (instanceVertexCount x) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) []) ↔
      ∀ j < N, relabelAt (List.replicate (Nat.sqrt (pairFstD x).length) true)
        (if (r.drop j).headD false then pairSndD x else pairFstD x)
        (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] (Strategy.encodeMsgs hist)))) =
          pairFstD ((fun v => pairSndD (pairSndD v))^[j] (Strategy.encodeMsgs hist)) := by
  rw [Fin.forall_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [Fin.val_mk, iterate_sndD_two_encodeMsgs, pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs,
    Strategy.pairFstD_encodeMsgs, List.drop_drop, relabelAt_replicate, ← getD_eq_headD_drop,
    ← getD_eq_headD_drop, ← getD_eq_headD_drop]
  cases r.getD j false <;> exact Iff.rfl

/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the parity of the message count (`odd_poly`), the
challenge `r_{|hist|/2}` (`challenge_poly`), the test `|hist| < 2|x|` (`ltLen2_poly`), and the
well-formedness test conjoined with the verdict scan (`giScan_poly`); the equation with
`giVerifierRep.next` is `halfRem_ne_nil_iff`, `halfCount_encodeMsgs`, `msgCount_encodeMsgs` and
`gi_verdict_iff`. -/
theorem giVerifierRep_efficient : giVerifierRep.Efficient := by
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf giScan_poly
  have hF := polyTimeComputable_ite odd_poly challenge_poly
    (polyTimeComputable_ite ltLen2_poly (polyTimeComputable_const []) hverdict)
  refine efficient_of_polyTime giVerifierRep hF ?_
  intro x z r hist
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  simp only [argM_ilayout, halfCount_encodeMsgs, halfRem_ne_nil_iff, msgCount_encodeMsgs, inParam_ilayout,
    List.length_replicate, inCoins_ilayout, argX_ilayout, vcount_ilayout, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_var, decide_eq_true_eq]
  by_cases hodd : hist.length % 2 = 1
  · rw [if_pos hodd, if_pos hodd, getD_eq_headD_drop]
  · rw [if_neg hodd, if_neg hodd]
    by_cases hlt : hist.length < 2 * x.length
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt, Bool.decide_and, Bool.decide_eq_true]
      congr 2
      exact decide_eq_decide.2 (gi_verdict_iff x hist r x.length)

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: shadow definitions and generic proof infrastructure

Proof infrastructure for `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism` ([PS10, §4.5],
Protocols 118.3 and 120.6). That file is at the file-size limit, so the proofs of its
theorems live in the sibling files `GraphIsomorphism/Proofs.lean` (this file),
`GraphIsomorphism/Efficiency.lean` and `GraphIsomorphism/Soundness.lean`, which the main
file imports. An imported file cannot refer to the main file's definitions, so this file
restates them **verbatim** in the inner namespace `TCSlib.Cryptography.GI` (the *shadow*
definitions): every shadow is definitionally equal to its original, and the main file closes
each of its targets by `exact GI.…`, which type-checks by `rfl`. The shadows are proof
devices, not public API; they must be kept in sync with the frozen definitions of the main
file (any divergence makes the main file's `exact` fail to type-check, so a divergence cannot
go unnoticed).

Besides the shadows, this file holds the generic infrastructure shared by the efficiency and
the soundness proofs: the decode/encode identities on a given vertex count, the
characterisation of well-formed instances, the transcripts of the single-iteration protocols,
the bit/tape bijections used to read a verifier's random tape as (challenge bit, sampler
coins), the fact that the permutation sampler reads only a prefix of its tape, and the
shadow copies of the concrete probability lemmas of the main file that the soundness proofs
need (Lem-119.a, Lem-120.b–c, the honest replies).

## Main definitions

* `TCSlib.Cryptography.GI.Isomorphic`, `GI.decGraphAt`, `GI.encInstance`,
  `GI.instanceVertexCount`, `GI.instanceG₀`, `GI.instanceG₁`, `GI.wellFormedInstance`,
  `GI.instanceVertices`, `GI.Liso`, `GI.Lniso`, `GI.Riso`, `GI.samplePerm`, `GI.permCoinLen`,
  `GI.permFailBound`, `GI.coinSlice` — shadows of the definitions of the main file.
* `TCSlib.Cryptography.GI.gniProver`, `GI.gniVerifier`, `GI.gniProtocol`, `GI.gniVerifierRep`,
  `GI.gniProtocolRep`, `GI.giProver`, `GI.giVerifier`, `GI.giProtocol`, `GI.giProverRep`,
  `GI.giVerifierRep`, `GI.giProtocolRep` — shadows of the strategies and protocols.
* `TCSlib.Cryptography.GI.tapeSplit` — a tape of `1 + c` bits as a bit and a tape of `c` bits.

## Main results

* `TCSlib.Cryptography.GI.encGraph_decGraphAt`, `GI.eq_encInstance_of_wellFormed` — a word of
  length `n²` is the encoding of its decoding; a well-formed instance is `encInstance` of its
  two graphs.
* `TCSlib.Cryptography.GI.efficient_of_polyTime` — a strategy whose next-message function is a
  polynomial-time function of the machine layout is efficient.
* `TCSlib.Cryptography.GI.gniProtocol_outV`, `GI.giProtocol_outV` and the `*_next_*` lemmas —
  the verdicts of the single-iteration protocols on encoded instances.
* `TCSlib.Cryptography.GI.pushesUniform_castLE`, `GI.statClose_samplePerm_long` — a prefix of a
  uniform tape is uniform, so the sampler is close to uniform on any tape long enough.
* `TCSlib.Cryptography.GI.uprob_guess_eq_half` — against isomorphic graphs the relabelled
  graph is independent of the challenge bit: any guess is right with probability exactly `1/2`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Shadow definitions (verbatim copies of `GraphIsomorphism.lean`) -/

/-- Shadow of `TCSlib.Cryptography.Isomorphic` (Def-117.e). -/
def Isomorphic {n : ℕ} (G₀ G₁ : Graph n) : Prop := ∃ σ : Equiv.Perm (Fin n), permGraph G₀ σ = G₁

/-- Shadow of the decidability instance of `Isomorphic`. -/
instance {n : ℕ} (G₀ G₁ : Graph n) : Decidable (Isomorphic G₀ G₁) := by
  unfold Isomorphic
  infer_instance

/-- Shadow of `TCSlib.Cryptography.decGraphAt`. -/
def decGraphAt (n : ℕ) (w : List Bool) : Graph n := fun u v => w.getD (finProdFinEquiv (u, v)) false

/-- Shadow of `TCSlib.Cryptography.encInstance`. -/
def encInstance {n : ℕ} (G₀ G₁ : Graph n) : List Bool := pairEncode (encGraph G₀) (encGraph G₁)

/-- Shadow of `TCSlib.Cryptography.instanceVertexCount`. -/
def instanceVertexCount (x : List Bool) : ℕ := Nat.sqrt (pairFstD x).length

/-- Shadow of `TCSlib.Cryptography.instanceG₀`. -/
def instanceG₀ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairFstD x)

/-- Shadow of `TCSlib.Cryptography.instanceG₁`. -/
def instanceG₁ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairSndD x)

/-- Shadow of `TCSlib.Cryptography.wellFormedInstance`. -/
def wellFormedInstance (x : List Bool) : Bool :=
  decide ((pairDecode x).isSome ∧ (pairFstD x).length = instanceVertexCount x * instanceVertexCount x ∧
    (pairSndD x).length = instanceVertexCount x * instanceVertexCount x)

/-- Shadow of `TCSlib.Cryptography.instanceVertices`. -/
def instanceVertices (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 3)

/-- Shadow of `TCSlib.Cryptography.Liso` (Def-118.a). -/
def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

/-- Shadow of `TCSlib.Cryptography.Lniso` (Def-118.a). -/
def Lniso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n), x = pairEncode (encGraph G₀) (encGraph G₁) ∧ ¬ Isomorphic G₀ G₁}

/-- Shadow of `TCSlib.Cryptography.Riso` (Def-118.a). -/
def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

/-- Shadow of `TCSlib.Cryptography.samplePerm` (D10). -/
noncomputable def samplePerm (n : ℕ) (r : List Bool) : Equiv.Perm (Fin n) :=
  (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1

/-- Shadow of `TCSlib.Cryptography.permCoinLen`. -/
def permCoinLen (n : ℕ) : ℕ := n * permTrials n * permBits n

/-- Shadow of `TCSlib.Cryptography.permFailBound`. -/
noncomputable def permFailBound (n : ℕ) : ℝ := n * (2 : ℝ)⁻¹ ^ n

/-- Shadow of `TCSlib.Cryptography.coinSlice`. -/
def coinSlice (c i : ℕ) (r : List Bool) : List Bool := (r.drop (i * c)).take c

/-- Shadow of `TCSlib.Cryptography.gniProver` [PS10, Protocol 118.3]. -/
def gniProver : Strategy where
  coins := .const 0
  next x _ _ hist :=
    [decide (¬ Isomorphic (instanceG₀ x) (decGraphAt (instanceVertexCount x) (hist.getLastD [])))]

/-- Shadow of `TCSlib.Cryptography.gniVerifier` [PS10, Protocol 118.3]. -/
noncomputable def gniVerifier : Strategy where
  coins := .add (.const 1) (.normal 1 2)
  next x _ r hist :=
    let b := r.headD false
    match hist with
    | [] => encGraph (permGraph (if b then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (r.drop 1)))
    | [b'] => [decide (wellFormedInstance x = true ∧ b'.headD false = b)]
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.gniProtocol` (Prot-118.3). -/
noncomputable def gniProtocol : Protocol where
  P := gniProver
  V := gniVerifier
  rounds := .const 2
  verifierFirst := true

/-- Shadow of `TCSlib.Cryptography.gniVerifierRep`. -/
noncomputable def gniVerifierRep : Strategy where
  coins := .mul .var (.add (.const 1) (.normal 1 2))
  next x _ r hist :=
    let c := 1 + (x.length + 1) ^ 2
    if hist.length < x.length then
      let ri := coinSlice c hist.length r
      encGraph (permGraph (if ri.headD false then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (ri.drop 1)))
    else
      [decide (wellFormedInstance x = true ∧
        ∀ j : Fin x.length, (hist.getD j []).headD false = (coinSlice c j r).headD false)]

/-- Shadow of `TCSlib.Cryptography.gniProtocolRep` (Prot-118.3). -/
noncomputable def gniProtocolRep : Protocol where
  P := gniProver
  V := gniVerifierRep
  rounds := .mul (.const 2) .var
  verifierFirst := true

/-- Shadow of `TCSlib.Cryptography.giProver` [PS10, Protocol 120.6]. -/
noncomputable def giProver : Strategy where
  coins := .normal 1 2
  next x y r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let σ := decPerm n y
    let π := samplePerm n r
    match hist with
    | [] => encGraph (permGraph G₀ π)
    | _ :: _ => encPerm (if (hist.headD []).headD false then π * σ⁻¹ else π)

/-- Shadow of `TCSlib.Cryptography.giVerifier` [PS10, Protocol 120.6]. -/
noncomputable def giVerifier : Strategy where
  coins := .const 1
  next x _ r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let G₁ : Graph n := fun u v => (pairSndD x).getD (finProdFinEquiv (u, v)) false
    let b := r.headD false
    match hist with
    | [H, γ] => [decide (wellFormedInstance x = true ∧
        encGraph (permGraph (if b then G₁ else G₀) (decPerm n γ)) = H)]
    | [_] => [b]
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.giProtocol` (Prot-120.6). -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

/-- Shadow of `TCSlib.Cryptography.giProverRep`. -/
noncomputable def giProverRep : Strategy where
  coins := .mul .var (.normal 1 2)
  next x y r hist :=
    let n := instanceVertexCount x
    let σ := decPerm n y
    let π := samplePerm n (coinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)
    if hist.length % 2 = 0 then encGraph (permGraph (instanceG₀ x) π)
    else encPerm (if (hist.getLastD []).headD false then π * σ⁻¹ else π)

/-- Shadow of `TCSlib.Cryptography.giVerifierRep`. -/
noncomputable def giVerifierRep : Strategy where
  coins := .var
  next x _ r hist :=
    let n := instanceVertexCount x
    if hist.length % 2 = 1 then [r.getD (hist.length / 2) false]
    else if hist.length < 2 * x.length then []
    else [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
      encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm n (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])]

/-- Shadow of `TCSlib.Cryptography.giProtocolRep` (Prot-120.6). -/
noncomputable def giProtocolRep : Protocol where
  P := giProverRep
  V := giVerifierRep
  rounds := .mul (.const 4) .var
  verifierFirst := false

/-! ### Isomorphism algebra (shadow copies of the main file's lemmas) -/

/-- Every graph is isomorphic to itself. -/
theorem Isomorphic.refl {n : ℕ} (G : Graph n) : Isomorphic G G := ⟨1, permGraph_one G⟩

/-- Isomorphism is symmetric. -/
theorem Isomorphic.symm {n : ℕ} {G₀ G₁ : Graph n} (h : Isomorphic G₀ G₁) : Isomorphic G₁ G₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, permGraph_permGraph_inv]⟩

/-- Isomorphism is transitive. -/
theorem Isomorphic.trans {n : ℕ} {G₀ G₁ G₂ : Graph n} (h₁ : Isomorphic G₀ G₁)
    (h₂ : Isomorphic G₁ G₂) : Isomorphic G₀ G₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [← permGraph_mul, hσ, hτ]⟩

/-- A graph is isomorphic to each of its relabellings. -/
theorem isomorphic_permGraph {n : ℕ} (G : Graph n) (σ : Equiv.Perm (Fin n)) :
    Isomorphic G (permGraph G σ) := ⟨σ, rfl⟩

/-- A graph is isomorphic to at most one of two non-isomorphic graphs (Lem-120.b). -/
theorem not_isomorphic_both {n : ℕ} {G₀ G₁ H : Graph n} (h : ¬ Isomorphic G₀ G₁) :
    ¬ (Isomorphic G₀ H ∧ Isomorphic G₁ H) := fun ⟨h₀, h₁⟩ => h (h₀.trans h₁.symm)

/-- The honest prover's reply of the graph isomorphism protocol is accepted (Lem-120.a). -/
theorem gi_honest_reply_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) (b : Bool) :
    permGraph (cond b G₁ G₀) (if b then π * σ⁻¹ else π) = permGraph G₀ π := by
  cases b
  · rfl
  · exact permGraph_mul_inv_of_eq hσ π

/-- The honest prover of the graph non-isomorphism protocol recovers the bit (Lem-119.d). -/
theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (b : Bool)
    (σ : Equiv.Perm (Fin n)) :
    decide (¬ Isomorphic G₀ (permGraph (cond b G₁ G₀) σ)) = b := by
  cases b
  · exact decide_eq_false (not_not.2 (isomorphic_permGraph G₀ σ))
  · exact decide_eq_true fun h' => h (h'.trans (isomorphic_permGraph G₁ σ).symm)

/-! ### Encoded instances -/

/-- Decoding an encoded graph on its own vertex count gives the graph back. -/
@[simp] theorem decGraphAt_encGraph {n : ℕ} (G : Graph n) : decGraphAt n (encGraph G) = G :=
  funext fun u => funext fun v => encGraph_getD G u v

/-- A word of length `n²` is the encoding of its decoding on `n` vertices. -/
theorem encGraph_decGraphAt {n : ℕ} {w : List Bool} (h : w.length = n * n) :
    encGraph (decGraphAt n w) = w := by
  apply List.ext_getElem
  · simp [h]
  · intro k hk hk'
    simp only [encGraph, List.getElem_ofFn, decGraphAt, Prod.mk.eta, Equiv.apply_symm_apply]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]

/-- An encoded instance on `n` vertices has `3n² + 2` bits. -/
theorem length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : (encInstance G₀ G₁).length = 3 * (n * n) + 2 := by
  simp only [encInstance, length_pairEncode, length_encGraph]
  ring

/-- `instanceVertices` recovers `n` from the length of an encoded instance. -/
theorem instanceVertices_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertices (encInstance G₀ G₁).length = n := by
  rw [instanceVertices, length_encInstance, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.sqrt_eq]

/-- The vertex count decoded from an encoded instance is `n`. -/
theorem instanceVertexCount_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertexCount (encInstance G₀ G₁) = n := by
  simp [instanceVertexCount, encInstance, Nat.sqrt_eq]

/-- Encoded instances are well formed. -/
theorem wellFormedInstance_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    wellFormedInstance (encInstance G₀ G₁) = true := by
  simp [wellFormedInstance, encInstance, instanceVertexCount, Nat.sqrt_eq, pairDecode_pairEncode]

/-- A well-formed instance is the encoding of its two decoded graphs. -/
theorem eq_encInstance_of_wellFormed {x : List Bool} (h : wellFormedInstance x = true) :
    x = encInstance (instanceG₀ x) (instanceG₁ x) := by
  simp only [wellFormedInstance, decide_eq_true_eq] at h
  obtain ⟨hs, h0, h1⟩ := h
  obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.1 hs
  have hx := eq_pairEncode_of_pairDecode x a b hab
  rw [encInstance, instanceG₀, instanceG₁, encGraph_decGraphAt h0, encGraph_decGraphAt h1, hx,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- A well-formed instance is an encoded pair of graphs on a common vertex set. -/
theorem exists_eq_encInstance_of_wellFormed {x : List Bool} (h : wellFormedInstance x = true) :
    ∃ (n : ℕ) (G₀ G₁ : Graph n), x = encInstance G₀ G₁ :=
  ⟨_, _, _, eq_encInstance_of_wellFormed h⟩

/-- Equal encodings come from the same vertex count and the same graph. -/
theorem sigma_eq_of_encGraph_eq {n n' : ℕ} {G : Graph n} {G' : Graph n'}
    (h : encGraph G = encGraph G') : (⟨n, G⟩ : Σ m, Graph m) = ⟨n', G'⟩ := by
  rw [← decGraph_encGraph G, ← decGraph_encGraph G', h]

/-- An encoded instance is in `L_iso` exactly when its graphs are isomorphic. -/
theorem encInstance_mem_Liso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Liso ↔ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', σ, hx, hσ⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨n, G₀, G₁, σ, rfl, hσ⟩

/-- An encoded instance is in `L_niso` exactly when its graphs are not isomorphic. -/
theorem encInstance_mem_Lniso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Lniso ↔ ¬ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', hx, hni⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact hni
  · intro h
    exact ⟨n, G₀, G₁, rfl, h⟩

/-- `decGraph` of a word whose length has square root `n` is the pair `⟨n, decGraphAt n w⟩`. -/
theorem decGraph_eq_of_sqrt {w : List Bool} {n : ℕ} (h : Nat.sqrt w.length = n) :
    decGraph w = ⟨n, decGraphAt n w⟩ := by
  subst h
  rfl

/-- The decoding of the empty word is the identity permutation (the default row search
returns the row index). -/
theorem decPerm_nil (n : ℕ) : decPerm n [] = 1 := by
  unfold decPerm
  have hid : (fun i : Fin n =>
      (Fin.find (fun j : Fin n => ([] : List Bool).getD (finProdFinEquiv (i, j)) false = true)).getD i) =
      id := by
    funext i
    have hnone : Fin.find (fun j : Fin n => ([] : List Bool).getD (finProdFinEquiv (i, j)) false = true) =
        none :=
      Fin.find_eq_none_iff.2 fun j => by simp
    rw [hnone]
    rfl
  simp only [hid]
  rw [dif_pos Function.bijective_id]
  exact Equiv.ext fun _ => rfl

/-! ### Efficiency from a polynomial-time layout function -/

/-- The interactive machine layout of a strategy activation,
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`Strategy.ofNUPPT`, `NUPPT.runAtL`). -/
def ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) : List Bool :=
  NUPPT.layout (List.replicate x.length true)
    (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r

/-- A strategy whose next-message function is a polynomial-time function `F` of the machine
layout `ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` is efficient:
`NUPPT.ofPolyTimeUniform` of `F` with the strategy's coin polynomial is the uniform machine
computing it (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem efficient_of_polyTime (S : Strategy) {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (h : ∀ x z r hist, S.next x z r hist = F (ilayout x z hist r)) : S.Efficient :=
  ⟨NUPPT.ofPolyTimeUniform hF S.coins, NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => by
      rw [h, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-! ### Transcripts of the single-iteration protocols -/

/-- The verdict of the graph non-isomorphism protocol against a prover `P'`: the verifier's
reply to the single message `P'` sends after receiving `H`. -/
theorem gniProtocol_outV (P' : Strategy) (x y z : List Bool) (r : gniProtocol.ExecCoins P' x) :
    gniProtocol.outV P' x y z r =
      gniVerifier.next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [gniVerifier.next x z (List.ofFn r.2) []]] := by
  simp [Protocol.outV, Protocol.transcriptWith, gniProtocol, exec, moverIsV]

/-- The verdict of the graph isomorphism protocol against a prover `P'`: the verifier's output
on the two messages `H` and `γ` of `P'`, the second being its reply to the challenge. -/
theorem giProtocol_outV (P' : Strategy) (x y z : List Bool) (r : giProtocol.ExecCoins P' x) :
    giProtocol.outV P' x y z r =
      giVerifier.next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1) [giVerifier.next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := by
  simp [Protocol.outV, Protocol.transcriptWith, giProtocol, exec, moverIsV]

/-- The first message of the graph non-isomorphism verifier on an encoded instance:
`σ(G_b)` for the first coin `b` and `σ` sampled from the remaining coins. -/
theorem gniVerifier_next_nil {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) :
    gniVerifier.next (encInstance G₀ G₁) z r [] =
      encGraph (permGraph (cond (r.headD false) G₁ G₀) (samplePerm n (r.drop 1))) := by
  show encGraph (permGraph (if r.headD false then
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁)) else
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁)) (r.drop 1))) = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph]
  cases r.headD false <;> rfl

/-- The verdict of the graph non-isomorphism verifier on one reply. -/
theorem gniVerifier_next_one (x z r b' : List Bool) :
    gniVerifier.next x z r [b'] =
      [decide (wellFormedInstance x = true ∧ b'.headD false = r.headD false)] := rfl

/-- The challenge of the graph isomorphism verifier is its single coin. -/
theorem giVerifier_next_one (x z r H : List Bool) : giVerifier.next x z r [H] = [r.headD false] := rfl

/-- The verdict of the graph isomorphism verifier on an encoded instance:
`γ(G_b) = H` for the challenge `b`. -/
theorem giVerifier_next_two {n : ℕ} (G₀ G₁ : Graph n) (z r H γ : List Bool) :
    giVerifier.next (encInstance G₀ G₁) z r [H, γ] =
      [decide (encGraph (permGraph (cond (r.headD false) G₁ G₀) (decPerm n γ)) = H)] := by
  show [decide (wellFormedInstance (encInstance G₀ G₁) = true ∧
    encGraph (permGraph (if r.headD false then
      decGraphAt (decGraph (pairFstD (encInstance G₀ G₁))).1 (pairSndD (encInstance G₀ G₁)) else
      (decGraph (pairFstD (encInstance G₀ G₁))).2)
      (decPerm (decGraph (pairFstD (encInstance G₀ G₁))).1 γ)) = H)] = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _,
    decGraph_encGraph, wellFormedInstance_encInstance]
  simp only [decGraphAt_encGraph, true_and]
  cases r.headD false <;> rfl

/-- The first message of the graph isomorphism prover on an encoded instance: `π(G₀)`. -/
theorem giProver_next_nil {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) :
    giProver.next (encInstance G₀ G₁) y r [] = encGraph (permGraph G₀ (samplePerm n r)) := by
  show encGraph (permGraph (decGraph (pairFstD (encInstance G₀ G₁))).2
    (samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r)) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]

/-- The reply of the graph isomorphism prover with witness `encPerm σ` to the challenge `m`. -/
theorem giProver_next_cons {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r m : List Bool)
    (h : List (List Bool)) :
    giProver.next (encInstance G₀ G₁) (encPerm σ) r (m :: h) =
      encPerm (if m.headD false then samplePerm n r * σ⁻¹ else samplePerm n r) := by
  show encPerm (if ((m :: h).headD []).headD false then
      samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r *
        (decPerm (decGraph (pairFstD (encInstance G₀ G₁))).1 (encPerm σ))⁻¹
    else samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]
  simp only [decPerm_encPerm, List.headD_cons]

/-! ### Unfolding the single-iteration strategies on arbitrary inputs -/

/-- The graph isomorphism prover's first message, unfolded. -/
theorem giProver_next_nil' (x y r : List Bool) :
    giProver.next x y r [] =
      encGraph (permGraph (decGraph (pairFstD x)).2 (samplePerm (decGraph (pairFstD x)).1 r)) := rfl

/-- The graph isomorphism prover's reply, unfolded. -/
theorem giProver_next_cons' (x y r m : List Bool) (h : List (List Bool)) :
    giProver.next x y r (m :: h) =
      encPerm (if m.headD false then
        samplePerm (decGraph (pairFstD x)).1 r * (decPerm (decGraph (pairFstD x)).1 y)⁻¹
      else samplePerm (decGraph (pairFstD x)).1 r) := rfl

/-- The graph isomorphism verifier's verdict, unfolded. -/
theorem giVerifier_next_two' (x z r H γ : List Bool) :
    giVerifier.next x z r [H, γ] =
      [decide (wellFormedInstance x = true ∧ encGraph (permGraph
        (if r.headD false then decGraphAt (decGraph (pairFstD x)).1 (pairSndD x)
          else (decGraph (pairFstD x)).2) (decPerm (decGraph (pairFstD x)).1 γ)) = H)] := rfl

/-- The graph isomorphism verifier on the empty history. -/
theorem giVerifier_next_nil' (x z r : List Bool) : giVerifier.next x z r [] = [false] := rfl

/-- The graph isomorphism verifier on three or more messages. -/
theorem giVerifier_next_long' (x z r H γ m : List Bool) (t : List (List Bool)) :
    giVerifier.next x z r (H :: γ :: m :: t) = [false] := rfl

/-- The graph non-isomorphism verifier's first message, unfolded. -/
theorem gniVerifier_next_nil' (x z r : List Bool) :
    gniVerifier.next x z r [] =
      encGraph (permGraph (if r.headD false then decGraphAt (instanceVertexCount x) (pairSndD x)
        else decGraphAt (instanceVertexCount x) (pairFstD x))
        (samplePerm (instanceVertexCount x) (r.drop 1))) := rfl

/-- The graph non-isomorphism verifier on two or more replies. -/
theorem gniVerifier_next_long' (x z r b' m : List Bool) (t : List (List Bool)) :
    gniVerifier.next x z r (b' :: m :: t) = [false] := rfl

/-! ### Tapes: the first bit and the rest; prefixes -/

/-- A tape of `1 + c` bits as its first bit and the remaining `c` bits (`Fin.consEquiv` after
the cast `c + 1 = 1 + c`). -/
def tapeSplit (c : ℕ) : Bool × (Fin c → Bool) ≃ (Fin (1 + c) → Bool) :=
  (Fin.consEquiv fun _ => Bool).trans (Equiv.arrowCongr (finCongr (Nat.add_comm c 1)) (Equiv.refl Bool))

/-- The list of a split tape is the bit followed by the list of the rest. -/
theorem ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    List.ofFn (tapeSplit c (b, t)) = b :: List.ofFn t := by
  rw [List.ofFn_congr (Nat.add_comm 1 c), List.ofFn_succ]
  rfl

/-- The first bit of a split tape. -/
theorem headD_ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    (List.ofFn (tapeSplit c (b, t))).headD false = b := by
  rw [ofFn_tapeSplit, List.headD_cons]

/-- The rest of a split tape. -/
theorem drop_ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    (List.ofFn (tapeSplit c (b, t))).drop 1 = List.ofFn t := by
  rw [ofFn_tapeSplit, List.drop_one, List.tail_cons]

/-- Restricting a uniform tape of `c` bits to its first `m ≤ c` bits gives a uniform tape:
the tape is the pair (prefix, suffix) through `finSumFinEquiv`, and the first projection pushes
uniform to uniform. -/
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

/-- An entry of the list of a tape below its length. -/
theorem getD_ofFn_lt {c : ℕ} (t : Fin c → Bool) {i : ℕ} (hi : i < c) (d : Bool) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The index `(i T + t) k + j` of a coin-table entry is below `n T k`. -/
theorem coinTable_index_lt {n T k : ℕ} (i : Fin n) (t : Fin T) (j : Fin k) :
    ((i : ℕ) * T + t) * k + j < n * T * k := by
  have h1 : (i : ℕ) * T + t + 1 ≤ n * T := by
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have ht : (t : ℕ) + 1 ≤ T := t.isLt
    calc (i : ℕ) * T + t + 1 ≤ i * T + T := by omega
      _ = (i + 1) * T := by ring
      _ ≤ n * T := Nat.mul_le_mul_right T hi
  calc ((i : ℕ) * T + t) * k + j < ((i : ℕ) * T + t) * k + k := by omega
    _ = ((i : ℕ) * T + t + 1) * k := by ring
    _ ≤ n * T * k := Nat.mul_le_mul_right k h1

/-- The coin table of a tape only depends on the first `n T k` bits. -/
theorem coinTable_ofFn_castLE {n T k c : ℕ} (h : n * T * k ≤ c) (t : Fin c → Bool) :
    coinTable n T k (List.ofFn t) =
      coinTable n T k (List.ofFn fun i : Fin (n * T * k) => t (Fin.castLE h i)) := by
  funext i t' j
  simp only [coinTable_apply]
  rw [getD_ofFn_lt t (lt_of_lt_of_le (coinTable_index_lt i t' j) h),
    getD_ofFn_lt _ (coinTable_index_lt i t' j)]
  rfl

/-- The permutation sampler reads only the first `permCoinLen n` bits of its tape. -/
theorem samplePerm_ofFn_castLE {n c : ℕ} (h : permCoinLen n ≤ c) (t : Fin c → Bool) :
    samplePerm n (List.ofFn t) =
      samplePerm n (List.ofFn fun i : Fin (permCoinLen n) => t (Fin.castLE h i)) := by
  unfold samplePerm
  rw [coinTable_ofFn_castLE h t]
  rfl

/-- Shadow of `statClose_samplePerm`: the sampler is within `permFailBound n` of uniform. -/
theorem statClose_samplePerm (n : ℕ) :
    StatClose (fun r : Fin (permCoinLen n) → Bool => samplePerm n (List.ofFn r))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) :=
  (statClose_permFromCoins_two_pow n 1).comp_pushesUniform
    (pushesUniform_coinTable n (permTrials n) (permBits n))

/-- On any tape of at least `permCoinLen n` bits the sampler is within `permFailBound n` of a
uniform permutation (`samplePerm_ofFn_castLE`, `pushesUniform_castLE`). -/
theorem statClose_samplePerm_long {n c : ℕ} (h : permCoinLen n ≤ c) :
    StatClose (fun t : Fin c → Bool => samplePerm n (List.ofFn t))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) := by
  have := (statClose_samplePerm n).comp_pushesUniform (pushesUniform_castLE h)
  intro T
  have hT := this T
  simpa only [samplePerm_ofFn_castLE h] using hT

/-- Shadow of `permCoinLen_le`: the sampler fits in `(N + 1)²` bits once `2n² ≤ N`. -/
theorem permCoinLen_le {n N : ℕ} (h : 2 * (n * n) ≤ N) : permCoinLen n ≤ (N + 1) ^ 2 := by
  have hnn : n * n ≤ N := le_trans (Nat.le_mul_of_pos_left (n * n) two_pos) h
  calc permCoinLen n = n * (2 * n * n) * permBits n := rfl
    _ ≤ n * (2 * n * n) * n := Nat.mul_le_mul_left _ (permBits_le n)
    _ = (2 * (n * n)) * (n * n) := by ring
    _ ≤ N * N := Nat.mul_le_mul h hnn
    _ ≤ (N + 1) ^ 2 := by nlinarith

/-- The failure bound is nonnegative. -/
theorem permFailBound_nonneg (n : ℕ) : 0 ≤ permFailBound n := by
  unfold permFailBound
  positivity

/-! ### Concrete probability lemmas (shadow copies) -/

/-- Shadow of `uprob_permGraph_eq_of_isomorphic'` (Lem-119.a): `σ(G₁)` and `σ(G₀)` have the
same law when `G₀ ≅ G₁`. -/
theorem uprob_permGraph_eq_of_isomorphic' {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → Prop) :
    uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₁ σ)) =
      uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ)) := by
  rw [← uprob_comp_equiv (Equiv.mulRight σ₀) (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ))]
  congr 1
  funext σ
  simp [← hσ, permGraph_mul]

/-- Against isomorphic graphs the relabelled graph `σ(G_b)` is independent of the bit `b`, so
any guess `g` of `b` from `σ(G_b)` is right with probability exactly `1/2` [PS10, proof of
Proposition 118.4, "`H` is independent of `b`"]. -/
theorem uprob_guess_eq_half {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (g : Graph n → Bool) :
    uprob (fun z : Bool × Equiv.Perm (Fin n) => g (permGraph (cond z.1 G₁ G₀) z.2) = z.1) = 1 / 2 := by
  rw [uprob_bool_prod]
  simp only [cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic' hσ (fun K => g K = true)]
  have h : uprob (fun σ : Equiv.Perm (Fin n) => g (permGraph G₀ σ) = false) =
      uprob (fun σ : Equiv.Perm (Fin n) => ¬ g (permGraph G₀ σ) = true) :=
    OneWay.uprob_congr fun σ => by simp
  rw [h, uprob_not]
  ring

/-- Shadow of `uprob_gi_cheat_le_half` (Lem-120.c): against non-isomorphic graphs a prover
answers both challenges correctly for no coin string, so it is accepted with probability at
most `1/2`. -/
theorem uprob_gi_cheat_le_half {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : ρ → Graph n) (γ : Bool → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : Bool × ρ => permGraph (cond z.1 G₁ G₀) (γ z.1 z.2) = H z.2) ≤ 1 / 2 := by
  rw [uprob_bool_prod]
  have hsub : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) ≤
      uprob (fun r : ρ => ¬ permGraph (cond true G₁ G₀) (γ true r) = H r) := by
    refine uprob_mono fun r h0 h1 => ?_
    exact not_isomorphic_both h ⟨⟨γ false r, h0⟩, ⟨γ true r, h1⟩⟩
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    have h1 : uprob (fun r : ρ => permGraph (cond true G₁ G₀) (γ true r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0, h1]
    norm_num
  · rw [uprob_not] at hsub
    linarith

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: completeness and soundness of the single iterations

[PS10, Proposition 118.4] (one iteration of the graph non-isomorphism protocol, soundness
error `1/2 + n·2^{-n}`) and [PS10, Proposition 120.7] (one iteration of the graph isomorphism
protocol, soundness error `1/2`, efficient prover), proved for the shadow protocols of
`GraphIsomorphism/Proofs.lean`; the main file `ZeroKnowledge/GraphIsomorphism.lean` closes
`gni_interactiveProofErr` and `gi_efficientProverProofErr` by `exact GI.…` (the efficiency
clauses are passed in as hypotheses, so that this file does not depend on the machine
constructions of `GraphIsomorphism/Efficiency.lean`).

**Completeness** is exact (`uprob = 1`): on an encoded instance the honest verdict is `[true]`
for every pair of random tapes (`gni_honest_reply`, `gi_honest_reply_eq`), whatever the
rejection-sampled permutation. **Soundness** of the graph non-isomorphism iteration is the
statistical argument of the text: against isomorphic graphs the relabelled graph `σ(G_b)` is
independent of `b` (`uprob_guess_eq_half`), and the honest verifier's `σ` is within
`permFailBound n` of uniform on its tape (`statClose_samplePerm_long`), whence
`Pr[accept] ≤ 1/2 + permFailBound n` after fixing the prover's coins
(`Protocol.exists_proverCoins_le`). Soundness of the graph isomorphism iteration is
`uprob_gi_cheat_le_half` (Lem-120.c): a prover can answer at most one of the two challenges.
Malformed common inputs are rejected outright by the well-formedness test.

## Main definitions

* `TCSlib.Cryptography.GI.vTapeSplit`, `GI.giBitEquiv`, `GI.giCoinEquiv` — the verifiers' random
  tapes as (challenge bit, sampler coins) and the joint coins as (bit, prover's coins).

## Main results

* `TCSlib.Cryptography.GI.gni_complete`, `GI.gni_accept_le` — completeness and the acceptance
  bound of one iteration of the graph non-isomorphism protocol.
* `TCSlib.Cryptography.GI.gi_complete`, `GI.gi_accept_le` — the same for the graph isomorphism
  protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErr` — [PS10, Proposition 118.4], one iteration.
* `TCSlib.Cryptography.GI.gi_efficientProverProofErr` — [PS10, Proposition 120.7], one iteration.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Verdicts of the graph non-isomorphism iteration on encoded instances -/

/-- The honest prover's reply to the graph `encGraph K` on an encoded instance:
`decide (¬ G₀ ≅ K)`. -/
theorem gniProver_next_encGraph {n : ℕ} (G₀ G₁ K : Graph n) (y r : List Bool) :
    gniProver.next (encInstance G₀ G₁) y r [encGraph K] = [decide (¬ Isomorphic G₀ K)] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (encGraph K)))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph, decGraphAt_encGraph]

/-- The verdict of the graph non-isomorphism iteration against a prover `P'` on an encoded
instance: the reply's first bit equals the verifier's first coin `b`, the graph sent being
`σ(G_b)` for `σ` sampled from the remaining coins. -/
theorem gni_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide ((P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
        [encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r.2).drop 1)))]).headD false = (List.ofFn r.2).headD false)] := by
  rw [gniProtocol_outV, gniVerifier_next_nil, gniVerifier_next_one, wellFormedInstance_encInstance]
  simp only [true_and]

/-- **Completeness of the graph non-isomorphism iteration** [PS10, Proposition 118.4]
(Lem-119.d): on a non-isomorphic encoded instance the honest prover's reply is the verifier's
bit for every pair of tapes (`gni_honest_reply`), so the verdict is `[true]` with probability
one. -/
theorem gni_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocol.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gni_outV_eq, gniProver_next_encGraph]
  simp only [List.headD_cons, gni_honest_reply h, decide_true]

/-- The verifier's tape of the graph non-isomorphism iteration as its first bit and the
sampler's `(N + 1)²` coins (`tapeSplit`, at the verifier's coin polynomial
`1 + (N + 1)²`). -/
def vTapeSplit (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ gniProtocol.V.Coins N :=
  tapeSplit (1 * (N + 1) ^ 2)

/-- The list of a split verifier tape. -/
theorem ofFn_vTapeSplit (N : ℕ) (b : Bool) (t : Fin (1 * (N + 1) ^ 2) → Bool) :
    List.ofFn (vTapeSplit N (b, t)) = b :: List.ofFn t :=
  ofFn_tapeSplit _ b t

/-- The sampler's coins fit in the verifier's tape: `permCoinLen n ≤ (|x| + 1)²` for an
encoded instance `x` on `n` vertices (`permCoinLen_le`, `length_encInstance`). -/
theorem permCoinLen_le_tape {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 := by
  rw [one_mul]
  exact permCoinLen_le (by rw [length_encInstance]; omega)

/-- **The acceptance bound of the graph non-isomorphism iteration against isomorphic graphs**
[PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the verifier
accepts with probability at most `1/2 + permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); the prover's reply
is then a function `g` of the graph it receives. Split the verifier's tape into the bit `b`
and the sampler's coins (`vTapeSplit`); the event is `g (σ(G_b)) = b` with `σ` the sampled
permutation. Replacing `σ` by a uniform permutation changes the probability by at most
`permFailBound n` (`statClose_samplePerm_long`, `StatClose.abs_uprob_sub_le_prod` with `b` as
the auxiliary coin), and for a uniform `σ` the probability is exactly `1/2`
(`uprob_guess_eq_half`). -/
theorem gni_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 + permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocol.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  set g : Graph n → Bool := fun K =>
    (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [encGraph K]).headD false with hg
  have hev : ∀ r₂ : gniProtocol.V.Coins (encInstance G₀ G₁).length,
      gniProtocol.outV P' (encInstance G₀ G₁) y z (r₁, r₂) = [true] ↔
        g (permGraph (cond ((List.ofFn r₂).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r₂).drop 1))) = (List.ofFn r₂).headD false := by
    intro r₂
    rw [gni_outV_eq]
    simp [hg]
  rw [OneWay.uprob_congr hev, ← uprob_comp_equiv (vTapeSplit (encInstance G₀ G₁).length)]
  have hev2 : ∀ p : Bool × (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool),
      g (permGraph (cond ((List.ofFn (vTapeSplit _ p)).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn (vTapeSplit _ p)).drop 1))) =
            (List.ofFn (vTapeSplit _ p)).headD false ↔
        g (permGraph (cond p.1 G₁ G₀) (samplePerm n (List.ofFn p.2))) = p.1 := by
    rintro ⟨b, t⟩
    rw [ofFn_vTapeSplit, List.headD_cons, List.drop_one, List.tail_cons]
  rw [OneWay.uprob_congr hev2,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool) Bool)]
  have hclose := (statClose_samplePerm_long (permCoinLen_le_tape G₀ G₁)).abs_uprob_sub_le_prod
    fun σ b => g (permGraph (cond b G₁ G₀) σ) = b
  have hideal : uprob (fun q : Equiv.Perm (Fin n) × Bool =>
      g (permGraph (cond q.2 G₁ G₀) (id q.1)) = q.2) = 1 / 2 := by
    rw [← uprob_comp_equiv (Equiv.prodComm Bool (Equiv.Perm (Fin n)))]
    exact uprob_guess_eq_half hσ g
  rw [hideal] at hclose
  have := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  linarith

/-- **One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n`** [PS10, Proposition 118.4, one
iteration] (Prop-118.4), given the verifier's efficiency.

**Proof sketch.** Completeness: `gni_complete` with the empty auxiliary input. Soundness: a
malformed `x` is rejected outright (`gniVerifier_next_one`); a well-formed `x ∉ L_niso` is
`encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gni_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gni_outV_eq`, `uprob_not`). -/
theorem gni_interactiveProofErr (hV : gniVerifier.Efficient) :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], fun z => gni_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gni_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocol.ExecCoins P' (encInstance G₀ G₁),
          gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gni_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocol.ExecCoins P' x, gniProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocol_outV, gniVerifier_next_one]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      linarith [permFailBound_nonneg (instanceVertices x.length)]

/-! ### Verdicts of the graph isomorphism iteration on encoded instances -/

/-- The verdict of the graph isomorphism iteration against a prover `P'` on an encoded
instance: `γ(G_b) = H` for the prover's two messages `H` (on the empty history) and `γ` (on
the challenge `[b]`). -/
theorem gi_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : giProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    giProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide (encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
        (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [[(List.ofFn r.2).headD false]]))) =
        P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])] := by
  rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two]

/-- **Completeness of the graph isomorphism iteration for every witness**
[PS10, Proposition 120.7] (Lem-120.a): with witness `encPerm σ`, `σ(G₀) = G₁`, the honest
transcript is `H = π(G₀)`, `γ = if b then π σ⁻¹ else π`, and `γ(G_b) = H` for every pair of
tapes (`gi_honest_reply_eq`), whatever the sampled `π`. -/
theorem gi_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins giProver (encInstance G₀ G₁) =>
      giProtocol.outV giProver (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gi_outV_eq, giProver_next_nil, giProver_next_cons, decPerm_encPerm, List.headD_cons,
    gi_honest_reply_eq hσ]
  simp

/-- The single coin of the graph isomorphism verifier as a tape (`Equiv.funUnique`). -/
def giBitEquiv (N : ℕ) : Bool ≃ giProtocol.V.Coins N := (Equiv.funUnique (Fin 1) Bool).symm

/-- The list of the verifier's single-coin tape. -/
theorem ofFn_giBitEquiv (N : ℕ) (b : Bool) : List.ofFn (giBitEquiv N b) = [b] := by
  show List.ofFn (fun _ : Fin 1 => b) = [b]
  rw [List.ofFn_succ, List.ofFn_zero]

/-- The joint coins of the graph isomorphism iteration as (challenge bit, prover's coins). -/
def giCoinEquiv (P' : Strategy) (x : List Bool) :
    Bool × P'.Coins x.length ≃ giProtocol.ExecCoins P' x :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (giBitEquiv x.length))

/-- The prover's coins of a transported pair. -/
theorem giCoinEquiv_fst (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).1 = r₁ := rfl

/-- The verifier's tape of a transported pair. -/
theorem giCoinEquiv_snd (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).2 = giBitEquiv x.length b := rfl

/-- **The acceptance bound of the graph isomorphism iteration against non-isomorphic graphs**
[PS10, proof of Proposition 120.7] (Lem-120.c): for `G₀ ≇ G₁` and every prover `P'`, the
verifier accepts with probability at most `1/2`.

**Proof sketch.** Acceptance means `γ(G_b) = H` for the decoded first message `H` and decoded
reply `γ` (`gi_outV_eq`, `decGraphAt_encGraph`); the event is contained in the event of
`uprob_gi_cheat_le_half` with `H r₁ := decGraphAt n (first message)` and
`γ b r₁ := decPerm n (reply to [b])`, after reading the joint coins as (bit, prover's coins)
(`giCoinEquiv`). -/
theorem gi_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 := by
  set H : P'.Coins (encInstance G₀ G₁).length → Graph n := fun r₁ =>
    decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) []) with hH
  set γ : Bool → P'.Coins (encInstance G₀ G₁).length → Equiv.Perm (Fin n) := fun b r₁ =>
    decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [[b]]) with hγ
  have hmono : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true] →
        permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀) (γ ((List.ofFn r.2).headD false) r.1) =
          H r.1 := by
    intro r hr
    rw [gi_outV_eq] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    show permGraph _ (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
      [[(List.ofFn r.2).headD false]])) = decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])
    rw [← hr, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giCoinEquiv P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_) (uprob_gi_cheat_le_half h H γ)
  rintro ⟨b, r₁⟩
  rw [giCoinEquiv_fst, giCoinEquiv_snd, ofFn_giBitEquiv, List.headD_cons]

/-- **One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, corrected: for `L_iso`] (Prop-120.7), given the parties'
efficiency.

**Proof sketch.** Completeness for every witness: `gi_complete`; completeness of
`InteractiveProofErr`: the witness `encPerm σ`. Soundness: a malformed `x` is rejected
outright (`giVerifier_next_two'`); a well-formed `x ∉ L_iso` is `encInstance G₀ G₁` with
`G₀ ≇ G₁` (`eq_encInstance_of_wellFormed`, `encInstance_mem_Liso_iff`) and `gi_accept_le`
bounds the acceptance probability, the verdict being a single bit (`gi_outV_eq`,
`uprob_not`). -/
theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Efficient) :
    EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, fun z => gi_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := gi_accept_le hni P' [] z
      have hnot : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
          giProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gi_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocol.ExecCoins P' x, giProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two']
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      norm_num
  efficientP := hP
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact gi_complete hσ z

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph non-isomorphism protocol: completeness and soundness

[PS10, Proposition 118.4] for the `|x|`-fold protocol `gniProtocolRep` (Prot-118.3, repeated),
proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`; the main file closes
`gni_interactiveProof` by `exact GI.gni_interactiveProof gniVerifierRep_efficient`.

The verifier's graphs `H_i = σ_i(G_{b_i})` depend only on the number of replies received, so the
transcript against any prover is explicit (`exec_vfirst_eq`): the prover's `i`-th reply is its
next-message function on `[H_0, …, H_i]`. **Completeness** is exact: the honest prover's reply
is `b_i` for every tape (`gni_honest_reply`). **Soundness**: against isomorphic graphs, after
fixing the prover's coins and reading the verifier's tape as the `|x|` blocks
`(b_i, sampler coins_i)` (`gniTapes`), the acceptance event is the adaptive guessing event of
`uprob_gni_rep_cheat` (Lem-119.b) once the `|x|` sampled permutations are replaced by uniform
ones, which costs `|x| · permFailBound n` (`statClose_pi` of `statClose_samplePerm_long`); so
`Pr[accept] ≤ 2^{-|x|} + |x| · permFailBound n`, a negligible function of `|x|`
(`negligible_two_pow_neg`, `negligible_mul_permFailBound`).

## Main definitions

* `TCSlib.Cryptography.GI.blocksEquiv`, `GI.gniTapes` — a tape of `m · c` bits as `m` blocks,
  and the verifier's tape as (bits, sampler coins).

## Main results

* `TCSlib.Cryptography.GI.exec_vfirst_eq` — transcripts of verifier-first protocols whose
  verifier's messages depend only on the number of replies.
* `TCSlib.Cryptography.GI.statClose_pi` — `StatClose` for `m` independent copies.
* `TCSlib.Cryptography.GI.gniRep_complete`, `GI.gniRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErrRep`, `GI.gni_interactiveProof` —
  [PS10, Proposition 118.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Transcripts of verifier-first protocols with history-independent graphs -/

/-- An entry of the list of a tuple below its length (any type). -/
theorem getD_ofFn_lt' {α : Type*} {c : ℕ} (t : Fin c → α) {i : ℕ} (hi : i < c) (d : α) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The list of a tuple given by a function on `ℕ` is the map over `List.range`. -/
theorem ofFn_eq_map_range {α : Type*} : ∀ {k : ℕ} (f : Fin k → α) (g : ℕ → α),
    (∀ t : Fin k, f t = g t) → List.ofFn f = List.map g (List.range k)
  | 0, _, _, _ => by simp
  | k + 1, f, g, h => by
    rw [List.ofFn_succ_last, List.range_succ, List.map_append, List.map_singleton,
      ofFn_eq_map_range (fun t => f t.castSucc) g (fun t => by
        show f t.castSucc = g t
        rw [h, Fin.coe_castSucc]), h, Fin.val_last]

/-- In a verifier-first execution of `2k` moves each party has received exactly `k` messages. -/
theorem exec_vfirst_length (P' V : Strategy) (x zP zV rP rV : List Bool) :
    ∀ k, (exec P' V true x zP zV rP rV (2 * k)).1.length = k ∧
      (exec P' V true x zP zV rP rV (2 * k)).2.length = k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : moverIsV true (2 * k) = true := by simp [moverIsV]
    have h2 : moverIsV true (2 * k + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, exec_succ, exec_succ]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false, List.length_append, List.length_singleton]
    omega

/-- **Transcripts against a verifier whose first `m` messages depend only on the number of
replies received.** If `V.next x zV rV hist = Hf hist.length` whenever `hist.length < m`,
then after `2i ≤ 2m` moves of the verifier-first execution the prover has received
`H_0, …, H_{i-1}` and the verifier the replies `P'.next x zP rP [H_0, …, H_j]` for `j < i`.

**Proof sketch.** Induction on `i`: move `2i` is the verifier's (`moverIsV true (2i)`), who sends
`Hf i` on its `i` replies; move `2i + 1` is the prover's, who replies to `[H_0, …, H_i]`
(`List.range_succ`, `List.ofFn_succ_last`). -/
theorem exec_vfirst_eq (P' V : Strategy) (x zP zV rP rV : List Bool) (m : ℕ) (Hf : ℕ → List Bool)
    (hV : ∀ hist : List (List Bool), hist.length < m → V.next x zV rV hist = Hf hist.length) :
    ∀ i ≤ m, exec P' V true x zP zV rP rV (2 * i) =
      (List.map Hf (List.range i),
        List.ofFn fun j : Fin i => P'.next x zP rP (List.map Hf (List.range (j + 1)))) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hrec := ih (by omega)
    have h1 : moverIsV true (2 * i) = true := by simp [moverIsV]
    have h2 : moverIsV true (2 * i + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, exec_succ, exec_succ, hrec]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false]
    rw [hV _ (by simp; omega)]
    simp only [List.length_ofFn]
    refine Prod.ext ?_ ?_
    · simp [List.range_succ]
    · rw [List.ofFn_succ_last]
      simp only [Fin.coe_castSucc, Fin.val_last, List.range_succ, List.map_append, List.map_singleton]

/-! ### The verdicts of the `|x|`-fold graph non-isomorphism protocol -/

/-- The honest prover's reply on an encoded instance: `decide (¬ G₀ ≅ last graph received)`. -/
theorem gniProver_next_enc {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool)) :
    gniProver.next (encInstance G₀ G₁) y r hist =
      [decide (¬ Isomorphic G₀ (decGraphAt n (hist.getLastD [])))] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (hist.getLastD [])))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold verifier's graph of iteration `|hist|` on an encoded instance, while the
protocol is not over: `σ(G_b)` for the bit `b` and the sampler coins of the coin block.

**Proof sketch.** Unfold the strategy on the branch `|hist| < |x|`, read the two graph words
off the encoded instance (`pairFstD_pairEncode`, `pairSndD_pairEncode`) and transport the vertex
count `instanceVertexCount (encInstance G₀ G₁) = n` (`generalize`/`subst`, then
`decGraphAt_encGraph`). -/
theorem gniVerifierRep_next_lt {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h : hist.length < (encInstance G₀ G₁).length) :
    gniVerifierRep.next (encInstance G₀ G₁) z r hist =
      encGraph (permGraph
        (cond ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false) G₁ G₀)
        (samplePerm n ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).drop 1))) := by
  show (if hist.length < (encInstance G₀ G₁).length then _ else _) = _
  rw [if_pos h]
  show encGraph (permGraph
    (if (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false then
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁)) else
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁))
      ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).drop 1))) = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph]
  cases (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false <;> rfl

/-- The `|x|`-fold verifier's verdict once `|x|` replies are in. -/
theorem gniVerifierRep_next_ge (x z r : List Bool) (hist : List (List Bool)) (h : x.length ≤ hist.length) :
    gniVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        (hist.getD j []).headD false = (coinSlice (1 + (x.length + 1) ^ 2) j r).headD false)] := by
  show (if hist.length < x.length then _ else _) = _
  rw [if_neg (not_lt.2 h)]

/-- The verdict of the `|x|`-fold protocol against a prover `P'`: the verifier's next-message
function on the `2|x|`-move execution. -/
theorem gniProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : gniProtocolRep.ExecCoins P' x) :
    gniProtocolRep.outV P' x y z r =
      gniVerifierRep.next x z (List.ofFn r.2)
        (exec P' gniVerifierRep true x y z (List.ofFn r.1) (List.ofFn r.2) (2 * x.length)).2 := rfl

/-- The graphs of the `|x|`-fold verifier on an encoded instance, as a function of the
iteration index. -/
noncomputable def gniGraphs {n : ℕ} (G₀ G₁ : Graph n) (rV : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph
    (cond ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).headD false) G₁ G₀)
    (samplePerm n ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).drop 1)))

/-- The verdict of the `|x|`-fold protocol against `P'` on an encoded instance: every reply's
first bit equals the corresponding bit of the verifier's tape, the `j`-th reply being `P'`'s
next message on the graphs `H_0, …, H_j`. -/
theorem gniRep_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocolRep.outV P' (encInstance G₀ G₁) y z r =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
        (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false)] := by
  rw [gniProtocolRep_outV, exec_vfirst_eq P' gniVerifierRep (encInstance G₀ G₁) y z (List.ofFn r.1)
    (List.ofFn r.2) (encInstance G₀ G₁).length (gniGraphs G₀ G₁ (List.ofFn r.2))
    (fun hist hh => gniVerifierRep_next_lt G₀ G₁ z (List.ofFn r.2) hist hh) _ le_rfl,
    gniVerifierRep_next_ge _ _ _ _ (by simp), wellFormedInstance_encInstance]
  simp only [true_and]
  congr 1
  refine decide_eq_decide.2 (forall_congr' fun j => ?_)
  rw [getD_ofFn_lt' _ j.isLt]

/-- **Completeness of the `|x|`-fold graph non-isomorphism protocol** [PS10, Proposition 118.4]:
on a non-isomorphic encoded instance the honest prover's every reply is the verifier's bit
(`gni_honest_reply`), for every pair of tapes. -/
theorem gniRep_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocolRep.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gniRep_outV_eq]
  have hj : ∀ j : Fin (encInstance G₀ G₁).length,
      (gniProver.next (encInstance G₀ G₁) y (List.ofFn r.1)
        (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
      (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false := by
    intro j
    rw [gniProver_next_enc, List.headD_cons, List.range_succ, List.map_append, List.map_singleton,
      List.getLastD_concat, gniGraphs, decGraphAt_encGraph, gni_honest_reply h]
  simp only [hj, implies_true, decide_true]

/-! ### Tapes as blocks -/

/-- A tape of `m · c` bits as `m` blocks of `c` bits (`finProdFinEquiv`: block `i` occupies
the positions `i c, …, i c + c - 1`). -/
def blocksEquiv (m c : ℕ) : (Fin m → Fin c → Bool) ≃ (Fin (m * c) → Bool) :=
  (Equiv.curry (Fin m) (Fin c) Bool).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Entry `k` of the tape of blocks is entry `k mod c` of block `k / c`. -/
theorem blocksEquiv_apply (m c : ℕ) (F : Fin m → Fin c → Bool) (k : Fin (m * c)) :
    blocksEquiv m c F k = F k.divNat k.modNat := by
  simp [blocksEquiv, Equiv.arrowCongr_apply, finProdFinEquiv_symm_apply, Function.uncurry]

/-- Block `j < m` of the tape of blocks is the `j`-th block.

**Proof sketch.** Compare entries (`List.ext_getElem?`): entry `t < c` of the slice is entry
`j c + t` of the tape, which `blocksEquiv_apply` reads as entry `(j c + t) mod c = t` of block
`(j c + t) / c = j`; entries `t ≥ c` are absent on both sides. -/
theorem coinSlice_blocksEquiv (m c : ℕ) (F : Fin m → Fin c → Bool) {j : ℕ} (hj : j < m) :
    coinSlice c j (List.ofFn (blocksEquiv m c F)) = List.ofFn (F ⟨j, hj⟩) := by
  apply List.ext_getElem?
  intro t
  simp only [coinSlice, List.getElem?_take, List.getElem?_drop, List.getElem?_ofFn]
  by_cases ht : t < c
  · have hc : 0 < c := by omega
    have hlt : j * c + t < m * c := by
      calc j * c + t < j * c + c := by omega
        _ = (j + 1) * c := by ring
        _ ≤ m * c := Nat.mul_le_mul_right c hj
    simp only [ht, if_true, hlt, dif_pos, blocksEquiv_apply]
    congr 2
    · apply Fin.ext
      rw [Fin.coe_divNat]
      show (j * c + t) / c = j
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt ht, zero_add]
    · apply Fin.ext
      rw [Fin.coe_modNat]
      show (j * c + t) % c = t
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  · simp [ht]

/-- The verifier's tape of the `|x|`-fold graph non-isomorphism protocol as the `|x|` bits and
the `|x|` sampler tapes of its coin blocks. -/
def gniTapes (N : ℕ) :
    (Fin N → Bool) × (Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) ≃ gniProtocolRep.V.Coins N :=
  (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin (1 * (N + 1) ^ 2) → Bool)).symm.trans
    ((Equiv.piCongrRight fun _ => tapeSplit (1 * (N + 1) ^ 2)).trans (blocksEquiv N (1 + 1 * (N + 1) ^ 2)))

/-- The tape of `gniTapes` is the tape of blocks of the split blocks. -/
theorem gniTapes_apply (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) :
    gniTapes N (b, ts) = blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j)) := rfl

/-- Coin block `j < N` of the tape `gniTapes N (b, ts)` is `b_j` followed by the sampler tape
`ts_j`. -/
theorem coinSlice_gniTapes (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool))
    {j : ℕ} (hj : j < N) :
    coinSlice (1 + (N + 1) ^ 2) j (List.ofFn (gniTapes N (b, ts))) = b ⟨j, hj⟩ :: List.ofFn (ts ⟨j, hj⟩) := by
  rw [gniTapes_apply, show 1 + (N + 1) ^ 2 = 1 + 1 * (N + 1) ^ 2 by ring, coinSlice_blocksEquiv _ _ _ hj,
    ofFn_tapeSplit]

/-! ### Products of close samplers -/

/-- `m` independent copies of a sampler `δ`-close to uniform are `m δ`-close to uniform.

**Proof sketch.** Induction on `m` through `Fin.consEquiv`: the `m + 1` copies are one copy
and `m` copies (`StatClose.prod`), reassembled by `Fin.cons` (`StatClose.map`); the case `m = 0`
is the equality of two point masses. -/
theorem statClose_pi {σ γ : Type*} [Fintype σ] [Fintype γ] {X : σ → γ} {δ : ℝ}
    (h : StatClose X (id : γ → γ) δ) :
    ∀ m : ℕ, StatClose (fun ts : Fin m → σ => fun k => X (ts k)) (id : (Fin m → γ) → (Fin m → γ)) (m * δ)
  | 0 => by
    intro T
    have h1 : (fun ts : Fin 0 → σ => T (fun k => X (ts k))) = fun _ => T Fin.elim0 := by
      funext ts
      congr 1
      funext k
      exact k.elim0
    have h2 : (fun s : Fin 0 → γ => T (id s)) = fun _ => T Fin.elim0 := by
      funext s
      congr 1
      funext k
      exact k.elim0
    rw [h1, h2]
    simp only [Nat.cast_zero, zero_mul]
    rcases em (T Fin.elim0) with hT | hT
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | m + 1 => by
    have ih := statClose_pi h m
    have hp := (h.prod ih).map (fun q : γ × (Fin m → γ) => (Fin.cons q.1 q.2 : Fin (m + 1) → γ))
    have h1 := (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
      (Fin.consEquiv fun _ => γ).symm
    intro T
    have := h1 T
    have e1 : ∀ ts : Fin (m + 1) → σ,
        (Fin.cons (X (ts 0)) (fun k => X (Fin.tail ts k)) : Fin (m + 1) → γ) = fun k => X (ts k) := by
      intro ts
      funext k
      cases k using Fin.cases with
      | zero => rfl
      | succ k => rfl
    have e2 : ∀ s : Fin (m + 1) → γ, (Fin.cons (s 0) (Fin.tail s) : Fin (m + 1) → γ) = s :=
      fun s => Fin.cons_self_tail s
    simp only [Fin.consEquiv_symm_apply, id] at this
    simp only [e1, e2] at this
    rw [show ((m + 1 : ℕ) : ℝ) * δ = δ + m * δ by push_cast; ring]
    exact this

/-! ### Soundness of the `|x|`-fold protocol -/

/-- The sampler's coins fit in a block of the `|x|`-fold verifier's tape. -/
theorem permCoinLen_le_block {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 :=
  permCoinLen_le_tape G₀ G₁

/-- The guess of a prover with fixed coins `r₁` in iteration `i`, as a function of the graphs
`H_0, …, H_i` received: the first bit of its reply (the `g_i` of `uprob_gni_rep_cheat`). -/
noncomputable def gGuess {n : ℕ} (P' : Strategy) (x y : List Bool) (r₁ : P'.Coins x.length)
    (i : Fin x.length) (Ks : Fin (i + 1) → Graph n) (_ : Unit) : Bool :=
  (P'.next x y (List.ofFn r₁) (List.ofFn fun k => encGraph (Ks k))).headD false

/-- **The acceptance bound of the `|x|`-fold graph non-isomorphism protocol against isomorphic
graphs** [PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the
verifier accepts with probability at most `2^{-|x|} + |x| · permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); its `i`-th reply
is then a function `g_i` of the graphs `H_0, …, H_i` (`gGuess`). Read the verifier's tape as
the `|x|` pairs (bit, sampler coins) (`gniTapes`, `coinSlice_gniTapes`): the acceptance event is
`∀ i, g_i(σ_0(G_{b_0}), …, σ_i(G_{b_i})) = b_i` with `σ_j` sampled from block `j`. Replacing the
`|x|` sampled permutations by uniform ones costs `|x| · permFailBound n`
(`statClose_samplePerm_long`, `statClose_pi`, `StatClose.abs_uprob_sub_le_prod`), and for uniform
permutations the event has probability exactly `2^{-|x|}` (`uprob_gni_rep_cheat`). -/
theorem gniRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤
      (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length + (encInstance G₀ G₁).length * permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocolRep.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  -- the event on the verifier's tape, through the blocks
  have hev : ∀ p : (Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)),
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z (r₁, gniTapes (encInstance G₀ G₁).length p) = [true] ↔
        ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i (prefixLE (fun j => permGraph (cond (p.1 j) G₁ G₀)
          (samplePerm n (List.ofFn (p.2 j)))) i) () = p.1 i := by
    rintro ⟨b, ts⟩
    rw [gniRep_outV_eq]
    simp only [List.cons.injEq, decide_eq_true_eq, and_true]
    refine forall_congr' fun i => ?_
    rw [coinSlice_gniTapes _ b ts i.isLt, List.headD_cons, gGuess,
      ofFn_eq_map_range (fun k : Fin (i + 1) => encGraph (prefixLE (fun j => permGraph (cond (b j) G₁ G₀)
        (samplePerm n (List.ofFn (ts j)))) i k)) (gniGraphs G₀ G₁ (List.ofFn (gniTapes _ (b, ts))))
        (fun t => by
          rw [gniGraphs, coinSlice_gniTapes _ b ts (by omega : (t : ℕ) < (encInstance G₀ G₁).length),
            List.headD_cons, List.drop_one, List.tail_cons]
          rfl)]
  rw [← uprob_comp_equiv (gniTapes (encInstance G₀ G₁).length), OneWay.uprob_congr hev,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (encInstance G₀ G₁).length →
      (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)) (Fin (encInstance G₀ G₁).length → Bool))]
  have hclose := (statClose_pi (statClose_samplePerm_long (permCoinLen_le_block G₀ G₁))
    (encInstance G₀ G₁).length).abs_uprob_sub_le_prod
    fun (σs : Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n))
      (b : Fin (encInstance G₀ G₁).length → Bool) => ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (b j) G₁ G₀) (σs j)) i) () = b i
  have hideal : uprob (fun q : (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)) ×
      (Fin (encInstance G₀ G₁).length → Bool) =>
      ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (q.2 j) G₁ G₀) (id q.1 j)) i) () = q.2 i) =
        (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
    rw [← uprob_comp_equiv ((Equiv.prodPUnit ((Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)))).trans (Equiv.prodComm _ _))]
    exact uprob_gni_rep_cheat hσ (gGuess P' (encInstance G₀ G₁) y r₁)
  rw [hideal] at hclose
  have h2 := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at h2 ⊢
  linarith

/-- **The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso` with
soundness error `2^{-|x|} + |x| · permFailBound n`** [PS10, Proposition 118.4] (Prop-118.4),
given the verifier's efficiency.

**Proof sketch.** Completeness is `gniRep_complete` with the empty auxiliary input. Soundness:
a well-formed `x ∉ L_niso` is `encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gniRep_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gniRep_outV_eq`, `uprob_not`); a malformed `x` is rejected on every
tape (`gniVerifierRep_next_ge`, `exec_vfirst_length`). -/
theorem gni_interactiveProofErrRep (hV : gniVerifierRep.Efficient) :
    InteractiveProofErr gniProtocolRep Lniso
      (fun N => (2 : ℝ)⁻¹ ^ N + N * permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], fun z => gniRep_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gniRep_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gniRep_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocolRep.ExecCoins P' x, gniProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocolRep_outV, gniVerifierRep_next_ge _ _ _ _
          (exec_vfirst_length P' gniVerifierRep x [] z (List.ofFn r.1) (List.ofFn r.2) x.length).2.ge]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have h1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      have h2 : (0 : ℝ) ≤ x.length * permFailBound (instanceVertices x.length) :=
        mul_nonneg (Nat.cast_nonneg _) (permFailBound_nonneg _)
      linarith

/-- **[PS10, Proposition 118.4]:** the `|x|`-fold graph non-isomorphism protocol is an
interactive proof for `L_niso`, given the verifier's efficiency: the soundness error
`2^{-N} + N · permFailBound (instanceVertices N)` of `gni_interactiveProofErrRep` is
negligible (`negligible_two_pow_neg`, `negligible_mul_permFailBound`). -/
theorem gni_interactiveProof (hV : gniVerifierRep.Efficient) : InteractiveProof gniProtocolRep Lniso :=
  (gni_interactiveProofErrRep hV).interactiveProof (negligible_two_pow_neg.add negligible_mul_permFailBound)

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph isomorphism protocol: completeness and soundness

[PS10, Proposition 120.7] for the `|x|`-fold protocol `giProtocolRep` (Prot-120.6, repeated,
four moves per iteration), proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`;
the main file closes `gi_rep_efficientProverProof` by
`exact GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient`.

The execution is described iteration by iteration (`repViews`, `exec_repViews`): in iteration
`i` the prover sends `H_i`, the verifier the challenge `[b_i]` with `b_i` its `i`-th coin
(`giVerifierRep_next_odd`), the prover `γ_i`, and the verifier the empty message (or, in the
last iteration, its verdict). The verifier's view is the interleaving `Vs` of the `H_i` and
`γ_i`; the prover's view, before the last iteration, is determined by the challenges
(`PsOf`). **Completeness** is exact (`gi_honest_reply_eq`). **Soundness**: the accepting event
implies the typed event of `uprob_gi_rep_cheat_le` (Lem-120.d) with `H_i` a function of the
earlier challenges and `γ_i` of the challenges up to `i`, whence `Pr[accept] ≤ 2^{-|x|}`.

## Main definitions

* `TCSlib.Cryptography.GI.repViews` — the two parties' views after `i` iterations.
* `TCSlib.Cryptography.GI.Vs`, `GI.PsOf`, `GI.PsOfFin` — the verifier's and the prover's views
  as functions of the messages and challenges.

## Main results

* `TCSlib.Cryptography.GI.exec_repViews` — the four-move iterations of a prover-first protocol.
* `TCSlib.Cryptography.GI.giRep_complete`, `GI.giRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr`, `GI.gi_rep_efficientProverProof` —
  [PS10, Proposition 120.7] for the repeated protocol.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Four-move iterations of a prover-first protocol -/

/-- The views (prover's received messages, verifier's received messages) after `i` iterations
of four moves: the prover sends `H`, the verifier `b`, the prover `γ`, the verifier `e`. -/
def repViews (P' V : Strategy) (x y z rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | i + 1 =>
    let v := repViews P' V x y z rP rV i
    let H := P'.next x y rP v.1
    let b := V.next x z rV (v.2 ++ [H])
    let γ := P'.next x y rP (v.1 ++ [b])
    let e := V.next x z rV (v.2 ++ [H, γ])
    (v.1 ++ [b, e], v.2 ++ [H, γ])

/-- After `4i` moves of a prover-first execution the views are `repViews i`
(`moverIsV false k = decide (k % 2 = 1)`: the prover moves at `4i` and `4i + 2`, the verifier
at `4i + 1` and `4i + 3`). -/
theorem exec_repViews (P' V : Strategy) (x y z rP rV : List Bool) :
    ∀ i, exec P' V false x y z rP rV (4 * i) = repViews P' V x y z rP rV i
  | 0 => rfl
  | i + 1 => by
    have h0 : moverIsV false (4 * i) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h1 : moverIsV false (4 * i + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    have h2 : moverIsV false (4 * i + 1 + 1) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h3 : moverIsV false (4 * i + 1 + 1 + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by ring, exec_succ, exec_succ, exec_succ, exec_succ,
      exec_repViews P' V x y z rP rV i]
    simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, repViews, List.append_assoc,
      List.singleton_append]

/-- The verifier's view after `i` iterations as the interleaving of the graphs and replies. -/
def Vs (H γ : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => Vs H γ i ++ [H i, γ i]

/-- The verifier's view after `i` iterations has `2i` messages. -/
theorem length_Vs (H γ : ℕ → List Bool) : ∀ i, (Vs H γ i).length = 2 * i
  | 0 => rfl
  | i + 1 => by
    rw [Vs, List.length_append, length_Vs H γ i]
    rfl

/-- Message `2j` of the verifier's view is the graph `H_j`. -/
theorem getD_Vs_even (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j) [] = H j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_even H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]), length_Vs, Nat.sub_self]
      rfl

/-- Message `2j + 1` of the verifier's view is the reply `γ_j`. -/
theorem getD_Vs_odd (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j + 1) [] = γ j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_odd H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]; omega), length_Vs,
        show 2 * j + 1 - 2 * j = 1 by omega]
      rfl

/-- The prover's view after `i` iterations when the verifier's even messages are empty: the
challenges `[b_0], [], …, [b_{i-1}], []`. -/
def PsOf (b : ℕ → Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => PsOf b i ++ [[b i], []]

/-- The prover's view depends only on the first `i` challenges. -/
theorem PsOf_congr {f g : ℕ → Bool} : ∀ i, (∀ k < i, f k = g k) → PsOf f i = PsOf g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [PsOf, PsOf, PsOf_congr i (fun k hk => h k (by omega)), h i (by omega)]

/-- The prover's view as a function of a tuple of challenges. -/
def PsOfFin {i : ℕ} (bs : Fin i → Bool) : List (List Bool) :=
  PsOf (fun k => if h : k < i then bs ⟨k, h⟩ else false) i

/-- The prover's view from the strict prefix of a challenge tuple is its view from the tape. -/
theorem PsOfFin_prefixLT {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (prefixLT b i) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The prover's view from the initial segment of a challenge prefix is its view from the tape. -/
theorem PsOfFin_init_prefixLE {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (Fin.init (prefixLE b i)) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The last challenge of a prefix `b_0, …, b_i` is `b_i`. -/
theorem prefixLE_last {m : ℕ} (b : Fin m → Bool) (i : Fin m) : prefixLE b i (Fin.last i) = b i := rfl

/-! ### The `|x|`-fold graph isomorphism verifier and prover, unfolded -/

/-- The `|x|`-fold verifier's challenge on an odd history: its coin `|hist| / 2`. -/
theorem giVerifierRep_next_odd (x z r : List Bool) (hist : List (List Bool)) (h : hist.length % 2 = 1) :
    giVerifierRep.next x z r hist = [r.getD (hist.length / 2) false] := by
  show (if hist.length % 2 = 1 then _ else _) = _
  rw [if_pos h]

/-- The `|x|`-fold verifier's empty message on an even history of fewer than `2|x|` messages. -/
theorem giVerifierRep_next_mid (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : hist.length < 2 * x.length) : giVerifierRep.next x z r hist = [] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_pos h2]

/-- The `|x|`-fold verifier's verdict on an even complete history. -/
theorem giVerifierRep_next_end (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : ¬ hist.length < 2 * x.length) :
    giVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
          (decPerm (instanceVertexCount x) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_neg h2]

/-- The `|x|`-fold verifier's verdict on an encoded instance: `γ_j(G_{b_j}) = H_j` for every
iteration, with the graphs read on `n` vertices. -/
theorem giVerifierRep_next_end_enc {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h1 : hist.length % 2 ≠ 1) (h2 : ¬ hist.length < 2 * (encInstance G₀ G₁).length) :
    giVerifierRep.next (encInstance G₀ G₁) z r hist =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        encGraph (permGraph (cond (r.getD j false) G₁ G₀) (decPerm n (hist.getD (2 * j + 1) []))) =
          hist.getD (2 * j) [])] := by
  rw [giVerifierRep_next_end _ _ _ _ h1 h2, wellFormedInstance_encInstance]
  simp only [true_and]
  show [decide (∀ j : Fin (encInstance G₀ G₁).length, encGraph (permGraph
    (if r.getD j false then decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁))
      else decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decPerm (instanceVertexCount (encInstance G₀ G₁)) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph, Bool.cond_eq_ite]

/-- The `|x|`-fold prover's graph on an even history of an encoded instance: `π(G₀)` for the
permutation sampled from coin block `|hist| / 2`. -/
theorem giProverRep_next_even {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool))
    (h : hist.length % 2 = 0) :
    giProverRep.next (encInstance G₀ G₁) y r hist =
      encGraph (permGraph G₀ (samplePerm n
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) := by
  show (if hist.length % 2 = 0 then encGraph (permGraph
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) else _) = _
  rw [if_pos h, show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold prover's reply on an odd history of an encoded instance with witness
`encPerm σ`: `π σ⁻¹` or `π` according to the last challenge received. -/
theorem giProverRep_next_odd {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r : List Bool)
    (hist : List (List Bool)) (h : hist.length % 2 ≠ 0) :
    giProverRep.next (encInstance G₀ G₁) (encPerm σ) r hist =
      encPerm (if (hist.getLastD []).headD false then
        samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) * σ⁻¹
      else samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r)) := by
  show (if hist.length % 2 = 0 then _ else encPerm (if (hist.getLastD []).headD false then
    samplePerm (instanceVertexCount (encInstance G₀ G₁))
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) *
      (decPerm (instanceVertexCount (encInstance G₀ G₁)) (encPerm σ))⁻¹
    else samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) = _
  rw [if_neg h]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decPerm_encPerm]

/-- The verdict of the `|x|`-fold protocol against `P'`: the verifier's next-message function on
the `4|x|`-move execution. -/
theorem giProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : giProtocolRep.ExecCoins P' x) :
    giProtocolRep.outV P' x y z r =
      giVerifierRep.next x z (List.ofFn r.2)
        (exec P' giVerifierRep false x y z (List.ofFn r.1) (List.ofFn r.2) (4 * x.length)).2 := rfl

/-! ### The views against the honest verifier -/

/-- Against the `|x|`-fold verifier, the verifier's view after `i` iterations interleaves the
prover's graphs (its next message on its view) and replies (its next message on its view
extended by the challenge `[b_j]`, `b_j` the verifier's `j`-th coin), and the prover's view
has `2i` messages.

**Proof sketch.** Induction on `i`: the challenge is the verifier's coin `i`
(`giVerifierRep_next_odd` on the odd history of `2i + 1` messages). -/
theorem repViews_snd (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, (repViews P' giVerifierRep x y z rP rV i).2 =
      Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
        (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ∧
      (repViews P' giVerifierRep x y z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    simp only [repViews]
    rw [h2, hb]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- Against the `|x|`-fold verifier, before the last iteration the prover's view is determined
by the challenges.

**Proof sketch.** Induction on `i < |x|`: the challenge of iteration `i` is the verifier's coin
`i` (`giVerifierRep_next_odd`) and its fourth message is empty, the history having `2i + 2 < 2|x|`
messages (`giVerifierRep_next_mid`). -/
theorem repViews_fst (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, i < x.length → (repViews P' giVerifierRep x y z rP rV i).1 = PsOf (fun k => rV.getD k false) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := repViews_fst P' x y z rP rV i (by omega)
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have he : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1,
            P'.next x y rP ((repViews P' giVerifierRep x y z rP rV i).1 ++ [[rV.getD i false]])]) = [] := by
      apply giVerifierRep_next_mid
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
    simp only [repViews]
    rw [h2, hb, he, ih]
    rfl

/-! ### Completeness -/

/-- The honest prover's graph of iteration `j`: `π_j(G₀)` for `π_j` sampled from coin block `j`
(block length `c`) of its tape. -/
noncomputable def honestH {n : ℕ} (G₀ : Graph n) (c : ℕ) (rP : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph G₀ (samplePerm n (coinSlice c j rP)))

/-- The honest prover's reply of iteration `j`: `π_j σ⁻¹` or `π_j` according to the verifier's
coin `j`. -/
noncomputable def honestγ {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : ℕ) (rP rV : List Bool) (j : ℕ) : List Bool :=
  encPerm (if rV.getD j false then samplePerm n (coinSlice c j rP) * σ⁻¹ else samplePerm n (coinSlice c j rP))

/-- The honest views on an encoded instance with witness `encPerm σ`: the verifier's view
interleaves `honestH` and `honestγ`.

**Proof sketch.** Induction on `i` with `giProverRep_next_even` (the prover's view has `2i`
messages), `giVerifierRep_next_odd` (the verifier's has `2i + 1`) and `giProverRep_next_odd`
(the last message the prover received is the challenge `[b_i]`, `List.getLastD_concat`). -/
theorem honest_views {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z rP rV : List Bool) :
    ∀ i, (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).2 =
        Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ∧
      (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := honest_views G₀ G₁ σ z rP rV i
    have hH : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 =
        encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP))) := by
      rw [giProverRep_next_even _ _ _ _ _ (by rw [h1]; omega), h1, show 2 * i / 2 = i by omega]
    have hb : giVerifierRep.next (encInstance G₀ G₁) z rV
        (Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ++
          [encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP)))]) =
        [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have hγ : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        ((repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 ++ [[rV.getD i false]]) =
        honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV i := by
      rw [giProverRep_next_odd _ _ _ _ _ (by rw [List.length_append, h1, List.length_singleton]; omega),
        List.getLastD_concat, List.headD_cons, List.length_append, h1, List.length_singleton,
        show (2 * i + 1) / 2 = i by omega]
      rfl
    simp only [repViews]
    rw [h2, hH, hb, hγ]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- **Completeness of the `|x|`-fold graph isomorphism protocol for every witness**
[PS10, Proposition 120.7]: every iteration's check `γ_j(G_{b_j}) = H_j` holds on the honest
views (`honest_views`, `gi_honest_reply_eq`), for every pair of tapes. -/
theorem giRep_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins giProverRep (encInstance G₀ G₁) =>
      giProtocolRep.outV giProverRep (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [giProtocolRep_outV, exec_repViews, (honest_views G₀ G₁ σ z _ _ _).1,
    giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  intro j
  rw [getD_Vs_odd _ _ _ _ j.isLt, getD_Vs_even _ _ _ _ j.isLt, honestγ, honestH, decPerm_encPerm,
    gi_honest_reply_eq hσ]

/-! ### Soundness -/

/-- The joint coins of the `|x|`-fold graph isomorphism protocol as (challenges, prover's
coins). -/
def giRepCoins (P' : Strategy) (x : List Bool) :
    (Fin x.length → Bool) × P'.Coins x.length ≃ giProtocolRep.ExecCoins P' x :=
  Equiv.prodComm _ _

/-- The decoded graph a prover with coins `r₁` sends in iteration `i` after the challenges `bs`
(the `H_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def Hfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length) (bs : Fin i → Bool)
    (r₁ : P'.Coins x.length) : Graph n :=
  decGraphAt n (P'.next x y (List.ofFn r₁) (PsOfFin bs))

/-- The decoded permutation a prover with coins `r₁` replies in iteration `i` after the
challenges `bs` (the last one being the current challenge; the `γ_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def γfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length)
    (bs : Fin (i + 1) → Bool) (r₁ : P'.Coins x.length) : Equiv.Perm (Fin n) :=
  decPerm n (P'.next x y (List.ofFn r₁) (PsOfFin (Fin.init bs) ++ [[bs (Fin.last i)]]))

/-- **The acceptance bound of the `|x|`-fold graph isomorphism protocol against non-isomorphic
graphs** [PS10, Proposition 120.7, "repeated … to drive the error as low as desired"]: for
`G₀ ≇ G₁` and every prover `P'`, the verifier accepts with probability at most `2^{-|x|}`.

**Proof sketch.** Acceptance means `γ_j(G_{b_j}) = H_j` for every `j` (`giVerifierRep_next_end_enc`,
`repViews_snd`), where `H_j` is the prover's message on its view `PsOf b j` and `γ_j` on
`PsOf b j ++ [[b_j]]` (`repViews_fst`); decoding both sides (`decGraphAt_encGraph`) gives the
event of `uprob_gi_rep_cheat_le` with `Hfun`, `γfun` (`PsOfFin_prefixLT`, `PsOfFin_init_prefixLE`),
after reading the joint coins as (challenges, prover's coins) (`giRepCoins`). -/
theorem giRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
  have hmono : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true] →
      ∀ i : Fin (encInstance G₀ G₁).length,
        permGraph (cond ((List.ofFn r.2).getD i false) G₁ G₀)
          (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
            (PsOf (fun k => (List.ofFn r.2).getD k false) i ++ [[(List.ofFn r.2).getD i false]]))) =
        decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (PsOf (fun k => (List.ofFn r.2).getD k false) i)) := by
    intro r hr i
    rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ y z _ _ _).1,
      giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    have hi := hr i
    rw [getD_Vs_odd _ _ _ _ i.isLt, getD_Vs_even _ _ _ _ i.isLt, repViews_fst P' _ y z _ _ i i.isLt] at hi
    rw [← hi, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giRepCoins P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_)
    (uprob_gi_rep_cheat_le h (Hfun P' (encInstance G₀ G₁) y) (γfun P' (encInstance G₀ G₁) y))
  rintro ⟨b, r₁⟩
  refine forall_congr' fun i => ?_
  show permGraph (cond ((List.ofFn b).getD i false) G₁ G₀) (decPerm n (P'.next _ y (List.ofFn r₁)
      (PsOf (fun k => (List.ofFn b).getD k false) i ++ [[(List.ofFn b).getD i false]]))) =
    decGraphAt n (P'.next _ y (List.ofFn r₁) (PsOf (fun k => (List.ofFn b).getD k false) i)) ↔
    permGraph (cond (b i) G₁ G₀) (γfun P' _ y i (prefixLE b i) r₁) = Hfun P' _ y i (prefixLT b i) r₁
  rw [getD_ofFn_lt' b i.isLt, Hfun, γfun, PsOfFin_init_prefixLE, prefixLE_last, PsOfFin_prefixLT]

/-- **The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
soundness error `2^{-|x|}` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, repeated] (Prop-120.7, Lem-120.d), given the parties' efficiency.

**Proof sketch.** Completeness for every witness is `giRep_complete`; soundness is
`giRep_accept_le` on well-formed inputs (a well-formed `x ∉ L_iso` has non-isomorphic graphs)
and the outright rejection of malformed inputs (`giVerifierRep_next_end`). -/
theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProofErr giProtocolRep Liso Riso (fun N => (2 : ℝ)⁻¹ ^ N) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, fun z => giRep_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := giRep_accept_le hni P' [] z
      have hnot : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ [] z _ _ _).1,
          giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocolRep.ExecCoins P' x, giProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, giVerifierRep_next_end _ _ _ _
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      linarith
  efficientP := hP
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact giRep_complete hσ z

/-- **[PS10, Proposition 120.7], repeated:** the `|x|`-fold graph isomorphism protocol is an
interactive proof for `L_iso` with efficient prover with respect to `R_iso`, given the
parties' efficiency (`gi_rep_efficientProverProofErr`, `negligible_two_pow_neg`). -/
theorem gi_rep_efficientProverProof (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProof giProtocolRep Liso Riso :=
  (gi_rep_efficientProverProofErr hP hV).efficientProverProof negligible_two_pow_neg

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical closeness of the graph isomorphism simulator

The probability bookkeeping behind Theorem 122.3 of `ZeroKnowledge/GraphIsomorphismZK.lean`
(`gi_statZK`): the string-level view of a cheating verifier `V'` in one iteration of
[PS10, Protocol 120.6] and the output of the string simulator `GIZK.sim` are statistically
close, assuming the typed closeness of the truncated simulator (Thm-122.3.trunc, proved in the
main file and passed here as a hypothesis).

The typed objects of the main file (`giRealView`, `giSimAttempt`, `giSimTrunc`) are shadowed
by `GIZK.realView`, `GIZK.simAttempt`, `GIZK.simTrunc` with identical bodies. The chain of
closeness steps is

1. the real view with the rejection-sampled `π` is within `permFailBound n` of the real view
   with a uniform `π` (`statClose_samplePerm_long`, `StatClose.prod`, `StatClose.map`);
2. the typed truncated simulator is within `2^{-n}` of the real view (hypothesis);
3. the string simulator reads its tape as `n` independent blocks `(π'_t, b'_t, r_t)`
   (`readBlocks`, a composition of maps pushing uniform to uniform), and replacing the `n`
   rejection-sampled `π'_t` by uniform ones costs `n · permFailBound n` (`statClose_pi`).

The real view is computed from `exec` (`viewV_encode`) and the string simulator is identified
with the typed one on an encoded instance (`attemptStr_ofFn`, `sim_ofFn_eq`).

## Main definitions

* `TCSlib.Cryptography.GIZK.realView`, `GIZK.simAttempt`, `GIZK.simTrunc` — shadows of the
  typed layer.
* `TCSlib.Cryptography.GIZK.vstar`, `GIZK.encView` — the cheating verifier as a function of
  the graph and its coins, and the string encoding of a typed view.
* `TCSlib.Cryptography.GIZK.tapeBlock`, `GIZK.blockFields`, `GIZK.readBlocks` — reading a
  tape as blocks and a block as its three fields.

## Main results

* `TCSlib.Cryptography.GIZK.statClose_pi` — closeness is preserved by `N`-fold independent
  products, with bound `N · δ`.
* `TCSlib.Cryptography.GIZK.pushesUniform_readBlocks` — the block reading of a uniform tape
  is uniform.
* `TCSlib.Cryptography.GIZK.viewV_encode` — the encoded view of `V'` in the real execution.
* `TCSlib.Cryptography.GIZK.sim_ofFn_eq` — the string simulator on an encoded instance is the
  encoded typed simulator on the sampled blocks.
* `TCSlib.Cryptography.GIZK.statClose_real_sim` — the assembled closeness bound
  `2^{-n} + (n + 1) · permFailBound n`.
* `TCSlib.Cryptography.GIZK.negligible_delta` — the bound is negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, Theorem 122.3 and Algorithm 123.4, pp. 122–124.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GIZK

open Complexity Turing Finset

/-! ### Shadows of the typed layer -/

/-- Shadow of `giRealView`: the view `(r, π(G₀), γ)` of a cheating verifier `V*` in one real
iteration on the prover's coins `π` and `V*`'s coins `r`. -/
def realView {n : ℕ} {ρ : Type*} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (V : Graph n → ρ → Bool)
    (w : Equiv.Perm (Fin n) × ρ) : ρ × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if V (permGraph G₀ w.1) w.2 then w.1 * σ⁻¹ else w.1)

/-- Shadow of `giSimAttempt`: one attempt of [PS10, Algorithm 123.4] on the coins
`((π', b'), r)`. -/
def simAttempt {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  if V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 then
    some (c.2, permGraph (cond c.1.2 G₁ G₀) c.1.1, c.1.1)
  else none

/-- Shadow of `giSimTrunc`: the first successful of `N` attempts, `none` if all fail. -/
def simTrunc {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  (List.finRange N).findSome? fun t => simAttempt G₀ G₁ V (c t)

/-- The cheating verifier `V'` on common input `x` and auxiliary input `z` as a function of
the received graph and of its typed coins: the first bit of its reply to `[encGraph H]`. -/
def vstar (V' : Strategy) (x z : List Bool) {n : ℕ} (H : Graph n) (r : V'.Coins x.length) : Bool :=
  (V'.next x z (List.ofFn r) [encGraph H]).headD false

/-- The string encoding of a typed view `(r, H, γ)` of `V'`: `⟨⟨x, z⟩, ⟨r, [encGraph H, encPerm γ]⟩⟩`. -/
def encView (V' : Strategy) (x z : List Bool) {n : ℕ}
    (v : V'.Coins x.length × Graph n × Equiv.Perm (Fin n)) : List Bool :=
  View.encode ⟨x, z, List.ofFn v.1, [encGraph v.2.1, encPerm v.2.2]⟩

/-! ### Tapes and the permutation sampler -/

/-- Restricting a uniform tuple of `c` entries to its first `m ≤ c` entries gives a uniform
tuple: the tuple is the pair (prefix, suffix) through `finSumFinEquiv`, and the first
projection pushes uniform to uniform. -/
theorem pushesUniform_castLE {B : Type*} [Fintype B] [Nonempty B] {m c : ℕ} (h : m ≤ c) :
    HardcoreBit.PushesUniform (fun t : Fin c → B => fun i : Fin m => t (Fin.castLE h i)) := by
  let e : (Fin c → B) ≃ (Fin m → B) × (Fin (c - m) → B) :=
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl B)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl B)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he : ∀ t : Fin c → B, (e t).1 = fun i : Fin m => t (Fin.castLE h i) := by
    intro t
    funext i
    simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply,
      finSumFinEquiv_apply_left]
    congr 1
  have := (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
  simpa only [he] using this

/-- An entry of the list of a tape below its length. -/
theorem getD_ofFn_lt {c : ℕ} (t : Fin c → Bool) {i : ℕ} (hi : i < c) (d : Bool) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The index `(i T + t) k + j` of a coin-table entry is below `n T k`. -/
theorem coinTable_index_lt {n T k : ℕ} (i : Fin n) (t : Fin T) (j : Fin k) :
    ((i : ℕ) * T + t) * k + j < n * T * k := by
  have h1 : (i : ℕ) * T + t + 1 ≤ n * T := by
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have ht : (t : ℕ) + 1 ≤ T := t.isLt
    calc (i : ℕ) * T + t + 1 ≤ i * T + T := by omega
      _ = (i + 1) * T := by ring
      _ ≤ n * T := Nat.mul_le_mul_right T hi
  calc ((i : ℕ) * T + t) * k + j < ((i : ℕ) * T + t) * k + k := by omega
    _ = ((i : ℕ) * T + t + 1) * k := by ring
    _ ≤ n * T * k := Nat.mul_le_mul_right k h1

/-- The coin table of a tape only depends on the first `n T k` bits. -/
theorem coinTable_ofFn_castLE {n T k c : ℕ} (h : n * T * k ≤ c) (t : Fin c → Bool) :
    coinTable n T k (List.ofFn t) =
      coinTable n T k (List.ofFn fun i : Fin (n * T * k) => t (Fin.castLE h i)) := by
  funext i t' j
  simp only [coinTable_apply]
  rw [getD_ofFn_lt t (lt_of_lt_of_le (coinTable_index_lt i t' j) h),
    getD_ofFn_lt _ (coinTable_index_lt i t' j)]
  rfl

/-- The permutation sampler reads only the first `permCoinLen n` bits of its tape. -/
theorem samplePerm_ofFn_castLE {n c : ℕ} (h : permCoinLen n ≤ c) (t : Fin c → Bool) :
    samplePerm n (List.ofFn t) =
      samplePerm n (List.ofFn fun i : Fin (permCoinLen n) => t (Fin.castLE h i)) := by
  unfold samplePerm
  rw [coinTable_ofFn_castLE h t]
  rfl

/-- On any tape of at least `permCoinLen n` bits the sampler is within `permFailBound n` of a
uniform permutation (`statClose_samplePerm`, `samplePerm_ofFn_castLE`, `pushesUniform_castLE`). -/
theorem statClose_samplePerm_long {n c : ℕ} (h : permCoinLen n ≤ c) :
    StatClose (fun t : Fin c → Bool => samplePerm n (List.ofFn t))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) := by
  have := (statClose_samplePerm n).comp_pushesUniform (pushesUniform_castLE h)
  intro T
  have hT := this T
  simpa only [samplePerm_ofFn_castLE h] using hT

/-! ### Products of close samplers -/

/-- Closeness is preserved by `N`-fold independent products, with bound `N · δ`.

**Proof sketch.** Induction on `N`. For `N = 0` both samplers are the constant `Fin.elim0`
and the two probabilities agree. For `N + 1`, split the tuples as (head, tail) by
`Fin.consEquiv` (`StatClose.comp_equiv_left`/`right`): the pair sampler is `StatClose.prod` of
`h` and the induction hypothesis, mapped by `Fin.cons` (`StatClose.map`), with bound
`δ + N δ`. -/
theorem statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (N : ℕ) :
    StatClose (fun s : Fin N → σ => fun t => X (s t)) (fun u : Fin N → τ => fun t => Y (u t))
      (N * δ) := by
  induction N with
  | zero =>
    intro T
    haveI : Nonempty (Fin 0 → σ) := ⟨Fin.elim0⟩
    haveI : Nonempty (Fin 0 → τ) := ⟨Fin.elim0⟩
    have hX : ∀ s : Fin 0 → σ, (fun t => X (s t)) = (fun t : Fin 0 => (Fin.elim0 t : γ)) :=
      fun s => funext fun t => t.elim0
    have hY : ∀ u : Fin 0 → τ, (fun t => Y (u t)) = (fun t : Fin 0 => (Fin.elim0 t : γ)) :=
      fun u => funext fun t => t.elim0
    have h1 : uprob (fun s : Fin 0 → σ => T (fun t => X (s t))) =
        uprob (fun _ : Fin 0 → σ => T (fun t : Fin 0 => (Fin.elim0 t : γ))) :=
      OneWay.uprob_congr fun s => by rw [hX s]
    have h2 : uprob (fun u : Fin 0 → τ => T (fun t => Y (u t))) =
        uprob (fun _ : Fin 0 → τ => T (fun t : Fin 0 => (Fin.elim0 t : γ))) :=
      OneWay.uprob_congr fun u => by rw [hY u]
    show |uprob (fun s : Fin 0 → σ => T (fun t => X (s t))) -
      uprob (fun u : Fin 0 → τ => T (fun t => Y (u t)))| ≤ ((0 : ℕ) : ℝ) * δ
    rw [h1, h2, Nat.cast_zero, zero_mul]
    by_cases hT : T (fun t : Fin 0 => (Fin.elim0 t : γ))
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | succ N ih =>
    have hp := (h.prod ih).map (fun p : γ × (Fin N → γ) => (Fin.cons (α := fun _ => γ) p.1 p.2))
    have hl : StatClose
        (fun s : Fin (N + 1) → σ => Fin.cons (α := fun _ => γ) (X (s 0)) (fun t => X (s t.succ)))
        (fun u : Fin (N + 1) → τ => Fin.cons (α := fun _ => γ) (Y (u 0)) (fun t => Y (u t.succ)))
        (δ + N * δ) :=
      (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
        (Fin.consEquiv fun _ => τ).symm
    have e1 : (fun s : Fin (N + 1) → σ => fun t => X (s t)) =
        fun s => Fin.cons (α := fun _ => γ) (X (s 0)) (fun t => X (s t.succ)) := by
      funext s t
      refine Fin.cases ?_ (fun j => ?_) t
      · simp
      · simp
    have e2 : (fun u : Fin (N + 1) → τ => fun t => Y (u t)) =
        fun u => Fin.cons (α := fun _ => γ) (Y (u 0)) (fun t => Y (u t.succ)) := by
      funext u t
      refine Fin.cases ?_ (fun j => ?_) t
      · simp
      · simp
    rw [e1, e2]
    refine hl.mono (le_of_eq ?_)
    push_cast
    ring

/-! ### Blocks of a tape -/

/-- Block `t` of a tape of `M · L` bits: the positions `t L, …, t L + L - 1`. -/
def tapeBlock (M L : ℕ) (r : Fin (M * L) → Bool) (t : Fin M) (i : Fin L) : Bool :=
  r ⟨t * L + i, by
    calc (t : ℕ) * L + i < (t : ℕ) * L + L := by omega
      _ = ((t : ℕ) + 1) * L := by ring
      _ ≤ M * L := Nat.mul_le_mul_right L t.isLt⟩

/-- Reading a tape as `M` blocks of `L` bits is a bijection (injective, and the two types
have `2^{M L}` elements). -/
theorem tapeBlock_bijective (M L : ℕ) : Function.Bijective (tapeBlock M L) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r r' h => ?_, ?_⟩
  · funext k
    rcases Nat.eq_zero_or_pos L with hL | hL
    · exact absurd k.isLt (by simp [hL])
    · have ht : (k : ℕ) / L < M := (Nat.div_lt_iff_lt_mul hL).2 k.isLt
      have hi : (k : ℕ) % L < L := Nat.mod_lt _ hL
      have := congrFun (congrFun h ⟨k / L, ht⟩) ⟨k % L, hi⟩
      simp only [tapeBlock] at this
      have e : (⟨(k : ℕ) / L * L + k % L, by
          calc (k : ℕ) / L * L + k % L = k := Nat.div_add_mod' _ _
            _ < M * L := k.isLt⟩ : Fin (M * L)) = k := Fin.ext (Nat.div_add_mod' _ _)
      rwa [e] at this
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul]
    ring_nf

/-- The `t`-th coin slice of the list of a tape is the list of its `t`-th block. -/
theorem coinSlice_ofFn {M L : ℕ} (r : Fin (M * L) → Bool) (t : Fin M) :
    coinSlice L t (List.ofFn r) = List.ofFn (tapeBlock M L r t) := by
  have hle : (t : ℕ) * L + L ≤ M * L := by
    calc (t : ℕ) * L + L = ((t : ℕ) + 1) * L := by ring
      _ ≤ M * L := Nat.mul_le_mul_right L t.isLt
  apply List.ext_getElem
  · simp only [coinSlice, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [coinSlice, List.getElem_take, List.getElem_drop, List.getElem_ofFn, tapeBlock]

/-- The three fields of a coin block of `1 + P + Q` bits: the permutation coins (positions
`1, …, P`), the guessed bit (position `0`) and the verifier's tape (positions `1 + P, …`). -/
def blockFields (P Q : ℕ) (g : Fin (1 + P + Q) → Bool) : ((Fin P → Bool) × Bool) × (Fin Q → Bool) :=
  ((fun i => g ⟨1 + i, by omega⟩, g ⟨0, by omega⟩), fun j => g ⟨1 + P + j, by omega⟩)

/-- Splitting a block into its fields is a bijection. -/
theorem blockFields_bijective (P Q : ℕ) : Function.Bijective (blockFields P Q) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun g g' h => ?_, ?_⟩
  · simp only [blockFields, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h0⟩, h2⟩ := h
    funext k
    rcases k with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact h0
    · by_cases hkP : k < 1 + P
      · have := congrFun h1 ⟨k - 1, by omega⟩
        convert this using 2 <;> exact Fin.ext (by simp; omega)
      · have := congrFun h2 ⟨k - (1 + P), by omega⟩
        convert this using 2 <;> exact Fin.ext (by simp; omega)
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    ring

/-- The first bit of the list of a block. -/
theorem headD_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    (List.ofFn g).headD false = g ⟨0, by omega⟩ := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_ofFn, dif_pos (by omega)]
  rfl

/-- The permutation coins of the list of a block. -/
theorem drop_one_take_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    ((List.ofFn g).drop 1).take P = List.ofFn (fun i : Fin P => g ⟨1 + i, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- The verifier's tape of the list of a block. -/
theorem drop_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    (List.ofFn g).drop (1 + P) = List.ofFn (fun j : Fin Q => g ⟨1 + P + j, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]

/-- The first `n ≤ M` blocks of a tape of `M` blocks of `1 + P + Q` bits, each split into its
fields. -/
def readBlocks (P Q M n : ℕ) (hn : n ≤ M) (r : Fin (M * (1 + P + Q)) → Bool) (t : Fin n) :
    ((Fin P → Bool) × Bool) × (Fin Q → Bool) :=
  blockFields P Q (tapeBlock M (1 + P + Q) r (Fin.castLE hn t))

/-- Reading the first `n` blocks of a uniform tape gives `n` independent uniform blocks: a
bijection (`tapeBlock_bijective`), a restriction (`pushesUniform_castLE`) and a blockwise
bijection (`blockFields_bijective`). -/
theorem pushesUniform_readBlocks (P Q M n : ℕ) (hn : n ≤ M) :
    HardcoreBit.PushesUniform (readBlocks P Q M n hn) := by
  have h1 := HardcoreBit.pushesUniform_equiv (Equiv.ofBijective _ (tapeBlock_bijective M (1 + P + Q)))
  have h2 := pushesUniform_castLE (B := Fin (1 + P + Q) → Bool) hn
  have h3 := HardcoreBit.pushesUniform_equiv
    (Equiv.piCongrRight fun _ : Fin n => Equiv.ofBijective _ (blockFields_bijective P Q))
  exact (h1.comp h2).comp h3

/-! ### The string simulator on an encoded instance -/

/-- One attempt of the string simulator on an encoded instance and a full coin block is the
encoding of the typed attempt on the block's fields (with the rejection-sampled permutation).

**Proof sketch.** Unfold `attemptStr`; the block's fields are read by `headD_ofFn_block`,
`drop_one_take_ofFn_block`, `drop_ofFn_block`; the vertex count `instanceVertexCount x = n`
and the graphs `instanceG₀ x = G₀`, `instanceG₁ x = G₁` are transported along
`pairFstD_pairEncode`, `decGraph_encGraph` (dependent positions, rewritten at once) and
`decGraphAt_encGraph`; then both sides are `if V*(H, r) = b' then some … else none`. -/
theorem attemptStr_ofFn (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool)
    (g : Fin (1 + ((encInstance G₀ G₁).length + 1) ^ 2 + V'.coinLen (encInstance G₀ G₁).length) → Bool) :
    attemptStr V' (encInstance G₀ G₁) z (List.ofFn g) =
      Option.map (encView V' (encInstance G₀ G₁) z)
        (simAttempt G₀ G₁ (vstar V' (encInstance G₀ G₁) z)
          ((samplePerm n (List.ofFn (blockFields _ _ g).1.1), (blockFields _ _ g).1.2),
            (blockFields _ _ g).2)) := by
  simp only [attemptStr, instanceG₀, instanceG₁, instanceVertexCount, headD_ofFn_block,
    drop_one_take_ofFn_block, drop_ofFn_block]
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _,
    show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _]
  generalize hm : Nat.sqrt (encGraph G₀).length = m
  obtain rfl : m = n := by rw [← hm, length_encGraph, Nat.sqrt_eq]
  simp only [decGraphAt_encGraph, blockFields]
  cases hb : g ⟨0, by omega⟩ <;>
    simp only [simAttempt, vstar, cond_false, cond_true, Bool.false_eq_true, if_false, if_true] <;>
    split_ifs <;> rfl

/-- The string simulator on an encoded instance with a tape of `M ≥ n` blocks is the
encoded typed simulator on the first `n` blocks, read by `readBlocks` with the
rejection-sampled permutations (`instanceVertexCount_encInstance`, `List.map_coe_finRange`,
`List.findSome?_map`, `List.map_findSome?`, `coinSlice_ofFn`, `attemptStr_ofFn`). -/
theorem sim_ofFn_eq (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) {M : ℕ} (hn : n ≤ M)
    (r : Fin (M * blockLen V' (encInstance G₀ G₁).length) → Bool) :
    sim V' (encInstance G₀ G₁) z (List.ofFn r) =
      (Option.map (encView V' (encInstance G₀ G₁) z)
        (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n fun t =>
          ((samplePerm n (List.ofFn (readBlocks _ _ M n hn r t).1.1), (readBlocks _ _ M n hn r t).1.2),
            (readBlocks _ _ M n hn r t).2))).getD [] := by
  unfold sim
  rw [instanceVertexCount_encInstance, ← List.map_coe_finRange, List.findSome?_map, simTrunc,
    List.map_findSome?]
  congr 2
  funext t
  simp only [Function.comp_apply]
  rw [show ((t : Fin n) : ℕ) = ((Fin.castLE hn t : Fin M) : ℕ) from rfl, coinSlice_ofFn,
    attemptStr_ofFn]
  rfl

/-! ### The real view -/

/-- The first message of the graph isomorphism prover on an encoded instance: `π(G₀)`. -/
theorem giProver_next_nil {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) :
    giProver.next (encInstance G₀ G₁) y r [] = encGraph (permGraph G₀ (samplePerm n r)) := by
  show encGraph (permGraph (decGraph (pairFstD (encInstance G₀ G₁))).2
    (samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r)) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]

/-- The reply of the graph isomorphism prover with witness `encPerm σ` to the challenge `m`. -/
theorem giProver_next_cons {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r m : List Bool)
    (h : List (List Bool)) :
    giProver.next (encInstance G₀ G₁) (encPerm σ) r (m :: h) =
      encPerm (if m.headD false then samplePerm n r * σ⁻¹ else samplePerm n r) := by
  show encPerm (if ((m :: h).headD []).headD false then
      samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r *
        (decPerm (decGraph (pairFstD (encInstance G₀ G₁))).1 (encPerm σ))⁻¹
    else samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]
  simp only [decPerm_encPerm, List.headD_cons]

/-- The messages received by the verifier in the three moves of a prover-first execution:
the prover's first message, and its reply to the verifier's answer to it (`exec` unfolded,
`moverIsV`). -/
theorem exec_three_snd (P V : Strategy) (x y z rP rV : List Bool) :
    (exec P V false x y z rP rV 3).2 =
      [P.next x y rP [], P.next x y rP [V.next x z rV [P.next x y rP []]]] := by
  simp [exec, moverIsV]

/-- The encoded view of a cheating verifier `V'` in one real iteration of
[PS10, Protocol 120.6] against the honest prover with witness `encPerm σ`: the encoding of
the typed real view on the rejection-sampled `π` (`exec_three_snd`, `giProver_next_nil`,
`giProver_next_cons`). -/
theorem viewV_encode (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool)
    (r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁)) :
    ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode =
      encView V' (encInstance G₀ G₁) z
        (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) (samplePerm n (List.ofFn r.1), r.2)) := by
  show View.encode ⟨encInstance G₀ G₁, z, List.ofFn r.2,
    (exec giProver V' false (encInstance G₀ G₁) (encPerm σ) z (List.ofFn r.1) (List.ofFn r.2) 3).2⟩ = _
  rw [exec_three_snd, giProver_next_nil, giProver_next_cons]
  rfl

/-! ### Assembly -/

/-- An encoded instance on `n` vertices has length at least `2n²` (and at least `n`). -/
theorem two_mul_sq_le_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    2 * (n * n) ≤ (encInstance G₀ G₁).length := by
  rw [length_encInstance]
  omega

/-- The vertex count is at most the length of an encoded instance (`Nat.le_mul_self`). -/
theorem le_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : n ≤ (encInstance G₀ G₁).length := by
  rw [length_encInstance]
  have := Nat.le_mul_self n
  omega

/-- Step 1 of the assembly: the real view with the rejection-sampled `π` is within
`permFailBound n` of the real view with a uniform `π` (`viewV_encode`,
`statClose_samplePerm_long`, `StatClose.prod`, `StatClose.map`). -/
theorem statClose_real_ideal (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (z : List Bool) :
    StatClose
      (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) =>
        ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode)
      (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length =>
        encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
      (permFailBound n + 0) := by
  have hP : permCoinLen n ≤ (PolyExpr.normal 1 2).eval (encInstance G₀ G₁).length := by
    rw [PolyExpr.eval_normal, one_mul]
    exact permCoinLen_le (two_mul_sq_le_length_encInstance G₀ G₁)
  have h := ((statClose_samplePerm_long hP).prod
    (StatClose.refl (fun r : V'.Coins (encInstance G₀ G₁).length => r))).map
    (fun w => encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
  intro T
  have hT := h T
  simpa only [viewV_encode] using hT

/-- Step 3 of the assembly: the encoded typed simulator on uniform blocks is within
`n · permFailBound n` of the string simulator on a tape of `|x| · blockLen V' |x|` bits.

**Proof sketch.** The block sampler `(π', b', r) ↦ ((samplePerm π', b'), r)` is within
`permFailBound n` of the identity (`statClose_samplePerm_long`, `StatClose.prod`), so its
`n`-fold product is within `n · permFailBound n` (`statClose_pi`); the tape read as `n` blocks
is uniform (`pushesUniform_readBlocks`, `StatClose.comp_pushesUniform`); map both sides by the
encoded truncated simulator (`StatClose.map`) and identify the string simulator with it
(`sim_ofFn_eq`). -/
theorem statClose_typed_string (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) :
    StatClose
      (fun c : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
        (Option.map (encView V' (encInstance G₀ G₁) z)
          (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n c)).getD [])
      (fun r : Fin ((encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) → Bool =>
        sim V' (encInstance G₀ G₁) z (List.ofFn r))
      (n * (permFailBound n + 0 + 0)) := by
  have hP' : permCoinLen n ≤ ((encInstance G₀ G₁).length + 1) ^ 2 :=
    permCoinLen_le (two_mul_sq_le_length_encInstance G₀ G₁)
  have hnM : n ≤ (encInstance G₀ G₁).length := le_length_encInstance G₀ G₁
  -- the block sampler `(π', b', r) ↦ ((samplePerm π', b'), r)` against the identity; the
  -- expected type is left to Lean (an ascription makes the elaborator's higher-order
  -- unification against `StatClose.prod` diverge)
  have hs := ((statClose_samplePerm_long hP').prod (StatClose.refl (fun b : Bool => b))).prod
      (StatClose.refl (fun r : V'.Coins (encInstance G₀ G₁).length => r))
  have hpi := statClose_pi hs n
  have hΨ := pushesUniform_readBlocks (((encInstance G₀ G₁).length + 1) ^ 2)
    (V'.coinLen (encInstance G₀ G₁).length) (encInstance G₀ G₁).length n hnM
  have h3 := (hpi.comp_pushesUniform hΨ).map
    (fun cs : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
      (Option.map (encView V' (encInstance G₀ G₁) z)
        (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n cs)).getD [])
  intro T
  have hT := h3.symm T
  simpa only [sim_ofFn_eq V' G₀ G₁ z hnM] using hT

/-- **The string simulator is close to the real view.** Given the typed closeness of the
truncated simulator (Thm-122.3.trunc, which is where `σ(G₀) = G₁` enters), the encoded view of `V'` in the real
iteration and the output of the string simulator on a tape of `|x| · blockLen V' |x|` bits are
within `2^{-n} + (n + 1) · permFailBound n`.

**Proof sketch.** Three `StatClose` steps joined by `StatClose.trans`: (1) the real view with
the sampled `π` against the real view with a uniform `π` (`statClose_real_ideal`), within
`permFailBound n`; (2) the hypothesis mapped by `v ↦ (Option.map encView v).getD []` and
reversed, within `2^{-n}`; (3) the typed simulator on uniform blocks against the string
simulator (`statClose_typed_string`), within `n · permFailBound n`. -/
theorem statClose_real_sim (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (z : List Bool)
    (hclose : StatClose (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n)
      (fun w => some (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) ((2 : ℝ)⁻¹ ^ n))
    (m : ℕ) (hm : m = (encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) :
    StatClose
      (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) =>
        ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode)
      (fun r : Fin m → Bool => sim V' (encInstance G₀ G₁) z (List.ofFn r))
      ((2 : ℝ)⁻¹ ^ n + ((n : ℝ) + 1) * permFailBound n) := by
  subst hm
  have h1 := statClose_real_ideal V' G₀ G₁ σ z
  have h2 : StatClose
      (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length =>
        encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
      (fun c : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
        (Option.map (encView V' (encInstance G₀ G₁) z)
          (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n c)).getD [])
      ((2 : ℝ)⁻¹ ^ n) :=
    hclose.symm.map fun o => (Option.map (encView V' (encInstance G₀ G₁) z) o).getD []
  have h3 := statClose_typed_string V' G₀ G₁ z
  refine ((h1.trans h2).trans h3).mono (le_of_eq ?_)
  ring

/-- The error bound `2^{-n} + (n + 1) · permFailBound n` at `n = instanceVertices |x|` is
negligible in `|x|` (Inf-4.4).

**Proof sketch.** `2^{-n}` is negligible by `negligible_two_pow_neg_sqrt_div` since
`√(N/4) ≤ instanceVertices N` for `N ≥ 8` (`Nat.sqrt_le_sqrt`, `pow_le_pow_of_le_one`), and
`(n + 1) · permFailBound n ≤ 2 N · permFailBound n` for `N ≥ 1` since `n ≤ N`, which is
negligible by `negligible_mul_permFailBound` (`Negligible.const_mul`, `Negligible.mono`);
conclude by `Negligible.add`. -/
theorem negligible_delta :
    Negligible fun N : ℕ => (2 : ℝ)⁻¹ ^ instanceVertices N +
      ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N) := by
  have h1 : Negligible fun N : ℕ => (2 : ℝ)⁻¹ ^ instanceVertices N := by
    refine (negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mono ⟨8, fun N hN => ?_⟩
    have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have h2 : Negligible fun N : ℕ =>
      ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N) := by
    refine (negligible_mul_permFailBound.const_mul 2).mono ⟨1, fun N hN => ?_⟩
    have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
    have hv' : (instanceVertices N : ℝ) + 1 ≤ 2 * N := by
      have h1 : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
      have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hpf : 0 ≤ permFailBound (instanceVertices N) := by
      unfold permFailBound
      positivity
    rw [abs_of_nonneg (mul_nonneg (by positivity) hpf),
      abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hpf))]
    calc ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N)
        ≤ 2 * N * permFailBound (instanceVertices N) := mul_le_mul_of_nonneg_right hv' hpf
      _ = 2 * (N * permFailBound (instanceVertices N)) := by ring
  exact h1.add h2

end TCSlib.Cryptography.GIZK

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph isomorphism simulator as a polynomial-time machine

The machine behind Claim-123.d of `ZeroKnowledge/GraphIsomorphismZK.lean`
(`exists_giSimulator`): the string-level simulator of [PS10, Algorithm 123.4], truncated at
`n` attempts (D8), is a polynomial-time function of its machine layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩`, hence a uniform `Complexity.NUPPT`.

The frozen string definitions of the main file (`giSimBlockLen`, `giSimCoins`,
`giSimAttemptStr`, `giSim`) are *shadowed* here by `GIZK.blockLen`, `GIZK.simCoins`,
`GIZK.attemptStr`, `GIZK.sim` with identical bodies, so that the machine can be built before
the main file; the main file identifies each shadow with its original by `rfl`.

One attempt at index `t` reads the `t`-th coin block (`coinSlice`, cut by the typed coin
cuts `Complexity.polyTimeComputable_pairTakePoly`/`pairDropPoly` with the block length in
unary), samples the permutation (`polyTimeComputable_encPermFromCoins`), relabels the guessed
graph (`polyTimeComputable_encPermGraph` on the padded graph word), runs the cheating
verifier's machine (`Strategy.Efficient`) and compares its challenge bit with the guess
(`polyTimeComputable_pairEq`). The loop over `t < n` is the bounded first-index search
`EncodingMachines.polyTimeComputable_firstIdx` (an instance of the repetition lemma
`Complexity.polyTimeComputable_iterateFind`), and `List.findSome?` over `List.range n` is
identified with the first accepted index (`findSome?_range_getD`).

## Main definitions

* `TCSlib.Cryptography.GIZK.blockLen`, `GIZK.simCoins`, `GIZK.attemptStr`, `GIZK.sim` —
  shadows of the string simulator of the main file.
* `TCSlib.Cryptography.GIZK.attemptAt` — the attempt at a given index on the simulator's
  machine layout.

## Main results

* `TCSlib.Cryptography.GIZK.attemptAt_poly` — the success test and the view of one attempt
  are polynomial-time functions of the indexed layout.
* `TCSlib.Cryptography.GIZK.sim_poly` — the simulator is a polynomial-time function of its
  layout.
* `TCSlib.Cryptography.GIZK.exists_simulator` — the simulator is a uniform PPT (Claim-123.d,
  shadow form).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, Algorithm 123.4, p. 123.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GIZK

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Shadows of the string simulator -/

/-- Shadow of `giSimBlockLen`: the coin block of one attempt against `V'` at instance length
`N` has one guessed bit, `(N + 1)²` permutation-sampling bits and `V'`'s tape. -/
def blockLen (V' : Strategy) (N : ℕ) : ℕ := 1 + (N + 1) ^ 2 + V'.coinLen N

/-- The block length as a syntactic polynomial of the instance length. -/
def blockPoly (V' : Strategy) : PolyExpr := .add (.add (.const 1) (.normal 1 2)) V'.coins

/-- `blockPoly` evaluates to `blockLen`. -/
theorem blockPoly_eval (V' : Strategy) (N : ℕ) : (blockPoly V').eval N = blockLen V' N := by
  simp [blockPoly, blockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- Shadow of `giSimCoins`: `|x|` blocks of `blockLen V' |x|` bits. -/
def simCoins (V' : Strategy) : PolyExpr :=
  .mul .var (.add (.add (.const 1) (.normal 1 2)) V'.coins)

/-- The coin polynomial evaluates to `N` blocks of `blockLen V' N` bits. -/
theorem simCoins_eval (V' : Strategy) (N : ℕ) : (simCoins V').eval N = N * blockLen V' N := by
  simp [simCoins, blockLen, PolyExpr.eval, PolyExpr.normal, Strategy.coinLen]

/-- Shadow of `giSimAttemptStr`: one attempt of [PS10, Algorithm 123.4] on the coin block
`c = b' :: (permutation coins ++ V'`'s tape)`. -/
noncomputable def attemptStr (V' : Strategy) (x z c : List Bool) : Option (List Bool) :=
  let n := instanceVertexCount x
  let b' := c.headD false
  let π := samplePerm n ((c.drop 1).take ((x.length + 1) ^ 2))
  let rV := c.drop (1 + (x.length + 1) ^ 2)
  let H := encGraph (permGraph (if b' then instanceG₁ x else instanceG₀ x) π)
  if (V'.next x z rV [H]).headD false = b' then some (View.encode ⟨x, z, rV, [H, encPerm π]⟩)
  else none

/-- Shadow of `giSim`: up to `n = instanceVertexCount x` attempts on consecutive coin blocks,
the first successful view, or `[]`. -/
noncomputable def sim (V' : Strategy) (x z r : List Bool) : List Bool :=
  ((List.range (instanceVertexCount x)).findSome? fun t =>
    attemptStr V' x z (coinSlice (blockLen V' x.length) t r)).getD []

/-! ### An FP toolkit -/

/-- Polynomial-time computability transfers along pointwise equality. -/
private theorem ptc_congr {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (h : ∀ w, g w = f w) : PolyTimeComputable g := by
  have : g = f := funext h
  rw [this]
  exact hf

/-- Bitwise exclusive-or of a word with itself is the all-`false` word of its length. -/
theorem zipWith_xor_self (l : List Bool) : List.zipWith xor l l = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.replicate_succ]

/-- `w ↦ 0^{|w|}` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on `⟨w, w⟩`). -/
theorem zeros_poly : PolyTimeComputable fun w => List.replicate w.length false :=
  ptc_congr (polyTimeComputable_pairXor.comp (polyTimeComputable_id.pairEncode polyTimeComputable_id))
    fun w => by simp

/-- The graph word `w` padded with `false` (or cut) to length `n²`: it decodes on `n`
vertices to the same graph as `w` and its length determines `n`. -/
def padSq (n : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate (n * n) false).take (n * n)

/-- The padded word has length `n²`. -/
theorem length_padSq (n : ℕ) (w : List Bool) : (padSq n w).length = n * n := by
  simp [padSq, List.length_take, List.length_append]

/-- The vertex count read off the padded word is `n`. -/
theorem sqrt_length_padSq (n : ℕ) (w : List Bool) : Nat.sqrt (padSq n w).length = n := by
  rw [length_padSq, Nat.sqrt_eq]

/-- Below `n²` the padded word reads as `w` with default `false`. -/
theorem getD_padSq (n : ℕ) (w : List Bool) {k : ℕ} (hk : k < n * n) :
    (padSq n w).getD k false = w.getD k false := by
  simp only [padSq, List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_replicate, if_pos (by omega), Option.getD_some,
      List.getElem?_eq_none (by omega)]
    rfl

/-- Padding does not change the decoded graph on `n` vertices. -/
theorem decGraphAt_padSq (n : ℕ) (w : List Bool) : decGraphAt n (padSq n w) = decGraphAt n w :=
  funext fun u => funext fun v => getD_padSq n w (finProdFinEquiv (u, v)).isLt

/-- Padding to the square of a unary count is polynomial-time: on `⟨u, w⟩`, `padSq |u| w`
(`Complexity.polyTimeComputable_pairTakePoly` at `n²` on `⟨u, w ++ 0^{|u|²}⟩`). -/
theorem padSq_poly : PolyTimeComputable fun z => padSq (pairFstD z).length (pairSndD z) := by
  have hsq : PolyTimeComputable fun z =>
      List.replicate ((PolyExpr.mul .var .var).eval (pairFstD z).length) true :=
    unaryPoly_comp (.mul .var .var) polyTimeComputable_pairFstD
  have hz := zeros_poly.comp hsq
  have hcat := polyTimeComputable_pairSndD.append hz
  have h := (polyTimeComputable_pairTakePoly (.mul .var .var)).comp
    (polyTimeComputable_pairFstD.pairEncode hcat)
  refine ptc_congr h fun z => ?_
  simp [padSq, PolyExpr.eval_mul]

/-- `decGraph` of a word whose length has square root `n` is `⟨n, decGraphAt n w⟩`. -/
theorem decGraph_eq_of_sqrt {w : List Bool} {n : ℕ} (h : Nat.sqrt w.length = n) :
    decGraph w = ⟨n, decGraphAt n w⟩ := by
  subst h
  rfl

/-- Relabelling a graph decoded on a given vertex count is polynomial-time: on
`⟨u, ⟨w, p⟩⟩` with `n = |u|`, the word `encGraph (permGraph (decGraphAt n w) (decPerm n p))`
(`polyTimeComputable_encPermGraph` on the padded word `padSq n w`). -/
theorem encPermGraphAt_poly : PolyTimeComputable fun z =>
    encGraph (permGraph (decGraphAt (pairFstD z).length (pairFstD (pairSndD z)))
      (decPerm (pairFstD z).length (pairSndD (pairSndD z)))) := by
  have hpad : PolyTimeComputable fun z => padSq (pairFstD z).length (pairFstD (pairSndD z)) :=
    ptc_congr (padSq_poly.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))) fun z => by simp
  have h := polyTimeComputable_encPermGraph.comp
    (hpad.pairEncode (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  refine ptc_congr h fun z => ?_
  simp only [Function.comp_apply]
  rw [pairFstD_pairEncode, pairSndD_pairEncode, decGraph_eq_of_sqrt (sqrt_length_padSq _ _)]
  simp only [decGraphAt_padSq]

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

/-- The success flag of an optional value `if c then some v else none` is `decide c`. -/
private theorem isSome_ite_some_none {α : Type*} (c : Prop) [Decidable c] (v : α) :
    [(if c then some v else none).isSome] = [decide c] := by
  by_cases h : c <;> simp [h]

/-- The default of an optional value `if c then some v else none` is `if c then v else d`. -/
private theorem getD_ite_some_none {α : Type*} (c : Prop) [Decidable c] (v d : α) :
    (if c then some v else none).getD d = if c then v else d := by
  by_cases h : c <;> simp [h]

/-- The attempt of the simulator at index `t` on the layout `w`. -/
noncomputable def attemptAt (V' : Strategy) (w : List Bool) (t : ℕ) : Option (List Bool) :=
  attemptStr V' (simX w) (simZ w) (coinSlice (blockLen V' (simX w).length) t (simR w))

/-- **One attempt is polynomial-time.** On the indexed layout `u = ⟨1^t, w⟩`, both the
success test of the `t`-th attempt and its (defaulted) view are polynomial-time functions.

**Proof sketch.** `V'.Efficient` gives a uniform machine `A` with `V'.next x z rV [H] =
A.output ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, ⟨H, []⟩⟩⟩, []⟩, rV⟩` (`Strategy.ofNUPPT_next`,
`NUPPT.runAtL_eq_output_layout`), polynomial-time by `A.polyTimeComputable_output` and
`NUPPT.polyTimeComputable_layout`. The block is `(r.drop (t · L)).take L` with `L` in unary
(`unaryPoly_comp (blockPoly V')`, `unaryMul_poly`, `pairDropPoly`, `truncate_poly`); its
fields are the head bit (`headBit_poly`), the permutation coins (`tail_poly`, `truncate_poly`
at `(|x|+1)²`) and the tape (`pairDropPoly`); the permutation word is
`polyTimeComputable_encPermFromCoins` on `⟨fst x, coins⟩`, the graph `H` is
`encPermGraphAt_poly` on `⟨1^n, ⟨G_{b'}, encPerm π⟩⟩` (`decPerm_encPerm`), the comparison is
`polyTimeComputable_pairEq` on the two one-bit words, and the view is assembled by
`PolyTimeComputable.pairEncode`. -/
theorem attemptAt_poly (V' : Strategy) (hV' : V'.Efficient) :
    PolyTimeComputable (fun u => [(attemptAt V' (pairSndD u) (pairFstD u).length).isSome]) ∧
    PolyTimeComputable (fun u => (attemptAt V' (pairSndD u) (pairFstD u).length).getD []) := by
  obtain ⟨A, hA, -, hnext⟩ := hV'
  have hx : PolyTimeComputable fun u => simX (pairSndD u) := simX_poly.comp polyTimeComputable_pairSndD
  have hz : PolyTimeComputable fun u => simZ (pairSndD u) := simZ_poly.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => simR (pairSndD u) := simR_poly.comp polyTimeComputable_pairSndD
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  -- the block length in unary
  have hL : PolyTimeComputable fun u => List.replicate (blockLen V' (simX (pairSndD u)).length) true := by
    have := unaryPoly_comp (blockPoly V') hx
    simpa only [blockPoly_eval] using this
  -- the block `c = (r.drop (t L)).take L`
  have hdrop : PolyTimeComputable fun u =>
      (simR (pairSndD u)).drop ((pairFstD u).length * blockLen V' (simX (pairSndD u)).length) := by
    have := (polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hL).pairEncode hr)
    refine ptc_congr this fun u => ?_
    simp
  have hc : PolyTimeComputable fun u =>
      coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u)) :=
    truncate_poly hdrop hL
  -- the guessed bit
  have hb : PolyTimeComputable fun u =>
      [(coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false] :=
    headBit_poly.comp hc
  -- `(|x| + 1)²` in unary
  have hP : PolyTimeComputable fun u => List.replicate (((simX (pairSndD u)).length + 1) ^ 2) true := by
    have := unaryPoly_comp (.normal 1 2) hx
    simpa only [PolyExpr.eval_normal, one_mul] using this
  -- the permutation coins
  have hpc : PolyTimeComputable fun u =>
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1).take
        (((simX (pairSndD u)).length + 1) ^ 2) := by
    have htail : PolyTimeComputable fun u =>
        (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1 := by
      have := tail_poly.comp hc
      simpa only [List.drop_one] using this
    exact truncate_poly htail hP
  -- the verifier's tape
  have hrV : PolyTimeComputable fun u =>
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2) := by
    have h1P : PolyTimeComputable fun u =>
        List.replicate (1 + ((simX (pairSndD u)).length + 1) ^ 2) true :=
      unaryAdd_poly (unaryConst_poly 1) hP
    have := (polyTimeComputable_pairDropPoly .var).comp (h1P.pairEncode hc)
    refine ptc_congr this fun u => ?_
    simp
  -- the vertex count in unary
  have hn : PolyTimeComputable fun u => List.replicate (instanceVertexCount (simX (pairSndD u))) true :=
    unarySqrt_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp hx))
  -- the sampled permutation as a word
  have hπ : PolyTimeComputable fun u => encPerm (samplePerm (instanceVertexCount (simX (pairSndD u)))
      (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop 1).take
        (((simX (pairSndD u)).length + 1) ^ 2))) := by
    have := polyTimeComputable_encPermFromCoins.comp ((polyTimeComputable_pairFstD.comp hx).pairEncode hpc)
    refine ptc_congr this fun u => ?_
    simp only [Function.comp_apply]
    rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  -- the guessed graph's word
  have hGb : PolyTimeComputable fun u =>
      if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false then pairSndD (simX (pairSndD u)) else pairFstD (simX (pairSndD u)) :=
    polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp hx) (polyTimeComputable_pairFstD.comp hx)
  -- the message `H`
  have hH : PolyTimeComputable fun u => encGraph (permGraph
      (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
      (samplePerm (instanceVertexCount (simX (pairSndD u)))
        (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
          1).take (((simX (pairSndD u)).length + 1) ^ 2)))) := by
    have := encPermGraphAt_poly.comp (hn.pairEncode (hGb.pairEncode hπ))
    refine ptc_congr this fun u => ?_
    simp only [Function.comp_apply]
    rw [pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate, decPerm_encPerm]
    split_ifs <;> rfl
  -- the verifier's reply
  have hmsg : PolyTimeComputable fun u => V'.next (simX (pairSndD u)) (simZ (pairSndD u))
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2))
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2))))] := by
    have hlay := NUPPT.polyTimeComputable_layout (polyTimeComputable_unary.comp hx)
      ((hx.pairEncode hz).pairEncode (hH.pairEncode (polyTimeComputable_const [])))
      (polyTimeComputable_const []) hrV
    have := A.polyTimeComputable_output.comp hlay
    have hadv : ∀ k, A.advice k = [] := hA
    refine ptc_congr this fun u => ?_
    rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hadv]
    rfl
  -- the success test
  have htest : PolyTimeComputable fun u => [decide ((V'.next (simX (pairSndD u)) (simZ (pairSndD u))
      ((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2))
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2))))]).headD false =
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
        false)] := by
    have := polyTimeComputable_pairEq.comp ((headBit_poly.comp hmsg).pairEncode hb)
    refine ptc_congr this fun u => ?_
    simp
  -- the view
  have hview : PolyTimeComputable fun u => View.encode ⟨simX (pairSndD u), simZ (pairSndD u),
      (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
        (1 + ((simX (pairSndD u)).length + 1) ^ 2),
      [encGraph (permGraph
        (if (coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).headD
          false then instanceG₁ (simX (pairSndD u)) else instanceG₀ (simX (pairSndD u)))
        (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2)))),
        encPerm (samplePerm (instanceVertexCount (simX (pairSndD u)))
          (((coinSlice (blockLen V' (simX (pairSndD u)).length) (pairFstD u).length (simR (pairSndD u))).drop
            1).take (((simX (pairSndD u)).length + 1) ^ 2)))]⟩ :=
    ptc_congr ((hx.pairEncode hz).pairEncode (hrV.pairEncode (hH.pairEncode
      (hπ.pairEncode (polyTimeComputable_const []))))) fun u => rfl
  refine ⟨?_, ?_⟩
  · refine ptc_congr htest fun u => ?_
    simp only [attemptAt, attemptStr]
    exact isSome_ite_some_none _ _
  · refine ptc_congr (polyTimeComputable_ite htest hview (polyTimeComputable_const [])) fun u => ?_
    simp only [attemptAt, attemptStr, decide_eq_true_eq]
    exact getD_ite_some_none _ _ _

/-! ### The loop over the attempts -/

/-- `List.findSome?` over `List.range m` returns the value at the least accepted index
(`List.range_add`, `List.range_succ`, `List.findSome?_append`). -/
theorem findSome?_range_eq_of {β : Type*} (f : ℕ → Option β) {m i : ℕ} (hi : i < m) {v : β}
    (hv : f i = some v) (hmin : ∀ j < i, f j = none) : (List.range m).findSome? f = some v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = i + 1 + k := ⟨m - (i + 1), by omega⟩
  rw [List.range_add, List.findSome?_append, List.range_succ, List.findSome?_append]
  have h0 : (List.range i).findSome? f = none :=
    List.findSome?_eq_none_iff.2 fun j hj => hmin j (List.mem_range.1 hj)
  rw [h0]
  simp [hv]

/-- The defaulted `List.findSome?` over `List.range m` through the first accepted index
`EncodingMachines.firstIdx`: the value there if the search succeeds, `[]` otherwise.

**Proof sketch.** If `firstIdx q m < m` then `f` is `some` there (`q_firstIdx`) and `none`
below (`firstIdx_min`), so `findSome?_range_eq_of` applies; otherwise `firstIdx q m = m` and
`f` is `none` on the whole range (`firstIdx_eq_iff`, `List.findSome?_eq_none_iff`). -/
theorem findSome?_range_getD (f : ℕ → Option (List Bool)) (m : ℕ) :
    ((List.range m).findSome? f).getD [] =
      if firstIdx (fun t => (f t).isSome) m < m then (f (firstIdx (fun t => (f t).isSome) m)).getD []
      else [] := by
  split_ifs with h
  · have hq := q_firstIdx h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hq
    rw [findSome?_range_eq_of f h hv fun j hj => ?_, hv]
    have := firstIdx_min hj
    cases hf : f j
    · rfl
    · rw [hf] at this
      simp at this
  · have hm : firstIdx (fun t => (f t).isSome) m = m := le_antisymm firstIdx_le (not_lt.1 h)
    have hall := firstIdx_eq_iff.1 hm
    rw [List.findSome?_eq_none_iff.2 fun j hj => ?_]
    · rfl
    · have := hall j (List.mem_range.1 hj)
      cases hf : f j
      · rfl
      · rw [hf] at this
        simp at this

/-- **The simulator is polynomial-time** as a function of its machine layout: the first
accepted attempt index is `EncodingMachines.polyTimeComputable_firstIdx` with the success test
of `attemptAt_poly`, and the output is that attempt's view (`attemptAt_poly`) or `[]`
(`findSome?_range_getD`). -/
theorem sim_poly (V' : Strategy) (hV' : V'.Efficient) :
    PolyTimeComputable fun w => sim V' (simX w) (simZ w) (simR w) := by
  obtain ⟨hp, hout⟩ := attemptAt_poly V' hV'
  have hlen : PolyTimeComputable fun w => List.replicate (instanceVertexCount (simX w)) true :=
    unarySqrt_poly (unaryLength_poly (polyTimeComputable_pairFstD.comp simX_poly))
  have hidx := polyTimeComputable_firstIdx (p := fun w t => (attemptAt V' w t).isSome) hp hlen
  have hsel : PolyTimeComputable fun w =>
      (attemptAt V' w (firstIdx (fun t => (attemptAt V' w t).isSome) (instanceVertexCount (simX w)))).getD [] := by
    have := hout.comp (hidx.pairEncode polyTimeComputable_id)
    refine ptc_congr this fun w => ?_
    simp
  have hF := polyTimeComputable_ite (ltTest_poly hidx hlen) hsel (polyTimeComputable_const [])
  refine ptc_congr hF fun w => ?_
  simp only [decide_eq_true_eq]
  exact findSome?_range_getD (attemptAt V' w) (instanceVertexCount (simX w))

/-- **The simulator is a uniform PPT** (Claim-123.d, shadow form): `NUPPT.ofPolyTimeUniform`
of `sim_poly` with the coin polynomial `simCoins V'` computes `sim V' x z r` on
`⟨x, z⟩` at parameter `|x|` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_simulator (V' : Strategy) (hV' : V'.Efficient) :
    ∃ S : NUPPT, S.Uniform ∧ S.coins = simCoins V' ∧
      ∀ x z (r : S.Coins x.length), S.simulate x z r = sim V' x z (List.ofFn r) := by
  have hF := sim_poly V' hV'
  refine ⟨NUPPT.ofPolyTimeUniform hF (simCoins V'), NUPPT.ofPolyTimeUniform_uniform _ _, rfl, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [simX, simZ, simR, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

end TCSlib.Cryptography.GIZK

## ===== TCSlib/Cryptography/ZeroKnowledge/Encoding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.Permutations
import TCSlib.Cryptography.ZeroKnowledge.EncodingPermutations
import TCSlib.Complexity.ClassNP.PolyTimePairing
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Sqrt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String encodings for the graph protocols

The string layer of Chapter 4 (Inf-4.1, Inf-4.2): the typed objects of the graph protocols
[PS10, §4.5–§4.7] — graphs on `Fin n` as adjacency matrices, permutations of `Fin n`,
`3`-colourings — with their encodings as bit strings, total decoders with defaults, the
decode-encode identities, the coin table that reads the random tape of a party as the
`n × T × k` array consumed by the rejection-sampled permutation `permFromCoins` of
`Asymptotic/Permutations.lean` (D10), and the polynomial-time computability statements of the
honest parties' string operations (Inf-4.2: applying a permutation to a graph, composing
permutations, sampling a permutation from coins).

Graphs are arbitrary Boolean relations `Fin n → Fin n → Bool` (loops and asymmetry allowed):
the protocols never use simplicity, and the encoding is the row-major `n²`-bit matrix with
`n` recovered as `Nat.sqrt` of the length. `permGraph G π u v := G (π⁻¹ u) (π⁻¹ v)` is the
relabelled graph `π(G)` of [PS10, §4.5] (`π(G)` has edge `(π u, π v)` iff `G` has `(u, v)`).

**Deviation (D10, Inf-4.2):** a uniformly random permutation `σ ← S_n` of [PS10, Protocols
118.3, 120.6, 127.5] is sampled from a bit-coin tape by `permFromCoins` (rejection sampling
with `T` trials of `k` bits per position), which fails with probability at most
`n (1 - 2^{-k})^T`; at the campaign parameters `permBits n = Nat.size n`,
`permTrials n = 2n²` the failure probability is at most `n · 2^{-n}`
(`uprob_permFromCoins_none_le_two_pow`), and the protocol theorems carry this statistical
term.

## Main definitions

* `TCSlib.Cryptography.Graph`, `TCSlib.Cryptography.permGraph` — graphs on `Fin n` and the
  relabelling `π(G)` [PS10, §4.5] (Def-117.e, string side).
* `TCSlib.Cryptography.encGraph`, `TCSlib.Cryptography.decGraph` — adjacency-matrix encoding
  and total decoding.
* `TCSlib.Cryptography.encPerm`, `TCSlib.Cryptography.decPerm` — the relation-matrix encoding
  of a permutation and its total decoding (identity on malformed words).
* `TCSlib.Cryptography.encColoring`, `TCSlib.Cryptography.decColoring` — two bits per vertex
  for `Fin 3`-colourings [PS10, Protocol 127.5].
* `TCSlib.Cryptography.coinTable` — the `n × T × k` coin array read from a random tape.

## Main results

* `TCSlib.Cryptography.permGraph_one`, `TCSlib.Cryptography.permGraph_mul` — relabelling is
  a right action: `1(G) = G`, `σ(π(G)) = (σ π)(G)` (the algebra of [PS10, Lemma 120.a]).
* `TCSlib.Cryptography.decGraph_encGraph`, `TCSlib.Cryptography.decPerm_encPerm`,
  `TCSlib.Cryptography.decColoring_encColoring` — decode-encode identities (proved);
  `TCSlib.Cryptography.encGraph_injective`, `TCSlib.Cryptography.encPerm_injective`.
* `TCSlib.Cryptography.pushesUniform_coinTable` — a uniform tape of `n T k` bits gives a
  uniform coin table (`coinTable_ofFn`).
* `TCSlib.Cryptography.encGraph_getD_nat`, `TCSlib.Cryptography.encPerm_getD_nat`,
  `TCSlib.Cryptography.decPerm_val`, `TCSlib.Cryptography.decPerm_symm_val` — numeric access
  to the encodings and the identification of `decPerm` with the numeric decoder model of
  `EncodingPermutations.lean` (`EncodingMachines.permNum`, `permInvNum`).
* `TCSlib.Cryptography.polyTimeComputable_encPermGraph`,
  `TCSlib.Cryptography.polyTimeComputable_encPermMulInv`,
  `TCSlib.Cryptography.polyTimeComputable_encPermFromCoins` — the honest parties' string
  operations are polynomial-time (Inf-4.2), through the bit-extraction principle and the
  numeric models of `EncodingMachines.lean` and `EncodingPermutations.lean`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Graphs and relabelling -/

/-- A graph on the vertex set `Fin n` as a Boolean adjacency relation [PS10, §4.5]
(Def-117.e, string side; simplicity is not needed by the protocols). -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- The relabelled graph `π(G)` [PS10, §4.5]: `π(G)` has the edge `(π u, π v)` exactly when
`G` has the edge `(u, v)`, i.e. `π(G) u v = G (π⁻¹ u) (π⁻¹ v)`. -/
def permGraph {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) : Graph n :=
  fun u v => G (π.symm u) (π.symm v)

/-- Unfolding of `permGraph`. -/
@[simp] theorem permGraph_apply {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    permGraph G π u v = G (π.symm u) (π.symm v) := rfl

/-- The identity relabelling is the identity. -/
@[simp] theorem permGraph_one {n : ℕ} (G : Graph n) : permGraph G 1 = G := rfl

/-- Relabelling is a right action: `σ(π(G)) = (σ * π)(G)` (the algebra behind
[PS10, Proposition 120.7], completeness: `(π σ⁻¹)(σ(G₀)) = π(G₀)`). -/
theorem permGraph_mul {n : ℕ} (G : Graph n) (π σ : Equiv.Perm (Fin n)) :
    permGraph (permGraph G π) σ = permGraph G (σ * π) := by
  funext u v
  simp [permGraph, Equiv.Perm.mul_def]

/-- Relabelling by `π` and then by `π⁻¹` gives the graph back. -/
theorem permGraph_permGraph_inv {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) :
    permGraph (permGraph G π) π⁻¹ = G := by
  rw [permGraph_mul, inv_mul_cancel, permGraph_one]

/-- The completeness identity of the graph-isomorphism protocol [PS10, Proposition 120.7]
(Lem-120.a): if `σ(G₀) = G₁` and `H = π(G₀)` then `(π σ⁻¹)(G₁) = H`. -/
theorem permGraph_mul_inv_of_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) :
    permGraph G₁ (π * σ⁻¹) = permGraph G₀ π := by
  rw [← hσ, permGraph_mul, inv_mul_cancel_right]

/-! ### Encodings of graphs -/

/-- The adjacency-matrix encoding of a graph: `n²` bits in row-major order (entry `(u, v)` at
position `finProdFinEquiv (u, v) = u * n + v`). -/
def encGraph {n : ℕ} (G : Graph n) : List Bool :=
  List.ofFn fun k : Fin (n * n) => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The total decoding of a graph: the number of vertices is `Nat.sqrt` of the length, the
entries are read with default `false`. -/
def decGraph (w : List Bool) : Σ n, Graph n :=
  ⟨Nat.sqrt w.length, fun u v => w.getD (finProdFinEquiv (u, v)) false⟩

/-- An encoded graph on `n` vertices has `n²` bits. -/
@[simp] theorem length_encGraph {n : ℕ} (G : Graph n) : (encGraph G).length = n * n := by
  simp [encGraph]

/-- The entries of an encoded graph. -/
theorem encGraph_getD {n : ℕ} (G : Graph n) (u v : Fin n) :
    (encGraph G).getD (finProdFinEquiv (u, v)) false = G u v := by
  have hk : (finProdFinEquiv (u, v) : ℕ) < (encGraph G).length := by
    rw [length_encGraph]
    exact (finProdFinEquiv (u, v)).isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [encGraph, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]

/-- Decoding an encoded graph gives the graph back (Inf-4.1). -/
theorem decGraph_encGraph {n : ℕ} (G : Graph n) : decGraph (encGraph G) = ⟨n, G⟩ := by
  have hn : Nat.sqrt (encGraph G).length = n := by rw [length_encGraph, Nat.sqrt_eq]
  unfold decGraph
  rw [hn, Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (funext fun u => funext fun v => encGraph_getD G u v)⟩

/-- The encoding of graphs is injective. -/
theorem encGraph_injective (n : ℕ) : Function.Injective (encGraph (n := n)) := by
  intro G G' h
  funext u v
  rw [← encGraph_getD G, ← encGraph_getD G', h]

/-! ### Encodings of permutations -/

/-- The relation-matrix encoding of a permutation: bit `(i, j)` is `decide (π i = j)`. -/
def encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : List Bool :=
  List.ofFn fun k : Fin (n * n) =>
    decide (π (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2)

/-- The total decoding of a permutation of `Fin n`: row `i` is read as the least `j` with bit
`(i, j)` set (default `i`); if the resulting map is bijective it is the permutation, otherwise
the identity. -/
noncomputable def decPerm (n : ℕ) (w : List Bool) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Function.Bijective (fun i : Fin n =>
      (Fin.find (fun j : Fin n => w.getD (finProdFinEquiv (i, j)) false = true)).getD i)
    then Equiv.ofBijective _ h else 1

/-- An encoded permutation of `Fin n` has `n²` bits. -/
@[simp] theorem length_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : (encPerm π).length = n * n := by
  simp [encPerm]

/-- The entries of an encoded permutation. -/
theorem encPerm_getD {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (encPerm π).getD (finProdFinEquiv (i, j)) false = decide (π i = j) := by
  have hk : (finProdFinEquiv (i, j) : ℕ) < (encPerm π).length := by
    rw [length_encPerm]
    exact (finProdFinEquiv (i, j)).isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [encPerm, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]

/-- Row `i` of an encoded permutation has exactly one set bit, at column `π i`: the decoder's
search finds it (for any decidability instance of the search predicate). -/
theorem encPerm_find_row {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n)
    [DecidablePred fun j : Fin n => (encPerm π).getD (finProdFinEquiv (i, j)) false = true] :
    Fin.find (fun j : Fin n => (encPerm π).getD (finProdFinEquiv (i, j)) false = true) =
      some (π i) := by
  rw [← Option.mem_def, Fin.mem_find_iff]
  refine ⟨by rw [encPerm_getD]; simp, fun j hj => ?_⟩
  rw [encPerm_getD] at hj
  exact le_of_eq (by simpa using hj)

/-- Decoding an encoded permutation gives the permutation back (Inf-4.1): by
`encPerm_find_row` the decoded map is `⇑π`, which is bijective, so the decoder's first branch
applies and `Equiv.ofBijective ⇑π _ = π`. -/
theorem decPerm_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : decPerm n (encPerm π) = π := by
  unfold decPerm
  split_ifs with h
  · refine Equiv.ext fun i => ?_
    rw [Equiv.ofBijective_apply]
    show (Fin.find _).getD i = π i
    rw [encPerm_find_row, Option.getD_some]
  · exfalso
    apply h
    convert π.bijective using 1
    funext i
    rw [encPerm_find_row, Option.getD_some]

/-- The encoding of permutations is injective. -/
theorem encPerm_injective (n : ℕ) : Function.Injective (encPerm (n := n)) := by
  intro π π' h
  refine Equiv.ext fun i => ?_
  have h1 := encPerm_getD π i (π i)
  rw [h, encPerm_getD] at h1
  have h2 : π' i = π i := by simpa using h1.symm
  exact h2.symm

/-! ### Encodings of colourings -/

/-- The encoding of a `3`-colouring of `Fin n` [PS10, Protocol 127.5]: two bits per vertex
(the colour `c ∈ {0, 1, 2}` as `[c / 2 = 1, c % 2 = 1]`), `2n` bits in all. -/
def encColoring {n : ℕ} (c : Fin n → Fin 3) : List Bool :=
  List.ofFn fun k : Fin (n * 2) =>
    let i := (finProdFinEquiv.symm k).1
    let b := (finProdFinEquiv.symm k).2
    if b = 0 then decide ((c i).val / 2 = 1) else decide ((c i).val % 2 = 1)

/-- The total decoding of a `3`-colouring of `Fin n`: the two bits of vertex `i` are read with
default `false` and combined modulo `3`. -/
def decColoring (n : ℕ) (w : List Bool) : Fin n → Fin 3 := fun i =>
  ⟨(2 * (w.getD (finProdFinEquiv (i, (0 : Fin 2))) false).toNat +
      (w.getD (finProdFinEquiv (i, (1 : Fin 2))) false).toNat) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- An encoded colouring of `n` vertices has `2n` bits. -/
@[simp] theorem length_encColoring {n : ℕ} (c : Fin n → Fin 3) :
    (encColoring c).length = n * 2 := by
  simp [encColoring]

/-- Decoding an encoded colouring gives the colouring back (Inf-4.1): the two bits of vertex
`i` are `decide (c i / 2 = 1)` and `decide (c i % 2 = 1)`, and for `c i ∈ {0, 1, 2}` the
number `2 · [c i / 2 = 1] + [c i % 2 = 1]` is `c i` (checked by `decide`). -/
theorem decColoring_encColoring {n : ℕ} (c : Fin n → Fin 3) : decColoring n (encColoring c) = c := by
  funext i
  have hget : ∀ b : Fin 2, (encColoring c).getD (finProdFinEquiv (i, b)) false =
      if b = 0 then decide ((c i).val / 2 = 1) else decide ((c i).val % 2 = 1) := by
    intro b
    have hk : (finProdFinEquiv (i, b) : ℕ) < (encColoring c).length := by
      rw [length_encColoring]
      exact (finProdFinEquiv (i, b)).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    simp only [encColoring, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hval : ∀ x : Fin 3,
      (2 * (decide (x.val / 2 = 1)).toNat + (decide (x.val % 2 = 1)).toNat) % 3 = x.val := by
    decide
  apply Fin.ext
  simp only [decColoring, hget, if_true, Fin.isValue, one_ne_zero, if_false]
  exact hval (c i)

/-! ### Coin tables -/

/-- The `n × T × k` coin array read from a random tape (bit `(i, t, j)` at position
`(i T + t) k + j`, default `false`): the input of `permFromCoins n k T` for a party whose
random tape is a string (D10). -/
def coinTable (n T k : ℕ) (r : List Bool) : Fin n → Fin T → Fin k → Bool :=
  fun i t j => r.getD (((i * T) + t) * k + j) false

/-- Unfolding of `coinTable`. -/
@[simp] theorem coinTable_apply (n T k : ℕ) (r : List Bool) (i : Fin n) (t : Fin T) (j : Fin k) :
    coinTable n T k r i t j = r.getD (((i * T) + t) * k + j) false := rfl

/-- The entries of the coin table of a tape of exactly `n T k` bits: entry `(i, t, j)` is the
tape bit at the index `finProdFinEquiv (finProdFinEquiv (i, t), j) = (i T + t) k + j`. -/
theorem coinTable_ofFn (n T k : ℕ) (r : Fin (n * T * k) → Bool) (i : Fin n) (t : Fin T)
    (j : Fin k) :
    coinTable n T k (List.ofFn r) i t j = r (finProdFinEquiv (finProdFinEquiv (i, t), j)) := by
  have hm : ((finProdFinEquiv (finProdFinEquiv (i, t), j) : Fin (n * T * k)) : ℕ) =
      ((i * T) + t) * k + j := by
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [coinTable_apply, ← hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _),
    Option.getD_some, Fin.eta]

/-- A uniform tape of `n T k` bits gives a uniform coin table: the map from tapes of length
`n T k` to tables is a bijection, hence pushes the uniform distribution to the uniform one
(the step that lets the ideal `permFromCoins` lemmas of `Sampling.lean` be applied to a party
sampling its permutation from its random tape).

**Proof sketch.** The index map `(i, t, j) ↦ (i T + t) k + j` is the bijection
`Fin n × Fin T × Fin k ≃ Fin (n T k)` (`finProdFinEquiv` twice, `Nat.lt_of_lt_of_le` for the
range), so `r ↦ coinTable n T k (List.ofFn r)` is the curried reindexing
`(Fin (n T k) → Bool) ≃ (Fin n → Fin T → Fin k → Bool)` (`Equiv.piCongrLeft`, `Equiv.curry`),
and `HardcoreBit.pushesUniform_equiv` applies (`List.getD_eq_getElem?_getD`,
`List.getElem?_ofFn` identify the entries). -/
theorem pushesUniform_coinTable (n T k : ℕ) :
    HardcoreBit.PushesUniform
      (fun r : Fin (n * T * k) → Bool => coinTable n T k (List.ofFn r)) := by
  have hbij : Function.Bijective
      (fun r : Fin (n * T * k) → Bool => coinTable n T k (List.ofFn r)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun r r' h => ?_, ?_⟩
    · funext m
      have h1 := congrFun (congrFun (congrFun h
        (finProdFinEquiv.symm (finProdFinEquiv.symm m).1).1)
        (finProdFinEquiv.symm (finProdFinEquiv.symm m).1).2) (finProdFinEquiv.symm m).2
      dsimp only at h1
      rwa [coinTable_ofFn, coinTable_ofFn, Prod.mk.eta, Equiv.apply_symm_apply, Prod.mk.eta,
        Equiv.apply_symm_apply] at h1
    · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul]
      ring_nf
  exact HardcoreBit.pushesUniform_equiv (Equiv.ofBijective _ hbij)

/-! ### Numeric access to the encodings -/

/-- Bit `v + n u` of an encoded graph is the entry `(u, v)` (`encGraph_getD` with
`finProdFinEquiv_apply_val`). -/
theorem encGraph_getD_nat {n : ℕ} (G : Graph n) (u v : Fin n) :
    (encGraph G).getD (v + n * u) false = G u v := by
  have h := encGraph_getD G u v
  rwa [finProdFinEquiv_apply_val] at h

/-- Bits beyond `n²` of an encoded graph read `false`. -/
theorem encGraph_getD_of_le {n : ℕ} (G : Graph n) {m : ℕ} (hm : n * n ≤ m) :
    (encGraph G).getD m false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_encGraph]; exact hm)]
  rfl

/-- Bit `j + n i` of an encoded permutation is `decide (π i = j)`. -/
theorem encPerm_getD_nat {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (encPerm π).getD (j + n * i) false = decide (π i = j) := by
  have h := encPerm_getD π i j
  rwa [finProdFinEquiv_apply_val] at h

/-- Bits beyond `n²` of an encoded permutation read `false`. -/
theorem encPerm_getD_of_le {n : ℕ} (π : Equiv.Perm (Fin n)) {m : ℕ} (hm : n * n ≤ m) :
    (encPerm π).getD m false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_encPerm]; exact hm)]
  rfl

/-- The row-major index of `(i, j)` in the two conventions: `i n + j = j + n i`. -/
theorem idx_comm (n i j : ℕ) : i * n + j = j + n * i := by ring

/-! ### The numeric model of the decoder -/

open EncodingMachines in
/-- The decoded map of `decPerm` (row `i` ↦ its first set column, default `i`) is `rowMap`
numerically.

**Proof sketch.** Case on `Fin.find`. If it is `none` (`Fin.find_eq_none_iff`) no column of row
`i` is set, so the search `rowFirst` is exhausted (`firstIdx_eq_of_forall`) and both sides are
`i`. If it is `some j` (`Fin.find_eq_some_iff`: `j` is set and minimal) the search returns `j`
(`firstIdx_eq_of`), which is below `n`, so `rowMap` is `j` too. The two index conventions
`finProdFinEquiv (i, j) = j + n i` and `i n + j` agree by `idx_comm`. -/
theorem decPerm_map_val {n : ℕ} (b : List Bool) (i : Fin n)
    [DecidablePred fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true] :
    (((Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i : Fin n) :
      ℕ) = rowMap n b i := by
  unfold rowMap rowFirst
  cases h : Fin.find (fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true) with
  | none =>
    rw [Fin.find_eq_none_iff] at h
    rw [Option.getD_none, if_pos]
    apply firstIdx_eq_of_forall
    intro j hj
    have := h ⟨j, hj⟩
    rw [finProdFinEquiv_apply_val] at this
    rw [idx_comm]
    exact Bool.eq_false_iff.2 this
  | some j =>
    rw [Fin.find_eq_some_iff] at h
    obtain ⟨hj, hmin⟩ := h
    rw [Option.getD_some]
    have hfirst : firstIdx (fun j' => b.getD (↑i * n + j') false) n = j := by
      apply firstIdx_eq_of j.isLt
      · rw [finProdFinEquiv_apply_val] at hj
        rw [idx_comm]
        exact hj
      · intro j' hj'
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hle := hmin ⟨j', lt_trans hj' j.isLt⟩
          (by rw [finProdFinEquiv_apply_val]; rw [idx_comm] at hc; exact hc)
        exact absurd hle (not_le.2 hj')
    rw [hfirst, if_neg j.isLt.ne]

open EncodingMachines in
/-- The decoded map of `decPerm` is bijective iff the numeric surjectivity test `isBij` holds
(`Finite.surjective_iff_bijective`, `isBij_iff`, `decPerm_map_val`). -/
theorem decPerm_bijective_iff {n : ℕ} (b : List Bool)
    [∀ i : Fin n, DecidablePred fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true] :
    Function.Bijective (fun i : Fin n =>
        (Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i) ↔
      isBij n b = true := by
  rw [isBij_iff, ← Finite.surjective_iff_bijective]
  constructor
  · intro hs u hu
    obtain ⟨i, hi⟩ := hs ⟨u, hu⟩
    simp only at hi
    exact ⟨i, i.isLt, by rw [← decPerm_map_val, hi]⟩
  · intro h u
    obtain ⟨i, hi, hiu⟩ := h u u.isLt
    exact ⟨⟨i, hi⟩, Fin.ext (by rw [decPerm_map_val]; exact hiu)⟩

open EncodingMachines in
/-- The decoded permutation, numerically: `decPerm n b i = permNum n b i`. -/
theorem decPerm_val {n : ℕ} (b : List Bool) (i : Fin n) :
    ((decPerm n b i : Fin n) : ℕ) = permNum n b i := by
  classical
  unfold decPerm permNum
  split_ifs with h1 h2 h2
  · rw [Equiv.ofBijective_apply]
    exact decPerm_map_val b i
  · exact absurd ((decPerm_bijective_iff b).1 h1) h2
  · exact absurd ((decPerm_bijective_iff b).2 h2) h1
  · rfl

open EncodingMachines in
/-- The inverse of the decoded permutation, numerically: `(decPerm n b)⁻¹ u = permInvNum n b u`.

**Proof sketch.** Unfold `decPerm`; the two branches agree with those of `permInvNum` by
`decPerm_bijective_iff`. In the bijective branch `i := (ofBijective map _).symm u` satisfies
`map i = u` (`Equiv.ofBijective_apply_symm_apply`), i.e. `rowMap n b i = u`
(`decPerm_map_val`), and no `i' < i` does (injectivity), so the search `rowInv` returns `i`
(`firstIdx_eq_of`). In the other branch both sides are the identity. -/
theorem decPerm_symm_val {n : ℕ} (b : List Bool) (u : Fin n) :
    (((decPerm n b).symm u : Fin n) : ℕ) = permInvNum n b u := by
  classical
  unfold decPerm permInvNum
  split_ifs with h1 h2 h2
  · have hmap := Equiv.ofBijective_apply_symm_apply _ h1 u
    unfold rowInv
    symm
    apply firstIdx_eq_of (Fin.isLt _)
    · rw [decide_eq_true_eq, ← decPerm_map_val, hmap]
    · intro i' hi'
      rw [decide_eq_false_iff_not]
      intro heq
      have hpre : (fun i : Fin n =>
          (Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i)
            ⟨i', lt_trans hi' (Fin.isLt _)⟩ = u :=
        Fin.ext (by rw [decPerm_map_val]; exact heq)
      have hval : (((Equiv.ofBijective _ h1).symm u : Fin n) : ℕ) = i' :=
        (congrArg Fin.val (h1.1 (hpre.trans hmap.symm))).symm
      omega
  · exact absurd ((decPerm_bijective_iff b).1 h1) h2
  · exact absurd ((decPerm_bijective_iff b).2 h2) h1
  · rfl

/-- `2^{Nat.size n} ≤ 2 n + 1` (`two_pow_permBits_le` for `n ≥ 1`, `1 ≤ 1` for `n = 0`): the
bound threaded through the block-value loops of the permutation sampler. -/
theorem two_pow_size_le_two_mul_succ (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_pow_permBits_le hn).trans (Nat.le_succ _)

/-! ### Polynomial-time string operations of the honest parties (Inf-4.2) -/

/-- Applying an encoded permutation to an encoded graph is polynomial-time
(`⟨encGraph G, encPerm π⟩ ↦ encGraph (π(G))`; the honest prover's first message in
[PS10, Protocol 120.6] and the relabelled graph of [PS10, Protocol 118.3]) (Inf-4.2).

**Proof sketch.** Both inputs have `n²` bits with `n = Nat.sqrt |·|`; the output bit at
position `(u, v)` is the input bit of `G` at `(π⁻¹ u, π⁻¹ v)`, where `π⁻¹ u` is the row index
`i` whose bit `(i, u)` is set. Machine: `polyTimeComputable_blockMap` over the `n²` output
positions (block length `1`, with the whole input threaded as the first pair component), each
block computed by a scan of the two matrices (`polyTimeComputable_iterateFind` over the `n`
candidate rows, the test being `polyTimeComputable_pairEq` on the relevant bits extracted by
`pairTakePoly`/`pairDropPoly`); `Nat.sqrt` is computed by iterating `polyTimeComputable_lenLe`
against `unaryPoly` squares (`polyTimeComputable_iterateFind`, at most `|w|` rounds). All
budgets are polynomial in the input length. -/
theorem polyTimeComputable_encPermGraph :
    PolyTimeComputable fun z =>
      encGraph (permGraph (decGraph (pairFstD z)).2 (decPerm _ (pairSndD z))) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encGraph (permGraph (decGraph (pairFstD z)).2 (decPerm _ (pairSndD z)))).length true := by
    simpa only [length_encGraph] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have ha : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hu := permInvNum_poly hN' hb (divNum_poly hm hN')
  have hv := permInvNum_poly hN' hb (modNum_poly hm hN')
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (getBit_poly ha (unaryAdd_poly hv (unaryMul_poly hN' hu))) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  show [(encGraph (permGraph (n := n) (decGraph (pairFstD (pairSndD w))).2
    (decPerm n (pairSndD (pairSndD w))))).getD m false] = _
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    conv_lhs => rw [hidx]
    rw [encGraph_getD_nat, permGraph_apply]
    show [(pairFstD (pairSndD w)).getD (finProdFinEquiv _) false] = _
    rw [finProdFinEquiv_apply_val, decPerm_symm_val, decPerm_symm_val]
  · rw [encGraph_getD_of_le _ (not_lt.1 hlt)]

/-- Composing an encoded permutation with the inverse of another is polynomial-time
(`⟨encPerm π, encPerm σ⟩ ↦ encPerm (π σ⁻¹)` at `n = Nat.sqrt |encPerm π|`; the honest prover's
third message in [PS10, Protocol 120.6]) (Inf-4.2).

**Proof sketch.** Output bit `(i, j)` is set iff `π (σ⁻¹ i) = j`, i.e. iff the row `l` with
bit `(l, i)` of `σ` set has bit `(l, j)` of `π` set: for each of the `n²` output positions
(`polyTimeComputable_blockMap`) a scan over the `n` rows (`polyTimeComputable_iterateFind`)
with bit tests by `pairTakePoly`/`pairDropPoly` and `polyTimeComputable_pairEq`; the decoder's
bijectivity test and the identity fallback are `polyTimeComputable_ite` over a scan checking
that every row and every column has exactly one set bit. -/
theorem polyTimeComputable_encPermMulInv :
    PolyTimeComputable fun z =>
      encPerm (decPerm (Nat.sqrt (pairFstD z).length) (pairFstD z) *
        (decPerm (Nat.sqrt (pairFstD z).length) (pairSndD z))⁻¹) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encPerm (decPerm (Nat.sqrt (pairFstD z).length) (pairFstD z) *
        (decPerm (Nat.sqrt (pairFstD z).length) (pairSndD z))⁻¹)).length true := by
    simpa only [length_encPerm] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have ha : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hi := permNum_poly hN' ha (permInvNum_poly hN' hb (divNum_poly hm hN'))
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (eqTest_poly hi (modNum_poly hm hN')) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    conv_lhs => rw [hidx]
    rw [encPerm_getD_nat, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    congr 1
    rw [decide_eq_decide, Fin.ext_iff, decPerm_val, decPerm_symm_val]
  · rw [encPerm_getD_of_le _ (not_lt.1 hlt)]

/-- Sampling a permutation of the vertices of an encoded graph from a random tape is
polynomial-time: `⟨encGraph G, r⟩ ↦ encPerm (permFromCoins n (permBits n) (permTrials n)
(coinTable n (permTrials n) (permBits n) r))` with `n = (decGraph (encGraph G)).1` and the
identity on failure — the honest parties' `σ ← S_n` of [PS10, Protocols 118.3, 120.6 and
127.5] under D10 at the campaign parameters (Inf-4.2); it is the shared string form of
`samplePerm` (`ZeroKnowledge/GraphIsomorphism.lean`).

**Repair (run-3 audit P2-1):** restated at the campaign parameters `permBits n = Nat.size n`
bits per trial and `permTrials n = 2n²` trials per position (`Asymptotic/Permutations.lean`);
the frozen `permFromCoins n n n` fails almost surely. The private
`polyTimeComputable_encSamplePerm` of `GraphIsomorphism.lean` is derived from this lemma.
(Run-3 audit P9-2, which reported the run-2 statement at `permFromCoins n n n` as diverging
from `samplePerm`, is resolved by the same repair: `samplePerm n r` unfolds to the sampler
stated here, so the lemma is the one the fill phase proves.)

**Proof sketch.** `n = Nat.sqrt |encGraph G|` (as in `polyTimeComputable_encPermGraph`), and
`1^{permBits n}` by `polyTimeComputable_lenLe` against the `unaryPoly` powers of two
(`polyTimeComputable_iterateFind`, at most `n` rounds). For each position `i < n`
(`polyTimeComputable_iterateEmit` over `i`), the `2n²` trials of `permBits n` bits are the
blocks of the tape (`polyTimeComputable_blockMap` with the unary block length), each read as a
number and compared with `n - i` (`bitsToNat` in binary by `computesFunInTime_polyBits`-style
arithmetic, or in unary by `unaryPoly` and `polyTimeComputable_lenLe`), the first accepted
one being `polyTimeComputable_iterateFind`; the Fisher–Yates product of the `n` transpositions
is accumulated as an `n²`-bit relation matrix (`polyTimeComputable_iterate` over `n` rounds,
each round swapping two rows); failure of any position selects the identity matrix
(`polyTimeComputable_ite`). -/
theorem polyTimeComputable_encPermFromCoins :
    PolyTimeComputable fun z =>
      encPerm ((permFromCoins (decGraph (pairFstD z)).1 (permBits (decGraph (pairFstD z)).1)
        (permTrials (decGraph (pairFstD z)).1)
        (coinTable (decGraph (pairFstD z)).1 (permTrials (decGraph (pairFstD z)).1)
          (permBits (decGraph (pairFstD z)).1) (pairSndD z))).getD 1) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encPerm ((permFromCoins (decGraph (pairFstD z)).1 (permBits (decGraph (pairFstD z)).1)
        (permTrials (decGraph (pairFstD z)).1)
        (coinTable (decGraph (pairFstD z)).1 (permTrials (decGraph (pairFstD z)).1)
          (permBits (decGraph (pairFstD z)).1) (pairSndD z))).getD 1)).length true := by
    simpa only [length_encPerm] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hr : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hK := unarySize_poly hN'
  have hT := unaryMul_poly (unaryMul_poly (unaryConst_poly 2) hN') hN'
  have hM := unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) hN') (unaryConst_poly 1)
  have hX := unaryMin_poly (divNum_poly hm hN') hN'
  have hval := permFromCoinsNum_poly hN' hK hT hr hX hM
    (fun w => two_pow_size_le_two_mul_succ _) (fun w => min_le_right _ _)
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (eqTest_poly hval (modNum_poly hm hN')) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  show [(encPerm ((permFromCoins (Nat.sqrt (pairFstD (pairSndD w)).length)
      (permBits (Nat.sqrt (pairFstD (pairSndD w)).length))
      (permTrials (Nat.sqrt (pairFstD (pairSndD w)).length))
      (coinTable (Nat.sqrt (pairFstD (pairSndD w)).length)
        (permTrials (Nat.sqrt (pairFstD (pairSndD w)).length))
        (permBits (Nat.sqrt (pairFstD (pairSndD w)).length)) (pairSndD (pairSndD w)))).getD 1)).getD
    (pairFstD w).length false] = _
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    rw [min_eq_left hu'.le]
    conv_lhs => rw [hidx]
    rw [encPerm_getD_nat]
    congr 1
    rw [decide_eq_decide, Fin.ext_iff,
      permFromCoins_getD_val (r := pairSndD (pairSndD w))
        (b := coinTable n (permTrials n) (permBits n) (pairSndD (pairSndD w))) (fun _ _ _ => rfl)]
    rfl
  · rw [encPerm_getD_of_le _ (not_lt.1 hlt)]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Find

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time machines for the string encodings of the graph protocols

The machine infrastructure behind the three polynomial-time statements of
`TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` (Inf-4.2: applying an encoded permutation to
an encoded graph, composing encoded permutations, sampling a permutation from coins). All of
it is built from the proved machine layer of `TCSlib/Complexity/Randomized/` — the
repetition lemma `Complexity.polyTimeComputable_iterateFind`, its emitting variant
`Complexity.polyTimeComputable_iterateEmit`, the typed cuts `pairTakePoly`/`pairDropPoly`, the
unary multiplication machine and the FP toolkit of `Build/StateLoop.lean` — and never touches
a machine directly.

The organising idea is that **numbers travel in unary** (`1^m = List.replicate m true`): a
"unary function" is a map `x ↦ 1^{f x}` with `f : List Bool → ℕ`, and the toolkit closes the
unary functions under addition, multiplication, truncated subtraction, polynomial evaluation,
comparison tests, bit extraction (`getD`), bounded first-index search (`firstIdx`), counted
loops, division and `Nat.sqrt`. The **bit-extraction principle** `polyTimeComputable_of_getD` then says that a
string function `F` is polynomial-time as soon as its length `|F z|` is a unary function and
its `m`-th bit `(F z).getD m false` is a polynomial-time test of `⟨1^m, z⟩`; the adjacency and
relation matrices of the graph protocols are produced bit by bit through it. The file is
independent of the encodings themselves (which import it), so that
`ZeroKnowledge/Encoding.lean` only has to identify the bits of its matrices with the numeric
functions proved polynomial-time here.

## Main definitions

* `TCSlib.Cryptography.EncodingMachines.firstIdx` — the least index `i < n` accepted by a
  test, or `n` when there is none.
* `TCSlib.Cryptography.EncodingMachines.cstep` — the unary counter step `⟨c, z⟩ ↦ ⟨1 :: c, z⟩`
  driving the searches and the bit-emitting loops.
* `TCSlib.Cryptography.EncodingMachines.loopState` — the state of a counted loop
  (`s ↦ upd ⟨x, ⟨1^i, s⟩⟩` from `init x`).
* `TCSlib.Cryptography.EncodingMachines.divNum`, `modNum` — Euclidean division as a bounded
  search.

## Main results

* `TCSlib.Cryptography.EncodingMachines.unaryAdd_poly`, `unaryMul_poly`, `unarySub_poly`,
  `unaryPolyOf_poly`, `leTest_poly`, `ltTest_poly`, `eqTest_poly`, `unaryMin_poly`,
  `getBit_poly` — the unary toolkit.
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_firstIdx` — bounded first-index
  search is polynomial-time (an instance of the repetition lemma).
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_of_getD` — the bit-extraction
  principle (an instance of `Complexity.polyTimeComputable_iterateEmit`).
* `TCSlib.Cryptography.EncodingMachines.polyTimeComputable_loopState` — counted loops with
  self-bounded updates are polynomial-time (a state loop).
* `TCSlib.Cryptography.EncodingMachines.unarySqrt_poly`, `divNum_poly`, `modNum_poly`,
  `unarySize_poly` — `Nat.sqrt`, division, remainder and `Nat.size` in unary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects; §2.2, FP.)
-/

namespace TCSlib.Cryptography.EncodingMachines

open Complexity Turing Complexity.StateLoop

/-! ### Unary arithmetic -/

/-- The sum of two unary functions is a unary function (concatenate the two unary strings,
`List.replicate_add`). -/
theorem unaryAdd_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x + g x) true := by
  simpa only [List.replicate_add] using hf.append hg

/-- The product of two unary functions is a unary function: pair the two unary strings and
apply the unary-multiplication machine `Turing.FinTM.computesFunInTime_unaryMul` (a copy of the
private `Complexity.polyTimeComputable_unaryMulFun` of `Randomized/Primitives.lean`). -/
theorem unaryMul_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x * g x) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have hmul : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert hmul.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- The truncated difference of two unary functions is a unary function: drop `g x` tokens
from `1^{f x}` (`Complexity.polyTimeComputable_pairDropPoly` at the variable length,
`List.drop_replicate`). -/
theorem unarySub_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x - g x) true := by
  convert (polyTimeComputable_pairDropPoly .var).comp (hg.pairEncode hf) using 1
  funext x
  simp [List.drop_replicate]

/-- A constant is a unary function. -/
theorem unaryConst_poly (c : ℕ) :
    PolyTimeComputable fun _ : List Bool => List.replicate c true :=
  polyTimeComputable_const _

/-- The length of a polynomial-time string function is a unary function
(`Complexity.polyTimeComputable_unary`). -/
theorem unaryLength_poly {h : List Bool → List Bool} (hh : PolyTimeComputable h) :
    PolyTimeComputable fun x => List.replicate (h x).length true :=
  polyTimeComputable_unary.comp hh

/-- A syntactic polynomial of a unary function is a unary function
(`Complexity.polyTimeComputable_unaryPoly` after the unary string). -/
theorem unaryPolyOf_poly (p : PolyExpr) {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (p.eval (f x)) true := by
  convert (polyTimeComputable_unaryPoly p).comp hf using 1
  funext x
  simp

/-- The comparison `f x ≤ g x` of two unary functions is a polynomial-time test
(`Complexity.StateLoop.lenLe_comp`). -/
theorem leTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x ≤ g x)] := by
  convert lenLe_comp hg hf using 1
  funext x
  simp

/-- The strict comparison `f x < g x` of two unary functions is a polynomial-time test
(`f + 1 ≤ g`). -/
theorem ltTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x < g x)] := by
  convert leTest_poly (unaryAdd_poly hf (unaryConst_poly 1)) hg using 1

/-- The equality `f x = g x` of two unary functions is a polynomial-time test
(`Complexity.polyTimeComputable_lenEq` on the pair of unary strings). -/
theorem eqTest_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => [decide (f x = g x)] := by
  convert polyTimeComputable_lenEq.comp (hf.pairEncode hg) using 1
  funext x
  simp

/-- The minimum of two unary functions is a unary function (`Complexity.polyTimeComputable_ite`
on the comparison test). -/
theorem unaryMin_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (min (f x) (g x)) true := by
  convert polyTimeComputable_ite (leTest_poly hf hg) hf hg using 1
  funext x
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (not_le.1 h).le]

/-- Reading bit number `f x` (default `false`) of a polynomial-time string `h x` is a
polynomial-time test: drop `f x` bits (`Complexity.polyTimeComputable_pairDropPoly`) and read
the head (`Complexity.StateLoop.headBit_poly`). -/
theorem getBit_poly {h : List Bool → List Bool} (hh : PolyTimeComputable h) {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => [(h x).getD (f x) false] := by
  convert headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp (hf.pairEncode hh))
    using 1
  funext x
  simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The Boolean value of a one-bit test as a unary function: `1^{[b x]}` has length `1` iff the
test holds (`Complexity.polyTimeComputable_ite` between the constants `1^1` and `1^0`). -/
theorem unaryOfTest_poly {b : List Bool → Bool} (hb : PolyTimeComputable fun x => [b x]) :
    PolyTimeComputable fun x => List.replicate (b x).toNat true := by
  convert polyTimeComputable_ite hb (unaryConst_poly 1) (unaryConst_poly 0) using 1
  funext x
  cases b x <;> rfl

/-! ### The unary counter loop -/

/-- The counter step `⟨c, z⟩ ↦ ⟨1 :: c, z⟩` on state words: iterated from `⟨[], z⟩` it
enumerates the words `⟨1^i, z⟩`, the arguments of the searches and bit-emitting loops below. -/
def cstep (w : List Bool) : List Bool := pairEncode (true :: pairFstD w) (pairSndD w)

/-- The counter step is polynomial-time. -/
theorem cstep_poly : PolyTimeComputable cstep :=
  ((cons_poly true).comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD

/-- The closed form of the counter orbit on a state word: `cstep^[i] ⟨c, z⟩ = ⟨1^i ++ c, z⟩`. -/
theorem cstep_iterate (c z : List Bool) (i : ℕ) :
    cstep^[i] (pairEncode c z) = pairEncode (List.replicate i true ++ c) z := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [cstep, List.replicate_succ]

/-- The counter orbit of an arbitrary word `x` stays within `2 i + 2 |x| + 2` after `i` rounds
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem length_cstep_iterate_le (x : List Bool) (i : ℕ) :
    (cstep^[i] x).length ≤ 2 * i + 2 * x.length + 2 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    rw [Function.iterate_succ_apply,
      show cstep x = pairEncode (true :: pairFstD x) (pairSndD x) from rfl, cstep_iterate,
      length_pairEncode]
    have := length_pairFstD_add_pairSndD_le x
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega

/-- The orbit polynomial `2 R(n) + 2 n + 2` of the counter loop with round polynomial `R`. -/
def cbound (R : PolyExpr) : PolyExpr :=
  .add (.mul (.const 2) R) (.add (.mul (.const 2) .var) (.const 2))

/-- The orbit hypothesis of the repetition lemma for the counter step: within `R|x|` rounds
the orbit of any word stays within `cbound R`. -/
theorem cstep_horbit (R : PolyExpr) (x : List Bool) (i : ℕ) (hi : i ≤ R.eval x.length) :
    (cstep^[i] x).length ≤ (cbound R).eval x.length := by
  have := length_cstep_iterate_le x i
  simp only [cbound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-! ### Bounded first-index search -/

/-- The least index `i < n` with `q i = true`, or `n` if there is none (the search performed by
the decoders of the graph protocols: the first set bit of a row, the preimage of a vertex, the
first accepted rejection trial). -/
noncomputable def firstIdx (q : ℕ → Bool) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ i < n, q i = true then Nat.find h else n

variable {q : ℕ → Bool} {n : ℕ}

/-- The search index is at most `n`. -/
theorem firstIdx_le : firstIdx q n ≤ n := by
  unfold firstIdx
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- The search index is `N` when `q N` holds, `N < n`, and `q` fails below `N`. -/
theorem firstIdx_eq_of {N : ℕ} (hN : N < n) (hq : q N = true) (hmin : ∀ i < N, q i = false) :
    firstIdx q n = N := by
  unfold firstIdx
  have h : ∃ i < n, q i = true := ⟨N, hN, hq⟩
  rw [dif_pos h]
  exact (Nat.find_eq_iff h).2 ⟨⟨hN, hq⟩, fun i hi hi' => by simp [hmin i hi] at hi'⟩

/-- The search index is `n` when `q` fails on the whole range. -/
theorem firstIdx_eq_of_forall (h : ∀ i < n, q i = false) : firstIdx q n = n := by
  unfold firstIdx
  rw [dif_neg]
  rintro ⟨i, hi, hq⟩
  simp [h i hi] at hq

/-- The search succeeds (`firstIdx q n < n`) iff some index of the range is accepted. -/
theorem firstIdx_lt_iff : firstIdx q n < n ↔ ∃ i < n, q i = true := by
  unfold firstIdx
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => (Nat.find_spec h).1⟩
  · simp [h]

/-- The search is exhausted (`firstIdx q n = n`) iff every index of the range is rejected. -/
theorem firstIdx_eq_iff : firstIdx q n = n ↔ ∀ i < n, q i = false := by
  constructor
  · intro h i hi
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact absurd h (firstIdx_lt_iff.2 ⟨i, hi, hc⟩).ne
  · exact firstIdx_eq_of_forall

/-- A successful search returns an accepted index. -/
theorem q_firstIdx (h : firstIdx q n < n) : q (firstIdx q n) = true := by
  have h' := firstIdx_lt_iff.1 h
  unfold firstIdx
  rw [dif_pos h']
  exact (Nat.find_spec h').2

/-- Every index below the search index is rejected. -/
theorem firstIdx_min {i : ℕ} (hi : i < firstIdx q n) : q i = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  have hlt : firstIdx q n < n := firstIdx_lt_iff.2 ⟨i, lt_of_lt_of_le hi firstIdx_le, hc⟩
  have h' := firstIdx_lt_iff.1 hlt
  unfold firstIdx at hi
  rw [dif_pos h'] at hi
  exact Nat.find_min h' hi ⟨lt_of_lt_of_le hi (Nat.find_spec h').1.le, hc⟩

/-- Two tests agreeing on the range have the same search index. -/
theorem firstIdx_congr {q' : ℕ → Bool} (h : ∀ i < n, q i = q' i) : firstIdx q n = firstIdx q' n := by
  unfold firstIdx
  have : (∃ i < n, q i = true) ↔ ∃ i < n, q' i = true :=
    ⟨fun ⟨i, hi, hq⟩ => ⟨i, hi, (h i hi) ▸ hq⟩, fun ⟨i, hi, hq⟩ => ⟨i, hi, (h i hi).symm ▸ hq⟩⟩
  by_cases hq : ∃ i < n, q i = true
  · rw [dif_pos hq, dif_pos (this.1 hq)]
    exact Nat.find_congr' fun {i} => and_congr_right fun hi => by rw [h i hi]
  · rw [dif_neg hq, dif_neg (fun h' => hq (this.2 h'))]

/-- **Bounded first-index search is polynomial-time:** if the test `p z i` is a polynomial-time
test of `⟨1^i, z⟩` and the bound `len z` is a unary function, then
`z ↦ 1^{firstIdx (p z) (len z)}` is polynomial-time computable.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` on the counter step
`cstep` from `⟨[], z⟩`, whose orbit is `⟨1^i, z⟩` (`cstep_iterate`) and polynomially bounded
for every word (`cstep_horbit`), with the acceptance test `len z ≤ i ∨ p z i`
(`Complexity.StateLoop.lenLe_comp`, `or_poly`), the payload `1^i` (the first projection), and
the round polynomial `C (n+1)^c` bounding `len` (`PolyTimeComputable.output_length_le`). The
loop's `List.find?` returns `firstIdx (p z) (len z)` by
`Complexity.StateLoop.find?_range_eq_some`: below it both disjuncts fail (`firstIdx_min`,
`firstIdx_le`), at it one holds (`q_firstIdx`, or `len z ≤ firstIdx` on exhaustion). -/
theorem polyTimeComputable_firstIdx {p : List Bool → ℕ → Bool}
    (hp : PolyTimeComputable fun w => [p (pairSndD w) (pairFstD w).length])
    {len : List Bool → ℕ} (hlen : PolyTimeComputable fun z => List.replicate (len z) true) :
    PolyTimeComputable fun z => List.replicate (firstIdx (p z) (len z)) true := by
  obtain ⟨C, c, hC⟩ := hlen.output_length_le
  have hlenP : ∀ z, len z ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have hacc : PolyTimeComputable fun w =>
      [decide (len (pairSndD w) ≤ (pairFstD w).length) || p (pairSndD w) (pairFstD w).length] := by
    refine or_poly ?_ hp
    convert lenLe_comp polyTimeComputable_pairFstD (hlen.comp polyTimeComputable_pairSndD) using 1
    funext w
    simp
  have hF := polyTimeComputable_iterateFind cstep_poly hacc polyTimeComputable_pairFstD
    (PolyExpr.normal C c) (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hF.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : firstIdx (p z) (len z) ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length :=
    firstIdx_le.trans ((hlenP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega)))
  rw [find?_range_eq_some hN ?_ ?_]
  · show List.replicate (firstIdx (p z) (len z)) true =
      pairFstD (cstep^[firstIdx (p z) (len z)] (pairEncode [] z))
    rw [horb, pairFstD_pairEncode]
  · intro i hi
    rw [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    have h1 : ¬ len z ≤ i := by
      have := firstIdx_le (q := p z) (n := len z)
      omega
    simp [h1, firstIdx_min hi]
  · rw [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    by_cases h : firstIdx (p z) (len z) < len z
    · simp [q_firstIdx h]
    · simp [not_lt.1 h]

/-! ### The bit-extraction principle -/

/-- Emitting `f i` at the indices `i < L` of `List.range N` gives `(List.range (min N L)).map f`. -/
theorem flatMap_range_ite_eq (f : ℕ → Bool) (L : ℕ) :
    ∀ N, (List.range N).flatMap (fun i => if i < L then [f i] else []) =
      (List.range (min N L)).map f
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_ite_eq f L N, List.flatMap_singleton]
    by_cases h : N < L
    · rw [if_pos h, show min (N + 1) L = N + 1 by omega, show min N L = N by omega,
        List.range_succ, List.map_append, List.map_singleton]
    · rw [if_neg h, List.append_nil, show min (N + 1) L = min N L by omega]

/-- A list is the list of its bits read with default `false` (`List.ofFn_getElem`,
`List.getD_eq_getElem`). -/
theorem map_range_getD (l : List Bool) :
    (List.range l.length).map (fun i => l.getD i false) = l := by
  conv_rhs => rw [← List.ofFn_getElem l]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  simp [List.getD_eq_getElem?_getD]

/-- **The bit-extraction principle:** a string function `F` is polynomial-time computable as
soon as its length is a unary function and its `m`-th bit `(F z).getD m false` is a
polynomial-time test of `⟨1^m, z⟩`.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateEmit` on the counter step
`cstep` from `⟨[], z⟩` (orbit `⟨1^i, z⟩`, `cstep_iterate`; bound `cstep_horbit`) with the emitter
`⟨1^i, z⟩ ↦ if i < |F z| then [(F z).getD i false] else []` (`Complexity.polyTimeComputable_ite`
on `ltTest_poly` and the bit test) and the round polynomial `C (n+1)^c` bounding `|F z|`
(`PolyTimeComputable.output_length_le`). The emitted chunks concatenate to
`(List.range |F z|).map (fun i => (F z).getD i false) = F z` (`flatMap_range_ite_eq`,
`map_range_getD`). -/
theorem polyTimeComputable_of_getD {F : List Bool → List Bool}
    (hbit : PolyTimeComputable fun w => [(F (pairSndD w)).getD (pairFstD w).length false])
    (hlen : PolyTimeComputable fun z => List.replicate (F z).length true) :
    PolyTimeComputable F := by
  obtain ⟨C, c, hC⟩ := hlen.output_length_le
  have hlenP : ∀ z, (F z).length ≤ (PolyExpr.normal C c).eval z.length := fun z => by
    have := hC z
    simpa [PolyExpr.eval_normal] using this
  have hg : PolyTimeComputable fun w => List.replicate (F (pairSndD w)).length true :=
    hlen.comp polyTimeComputable_pairSndD
  have htest : PolyTimeComputable fun w =>
      [decide ((pairFstD w).length < (F (pairSndD w)).length)] :=
    ltTest_poly (unaryLength_poly polyTimeComputable_pairFstD) hg
  have hemit := polyTimeComputable_ite htest hbit (polyTimeComputable_const [])
  have hE := polyTimeComputable_iterateEmit cstep_poly hemit (PolyExpr.normal C c)
    (cbound (PolyExpr.normal C c)) (cstep_horbit _)
  have hpre : PolyTimeComputable fun z => pairEncode [] z :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  convert hE.comp hpre using 1
  funext z
  simp only [Function.comp_apply]
  have horb : ∀ i, cstep^[i] (pairEncode [] z) = pairEncode (List.replicate i true) z :=
    fun i => by rw [cstep_iterate, List.append_nil]
  have hN : (F z).length ≤ (PolyExpr.normal C c).eval (pairEncode [] z).length + 1 :=
    ((hlenP z).trans ((PolyExpr.normal C c).eval_mono
      (by rw [length_pairEncode]; omega))).trans (Nat.le_succ _)
  simp only [horb, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    decide_eq_true_eq]
  rw [flatMap_range_ite_eq, min_eq_right hN, map_range_getD]

/-! ### Square roots in unary -/

/-- `Nat.sqrt` of a unary function is a unary function: the search for the least `i` with
`f x < (i + 1)²` over `i ≤ f x` (`polyTimeComputable_firstIdx`, `Nat.lt_succ_sqrt`,
`Nat.le_sqrt`). -/
theorem unarySqrt_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (Nat.sqrt (f x)) true := by
  have hi : PolyTimeComputable fun w => List.replicate ((pairFstD w).length + 1) true :=
    unaryAdd_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 1)
  have hp : PolyTimeComputable fun w =>
      [decide (f (pairSndD w) < ((pairFstD w).length + 1) * ((pairFstD w).length + 1))] :=
    ltTest_poly (hf.comp polyTimeComputable_pairSndD) (unaryMul_poly hi hi)
  have hlen : PolyTimeComputable fun z => List.replicate (f z + 1) true :=
    unaryAdd_poly hf (unaryConst_poly 1)
  convert polyTimeComputable_firstIdx (p := fun z i => decide (f z < (i + 1) * (i + 1))) hp hlen
    using 1
  funext z
  congr 1
  symm
  apply firstIdx_eq_of
  · exact Nat.lt_succ_of_le (Nat.sqrt_le_self _)
  · simpa using Nat.lt_succ_sqrt (f z)
  · intro i hi
    simpa using Nat.le_sqrt.1 hi

/-! ### Truncation -/

/-- Truncating a polynomial-time string to a unary length is polynomial-time
(`Complexity.polyTimeComputable_pairTakePoly` at the variable length). -/
theorem truncate_poly {s : List Bool → List Bool} (hs : PolyTimeComputable s)
    {M : List Bool → ℕ} (hM : PolyTimeComputable fun x => List.replicate (M x) true) :
    PolyTimeComputable fun x => (s x).take (M x) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (hM.pairEncode hs) using 1
  funext x
  simp

/-! ### Counted loops -/

/-- **State loops** (a copy of the private `polyTimeComputable_stateFind` of
`TCSlib/Complexity/Randomized/Repetition.lean`, requested as a shared lemma). A state word
`⟨x, s⟩` retains the input `x` and evolves its state from `start x` by `s ↦ step ⟨x, s⟩`
(`Complexity.StateLoop.orbit`); a test `acc` on the state word is `false` before round `N x`
and `true` at round `N x ≤ R|x|`, the states up to that round have length at most `B|x|`, and
`out` reads the answer off the final state word. Then `x ↦ out ⟨x, orbit x (N x)⟩` is
polynomial-time computable.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` on the length-guarded
step `Complexity.StateLoop.gstep step B` with `R` as the round polynomial and
`StateLoop.gstepBound B` as the orbit bound (valid for every word by
`StateLoop.length_gstep_iterate_le`), pre-composed with `x ↦ ⟨x, start x⟩`. On the genuine
orbit the guard never fires (`StateLoop.gstep_iterate_eq`), so the loop's `find?` returns
`some (N x)` (`StateLoop.find?_range_eq_some`) and the payload is `out ⟨x, orbit x (N x)⟩`. -/
theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
    {acc : List Bool → Bool} {out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
    (R B : PolyExpr) (N : List Bool → ℕ) (hN : ∀ x, N x ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ N x → (orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ x i, i < N x → acc (pairEncode x (orbit start step x i)) = false)
    (hlast : ∀ x, acc (pairEncode x (orbit start step x (N x))) = true) :
    PolyTimeComputable fun x => out (pairEncode x (orbit start step x (N x))) := by
  have hF := polyTimeComputable_iterateFind (gstep_poly hstep B) hacc hout R (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  convert hF.comp hpre using 1
  funext x
  simp only [Function.comp_apply]
  have horb := gstep_iterate_eq start step B x (N x) (hbound x)
  have hle : N x ≤ R.eval (pairEncode x (start x)).length :=
    (hN x).trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((gstep step B)^[i] (pairEncode x (start x)))) = some (N x) := by
    apply find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst x i hi
    · rw [horb (N x) le_rfl]
      exact hlast x
  rw [hfind]
  exact (congrArg out (horb (N x) le_rfl)).symm

/-- The state of a **counted loop** after `i` rounds: from `init x`, round `i` replaces the
state `s` by `upd ⟨x, ⟨1^i, s⟩⟩` (the update reads the input, the round counter and the state
off one word). -/
def loopState (upd init : List Bool → List Bool) (x : List Bool) : ℕ → List Bool
  | 0 => init x
  | i + 1 => upd (pairEncode x (pairEncode (List.replicate i true) (loopState upd init x i)))

/-- The initial state of a counted loop. -/
@[simp] theorem loopState_zero (upd init : List Bool → List Bool) (x : List Bool) :
    loopState upd init x 0 = init x := rfl

/-- One round of a counted loop. -/
@[simp] theorem loopState_succ (upd init : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    loopState upd init x (i + 1) =
      upd (pairEncode x (pairEncode (List.replicate i true) (loopState upd init x i))) := rfl

namespace CountLoop

/-- The initial state word `⟨[], init x⟩`: empty counter, initial state. -/
def start (init : List Bool → List Bool) (x : List Bool) : List Bool := pairEncode [] (init x)

/-- The step on `⟨x, ⟨cnt, s⟩⟩`: append a token to the counter and update the state. -/
def step (upd : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w)) (upd w)

/-- The acceptance test on `⟨x, ⟨cnt, s⟩⟩`: the counter has reached `N x`. -/
def acc (N : List Bool → ℕ) (w : List Bool) : Bool :=
  decide (N (pairFstD w) ≤ (pairFstD (pairSndD w)).length)

/-- The output on `⟨x, ⟨cnt, s⟩⟩`: the state `s`. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The initial state word is polynomial-time. -/
theorem start_poly {init : List Bool → List Bool} (hinit : PolyTimeComputable init) :
    PolyTimeComputable (start init) :=
  (polyTimeComputable_const []).pairEncode hinit

/-- The step is polynomial-time. -/
theorem step_poly {upd : List Bool → List Bool} (hupd : PolyTimeComputable upd) :
    PolyTimeComputable (step upd) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    hupd

/-- The acceptance test is polynomial-time (`leTest_poly` against the unary round count). -/
theorem acc_poly {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true) :
    PolyTimeComputable fun w => [acc N w] := by
  have h1 : PolyTimeComputable fun w => List.replicate (N (pairFstD w)) true :=
    hN.comp polyTimeComputable_pairFstD
  exact leTest_poly h1
    (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The closed form of the orbit: `⟨1^i, loopState upd init x i⟩`. -/
theorem orbit_eq (upd init : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit (start init) (step upd) x i =
      pairEncode (List.replicate i true) (loopState upd init x i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [orbit_succ, ih]
    simp [step, List.replicate_succ]

end CountLoop

/-- **Counted loops are polynomial-time:** if the update and the initial state are
polynomial-time, the round count `N x` is a unary function, and the initial state and every
update of a state word `⟨x, s⟩` have length at most `B|x|`, then `x ↦ loopState upd init x (N x)`
is polynomial-time computable.

**Proof sketch.** A state loop (`polyTimeComputable_stateFind`, data in `CountLoop`) on the
state word `⟨x, ⟨1^i, S_i⟩⟩` with `S_i = loopState upd init x i` (`CountLoop.orbit_eq`): the step
appends a token to the counter and applies `upd` to the whole word; the acceptance test is the
length comparison `N x ≤ i` against `1^{N x}` (`leTest_poly`), `false` below round `N x` and
`true` there; the output projects the state. Every state has length at most `B|x|`
(`hinitB`, `hupdB`), so the orbit `⟨1^i, S_i⟩` has length at most `2 N x + 2 + B|x|`, and the
round polynomial `C (n+1)^c` bounding `N` comes from `PolyTimeComputable.output_length_le`. -/
theorem polyTimeComputable_loopState {upd init : List Bool → List Bool}
    (hupd : PolyTimeComputable upd) (hinit : PolyTimeComputable init)
    {N : List Bool → ℕ} (hN : PolyTimeComputable fun x => List.replicate (N x) true)
    (B : PolyExpr) (hinitB : ∀ x, (init x).length ≤ B.eval x.length)
    (hupdB : ∀ x s, (upd (pairEncode x s)).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => loopState upd init x (N x) := by
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNR : ∀ x, N x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hstate : ∀ x i, (loopState upd init x i).length ≤ B.eval x.length := by
    intro x i
    cases i with
    | zero => exact hinitB x
    | succ i => exact hupdB x _
  have hbound : ∀ x i, i ≤ N x →
      (orbit (CountLoop.start init) (CountLoop.step upd) x i).length ≤
        (PolyExpr.add (.mul (.const 2) (PolyExpr.normal C c)) (.add (.const 2) B)).eval
          x.length := by
    intro x i hi
    rw [CountLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have h1 := hstate x i
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

/-! ### Division and remainder in unary -/

/-- Euclidean division as a bounded search: `a / m` is the least `q` with `a < (q + 1) m`
(and `0` for `m = 0`). -/
noncomputable def divNum (a m : ℕ) : ℕ :=
  if m = 0 then 0 else firstIdx (fun q => decide (a < (q + 1) * m)) (a + 1)

/-- `divNum a m = a / m`. -/
theorem divNum_eq (a m : ℕ) : divNum a m = a / m := by
  unfold divNum
  split_ifs with h
  · simp [h]
  · have hm : 0 < m := Nat.pos_of_ne_zero h
    apply firstIdx_eq_of
    · exact Nat.lt_succ_of_le (Nat.div_le_self a m)
    · simp only [decide_eq_true_eq]
      rw [Nat.mul_comm]
      exact Nat.lt_mul_div_succ a hm
    · intro q hq
      simp only [decide_eq_false_iff_not, not_lt]
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hm] at hq
      exact hq

/-- The remainder `a - (a / m) m`. -/
noncomputable def modNum (a m : ℕ) : ℕ := a - divNum a m * m

/-- `modNum a m = a % m`. -/
theorem modNum_eq (a m : ℕ) : modNum a m = a % m := by
  unfold modNum
  rw [divNum_eq]
  exact (Nat.eq_sub_of_add_eq (Nat.mod_add_div' a m)).symm

/-- Division of unary functions is a unary function (`polyTimeComputable_firstIdx` with the
test `a < (q + 1) m`, `Complexity.polyTimeComputable_ite` for the zero divisor). -/
theorem divNum_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (divNum (f x) (g x)) true := by
  have hf' : PolyTimeComputable fun w => List.replicate (f (pairSndD w)) true :=
    hf.comp polyTimeComputable_pairSndD
  have hg' : PolyTimeComputable fun w => List.replicate (g (pairSndD w)) true :=
    hg.comp polyTimeComputable_pairSndD
  have hsearch : PolyTimeComputable fun x =>
      List.replicate (firstIdx (fun q => decide (f x < (q + 1) * g x)) (f x + 1)) true :=
    polyTimeComputable_firstIdx (p := fun x q => decide (f x < (q + 1) * g x))
      (ltTest_poly hf' (unaryMul_poly
        (unaryAdd_poly (unaryLength_poly polyTimeComputable_pairFstD) (unaryConst_poly 1)) hg'))
      (unaryAdd_poly hf (unaryConst_poly 1))
  unfold divNum
  convert polyTimeComputable_ite (eqTest_poly hg (unaryConst_poly 0)) (unaryConst_poly 0) hsearch
    using 1
  funext x
  by_cases h : g x = 0 <;> simp [h]

/-- The remainder of unary functions is a unary function. -/
theorem modNum_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (modNum (f x) (g x)) true :=
  unarySub_poly hf (unaryMul_poly (divNum_poly hf hg) hg)

/-! ### Binary length in unary -/

/-- `Nat.size` of a unary function is a unary function: the binary representation of the
length of `1^{f x}` (`Turing.FinTM.computesFunInTime_lengthBits`) has `Nat.size (f x)` digits
(`Nat.size_eq_bits_len`). -/
theorem unarySize_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) :
    PolyTimeComputable fun x => List.replicate (Nat.size (f x)) true := by
  have hbits : PolyTimeComputable fun x => Nat.bits x.length :=
    polyTimeComputable_of_linear Turing.FinTM.computesFunInTime_lengthBits
  convert unaryLength_poly (hbits.comp hf) using 1
  funext x
  simp [Nat.size_eq_bits_len]

end TCSlib.Cryptography.EncodingMachines

## ===== TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Cryptography.Asymptotic.Permutations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Numeric models of the permutation decoder and of the permutation sampler

The second half of the machine infrastructure behind the polynomial-time statements of
`TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` (Inf-4.2). The decoder `decPerm` of an
encoded permutation and the rejection-sampled Fisher–Yates permutation `permFromCoins` of
`Asymptotic/Permutations.lean` are typed objects (`Equiv.Perm (Fin n)`, `Option`, `Fin.find`,
`Function.Bijective`); a machine computes with numbers in unary. This file defines **numeric
models** of both — plain functions `ℕ → ℕ` on the relation matrix `b : List Bool` of side `n`
(`rowFirst`, `rowMap`, `rowInv`, `isBij`, `permNum`, `permInvNum`) and on the coin tape
`r : List Bool` (`blockVal`, `trialIdx`, `offsetVal`, `fyFail`, `fyTarget`, `fyApply`,
`permFromCoinsNum`) — proves them polynomial-time in unary with the toolkit of
`EncodingMachines.lean` (bounded searches, counted loops, unary arithmetic), and identifies
the sampler model with the typed sampler (`permFromCoins_getD_val`). The identification of the
decoder model with `decPerm` lives in `Encoding.lean`, next to the decoder.

## Main definitions

* `TCSlib.Cryptography.EncodingMachines.rowFirst`, `rowMap`, `rowInv`, `isBij`, `permNum`,
  `permInvNum` — the numeric model of the permutation decoder: image and preimage of a vertex
  under the relation matrix, surjectivity test, and the decoded permutation with its inverse.
* `TCSlib.Cryptography.EncodingMachines.blockVal`, `trialIdx`, `offsetVal`, `fyFail`,
  `fyTarget`, `fyApply`, `permFromCoinsNum` — the numeric model of the permutation sampler:
  the value of a `k`-bit block of the tape, the first accepted trial of a position, its offset,
  the failure test, the Fisher–Yates target and the composed swaps.

## Main results

* `TCSlib.Cryptography.EncodingMachines.permNum_poly`, `permInvNum_poly` — the decoded
  permutation and its inverse are unary polynomial-time functions of `⟨1^n, b, 1^i⟩`.
* `TCSlib.Cryptography.EncodingMachines.permFromCoinsNum_poly` — the sampled permutation is a
  unary polynomial-time function of the tape and the parameters.
* `TCSlib.Cryptography.EncodingMachines.permFromCoins_getD_val` — the numeric model of the
  sampler agrees with `permFromCoins` (with the identity on failure) on every vertex.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects; §2.2, FP.)
-/

namespace TCSlib.Cryptography.EncodingMachines

open Complexity Turing

/-! ### The numeric model of the permutation decoder -/

/-- The least column `j < n` whose bit `(i, j)` (position `i n + j`) is set in the relation
matrix `b` of side `n`, or `n` if row `i` has no set bit. -/
noncomputable def rowFirst (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  firstIdx (fun j => b.getD (i * n + j) false) n

/-- The decoded image of row `i`: its first set column, or `i` itself if the row is empty (the
numeric form of the decoder's `(Fin.find _).getD i`). -/
noncomputable def rowMap (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  if rowFirst n b i = n then i else rowFirst n b i

/-- The least row `i < n` mapped to `u`, or `n` if there is none. -/
noncomputable def rowInv (n : ℕ) (b : List Bool) (u : ℕ) : ℕ :=
  firstIdx (fun i => decide (rowMap n b i = u)) n

/-- The surjectivity test of the decoded map: every `u < n` has a preimage. -/
noncomputable def isBij (n : ℕ) (b : List Bool) : Bool :=
  decide (firstIdx (fun u => decide (rowInv n b u = n)) n = n)

/-- The decoded permutation as a numeric function: the decoded map if it is bijective, the
identity otherwise (the numeric form of `decPerm`). -/
noncomputable def permNum (n : ℕ) (b : List Bool) (i : ℕ) : ℕ :=
  if isBij n b then rowMap n b i else i

/-- The inverse of the decoded permutation as a numeric function. -/
noncomputable def permInvNum (n : ℕ) (b : List Bool) (u : ℕ) : ℕ :=
  if isBij n b then rowInv n b u else u

/-- The decoded image of a row `i < n` is below `n`. -/
theorem rowMap_lt {n : ℕ} {b : List Bool} {i : ℕ} (hi : i < n) : rowMap n b i < n := by
  unfold rowMap
  split_ifs with h
  · exact hi
  · exact lt_of_le_of_ne firstIdx_le h

/-- The surjectivity test holds iff every `u < n` is the image of some row `i < n`. -/
theorem isBij_iff {n : ℕ} {b : List Bool} :
    isBij n b = true ↔ ∀ u < n, ∃ i < n, rowMap n b i = u := by
  unfold isBij
  rw [decide_eq_true_eq, firstIdx_eq_iff]
  refine forall_congr' fun u => forall_congr' fun _ => ?_
  rw [decide_eq_false_iff_not]
  unfold rowInv
  constructor
  · intro h
    obtain ⟨i, hi, hq⟩ := firstIdx_lt_iff.1 (lt_of_le_of_ne firstIdx_le h)
    exact ⟨i, hi, of_decide_eq_true hq⟩
  · rintro ⟨i, hi, hq⟩
    exact (firstIdx_lt_iff.2 ⟨i, hi, decide_eq_true hq⟩).ne

/-- The decoded permutation maps `i < n` below `n`. -/
theorem permNum_lt {n : ℕ} {b : List Bool} {i : ℕ} (hi : i < n) : permNum n b i < n := by
  unfold permNum
  split_ifs
  · exact rowMap_lt hi
  · exact hi

/-- `rowFirst` is a unary polynomial-time function of its unary arguments and the matrix
(`polyTimeComputable_firstIdx` with the bit test `getBit_poly`). -/
theorem rowFirst_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (rowFirst (Nn z) (B z) (I z)) true := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hI' : PolyTimeComputable fun w => List.replicate (I (pairSndD w)) true :=
    hI.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [(B (pairSndD w)).getD (I (pairSndD w) * Nn (pairSndD w) + (pairFstD w).length) false] :=
    getBit_poly (hB.comp polyTimeComputable_pairSndD)
      (unaryAdd_poly (unaryMul_poly hI' hN') (unaryLength_poly polyTimeComputable_pairFstD))
  exact polyTimeComputable_firstIdx (p := fun z j => (B z).getD (I z * Nn z + j) false) hp hN

/-- `rowMap` is a unary polynomial-time function. -/
theorem rowMap_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (rowMap (Nn z) (B z) (I z)) true := by
  unfold rowMap
  convert polyTimeComputable_ite (eqTest_poly (rowFirst_poly hN hB hI) hN) hI
    (rowFirst_poly hN hB hI) using 1
  funext z
  by_cases h : rowFirst (Nn z) (B z) (I z) = Nn z <;> simp [h]

/-- `rowInv` is a unary polynomial-time function (a search over the rows with the equality test
on `rowMap`). -/
theorem rowInv_poly {Nn U : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hU : PolyTimeComputable fun z => List.replicate (U z) true) :
    PolyTimeComputable fun z => List.replicate (rowInv (Nn z) (B z) (U z)) true := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hU' : PolyTimeComputable fun w => List.replicate (U (pairSndD w)) true :=
    hU.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [decide (rowMap (Nn (pairSndD w)) (B (pairSndD w)) (pairFstD w).length = U (pairSndD w))] :=
    eqTest_poly (rowMap_poly hN' (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)) hU'
  exact polyTimeComputable_firstIdx (p := fun z i => decide (rowMap (Nn z) (B z) i = U z)) hp hN

/-- The surjectivity test is polynomial-time (a search over the vertices for one without a
preimage). -/
theorem isBij_poly {Nn : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => [isBij (Nn z) (B z)] := by
  have hN' : PolyTimeComputable fun w => List.replicate (Nn (pairSndD w)) true :=
    hN.comp polyTimeComputable_pairSndD
  have hp : PolyTimeComputable fun w =>
      [decide (rowInv (Nn (pairSndD w)) (B (pairSndD w)) (pairFstD w).length = Nn (pairSndD w))] :=
    eqTest_poly (rowInv_poly hN' (hB.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)) hN'
  exact eqTest_poly
    (polyTimeComputable_firstIdx (p := fun z u => decide (rowInv (Nn z) (B z) u = Nn z)) hp hN) hN

/-- The decoded permutation is a unary polynomial-time function. -/
theorem permNum_poly {Nn I : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true) :
    PolyTimeComputable fun z => List.replicate (permNum (Nn z) (B z) (I z)) true := by
  unfold permNum
  convert polyTimeComputable_ite (isBij_poly hN hB) (rowMap_poly hN hB hI) hI using 1
  funext z
  by_cases h : isBij (Nn z) (B z) = true <;> simp [h]

/-- The inverse of the decoded permutation is a unary polynomial-time function. -/
theorem permInvNum_poly {Nn U : List Bool → ℕ} {B : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true) (hB : PolyTimeComputable B)
    (hU : PolyTimeComputable fun z => List.replicate (U z) true) :
    PolyTimeComputable fun z => List.replicate (permInvNum (Nn z) (B z) (U z)) true := by
  unfold permInvNum
  convert polyTimeComputable_ite (isBij_poly hN hB) (rowInv_poly hN hB hU) hU using 1
  funext z
  by_cases h : isBij (Nn z) (B z) = true <;> simp [h]

/-! ### The numeric model of the permutation sampler -/

/-- The value of the `k`-bit block of the tape `r` starting at position `base` (most significant
bit first, missing bits read as `false`): the numeric form of `bitsToNat` on a block of the coin
table. -/
def blockVal (r : List Bool) (base k : ℕ) : ℕ :=
  (List.range k).foldl (fun a t => 2 * a + (r.getD (base + t) false).toNat) 0

/-- The empty block has value `0`. -/
@[simp] theorem blockVal_zero (r : List Bool) (base : ℕ) : blockVal r base 0 = 0 := rfl

/-- One more bit doubles the value and adds the bit. -/
theorem blockVal_succ (r : List Bool) (base k : ℕ) :
    blockVal r base (k + 1) = 2 * blockVal r base k + (r.getD (base + k) false).toNat := by
  unfold blockVal
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A `k`-bit block has value below `2^k`. -/
theorem blockVal_lt (r : List Bool) (base : ℕ) : ∀ k, blockVal r base k < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [blockVal_succ, pow_succ]
    have h1 := blockVal_lt r base k
    have h2 := Bool.toNat_le (r.getD (base + k) false)
    omega

/-- `bitsToNat` of a block of the tape is `blockVal` (induction on the block length through
`List.ofFn_succ'`). -/
theorem bitsToNat_eq_blockVal (r : List Bool) (base : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => r.getD (base + j) false) = blockVal r base k
  | 0 => by simp [bitsToNat]
  | k + 1 => by
    rw [blockVal_succ, ← bitsToNat_eq_blockVal r base k]
    unfold bitsToNat
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [show (r.getD (base + k) false).toNat = cond (r.getD (base + k) false) 1 0 from rfl,
      Bool.cond_eq_ite]

/-- The first trial `t < T` of position `i` whose block reads below `n - i`, or `T` if every
trial is rejected. -/
noncomputable def trialIdx (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  firstIdx (fun t => decide (blockVal r ((i * T + t) * k) k < n - i)) T

/-- The offset of position `i`: the value of its first accepted block. -/
noncomputable def offsetVal (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  blockVal r ((i * T + trialIdx n k T r i) * k) k

/-- The sampler fails iff some position `i < n` has no accepted trial. -/
noncomputable def fyFail (n k T : ℕ) (r : List Bool) : Bool :=
  decide (firstIdx (fun i => decide (trialIdx n k T r i = T)) n < n)

/-- The transposition `(a b)` on numbers. -/
def swapNum (a b y : ℕ) : ℕ := if y = a then b else if y = b then a else y

/-- The Fisher–Yates target of position `i`: `i + offset` when the position has an accepted
trial, `i` otherwise. -/
noncomputable def fyTarget (n k T : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  if trialIdx n k T r i < T then i + offsetVal n k T r i else i

/-- The composed swaps `s_{n-m} ∘ ⋯ ∘ s_{n-1}` applied to `x`: the state of the Fisher–Yates
loop after `m` rounds (the last position is applied first). -/
noncomputable def fyIter (n k T : ℕ) (r : List Bool) (x m : ℕ) : ℕ :=
  (List.range' (n - m) m).foldr (fun i y => swapNum i (fyTarget n k T r i) y) x

/-- The Fisher–Yates permutation `s_0 ∘ s_1 ∘ ⋯ ∘ s_{n-1}` applied to `x`. -/
noncomputable def fyApply (n k T : ℕ) (r : List Bool) (x : ℕ) : ℕ :=
  (List.range n).foldr (fun i y => swapNum i (fyTarget n k T r i) y) x

/-- The sampled permutation applied to `x`, with the identity on failure (the numeric form of
`(permFromCoins n k T b).getD 1`). -/
noncomputable def permFromCoinsNum (n k T : ℕ) (r : List Bool) (x : ℕ) : ℕ :=
  if fyFail n k T r then x else fyApply n k T r x

/-- The accepted offset of a position `i` is below `n - i`. -/
theorem offsetVal_lt {n k T : ℕ} {r : List Bool} {i : ℕ} (h : trialIdx n k T r i < T) :
    offsetVal n k T r i < n - i := by
  have := q_firstIdx h
  simpa [offsetVal, trialIdx] using this

/-- The Fisher–Yates target of a position `i < n` is below `n`. -/
theorem fyTarget_lt {n k T : ℕ} {r : List Bool} {i : ℕ} (hi : i < n) : fyTarget n k T r i < n := by
  unfold fyTarget
  split_ifs with h
  · have := offsetVal_lt h
    omega
  · exact hi

/-- A transposition of two numbers below `n` keeps a number `≤ n` at most `n`. -/
theorem swapNum_le {n a b y : ℕ} (ha : a < n) (hb : b < n) (hy : y ≤ n) : swapNum a b y ≤ n := by
  unfold swapNum
  split_ifs <;> omega

/-- The Fisher–Yates loop starts at `x`. -/
theorem fyIter_zero (n k T : ℕ) (r : List Bool) (x : ℕ) : fyIter n k T r x 0 = x := by
  simp [fyIter]

/-- One round of the Fisher–Yates loop applies the swap of position `n - 1 - m`. -/
theorem fyIter_succ {n : ℕ} (k T : ℕ) (r : List Bool) (x : ℕ) {m : ℕ} (hm : m < n) :
    fyIter n k T r x (m + 1) =
      swapNum (n - 1 - m) (fyTarget n k T r (n - 1 - m)) (fyIter n k T r x m) := by
  unfold fyIter
  rw [show n - (m + 1) = n - 1 - m by omega, List.range'_succ, List.foldr_cons,
    show n - 1 - m + 1 = n - m by omega]

/-- After `n` rounds the loop has applied the whole permutation. -/
theorem fyIter_self (n k T : ℕ) (r : List Bool) (x : ℕ) : fyIter n k T r x n = fyApply n k T r x := by
  unfold fyIter fyApply
  rw [Nat.sub_self, List.range_eq_range']

/-- The loop state stays at most `n` from a start `x ≤ n`. -/
theorem fyIter_le {n k T : ℕ} {r : List Bool} {x : ℕ} (hx : x ≤ n) :
    ∀ m, m ≤ n → fyIter n k T r x m ≤ n
  | 0, _ => by rw [fyIter_zero]; exact hx
  | m + 1, hm => by
    rw [fyIter_succ k T r x (by omega)]
    exact swapNum_le (by omega) (fyTarget_lt (by omega)) (fyIter_le hx m (by omega))

/-! ### The machines of the sampler model -/

/-- Composition of a unary function with a polynomial-time string function. -/
theorem unaryComp_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable fun x => List.replicate (f (g x)) true :=
  hf.comp hg

/-- **Block values are unary polynomial-time** for blocks whose length `K z` is bounded by
`2^{K z} ≤ M z` with `M` a unary function.

**Proof sketch.** A counted loop (`polyTimeComputable_loopState`) of `K z` rounds from `1^0`
whose round `m` replaces the unary value `1^v` by `1^v ++ 1^v ++ [bit]` with the bit
`r.getD (base + m)` of the tape (`getBit_poly`), truncated to `M z` tokens (`truncate_poly`)
so that every update is bounded by `M z ≤ C(|z|+1)^c`. On the genuine orbit the truncation is
the identity since `blockVal … (m+1) < 2^{m+1} ≤ 2^{K z} ≤ M z` (`blockVal_lt`), so the state
after `m ≤ K z` rounds is `1^{blockVal (Rr z) (Base z) m}` (`blockVal_succ`,
`List.take_replicate`). -/
theorem blockVal_poly {Rr : List Bool → List Bool} {Base K M : List Bool → ℕ}
    (hR : PolyTimeComputable Rr) (hBase : PolyTimeComputable fun z => List.replicate (Base z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (blockVal (Rr z) (Base z) (K z)) true := by
  let upd : List Bool → List Bool := fun w =>
    ((pairSndD (pairSndD w) ++ pairSndD (pairSndD w)) ++
      (if (Rr (pairFstD w)).getD (Base (pairFstD w) + (pairFstD (pairSndD w)).length) false = true
        then [true] else [])).take (M (pairFstD w))
  have hs : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hbit : PolyTimeComputable fun w =>
      [(Rr (pairFstD w)).getD (Base (pairFstD w) + (pairFstD (pairSndD w)).length) false] :=
    getBit_poly (hR.comp polyTimeComputable_pairFstD)
      (unaryAdd_poly (unaryComp_poly hBase polyTimeComputable_pairFstD)
        (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
  have hupd : PolyTimeComputable upd :=
    truncate_poly ((hs.append hs).append
      (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const [])))
      (unaryComp_poly hM polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hM.output_length_le
  have hMC : ∀ x, M x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd (polyTimeComputable_const []) hK
    (PolyExpr.normal C c) (fun x => by simp) (fun x s => by
      show ((_ : List Bool).take (M (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hMC x))
  convert hloop using 1
  funext z
  have key : ∀ m, m ≤ K z →
      loopState upd (fun _ => []) z m = List.replicate (blockVal (Rr z) (Base z) m) true := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [loopState_succ, ih (Nat.le_of_succ_le hm)]
      simp only [upd, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      have hle : 2 * blockVal (Rr z) (Base z) m + ((Rr z).getD (Base z + m) false).toNat ≤ M z := by
        have h1 := blockVal_lt (Rr z) (Base z) (m + 1)
        rw [blockVal_succ] at h1
        have h2 : 2 ^ (m + 1) ≤ 2 ^ K z := Nat.pow_le_pow_right (by norm_num) hm
        have h3 := hKM z
        omega
      have hrep : (List.replicate (blockVal (Rr z) (Base z) m) true ++
          List.replicate (blockVal (Rr z) (Base z) m) true) ++
          (if (Rr z).getD (Base z + m) false = true then [true] else []) =
          List.replicate (2 * blockVal (Rr z) (Base z) m +
            ((Rr z).getD (Base z + m) false).toNat) true := by
        rw [← List.replicate_add]
        cases (Rr z).getD (Base z + m) false
        · simp [two_mul]
        · rw [if_pos rfl, ← List.replicate_succ', Bool.toNat_true, two_mul]
      rw [hrep, List.take_replicate, min_eq_right hle, blockVal_succ]
  exact (key (K z) le_rfl).symm

/-- The first accepted trial of a position is a unary polynomial-time function.

**Proof sketch.** `polyTimeComputable_firstIdx` over the trials `t < T` with the test
`blockVal r ((i T + t) k) k < n - i`, itself polynomial-time by `blockVal_poly` on the unary block
start `(i T + t) k` (`unaryMul_poly`, `unaryAdd_poly`) and `ltTest_poly` against the unary
difference `n - i` (`unarySub_poly`); the parameters are read off the second component of
the search word `⟨1^t, z⟩`. -/
theorem trialIdx_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (trialIdx (Nn z) (K z) (Tt z) (Rr z) (I z)) true := by
  have hp : PolyTimeComputable fun w =>
      [decide (blockVal (Rr (pairSndD w))
        ((I (pairSndD w) * Tt (pairSndD w) + (pairFstD w).length) * K (pairSndD w)) (K (pairSndD w)) <
          Nn (pairSndD w) - I (pairSndD w))] :=
    ltTest_poly (blockVal_poly (hR.comp polyTimeComputable_pairSndD)
      (unaryMul_poly (unaryAdd_poly (unaryMul_poly (unaryComp_poly hI polyTimeComputable_pairSndD)
        (unaryComp_poly hT polyTimeComputable_pairSndD))
          (unaryLength_poly polyTimeComputable_pairFstD))
        (unaryComp_poly hK polyTimeComputable_pairSndD))
      (unaryComp_poly hK polyTimeComputable_pairSndD) (unaryComp_poly hM polyTimeComputable_pairSndD)
      (fun w => hKM (pairSndD w)))
      (unarySub_poly (unaryComp_poly hN polyTimeComputable_pairSndD)
        (unaryComp_poly hI polyTimeComputable_pairSndD))
  exact polyTimeComputable_firstIdx
    (p := fun z t => decide (blockVal (Rr z) ((I z * Tt z + t) * K z) (K z) < Nn z - I z)) hp hT

/-- The accepted offset of a position is a unary polynomial-time function. -/
theorem offsetVal_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (offsetVal (Nn z) (K z) (Tt z) (Rr z) (I z)) true :=
  blockVal_poly hR (unaryMul_poly (unaryAdd_poly (unaryMul_poly hI hT)
    (trialIdx_poly hN hK hT hR hI hM hKM)) hK) hK hM hKM

/-- The failure test of the sampler is polynomial-time (a search over the positions for one
whose every trial is rejected). -/
theorem fyFail_poly {Nn K Tt M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => [fyFail (Nn z) (K z) (Tt z) (Rr z)] := by
  have hp : PolyTimeComputable fun w =>
      [decide (trialIdx (Nn (pairSndD w)) (K (pairSndD w)) (Tt (pairSndD w)) (Rr (pairSndD w))
        (pairFstD w).length = Tt (pairSndD w))] :=
    eqTest_poly (trialIdx_poly (unaryComp_poly hN polyTimeComputable_pairSndD)
      (unaryComp_poly hK polyTimeComputable_pairSndD) (unaryComp_poly hT polyTimeComputable_pairSndD)
      (hR.comp polyTimeComputable_pairSndD) (unaryLength_poly polyTimeComputable_pairFstD)
      (unaryComp_poly hM polyTimeComputable_pairSndD) (fun w => hKM (pairSndD w)))
      (unaryComp_poly hT polyTimeComputable_pairSndD)
  exact ltTest_poly (polyTimeComputable_firstIdx
    (p := fun z i => decide (trialIdx (Nn z) (K z) (Tt z) (Rr z) i = Tt z)) hp hN) hN

/-- The Fisher–Yates target is a unary polynomial-time function. -/
theorem fyTarget_poly {Nn K Tt I M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hI : PolyTimeComputable fun z => List.replicate (I z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z) :
    PolyTimeComputable fun z => List.replicate (fyTarget (Nn z) (K z) (Tt z) (Rr z) (I z)) true := by
  unfold fyTarget
  convert polyTimeComputable_ite (ltTest_poly (trialIdx_poly hN hK hT hR hI hM hKM) hT)
    (unaryAdd_poly hI (offsetVal_poly hN hK hT hR hI hM hKM)) hI using 1
  funext z
  by_cases h : trialIdx (Nn z) (K z) (Tt z) (Rr z) (I z) < Tt z <;> simp [h]

/-- The transposition of unary functions is a unary polynomial-time function. -/
theorem swapNum_poly {A B Y : List Bool → ℕ}
    (hA : PolyTimeComputable fun z => List.replicate (A z) true)
    (hB : PolyTimeComputable fun z => List.replicate (B z) true)
    (hY : PolyTimeComputable fun z => List.replicate (Y z) true) :
    PolyTimeComputable fun z => List.replicate (swapNum (A z) (B z) (Y z)) true := by
  unfold swapNum
  convert polyTimeComputable_ite (eqTest_poly hY hA) hB
    (polyTimeComputable_ite (eqTest_poly hY hB) hA hY) using 1
  funext z
  simp only [decide_eq_true_eq]
  split_ifs <;> rfl

/-- **The Fisher–Yates permutation is unary polynomial-time** on a start `X z ≤ Nn z`.

**Proof sketch.** A counted loop (`polyTimeComputable_loopState`) of `Nn z` rounds from `1^{X z}`
whose round `m` applies the transposition of position `i = n - 1 - m` (`unarySub_poly`) with
target `fyTarget … i` (`fyTarget_poly`) to the current image `|s|` (`swapNum_poly`), truncated
to `n` tokens (`truncate_poly`) so that every update is bounded by `n ≤ C(|z|+1)^c`. On the
genuine orbit the truncation is the identity since the image stays at most `n` (`fyIter_le`,
`swapNum_le`, `fyTarget_lt`), so the state after `m ≤ n` rounds is `1^{fyIter … m}`
(`fyIter_succ`) and after `n` rounds `1^{fyApply …}` (`fyIter_self`). -/
theorem fyApply_poly {Nn K Tt X M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hX : PolyTimeComputable fun z => List.replicate (X z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z)
    (hXN : ∀ z, X z ≤ Nn z) :
    PolyTimeComputable fun z => List.replicate (fyApply (Nn z) (K z) (Tt z) (Rr z) (X z)) true := by
  let I : List Bool → ℕ := fun w => Nn (pairFstD w) - 1 - (pairFstD (pairSndD w)).length
  let upd : List Bool → List Bool := fun w =>
    (List.replicate (swapNum (I w)
      (fyTarget (Nn (pairFstD w)) (K (pairFstD w)) (Tt (pairFstD w)) (Rr (pairFstD w)) (I w))
      (pairSndD (pairSndD w)).length) true).take (Nn (pairFstD w))
  have hI : PolyTimeComputable fun w => List.replicate (I w) true :=
    unarySub_poly (unarySub_poly (unaryComp_poly hN polyTimeComputable_pairFstD) (unaryConst_poly 1))
      (unaryLength_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  have hupd : PolyTimeComputable upd :=
    truncate_poly (swapNum_poly hI (fyTarget_poly (unaryComp_poly hN polyTimeComputable_pairFstD)
      (unaryComp_poly hK polyTimeComputable_pairFstD) (unaryComp_poly hT polyTimeComputable_pairFstD)
      (hR.comp polyTimeComputable_pairFstD) hI (unaryComp_poly hM polyTimeComputable_pairFstD)
      (fun w => hKM (pairFstD w)))
      (unaryLength_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
      (unaryComp_poly hN polyTimeComputable_pairFstD)
  obtain ⟨C, c, hC⟩ := hN.output_length_le
  have hNC : ∀ x, Nn x ≤ (PolyExpr.normal C c).eval x.length := fun x => by
    have := hC x
    simpa [PolyExpr.eval_normal] using this
  have hloop := polyTimeComputable_loopState hupd hX hN (PolyExpr.normal C c)
    (fun x => by rw [List.length_replicate]; exact (hXN x).trans (hNC x))
    (fun x s => by
      show ((_ : List Bool).take (Nn (pairFstD (pairEncode x s)))).length ≤ _
      rw [pairFstD_pairEncode]
      exact (List.length_take_le _ _).trans (hNC x))
  convert hloop using 1
  funext z
  have key : ∀ m, m ≤ Nn z →
      loopState upd (fun z => List.replicate (X z) true) z m =
        List.replicate (fyIter (Nn z) (K z) (Tt z) (Rr z) (X z) m) true := by
    intro m
    induction m with
    | zero => intro _; simp [fyIter_zero]
    | succ m ih =>
      intro hm
      rw [loopState_succ, ih (Nat.le_of_succ_le hm), fyIter_succ (K z) (Tt z) (Rr z) (X z) hm]
      simp only [upd, I, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      rw [List.take_replicate, min_eq_right]
      exact swapNum_le (by omega) (fyTarget_lt (by omega)) (fyIter_le (hXN z) m (by omega))
  rw [key (Nn z) le_rfl, fyIter_self]

/-- The sampled permutation (identity on failure) is a unary polynomial-time function. -/
theorem permFromCoinsNum_poly {Nn K Tt X M : List Bool → ℕ} {Rr : List Bool → List Bool}
    (hN : PolyTimeComputable fun z => List.replicate (Nn z) true)
    (hK : PolyTimeComputable fun z => List.replicate (K z) true)
    (hT : PolyTimeComputable fun z => List.replicate (Tt z) true) (hR : PolyTimeComputable Rr)
    (hX : PolyTimeComputable fun z => List.replicate (X z) true)
    (hM : PolyTimeComputable fun z => List.replicate (M z) true) (hKM : ∀ z, 2 ^ K z ≤ M z)
    (hXN : ∀ z, X z ≤ Nn z) :
    PolyTimeComputable fun z =>
      List.replicate (permFromCoinsNum (Nn z) (K z) (Tt z) (Rr z) (X z)) true := by
  unfold permFromCoinsNum
  convert polyTimeComputable_ite (fyFail_poly hN hK hT hR hM hKM) hX
    (fyApply_poly hN hK hT hR hX hM hKM hXN) using 1
  funext z
  by_cases h : fyFail (Nn z) (K z) (Tt z) (Rr z) = true <;> simp [h]

/-! ### Identification with the typed sampler -/

/-- `List.findSome?` over `List.range T` is the value at the first index with a `some`, if any
(`firstIdx` on the `isSome` test).

**Proof sketch.** Induction on `T` through `List.range_succ` and `List.findSome?_append`. If the
search over `range T` already succeeds, appending `T` changes neither the search index
(`firstIdx_eq_of`, `firstIdx_min`) nor the `findSome?` (`Option.or_of_isSome`). Otherwise every
`t < T` is rejected (`firstIdx_eq_iff`), the `findSome?` is `g T`, and the search index over
`T + 1` is `T` if `g T` is a `some` and `T + 1` (giving `none = g T`) if not. -/
theorem findSome?_range_eq {β : Type*} (g : ℕ → Option β) : ∀ T : ℕ,
    (List.range T).findSome? g =
      if firstIdx (fun t => (g t).isSome) T < T then g (firstIdx (fun t => (g t).isSome) T)
      else none
  | 0 => by simp
  | T + 1 => by
    have hsing : [T].findSome? g = g T := by
      cases h : g T <;> simp [h]
    rw [List.range_succ, List.findSome?_append, findSome?_range_eq g T, hsing]
    by_cases h : firstIdx (fun t => (g t).isSome) T < T
    · have hq := q_firstIdx h
      have heq : firstIdx (fun t => (g t).isSome) (T + 1) = firstIdx (fun t => (g t).isSome) T :=
        firstIdx_eq_of (by omega) hq (fun i hi => firstIdx_min hi)
      rw [if_pos h, heq, if_pos (by omega), Option.or_of_isSome hq]
    · have hT : firstIdx (fun t => (g t).isSome) T = T :=
        le_antisymm firstIdx_le (not_lt.1 h)
      have hall : ∀ i < T, (g i).isSome = false := firstIdx_eq_iff.1 hT
      rw [if_neg h, Option.none_or]
      by_cases hgT : (g T).isSome = true
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T :=
          firstIdx_eq_of (by omega) hgT hall
        rw [heq, if_pos (by omega)]
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T + 1 :=
          firstIdx_eq_of_forall fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact hall i hi
            · exact Bool.eq_false_iff.2 hgT
        rw [heq, if_neg (lt_irrefl _)]
        exact Option.not_isSome_iff_eq_none.1 (by simpa using hgT)

/-- `List.findSome?` over `List.finRange T` as a `findSome?` over `List.range T`. -/
theorem findSome?_finRange_eq {β : Type*} {T : ℕ} (f : Fin T → Option β) :
    (List.finRange T).findSome? f =
      (List.range T).findSome? (fun t => if h : t < T then f ⟨t, h⟩ else none) := by
  rw [← List.map_coe_finRange, List.findSome?_map]
  congr 1
  funext t
  simp [Function.comp, t.isLt]

/-- The rejection sampler of position `i` on the blocks of the tape succeeds iff some trial is
accepted (`trialIdx < T`), and then returns the accepted offset `offsetVal`.

**Proof sketch.** `rejectionSample` is a `findSome?` over `List.finRange T`
(`findSome?_finRange_eq`, `findSome?_range_eq`), so it is the trial `uniformFromBits` at the
first index whose block reads below `n - i`; the `isSome` test of a trial is the comparison
`bitsToNat (c t) < n - i`, and `bitsToNat (c t) = blockVal r ((i T + t) k) k`
(`bitsToNat_eq_blockVal` with the block hypothesis `hc`), so the search index is `trialIdx`
(`firstIdx_congr`) and the accepted trial reads `offsetVal`. -/
theorem rejectionSample_eq_dite {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false) :
    rejectionSample (n - i) k T c =
      if h : trialIdx n k T r i < T then some ⟨offsetVal n k T r i, offsetVal_lt h⟩ else none := by
  have hval : ∀ t : Fin T, bitsToNat (c t) = blockVal r ((i * T + t) * k) k := fun t => by
    rw [← bitsToNat_eq_blockVal]
    congr 1
    funext j
    exact hc t j
  unfold rejectionSample
  rw [findSome?_finRange_eq, findSome?_range_eq]
  have hq : firstIdx (fun t => (if h : t < T then uniformFromBits (n - i) k (c ⟨t, h⟩) else none).isSome) T =
      trialIdx n k T r i := by
    apply firstIdx_congr
    intro t ht
    rw [dif_pos ht]
    unfold uniformFromBits
    rw [hval]
    split_ifs with h <;> simp [h]
  rw [hq]
  by_cases h : trialIdx n k T r i < T
  · rw [if_pos h, dif_pos h, dif_pos h]
    unfold uniformFromBits
    rw [hval]
    split_ifs with h2
    · rfl
    · exact absurd (offsetVal_lt h) h2
  · rw [if_neg h, dif_neg h]

/-- The rejection sampler of position `i` succeeds iff `trialIdx < T`. -/
theorem rejectionSample_isSome_iff {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false) :
    (rejectionSample (n - i) k T c).isSome ↔ trialIdx n k T r i < T := by
  rw [rejectionSample_eq_dite hc]
  split_ifs with h <;> simp [h]

/-- The value of a successful rejection sampler of position `i` is `offsetVal`. -/
theorem rejectionSample_get_val {n k T i : ℕ} {r : List Bool} {c : Fin T → Fin k → Bool}
    (hc : ∀ (t : Fin T) (j : Fin k), c t j = r.getD ((i * T + t) * k + j) false)
    (h : (rejectionSample (n - i) k T c).isSome) :
    ((rejectionSample (n - i) k T c).get h).val = offsetVal n k T r i := by
  have h' := (rejectionSample_isSome_iff hc).1 h
  have := rejectionSample_eq_dite (n := n) hc
  rw [dif_pos h'] at this
  simp [this]

/-- A transposition of `Fin n`, numerically. -/
theorem swap_val {n : ℕ} (a b y : Fin n) : ((Equiv.swap a b y : Fin n) : ℕ) = swapNum a b y := by
  rw [Equiv.swap_apply_def]
  unfold swapNum
  by_cases h1 : y = a
  · subst h1; simp
  · by_cases h2 : y = b
    · subst h2; simp [h1, Fin.val_eq_val]
    · have h1' : (y : ℕ) ≠ a := fun h => h1 (Fin.ext h)
      have h2' : (y : ℕ) ≠ b := fun h => h2 (Fin.ext h)
      simp [h1, h2, h1', h2']

/-- Folding transpositions over a list of positions, numerically: the composed permutation
applied to `x` is the fold of `swapNum` over the list of positions. -/
theorem foldr_swap_val {n : ℕ} (tg : Fin n → Fin n) (tgN : ℕ → ℕ)
    (htg : ∀ i : Fin n, (tg i : ℕ) = tgN i) :
    ∀ (l : List (Fin n)) (x : Fin n),
      ((l.foldr (fun i σ => Equiv.swap i (tg i) * σ) 1 x : Fin n) : ℕ) =
        (l.map Fin.val).foldr (fun i y => swapNum i (tgN i) y) x
  | [], x => by simp
  | i :: l, x => by
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, Equiv.Perm.mul_apply, swap_val,
      ← foldr_swap_val tg tgN htg l x, htg]

/-- The Fisher–Yates permutation with the accepted offsets as offsets is `fyApply`
(`foldr_swap_val`; no modulus wraps since every accepted offset is below `n - i`). -/
theorem fisherYates_val_eq {n k T : ℕ} {r : List Bool} {c : Fin n → ℕ}
    (hok : ∀ i : Fin n, trialIdx n k T r i < T) (hc : ∀ i : Fin n, c i = offsetVal n k T r i)
    (x : Fin n) : ((fisherYates n c x : Fin n) : ℕ) = fyApply n k T r x := by
  unfold fisherYates fyApply
  rw [← List.map_coe_finRange]
  apply foldr_swap_val
  intro i
  have h1 := offsetVal_lt (hok i)
  have h2 := i.isLt
  show (↑i + c ↑i % (n - ↑i)) % n = fyTarget n k T r ↑i
  rw [fyTarget, if_pos (hok i), hc i, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

/-- **The numeric model agrees with the typed sampler:** on a coin table whose block `(i, t)`
reads the tape bits `(i T + t) k + j`, the permutation `permFromCoins n k T b` with the identity
on failure sends the vertex `x` to `permFromCoinsNum n k T r x`.

**Proof sketch.** Unfold `permFromCoins`: the success condition `∀ i, (rejectionSample …).isSome`
is `¬ fyFail` (`rejectionSample_isSome_iff`, `firstIdx_lt_iff`), the sampled offsets are the
`offsetVal`s (`rejectionSample_get_val`), and `fisherYates_val_eq` identifies the permutation;
on failure both sides are the identity. -/
theorem permFromCoins_getD_val {n k T : ℕ} {r : List Bool} {b : Fin n → Fin T → Fin k → Bool}
    (hb : ∀ (i : Fin n) (t : Fin T) (j : Fin k), b i t j = r.getD ((i * T + t) * k + j) false)
    (x : Fin n) :
    (((permFromCoins n k T b).getD 1 x : Fin n) : ℕ) = permFromCoinsNum n k T r x := by
  have hsome : ∀ i : Fin n,
      (rejectionSample (n - i) k T (b i)).isSome ↔ trialIdx n k T r i < T :=
    fun i => rejectionSample_isSome_iff (hb i)
  have hfail : fyFail n k T r = true ↔ ¬ ∀ i : Fin n, (rejectionSample (n - i) k T (b i)).isSome := by
    unfold fyFail
    rw [decide_eq_true_eq, firstIdx_lt_iff]
    constructor
    · rintro ⟨i, hi, hq⟩ hall
      have h1 := (hsome ⟨i, hi⟩).1 (hall ⟨i, hi⟩)
      rw [decide_eq_true_eq] at hq
      exact absurd h1 (by rw [Fin.val_mk, hq]; exact lt_irrefl _)
    · intro hnot
      obtain ⟨i, hi⟩ := not_forall.1 hnot
      refine ⟨i, i.isLt, ?_⟩
      rw [decide_eq_true_eq]
      exact le_antisymm firstIdx_le (not_lt.1 (mt (hsome i).2 hi))
  unfold permFromCoins permFromCoinsNum
  split_ifs with h1 h2 h2
  · exact absurd h1 (hfail.1 h2)
  · rw [Option.getD_some]
    exact fisherYates_val_eq (fun i => (hsome i).1 (h1 i))
      (fun i => rejectionSample_get_val (hb i) (h1 i)) x
  · simp
  · exact absurd (hfail.2 h1) h2

end TCSlib.Cryptography.EncodingMachines

## ===== TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.ZeroKnowledge.Interaction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the commitment theorems

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.ZeroKnowledge.Commitment` [PS10, §4.7.1]: multi-value hiding of a
commitment scheme (Claim-126.a), the hiding of the bitwise scheme of Theorem 126.4
(Claim-127.d) and the polynomial-time evaluator of its `Com` (Alg-127.a). Nothing here mentions
the commitment definitions themselves; the file supplies

* **averaging over a coin factor** (`exists_fixCoins`): for a distinguisher whose coins split as
  `κ × ρ`, some fixed value `c₀` of the first factor has at least the advantage of the
  distinguisher. This is the non-uniform way to run the coordinatewise hybrid reduction
  `pairRed` of Claim-126.a without any sampler: the randomness of the other coordinates is
  hard-wired as advice, so neither hiding theorem needs an efficient evaluator of the scheme
  (the text's "simple hybrid argument" tacitly uses the non-uniformity of [PS10, Definition 126.3]);
* **coin transport** (`acceptProb_distinguisher_of_runAtL`, `acceptProb_distinguisherL_of_runAtL`):
  a machine with `D`'s coins whose activation is `D` on a pre-processed input has the acceptance
  probabilities of the pre-processed distinguisher;
* **splitting a tuple at a position** (`ofFn_update_eq`, `ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update`): the block string, respectively the message encoding
  `Strategy.encodeMsgs`, of a tuple with one position replaced by a challenge `z` is a fixed
  prefix, then `z` (respectively the pair `⟨z, ·⟩`), then a fixed suffix;
* **the splice machines** (`exists_spliceRed`, `exists_pairSpliceRed`): the `NUPPT`s that
  plant their argument between two hard-wired strings and call `D` once
  (`Complexity.NUPPT.exists_comp`, `Complexity.NUPPT.exists_withAdvice`);
* **the bitwise commitment loop** (`ComLoop`): the state loop evaluating
  `Com(v, (r_i)_i) = (F ⟨1^n, r_i⟩ ‖ (v_i ⊕ H ⟨1^n, r_i⟩))_i` from evaluators `F`, `H` of `f`, `h`
  (`Complexity.polyTimeComputable_iterateEmit`), with the closed form of its emissions.

## Main definitions

* `TCSlib.Cryptography.CommitmentLemmas.spliceFun`, `pairSpliceFun` — the splice pre-processings.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.step`, `ComLoop.emit`, `ComLoop.loopOut`,
  `ComLoop.init` — the bitwise commitment loop.

## Main results

* `TCSlib.Cryptography.CommitmentLemmas.exists_fixCoins` — averaging over a coin factor.
* `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL`,
  `acceptProb_distinguisherL_of_runAtL` — coin transport.
* `TCSlib.Cryptography.CommitmentLemmas.ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update` — splitting a tuple at a position.
* `TCSlib.Cryptography.CommitmentLemmas.exists_spliceRed`, `exists_pairSpliceRed` — the
  splice machines.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly`, `ComLoop.emit_init_of_lt`,
  `ComLoop.emit_init_of_le` — the loop is polynomial-time and its emissions are the one-bit
  commitments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.1.1: Lemma 71.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.3 (the multicopy hybrid argument).
-/

namespace TCSlib.Cryptography.CommitmentLemmas

open Complexity Turing Finset

/-! ### Averaging over a coin factor -/

/-- Some point of a finite nonempty type carries at least the absolute value of the average:
`|E f| ≤ |f c₀|` for some `c₀` (`Finset.exists_le_of_sum_le` against the constant `|E f|`). -/
theorem exists_abs_uexp_le {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :
    ∃ c₀, |uexp f| ≤ |f c₀| := by
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ _c : κ, |uexp f| ≤ ∑ c, |f c| := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uexp, abs_div, abs_of_pos hcard,
      mul_div_cancel₀ _ hcard.ne']
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨c₀, hc₀⟩

/-- The acceptance probability of a distinguisher with coins `κ × ρ` is the average over the
first coin factor of the acceptance probabilities with that factor fixed (`uprob_prod` after
regrouping the sample space). -/
theorem acceptProb_eq_uexp_fst {σ γ κ ρ : Type*} [Fintype σ] [Fintype κ] [Fintype ρ]
    (X : σ → γ) (D : γ → κ × ρ → Bool) :
    acceptProb X D = uexp fun c₀ => acceptProb X fun z c => D z (c₀, c) := by
  unfold acceptProb
  refine ((uprob_comp_equiv (EnsembleLemmas.swapAux κ σ ρ)
    fun z : σ × (κ × ρ) => D (X z.1) z.2 = true).symm.trans ?_)
  rw [uprob_prod]
  rfl

/-- **Averaging over a coin factor**: for a distinguisher `D` whose coins split as `κ × ρ`,
some fixed value `c₀` of the first factor does at least as well as `D` itself,
`distAdv X Y D ≤ distAdv X Y (D(·, (c₀, ·)))`. This is how a non-uniform reduction hard-wires
the randomness of the other coordinates of a hybrid argument instead of sampling them
([PS10, Definition 26.8], advice).

**Proof sketch.** Both acceptance probabilities are averages over `c₀`
(`acceptProb_eq_uexp_fst`), so the advantage is `|E_{c₀}[a(c₀) − b(c₀)]|`, and some `c₀` has
`|a(c₀) − b(c₀)|` at least the average (`exists_abs_uexp_le`). -/
theorem exists_fixCoins {σ τ γ κ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [Fintype ρ]
    [Nonempty κ] (X : σ → γ) (Y : τ → γ) (D : γ → κ × ρ → Bool) :
    ∃ c₀ : κ, distAdv X Y D ≤ distAdv X Y fun z c => D z (c₀, c) := by
  obtain ⟨c₀, hc₀⟩ := exists_abs_uexp_le fun c₀ : κ =>
    acceptProb X (fun z c => D z (c₀, c)) - acceptProb Y (fun z c => D z (c₀, c))
  refine ⟨c₀, ?_⟩
  unfold distAdv
  rw [acceptProb_eq_uexp_fst X D, acceptProb_eq_uexp_fst Y D]
  convert hc₀ using 2
  rw [uexp, uexp, uexp, ← sub_div, Finset.sum_sub_distrib]

/-- The distinguishing advantage is symmetric in the two distributions. -/
theorem distAdv_comm {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = distAdv Y X D :=
  abs_sub_comm _ _

/-! ### Coin transport -/

/-- A machine `B` with `D`'s coins whose activation on `y` is `D`'s on `g y` has, as a typed
distinguisher, the acceptance probabilities of the distinguisher `D(1^n, g ·)` (the coin types
correspond along `B.coins = D.coins`). -/
theorem acceptProb_distinguisher_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n m : ℕ} (X : σ → Fin m → Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisher n m) =
      acceptProb X fun z c => D.distinguisherL n (g (List.ofFn z)) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.distinguisherL, NUPPT.runAt_eq, hofn, hrun]

/-- As `acceptProb_distinguisher_of_runAtL`, for untyped samples. -/
theorem acceptProb_distinguisherL_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n : ℕ} (X : σ → List Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisherL n) = acceptProb X fun z c => D.distinguisherL n (g z) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisherL, NUPPT.runAt_eq, hofn, hrun]

/-! ### Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`; private copy of
`ofFn_eq_append_cons` of `Asymptotic/PublicKeyLemmas.lean`, which this file does not import). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- `List.ofFn (update W k z)` is the entries before `k`, then `z`, then the entries after `k`.

**Proof sketch.** `ofFn_eq_append_cons` splits `List.ofFn (update W k z)` at `k`; the entry at
`k` is `z` (`Function.update_self`) and the entries before and after `k` are those of `W`
(`Function.update_of_ne`, the indices `castLE i < k` and `k + 1 + i` differing from `k`). -/
theorem ofFn_update_eq {α : Type*} {N : ℕ} (W : Fin N → α) (k : Fin N) (z : α) :
    List.ofFn (Function.update W k z) = (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
      z :: List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩ := by
  rw [ofFn_eq_append_cons (Function.update W k z) k, Function.update_self]
  have h₁ : ∀ i : Fin k, Function.update W k z (Fin.castLE k.2.le i) = W (Fin.castLE k.2.le i) := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    have hi := i.2
    simp only [Fin.coe_castLE] at hv
    omega
  have h₂ : ∀ i : Fin (N - k - 1),
      Function.update W k z ⟨k + 1 + i, by omega⟩ = W ⟨k + 1 + i, by omega⟩ := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  simp only [h₁, h₂]

/-- The concatenation of `j` strings of `L` bits has `j · L` bits. -/
theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L := by
  simp [List.length_flatten, List.sum_ofFn]

/-- The block string of a tuple with block `k` replaced by `z`: the blocks before `k`, then
`z`, then the blocks after `k` (`FunFamily.ofFn_blocks_symm`, `ofFn_update_eq`). -/
theorem ofFn_blocks_symm_update {q ℓ : ℕ} (W : Fin q → Fin ℓ → Bool) (k : Fin q)
    (z : Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks q ℓ).symm (Function.update W k z)) =
      (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten ++ List.ofFn z ++
        (List.ofFn fun i : Fin (q - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten := by
  rw [FunFamily.ofFn_blocks_symm]
  have h2 : (fun i => List.ofFn (Function.update W k z i)) =
      Function.update (fun i => List.ofFn (W i)) k (List.ofFn z) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h2, ofFn_update_eq, List.flatten_append, List.flatten_cons, List.append_assoc]

/-- The encoding of a concatenated history is the concatenation of the encodings
(`pairEncode a (b ++ c) = pairEncode a b ++ c`). -/
theorem encodeMsgs_append (L M : List (List Bool)) :
    Strategy.encodeMsgs (L ++ M) = Strategy.encodeMsgs L ++ Strategy.encodeMsgs M := by
  induction L with
  | nil => rfl
  | cons m L ih => simp [ih, pairEncode, List.append_assoc]

/-- The encoding of a history of messages of length `≤ M` has length at most
`|L| · (2M + 2)` (`length_pairEncode`). -/
theorem length_encodeMsgs_le (L : List (List Bool)) (M : ℕ) (hM : ∀ m ∈ L, m.length ≤ M) :
    (Strategy.encodeMsgs L).length ≤ L.length * (2 * M + 2) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    have h1 := hM m (by simp)
    have h2 := ih fun m' hm' => hM m' (by simp [hm'])
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The encoding of a tuple with position `k` replaced by `z`: the encoding of the entries
before `k`, then the pair `⟨z, ·⟩` around the encoding of the entries after `k`
(`ofFn_update_eq`, `encodeMsgs_append`). -/
theorem encodeMsgs_ofFn_update {N : ℕ} (W : Fin N → List Bool) (k : Fin N) (z : List Bool) :
    Strategy.encodeMsgs (List.ofFn (Function.update W k z)) =
      Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
        pairEncode z (Strategy.encodeMsgs
          (List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩)) := by
  rw [ofFn_update_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]

/-- Chunks that are empty from index `n` on do not contribute: the concatenation over
`range m` equals the one over `range n` for `n ≤ m`. -/
theorem flatMap_range_eq_of_nil (F : ℕ → List Bool) {n m : ℕ} (hnm : n ≤ m)
    (hF : ∀ i, n ≤ i → F i = []) : (List.range m).flatMap F = (List.range n).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h : (List.range d).flatMap (fun a => F (n + a)) = [] :=
    List.flatMap_eq_nil_iff.2 fun x _ => hF _ (Nat.le_add_right n x)
  rw [h, List.append_nil]

/-- The head of a dropped list is the element at the dropping index (`List.getD`). -/
theorem headD_drop (l : List Bool) (i : ℕ) (d : Bool) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-! ### The splice machines -/

/-- The splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ z ++ suf`. -/
def spliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairFstD y ++ pairSndD (pairSndD y)

/-- The splice pre-processing is polynomial-time. -/
theorem spliceFun_poly : PolyTimeComputable spliceFun :=
  ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    polyTimeComputable_pairFstD).append
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The splice pre-processing on a well-formed argument. -/
@[simp] theorem spliceFun_pairEncode (z pre suf : List Bool) :
    spliceFun (pairEncode z (pairEncode pre suf)) = pre ++ z ++ suf := by
  simp [spliceFun]

/-- The pair-splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ ⟨z, suf⟩`. -/
def pairSpliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairEncode (pairFstD y) (pairSndD (pairSndD y))

/-- The pair-splice pre-processing is polynomial-time. -/
theorem pairSpliceFun_poly : PolyTimeComputable pairSpliceFun :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The pair-splice pre-processing on a well-formed argument. -/
@[simp] theorem pairSpliceFun_pairEncode (z pre suf : List Bool) :
    pairSpliceFun (pairEncode z (pairEncode pre suf)) = pre ++ pairEncode z suf := by
  simp [pairSpliceFun]

/-- **The splice machine**: for an `NUPPT` `D` and polynomially bounded strings `pre n`, `suf n`
there is an `NUPPT` `B` with `D`'s coins computing `D(1^n, pre n ++ y ++ suf n; r)`
(`Complexity.NUPPT.exists_comp` with `spliceFun`, then `Complexity.NUPPT.exists_withAdvice`
hard-wiring `⟨pre n, suf n⟩`). -/
theorem exists_spliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧ ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ y ++ suf n) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp spliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, spliceFun_pairEncode]
  rfl

/-- **The pair-splice machine**: as `exists_spliceRed`, computing
`D(1^n, pre n ++ ⟨y, suf n⟩; r)` (the argument planted as a message of an encoded history). -/
theorem exists_pairSpliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ pairEncode y (suf n)) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp pairSpliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, pairSpliceFun_pairEncode]
  rfl

/-! ### The bitwise commitment loop -/

namespace ComLoop

/-- The unary parameter slot `u` of the state word `⟨u, ⟨vs, rs⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The remaining value bits `vs` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining randomness `rs` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The state word `⟨u, ⟨vs, rs⟩⟩`. -/
def st (u vs rs : List Bool) : List Bool := pairEncode u (pairEncode vs rs)

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u vs rs : List Bool) : p₁ (st u vs rs) = u := by simp [p₁, st]

/-- Reading the value bits. -/
@[simp] theorem p₂_st (u vs rs : List Bool) : p₂ (st u vs rs) = vs := by simp [p₂, st]

/-- Reading the randomness. -/
@[simp] theorem p₃_st (u vs rs : List Bool) : p₃ (st u vs rs) = rs := by simp [p₃, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Assembling a state word from three polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) :=
  h₁.pairEncode (h₂.pairEncode h₃)

/-- The evaluators' argument at a state word: `⟨u, rs.take |u|⟩`, i.e. `⟨1^n, r_i⟩` for the
current randomness block. -/
def arg (w : List Bool) : List Bool := pairEncode (p₁ w) ((p₃ w).take (p₁ w).length)

/-- The argument is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` on
`⟨u, rs⟩`). -/
theorem arg_poly : PolyTimeComputable arg := by
  convert p₁_poly.pairEncode
    ((polyTimeComputable_pairTakePoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [arg]

/-- The step: drop the first value bit and the first `|u|` randomness bits. -/
def step (w : List Bool) : List Bool := st (p₁ w) (p₂ w).tail ((p₃ w).drop (p₁ w).length)

/-- The step is polynomial-time (`StateLoop.tail_poly`,
`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rs⟩`). -/
theorem step_poly : PolyTimeComputable step := by
  convert st_poly p₁_poly (StateLoop.tail_poly.comp p₂_poly)
    ((polyTimeComputable_pairDropPoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most four symbols (the pairing overhead; both components
only shrink). -/
theorem length_step_le (w : List Bool) : (step w).length ≤ w.length + 4 := by
  have h₁ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le w
  have h₂ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le (pairSndD w)
  simp only [step, st, length_pairEncode, List.length_tail, List.length_drop, p₁, p₂, p₃]
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    (step^[i] w).length ≤ w.length + 4 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le (step^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨vs, rs⟩⟩`: after `i` rounds the state word is
`⟨u, ⟨vs.drop i, rs.drop (i · |u|)⟩⟩`. -/
theorem iterate_step (u vs rs : List Bool) (i : ℕ) :
    step^[i] (st u vs rs) = st u (vs.drop i) (rs.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, p₁_st, p₂_st, p₃_st, List.tail_drop, List.drop_drop]
    congr 2
    ring

variable (F H : List Bool → List Bool)

/-- The emission at a state word: nothing once the value bits are exhausted, else the one-bit
commitment `F ⟨u, r_i⟩ ++ [v_i ⊕ H ⟨u, r_i⟩]` of the current value bit with the current block
(Alg-127.a). -/
def emit (w : List Bool) : List Bool :=
  if p₂ w = [] then [] else F (arg w) ++ [xor ((p₂ w).headD false) ((H (arg w)).headD false)]

/-- The emission is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
`StateLoop.isNil_poly`, `StateLoop.headBit_poly`, `StateLoop.xor_poly`,
`PolyTimeComputable.append`). -/
theorem emit_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (emit F H) := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp p₂_poly) (polyTimeComputable_const [])
    ((hF.comp arg_poly).append (StateLoop.xor_poly (StateLoop.headBit_poly.comp p₂_poly)
      (StateLoop.headBit_poly.comp (hH.comp arg_poly)))) using 1
  funext w
  simp [emit]

/-- The loop output: the emissions along the `|x| + 1` rounds from `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => emit F H (step^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 4 |x| = 5 |x|`). -/
theorem loopOut_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (loopOut F H) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit step_poly (emit_poly F H hF hH) .var (.mul (.const 5) .var)
    fun x i hi => ?_
  have := length_iterate_step_le x i
  simp only [PolyExpr.eval_var] at hi
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The initial state from the argument `⟨v, r⟩`: `⟨1^{|v|}, ⟨v, padL (|v|²) r⟩⟩` (the
randomness padded or cut to `|v|²` bits, as `padFin` does). -/
def init (w : List Bool) : List Bool :=
  st (List.replicate (pairFstD w).length true) (pairFstD w)
    (EnsembleLemmas.padL ((pairFstD w).length * (pairFstD w).length) (pairSndD w))

/-- The initial state is polynomial-time (`Complexity.polyTimeComputable_unary`,
`EnsembleLemmas.polyTimeComputable_padL`). -/
theorem init_poly : PolyTimeComputable init := by
  convert st_poly (polyTimeComputable_unary.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairFstD (EnsembleLemmas.polyTimeComputable_padL (.mul .var .var)
      polyTimeComputable_pairFstD polyTimeComputable_pairSndD) using 1

/-- The initial state only depends on the two components of the argument. -/
theorem init_eq (w : List Bool) : init w = init (pairEncode (pairFstD w) (pairSndD w)) := by
  simp [init]

/-- Once the value bits are exhausted (round `i ≥ |v|`), the loop emits nothing. -/
theorem emit_init_of_le {v r : List Bool} {i : ℕ} (hi : v.length ≤ i) :
    emit F H (step^[i] (init (pairEncode v r))) = [] := by
  simp [init, iterate_step, emit, List.drop_eq_nil_of_le hi]

/-- At round `i < |v|` the loop emits the one-bit commitment of the bit `v[i]` with the `i`-th
block of the padded randomness: `F ⟨1^n, r_i⟩ ++ [v[i] ⊕ (H ⟨1^n, r_i⟩)[0]]` with
`r_i = blocks n n (padFin (n²) r) i`, `n = |v|` (`EnsembleLemmas.take_drop_ofFn_blocks`). -/
theorem emit_init_of_lt {v r : List Bool} {i : ℕ} (hi : i < v.length) :
    emit F H (step^[i] (init (pairEncode v r))) =
      F (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks v.length v.length
        (padFin (v.length * v.length) r) ⟨i, hi⟩))) ++
      [xor (v.getD i false) ((H (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks
        v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩)))).headD false)] := by
  have hne : v.drop i ≠ [] := by
    rw [Ne, List.drop_eq_nil_iff]
    omega
  have hblock : ((EnsembleLemmas.padL (v.length * v.length) r).drop (i * v.length)).take v.length =
      List.ofFn (EnsembleLemmas.blocks v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩) :=
    EnsembleLemmas.take_drop_ofFn_blocks (padFin (v.length * v.length) r) i hi
  simp only [init, pairFstD_pairEncode, pairSndD_pairEncode, iterate_step, List.length_replicate,
    emit, arg, p₁_st, p₂_st, p₃_st, hne, if_false, hblock, NUPPT.advInput, headD_drop]

end ComLoop

end TCSlib.Cryptography.CommitmentLemmas

## ===== TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Transfer infrastructure for zero-knowledge proofs along Levin reductions

Proof infrastructure for `TCSlib.Cryptography.ZeroKnowledge.NP` (Claim-124.d, the transfer of
interactive proofs with efficient prover and of zero-knowledge along a Levin reduction
`(f, w)` with length polynomial `p`), kept in a sibling file so that the public statements of
`NP.lean` stay where the audit froze them. Nothing here is specific to 3-colouring.

Three kinds of tools:

* **Executions.** `exec_congr`: two executions whose next-message functions agree on every
  history (possibly with different common inputs, auxiliary inputs and random tapes) have the
  same transcripts.
* **Uniform coin projections.** The pulled-back protocol runs at parameter `|x|` with the coin
  polynomials of `π` evaluated at `p(|x|) = |f x|`, while the machines of the zero-knowledge
  reduction (the verifier `V*'` for `π`, the distinguisher `D'`) run at parameter `|f x| ≥ |x|`
  and read only the first `coinLen |x|` bits of their tapes. A map `g : Ω → Ω'` between finite
  coin spaces is a *uniform projection* (`UnifProj g`) when it is the first component of a
  bijection `Ω ≃ Ω' × K`; the truncation `coinTrunc : (Fin M → Bool) → (Fin m → Bool)` of a coin
  string to its first `m ≤ M` bits is one, uniform projections are closed under products, and
  the law of an event is invariant under them (`UnifProj.uprob_comp`,
  `acceptProb_eq_of_unifProj`, `distAdv_eq_of_unifProj`: "the padding is uniform and
  independent").
* **The machines of the reduction.** `liftVerifier V'` is the verifier `V*'` for `π` obtained
  from a verifier `V'` of the pulled-back protocol (it recovers `x` and `z` from its auxiliary
  input `⟨x, z⟩`, ignores the common input `f x`, and runs `V'` on the first `V'.coinLen |x|`
  coins; `liftVerifier_efficient`); `postView c` re-encodes a view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩`
  of `V*'` as the view `⟨⟨x, z⟩, ⟨r'.take (c |x|), msgs⟩⟩` of `V'` (`postView_encode`,
  `polyTimeComputable_postView`); `exists_liftSimulator` builds the simulator for `V'` from
  the one for `V*'` (`NUPPT.exists_comp`, `NUPPT.exists_reparam`), and `exists_liftDistinguisher`
  the distinguisher for `π` at parameter `p(|x|)` from one for the pulled-back protocol at
  parameter `|x|` (`NUPPT.exists_reparam_advice` along a left inverse `φ` of `p.eval`, which
  exists because a syntactic polynomial with `p ≥ id` is strictly increasing,
  `polyExpr_strictMono_of_le`).

## Main definitions

* `TCSlib.Cryptography.LevinTransfer.coinTrunc`, `TCSlib.Cryptography.LevinTransfer.UnifProj`
  — truncation of coin strings and uniform projections of finite coin spaces.
* `TCSlib.Cryptography.LevinTransfer.liftVerifier`,
  `TCSlib.Cryptography.LevinTransfer.postView` — the verifier `V*'` and the view re-encoder of
  the zero-knowledge transfer (Claim-124.d).

## Main results

* `TCSlib.Cryptography.LevinTransfer.exec_congr` — executions with pointwise equal
  next-message functions coincide.
* `TCSlib.Cryptography.LevinTransfer.UnifProj.uprob_comp`,
  `TCSlib.Cryptography.LevinTransfer.distAdv_eq_of_unifProj` — events and distinguishing
  advantages are invariant under uniform projections of the coin spaces.
* `TCSlib.Cryptography.LevinTransfer.polyExpr_strictMono_of_le` — a syntactic polynomial
  dominating the identity is strictly increasing (hence injective).
* `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient`,
  `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator`,
  `TCSlib.Cryptography.LevinTransfer.exists_liftDistinguisher`,
  `TCSlib.Cryptography.LevinTransfer.distinguisherL_lift` — the machines of the reduction
  and their functional equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, step 2.)
-/

namespace TCSlib.Cryptography.LevinTransfer

open Complexity Turing

/-! ### Executions with pointwise equal next-message functions -/

/-- Two executions whose next-message functions agree on every history — with possibly
different common inputs, auxiliary inputs and random tapes — have the same transcripts after
any number of moves (induction on the number of moves, `exec_succ`). This is the congruence
behind every "the pulled-back protocol on `x` is `π` on `f x`" step of Claim-124.d. -/
theorem exec_congr {P₁ V₁ P₂ V₂ : Strategy} {x₁ zP₁ zV₁ rP₁ rV₁ x₂ zP₂ zV₂ rP₂ rV₂ : List Bool}
    (hP : ∀ hist, P₁.next x₁ zP₁ rP₁ hist = P₂.next x₂ zP₂ rP₂ hist)
    (hV : ∀ hist, V₁.next x₁ zV₁ rV₁ hist = V₂.next x₂ zV₂ rV₂ hist) (vFirst : Bool) (k : ℕ) :
    exec P₁ V₁ vFirst x₁ zP₁ zV₁ rP₁ rV₁ k = exec P₂ V₂ vFirst x₂ zP₂ zV₂ rP₂ rV₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ, exec_succ, ih]
    simp only [hP, hV]

/-! ### Coin truncation and uniform projections -/

/-- The first `m` bits of a coin string of length `M ≥ m`, as a typed coin string. -/
def coinTrunc {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) : Fin m → Bool := fun i => r (Fin.castLE h i)

/-- The list of a truncated coin string is the `take` of the list of the full string. -/
theorem ofFn_coinTrunc {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) :
    List.ofFn (coinTrunc h r) = (List.ofFn r).take m := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  simp [coinTrunc, List.getElem_take, List.getElem_ofFn]

/-- Truncating to the full length changes nothing (the typed cast of a coin string between
two coin spaces of equal size; the inequality `h` is a separate argument so that `rw` can
match it against the proof term found in the goal). -/
theorem ofFn_coinTrunc_of_eq {m M : ℕ} (h : m ≤ M) (h' : m = M) (r : Fin M → Bool) :
    List.ofFn (coinTrunc h r) = List.ofFn r := by
  rw [ofFn_coinTrunc, List.take_of_length_le (by simp [h'])]

/-- The bijection `{0,1}^M ≃ {0,1}^m × {0,1}^{M - m}` splitting a coin string at position
`m ≤ M` (`finSumFinEquiv`, `Equiv.sumArrowEquivProdArrow`). -/
def truncEquiv {m M : ℕ} (h : m ≤ M) : (Fin M → Bool) ≃ (Fin m → Bool) × (Fin (M - m) → Bool) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl Bool)).trans
    ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _))

/-- The first component of the splitting bijection is the truncation. -/
theorem truncEquiv_fst {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) :
    (truncEquiv h r).1 = coinTrunc h r := by
  funext i
  simp only [truncEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.symm_symm, finSumFinEquiv_apply_left, finCongr_symm, finCongr_apply, coinTrunc]
  congr 1

/-- A map `g : Ω → Ω'` between finite coin spaces is a **uniform projection** when it is the
first component of a bijection `Ω ≃ Ω' × K` with `K` nonempty: the image of the uniform
distribution on `Ω` under `g` is the uniform distribution on `Ω'`, the fibres being the
"independent padding" `K`. -/
def UnifProj {Ω Ω' : Type} (g : Ω → Ω') : Prop :=
  ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (e : Ω ≃ Ω' × K), ∀ ω, (e ω).1 = g ω

/-- The law of an event is invariant under a uniform projection: `Pr_ω[q (g ω)] = Pr[q]`
(`uprob_comp_equiv` along the bijection, then `uprob_fst`). -/
theorem UnifProj.uprob_comp {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] {g : Ω → Ω'} (hg : UnifProj g)
    (q : Ω' → Prop) : uprob (fun ω => q (g ω)) = uprob q := by
  obtain ⟨K, _, _, e, he⟩ := hg
  have : (fun ω => q (g ω)) = fun ω => (fun z : Ω' × K => q z.1) (e ω) := by
    funext ω
    simp [he]
  rw [this]
  exact (uprob_comp_equiv e (fun z : Ω' × K => q z.1)).trans (uprob_fst q)

/-- Truncating a uniform coin string is a uniform projection (`truncEquiv`). -/
theorem unifProj_coinTrunc {m M : ℕ} (h : m ≤ M) : UnifProj (coinTrunc h) :=
  ⟨Fin (M - m) → Bool, inferInstance, inferInstance, truncEquiv h, truncEquiv_fst h⟩

/-- Uniform projections are closed under products (`Equiv.prodProdProdComm`). -/
theorem UnifProj.prod {Ω₁ Ω₁' Ω₂ Ω₂' : Type} {g₁ : Ω₁ → Ω₁'} {g₂ : Ω₂ → Ω₂'}
    (h₁ : UnifProj g₁) (h₂ : UnifProj g₂) : UnifProj (Prod.map g₁ g₂) := by
  obtain ⟨K₁, _, _, e₁, he₁⟩ := h₁
  obtain ⟨K₂, _, _, e₂, he₂⟩ := h₂
  refine ⟨K₁ × K₂, inferInstance, inferInstance,
    (Equiv.prodCongr e₁ e₂).trans (Equiv.prodProdProdComm Ω₁' K₁ Ω₂' K₂), fun ω => ?_⟩
  obtain ⟨ω₁, ω₂⟩ := ω
  simp [Equiv.prodProdProdComm, Prod.map, he₁, he₂]

/-- A distinguisher's acceptance probability is invariant under uniform projections of the
sampler's seed space and of its own coin space. -/
theorem acceptProb_comp_unifProj {σ σ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype ρ]
    [Fintype ρ'] (X : σ → γ) (D : γ → ρ → Bool) {gσ : σ' → σ} {gρ : ρ' → ρ}
    (hσ : UnifProj gσ) (hρ : UnifProj gρ) :
    acceptProb (fun s => X (gσ s)) (fun v r => D v (gρ r)) = acceptProb X D := by
  unfold acceptProb
  exact (hσ.prod hρ).uprob_comp (fun z : σ × ρ => D (X z.1) z.2 = true)

/-- Acceptance probabilities agree when the primed experiment is the unprimed one composed
with uniform projections: if `D' (X' s) r = D (X (gσ s)) (gρ r)` pointwise, then
`Pr[D'(X') = 1] = Pr[D(X) = 1]`. -/
theorem acceptProb_eq_of_unifProj {σ σ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype ρ]
    [Fintype ρ'] {X : σ → γ} {X' : σ' → γ} {D : γ → ρ → Bool} {D' : γ → ρ' → Bool}
    {gσ : σ' → σ} {gρ : ρ' → ρ} (hσ : UnifProj gσ) (hρ : UnifProj gρ)
    (hX : ∀ s r, D' (X' s) r = D (X (gσ s)) (gρ r)) : acceptProb X' D' = acceptProb X D := by
  rw [← acceptProb_comp_unifProj X D hσ hρ]
  unfold acceptProb
  congr 1
  funext z
  rw [hX]

/-- Distinguishing advantages agree when both samplers and the distinguisher of the primed
experiment are those of the unprimed one composed with uniform projections (the "padding is
uniform and independent" step of Claim-124.d). -/
theorem distAdv_eq_of_unifProj {σ σ' τ τ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype τ]
    [Fintype τ'] [Fintype ρ] [Fintype ρ'] {X : σ → γ} {X' : σ' → γ} {Y : τ → γ} {Y' : τ' → γ}
    {D : γ → ρ → Bool} {D' : γ → ρ' → Bool} {gσ : σ' → σ} {gτ : τ' → τ} {gρ : ρ' → ρ}
    (hσ : UnifProj gσ) (hτ : UnifProj gτ) (hρ : UnifProj gρ)
    (hX : ∀ s r, D' (X' s) r = D (X (gσ s)) (gρ r))
    (hY : ∀ t r, D' (Y' t) r = D (Y (gτ t)) (gρ r)) : distAdv X' Y' D' = distAdv X Y D := by
  unfold distAdv
  rw [acceptProb_eq_of_unifProj hσ hρ hX, acceptProb_eq_of_unifProj hτ hρ hY]

/-! ### Syntactic polynomials dominating the identity are strictly increasing -/

/-- A syntactic polynomial is either constant or strictly increasing.

**Proof sketch.** Induction on the expression. A constant is constant and the variable is
strictly increasing. A sum of two constants is constant, and a sum with at least one strictly
increasing summand is strictly increasing (`Nat.add_lt_add_left/right`, `Nat.add_lt_add`). A
product of two constants is constant; a constant times a strictly increasing function is
constant when the constant is `0` and strictly increasing otherwise
(`Nat.mul_lt_mul_of_pos_left/right`); a product of two strictly increasing functions with
values in `ℕ` is strictly increasing (`Nat.mul_lt_mul_of_lt_of_lt`). The power `p ^ 0` is
constant, and `p ^ (c + 1)` is constant or strictly increasing according to `p`
(`Nat.pow_lt_pow_left`). -/
theorem polyExpr_eval_const_or_strictMono (p : PolyExpr) :
    (∀ N, p.eval N = p.eval 0) ∨ StrictMono p.eval := by
  induction p with
  | const c => exact Or.inl fun _ => rfl
  | var => exact Or.inr strictMono_id
  | add p q hp hq =>
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl fun N => by simp only [PolyExpr.eval_add, hp N, hq N]
    · exact Or.inr fun a b h => by
        simp only [PolyExpr.eval_add, hp a, hp b]
        exact Nat.add_lt_add_left (hq h) _
    · exact Or.inr fun a b h => by
        simp only [PolyExpr.eval_add, hq a, hq b]
        exact Nat.add_lt_add_right (hp h) _
    · exact Or.inr fun a b h => Nat.add_lt_add (hp h) (hq h)
  | mul p q hp hq =>
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hp N, hq N]
    · by_cases h0 : p.eval 0 = 0
      · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hp N, h0, Nat.zero_mul]
      · exact Or.inr fun a b h => by
          simp only [PolyExpr.eval_mul, hp a, hp b]
          exact Nat.mul_lt_mul_of_pos_left (hq h) (Nat.pos_of_ne_zero h0)
    · by_cases h0 : q.eval 0 = 0
      · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hq N, h0, Nat.mul_zero]
      · exact Or.inr fun a b h => by
          simp only [PolyExpr.eval_mul, hq a, hq b]
          exact Nat.mul_lt_mul_of_pos_right (hp h) (Nat.pos_of_ne_zero h0)
    · exact Or.inr fun a b h => Nat.mul_lt_mul_of_lt_of_lt (hp h) (hq h)
  | pow p c hp =>
    cases c with
    | zero => exact Or.inl fun N => by simp [PolyExpr.eval_pow]
    | succ c =>
      rcases hp with hp | hp
      · exact Or.inl fun N => by simp only [PolyExpr.eval_pow, hp N]
      · exact Or.inr fun a b h => Nat.pow_lt_pow_left (hp h) (Nat.succ_ne_zero c)

/-- A syntactic polynomial dominating the identity is strictly increasing (it is not constant,
since `p(p(0) + 1) ≥ p(0) + 1 > p(0)`), hence injective: the length polynomial of a Levin
reduction has a left inverse, along which the distinguisher of the zero-knowledge transfer is
re-parametrized. -/
theorem polyExpr_strictMono_of_le {p : PolyExpr} (hp : ∀ N, N ≤ p.eval N) : StrictMono p.eval := by
  rcases polyExpr_eval_const_or_strictMono p with h | h
  · exfalso
    have := hp (p.eval 0 + 1)
    rw [h (p.eval 0 + 1)] at this
    omega
  · exact h

/-! ### The verifier `V*'` of the zero-knowledge transfer -/

/-- The verifier `V*'` for `π` built from a verifier `V'` of the pulled-back protocol
[PS10, §4.7, Theorem 124.1, step 2] (Claim-124.d, zero-knowledge half): it recovers the
original instance `x` and auxiliary input `z` from its auxiliary input `⟨x, z⟩`, ignores the
common input `x' = f x`, and runs `V'` on the first `V'.coinLen |x|` bits of its random tape.
Its coin polynomial is `V'.coins`, so at `|x'| = p(|x|) ≥ |x|` the tape is long enough
(`PolyExpr.eval_mono`). -/
def liftVerifier (V' : Strategy) : Strategy where
  next _ z' r hist :=
    V'.next (pairFstD z') (pairSndD z') (r.take (V'.coinLen (pairFstD z').length)) hist
  coins := V'.coins

/-- The next-message function of `liftVerifier V'` on the auxiliary input `⟨x, z⟩`. -/
theorem liftVerifier_next (V' : Strategy) (x' x z r : List Bool) (hist : List (List Bool)) :
    (liftVerifier V').next x' (pairEncode x z) r hist =
      V'.next x z (r.take (V'.coinLen x.length)) hist := by
  simp [liftVerifier]

/-- The coin length of `liftVerifier V'` is that of `V'`. -/
theorem liftVerifier_coinLen (V' : Strategy) (n : ℕ) :
    (liftVerifier V').coinLen n = V'.coinLen n := rfl

/-- `liftVerifier V'` is efficient when `V'` is.

**Proof sketch.** From `hV'` take the uniform `A` with `V'.next x z r hist =
A.runAtL |x| ⟨⟨x, z⟩, msgs⟩ r`. On the raw layout `⟨⟨⟨1^{|x'|}, ⟨⟨x', ⟨x, z⟩⟩, msgs⟩⟩, []⟩, r⟩`
the function `⟨x, z⟩ ↦ A.output ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r.take (A.coins |x|)⟩` is
polynomial-time: the slots are projection chains (`NUPPT.inArg`, `NUPPT.inCoins`, `pairFstD`,
`pairSndD`), `1^{|x|}` is `Complexity.polyTimeComputable_unary`, the cut is
`Complexity.polyTimeComputable_pairTakePoly A.coins` on `⟨x, r⟩`, the layout is
`NUPPT.polyTimeComputable_layout` and the machine `NUPPT.polyTimeComputable_output`.
`NUPPT.ofPolyTimeUniform` of it with coins `A.coins = V'.coins` is uniform and computes
`liftVerifier V'` (`NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.runAtL_eq_output_layout`, the
advice of `A` being empty). -/
theorem liftVerifier_efficient {V' : Strategy} (hV' : V'.Efficient) :
    (liftVerifier V').Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hV'
  have hz' : PolyTimeComputable fun L => pairSndD (pairFstD (NUPPT.inArg L)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)
  have hxx : PolyTimeComputable fun L => pairFstD (pairSndD (pairFstD (NUPPT.inArg L))) :=
    polyTimeComputable_pairFstD.comp hz'
  have hzz : PolyTimeComputable fun L => pairSndD (pairSndD (pairFstD (NUPPT.inArg L))) :=
    polyTimeComputable_pairSndD.comp hz'
  have hm : PolyTimeComputable fun L => pairSndD (NUPPT.inArg L) :=
    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hu : PolyTimeComputable fun L =>
      List.replicate (pairFstD (pairSndD (pairFstD (NUPPT.inArg L)))).length true :=
    polyTimeComputable_unary.comp hxx
  have htake : PolyTimeComputable fun L =>
      (NUPPT.inCoins L).take (A.coins.eval (pairFstD (pairSndD (pairFstD (NUPPT.inArg L)))).length) := by
    convert (polyTimeComputable_pairTakePoly A.coins).comp
      (hxx.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
    funext L
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF := A.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hu ((hxx.pairEncode hzz).pairEncode hm)
      (polyTimeComputable_const []) htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF A.coins, NUPPT.ofPolyTimeUniform_uniform hF _, hc,
    fun x' z' r hist => ?_⟩
  rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
  show V'.next _ _ _ _ = _
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA]
  simp only [Function.comp_apply, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, Strategy.coinLen, hc]

/-! ### Re-encoding views -/

/-- The view re-encoder of the zero-knowledge transfer: a view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` of
`V*' = liftVerifier V'` in `π` becomes the view `⟨⟨x, z⟩, ⟨r'.take (c |x|), msgs⟩⟩` of `V'` in
the pulled-back protocol, where `c = V'.coins` (the simulator for `V'` is `postView` of the
simulator for `V*'`, and the distinguisher for `V*'` is the one for `V'` after `postView`). -/
def postView (c : PolyExpr) (v : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD v))
    (pairEncode ((pairFstD (pairSndD v)).take (c.eval (pairFstD (pairSndD (pairFstD v))).length))
      (pairSndD (pairSndD v)))

/-- `postView` on an encoded view with auxiliary input `⟨x, z⟩`. -/
theorem postView_encode (c : PolyExpr) (x' x z r' : List Bool) (msgs : List (List Bool)) :
    postView c (View.encode ⟨x', pairEncode x z, r', msgs⟩) =
      View.encode ⟨x, z, r'.take (c.eval x.length), msgs⟩ := by
  simp [postView, View.encode]

/-- `postView c` is polynomial-time (projection chains, `polyTimeComputable_pairTakePoly c`
on `⟨x, r'⟩`, `PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_postView (c : PolyExpr) : PolyTimeComputable (postView c) := by
  have h1 : PolyTimeComputable fun v => pairSndD (pairFstD v) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hx : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD v)) :=
    polyTimeComputable_pairFstD.comp h1
  have hr : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun v => pairSndD (pairSndD v) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have htake : PolyTimeComputable fun v =>
      (pairFstD (pairSndD v)).take (c.eval (pairFstD (pairSndD (pairFstD v))).length) := by
    convert (polyTimeComputable_pairTakePoly c).comp (hx.pairEncode hr) using 1
    funext v
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact h1.pairEncode (htake.pairEncode hm)

/-! ### The simulator and the distinguisher of the zero-knowledge transfer -/

/-- **The simulator for `V'` from the simulator for `V*'`** (Claim-124.d): for a machine `S'`
(the simulator for `liftVerifier V'` in `π`), a polynomial-time `f` and polynomials `c`, `p`,
there is a machine `S` with coins `S'.coins.subst p`, uniform when `S'` is, with
`S(1^n, y; r) = postView c (S'(1^{p n}, ⟨f (fst y), y⟩; r))` — on `y = ⟨x, z⟩` this is
`postView` of `S'` run on `(f x, ⟨x, z⟩)` at parameter `p(|x|) = |f x|`
(`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, `post := postView c`, then
`NUPPT.exists_reparam p`). -/
theorem exists_liftSimulator (S' : NUPPT) {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (c p : PolyExpr) :
    ∃ S : NUPPT, S.coins = S'.coins.subst p ∧ (S'.Uniform → S.Uniform) ∧
      ∀ n y r, S.runAtL n y r = postView c (S'.runAtL (p.eval n) (pairEncode (f (pairFstD y)) y) r) := by
  obtain ⟨B, hBc, -, hBadv, hB⟩ := S'.exists_comp
    ((hf.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_id)
    (polyTimeComputable_postView c)
  obtain ⟨S, hSc, hSu, hS⟩ := B.exists_reparam p
  refine ⟨S, by rw [hSc, hBc], fun hu => hSu fun n => by rw [hBadv]; exact hu n, fun n y r => ?_⟩
  rw [hS, hB]
  rfl

/-- **The distinguisher for `π` from the distinguisher for the pulled-back protocol**
(Claim-124.d): for a machine `D`, a map `φ` with `φ n ≤ n` (a left inverse of the length
polynomial) and a polynomial `c`, there is a machine `D'` with `D`'s coins such that
`D'(1^n, v; r) = D(1^{φ n}, postView c v; r.take (D.coinLen (φ n)))`
(`NUPPT.exists_reparam_advice` along `φ` with majorant `var`, then `NUPPT.exists_comp` with
`pre := postView c`). -/
theorem exists_liftDistinguisher (D : NUPPT) (φ : ℕ → ℕ) (hφ : ∀ n, φ n ≤ n) (c : PolyExpr) :
    ∃ D' : NUPPT, D'.coins = D.coins ∧
      ∀ n y r, D'.runAtL n y r = D.runAtL (φ n) (postView c y) (r.take (D.coinLen (φ n))) := by
  obtain ⟨B, hBc, hB⟩ := D.exists_reparam_advice φ .var hφ
  obtain ⟨D', hDc, -, -, hD'⟩ := B.exists_comp (polyTimeComputable_postView c) polyTimeComputable_id
  refine ⟨D', by rw [hDc, hBc, PolyExpr.subst_var], fun n y r => ?_⟩
  rw [hD', hB]
  rfl

/-- The verdict of the lifted distinguisher at parameter `n` with `φ n = m` is the verdict of
`D` at parameter `m` on the re-encoded sample with the truncated coins
(`NUPPT.distinguisherL`, `ofFn_coinTrunc`). -/
theorem distinguisherL_lift {D D' : NUPPT} {φ : ℕ → ℕ} {c : PolyExpr}
    (hD' : ∀ n y r, D'.runAtL n y r = D.runAtL (φ n) (postView c y) (r.take (D.coinLen (φ n))))
    {n m : ℕ} (hφn : φ n = m) (hle : D.coinLen m ≤ D'.coinLen n) (v : List Bool)
    (ρ : D'.Coins n) :
    D'.distinguisherL n v ρ = D.distinguisherL m (postView c v) (coinTrunc hle ρ) := by
  simp only [NUPPT.distinguisherL, NUPPT.runAt_eq, hD', hφn, ofFn_coinTrunc]

end TCSlib.Cryptography.LevinTransfer
