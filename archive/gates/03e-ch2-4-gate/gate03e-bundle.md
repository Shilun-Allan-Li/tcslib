## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack.md =====

# Gate 03e ([PS10] ch. 2–4, interaction and ZK definitions): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/e/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the interaction model (strategies, executions, views, protocols), interactive proofs, the zero-knowledge definitions, commitments, and the NP layer used by Thm 124.1.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03e-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.4–§4.7 (book pp. 114–127) and the appendix definition Def 191.11.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a verifier that is efficient but reads exponentially long messages;
- a "proof" whose soundness holds only because the verifier's verdict is ill-defined;
- a simulator that is efficient only because the auxiliary input is bounded.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03d's files: earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.15 the frozen ch. 4 signatures (with D8, the interaction reading), §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-114.a, Def-114.b, Def-115.a–d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-117.b, Claim-117.c, Def-119.5, Def-119.e, Def-191.11, Def-121.1, Def-121.2, Def-122.a, Claim-122.b, Def-124.a, Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b–d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the protocols and their proofs (graph isomorphism, 3-colouring: packs 03g and 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/e/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 358 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   25 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 26 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 22 use only the standard axioms, and
   4 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these five files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Strategy`, `View`, `Protocol`, `InteractiveProof`, `ZK`, `PerfectZK`, `PerfectZKAbort` and
  `Commitment`. **Context for the auditor:** ch. 5–8 runs protocols in a new framework, through a
  bridge to these definitions (`Party.exec`, under D8's reading). The ruling of 2026-11-05 carries
  D8's strict or truncated simulators into the sequential composition of ch. 7.

## Specific questions

1. **The interaction model (Defs 114.a–116.b; D8).**
   - Is the fixed-alternation reading of D8 (the next-message function on the complete history is
     the output; a halting party sends `[]`) benign for every use in ch. 4?
   - Is the verdict convention (P9-3: the verifier's last message is its verdict when it moves
     last) a restriction that excludes any protocol of the source?
2. **Efficiency (Def 116.b).**
   - `Strategy.Efficient` is polynomial in the total input length, with `ReadsPrefix` restoring
     the bound in `|x|`. Is that faithful to "time `t(|x|)` regardless of messages"?
   - Is `ReadsPrefix` required wherever the source needs it?
   - **Known consequence (maintainer, 2026-11-05).** `ZK` quantifies over `Strategy.Efficient`
     verifiers without `ReadsPrefix`. Such a verifier may double its messages from activation to
     activation, so over polynomially many rounds, against an honest prover that echoes it, its
     view can grow exponentially, and no strict-PPT simulator can output it. Ch. 5–8's sequential
     composition (Thm 175.1) therefore assumes bounded honest-prover messages
     (`Protocol.ProverBounded`). Does any ch. 2–4 ZK theorem depend on this gap? The honest
     provers of the graph protocols have fixed message lengths. Should `ZK` itself require
     `ReadsPrefix` of `V*`? (Queued for the user as Q-1.)
3. **Interactive proofs (Def 116.1).** Are completeness and soundness stated against every
   (unbounded) prover, with the source's error bounds?
4. **Zero knowledge (Defs 121.1, 121.2, 122.a).**
   - Are `ZK` (every n.u.p.p.t. `V*` with auxiliary input), `PerfectZK` and the statistical form
     faithful?
   - D8 uses strict PPT simulators where the source has expected polynomial time. Is
     `PerfectZKAbort` (truncation with abort) an adequate stand-in for the source's perfect ZK
     protocols?
5. **Commitments (Def 126.3, Thm 126.4, Alg 127.a).** Are hiding and binding at the source's
   strength (computational hiding, perfect binding), and is the OWP-based scheme stated correctly?
6. **NP and Levin reductions (Def 124.a, Def 191.11; `NP.lean`).** Is the NP relation (efficient
   verifier, polynomially bounded witness) and the witness-preserving reduction the one
   Thm 124.1's form (A) needs?

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e/replay.log =====

# closure of pack 03e's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 358 modules, extracted from g03-replay.log
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
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 7s errors=0 sorry=0
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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03e's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.npProtocol_interactiveProof: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.WitnessRelation.mem_NP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_witnessRelation_of_mem_NP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatZK.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatZK.hvzk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.ZK.hvzk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.PerfectZK.zk: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_inv_pow_sqrt_div: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_pairRed_ge: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComStr_binding: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_bitComPredictor: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.HardCore.bitHiding: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.BitHiding.owpComStr_hides: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owpComStr_polyTimeComputable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.owp_commitment: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_commitment_of_owp_hardCore: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_levinReduction: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_owp_levinReduction: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_mem_NP: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.WitnessRelation.mem_IP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NP_subset_IP: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV: propext
TCSlib.Cryptography.Strategy.ReadsPrefix.mono: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.npProtocol_readsPrefix: propext, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e/admissions.txt =====

# declarations with `sorry` in pack 03e's files, at a3c5fa8b72e50939822f22364647dc844a3914a0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/e/lint.log =====

# scripts/style_lint.py on pack 03e's files, at a3c5fa8b72e50939822f22364647dc844a3914a0






0 findings in 5 files

## ===== TCSlib/Cryptography/ZeroKnowledge/Interaction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive protocols: strategies, executions, views

The interaction model of [PS10, §4.4] in the form frozen by the campaign's foundation
decision D8 (`briefs/pass-shelat/DESIGN.md` §2.15). An interactive machine is a *next-message
strategy* `next x z r received`: given the common input `x`, the auxiliary input `z`, the
random tape `r` and the messages received so far, it returns the next message to send; its
value on the complete history is the party's output. A protocol is a pair of strategies with
an explicit polynomial number of messages (`rounds : PolyExpr`) and a first mover. The
execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)` is the fixed alternation of `rounds.eval |x|` moves
(`exec`), and the four derived objects of the text — the view of each party, the transcript,
and the outputs — are projections of it.

**Deviation (D8, recorded once here for the whole chapter):** no tapes, states or idle
transitions are modelled; "entering the idle state" is returning from `next`; the number of
messages is fixed by the protocol (a party that would halt is modelled as sending `[]`), and the
verifier's verdict is `V.next` on the complete history, so it is always defined. The text's
"a round ends when the active machine halts — in which case the protocol ends" makes the
literal `Pr[out_V = 0]` of [PS10, Definition 116.1] unsatisfiable against a prover that halts
at once; the fixed-alternation reading is the one under which that clause is satisfiable.
Verdict convention (run-3 audit P9-3): when the verifier is the last mover, the verdict
activation has exactly the arguments of the activation that produced its last message, so its
last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chapter's protocols
are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
message as the verdict.
`Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
whole random tape; the time is polynomial in the total input length rather than in `|x|`
alone (the text's `t(|x|)` "regardless of messages" would leave the simulator's call to `V*`
on long auxiliary inputs ill-defined; see D8). Consequently `Efficient` alone does not bound a
party's work in `|x|` against a counterparty that sends long messages; the message-prefix cap
`Strategy.ReadsPrefix m` — the strategy depends only on the first `m(|x|)` bits of each received
message, as a time-`t(|x|)` machine of the text necessarily does — restores the text's bound,
and the class `IP` (`InteractiveProofs.lean`) requires it of the verifier (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.Strategy` — a next-message strategy with an explicit coin polynomial
  [PS10, §4.4] (Def-114.a); `Strategy.ofNUPPT`, `Strategy.Efficient` (Def-116.b, the machine
  half), `Strategy.ReadsPrefix` (Def-116.b, the message-prefix cap of the text's bound in `|x|`).
* `TCSlib.Cryptography.exec` — the messages received by each party after `k` moves
  [PS10, §4.4] (Def-115.a).
* `TCSlib.Cryptography.View`, `TCSlib.Cryptography.View.encode` — a party's view
  `(x, z, r, received)` and its string encoding (Def-115.b).
* `TCSlib.Cryptography.Protocol` — two strategies, the number of messages and the first mover
  (Def-114.b); `Protocol.transcriptWith`, `Protocol.transcript` (Def-115.c), `Protocol.outV`,
  `Protocol.outP`, `Strategy.out` (Def-115.d), `Protocol.viewV`, `Protocol.viewP`,
  `Protocol.execution` (Def-115.a/b), `Protocol.withV`.

## Main results

* `TCSlib.Cryptography.exec_length` — after `k` moves exactly `k` messages have been sent.
* `TCSlib.Cryptography.Strategy.ofNUPPT_efficient` — every uniform machine is an efficient
  strategy (non-vacuity of Def-116.b).
* `TCSlib.Cryptography.Strategy.ReadsPrefix.mono`,
  `TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr` — the message-prefix cap is monotone
  in the cap and makes the next message a function of the truncated history.
* `TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV` — when the verifier is the last
  mover, its last message is its verdict (the verdict convention of D8).
* `TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp`,
  `TCSlib.Cryptography.Protocol.exists_proverCoins_le` — random executions are samplers on the
  product of the two coin spaces (Def-116.a), and a prover's coins may be fixed without
  decreasing any event's probability (the "without loss of generality deterministic `P*`"
  remark of the soundness clause).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.4 Interactive protocols, pp. 114–116.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, interactive proofs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Strategies -/

/-- A next-message strategy [PS10, §4.4] (Def-114.a): `next x z r received` is the message a
party sends on common input `x`, auxiliary input `z` and random tape `r` after having
*received* the listed messages; on the complete history its value is the party's output. The
random tape has the explicit polynomial length `coins.eval |x|`.

**Deviation (D8):** no tapes, states or idle transitions; the output function of the text is
the next-message function on the complete history. -/
structure Strategy where
  /-- The next-message function `(x, z, r, received) ↦ message`. -/
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool
  /-- The length of the random tape as a polynomial in `|x|`. -/
  coins : PolyExpr

namespace Strategy

/-- The number of random bits of a strategy at common-input length `n`. -/
def coinLen (S : Strategy) (n : ℕ) : ℕ := S.coins.eval n

/-- The random tape of a strategy at common-input length `n`: `coinLen n` uniform bits. -/
abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool

/-- The string encoding of a list of messages: right-nested `pairEncode` pairs ending in `[]`
(the encoding of the received-messages component of a view, Inf-4.1). -/
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- The encoding of the empty history is the empty string. -/
@[simp] theorem encodeMsgs_nil : encodeMsgs [] = [] := rfl

/-- The encoding of `m :: h` is the pair `⟨m, encodeMsgs h⟩`. -/
@[simp] theorem encodeMsgs_cons (m : List Bool) (h : List (List Bool)) :
    encodeMsgs (m :: h) = pairEncode m (encodeMsgs h) := rfl

/-- The first projection of an encoded history is its first message (`[]` when empty). -/
theorem pairFstD_encodeMsgs (h : List (List Bool)) : pairFstD (encodeMsgs h) = h.headD [] := by
  cases h with
  | nil => rfl
  | cons m h => simp

/-- The strategy computed by a machine `A`: one activation at parameter `|x|` on
`⟨⟨x, z⟩, messages⟩` with the whole random tape (`A.runAtL`); the coin polynomial is `A.coins`
[PS10, §4.4, the interactive machine as a Turing machine with a random tape]. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r
  coins := A.coins

/-- The next-message function of `ofNUPPT A` unfolds to one activation of `A`. -/
theorem ofNUPPT_next (A : NUPPT) (x z r : List Bool) (hist : List (List Bool)) :
    (ofNUPPT A).next x z r hist =
      A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r := rfl

/-- A PPT strategy [PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the
next-message function is computed by a uniform `NUPPT` with the same coin polynomial, one
activation per message at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.

**Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
|messages|` instead of the text's `t(|x|)` "regardless of the messages". The number of
activations is bounded by the protocol's `rounds`, but the messages of an unbounded
counterparty may be arbitrarily long, so `Efficient` alone does not bound a party's work in
`|x|` (run-3 audit P9-1). The text's bound is recovered by adding the message-prefix cap
`ReadsPrefix m`: an efficient strategy that reads only `m(|x|)` bits of each message runs in
time polynomial in `|x| + |z|`, and the class `IP` requires the cap of the verifier. -/
def Efficient (S : Strategy) : Prop :=
  ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
    ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist

/-- Non-vacuity of `Strategy.Efficient`: the strategy of a uniform machine is efficient. -/
theorem ofNUPPT_efficient (A : NUPPT) (hA : A.Uniform) : (ofNUPPT A).Efficient :=
  ⟨A, hA, rfl, fun _ _ _ _ => rfl⟩

/-- An efficient strategy has the coin polynomial of some uniform machine computing it. -/
theorem Efficient.exists_uniform {S : Strategy} (h : S.Efficient) :
    ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins := by
  obtain ⟨A, hA, hc, -⟩ := h
  exact ⟨A, hA, hc⟩

/-- A strategy reads at most an `m(|x|)`-bit prefix of each received message [PS10, §4.4, time
complexity: an interactive machine of time complexity `t(|x|)` reads at most `t(|x|)` cells of
its communication tape per activation, "independently of the content of the messages it
receives"] (Def-116.b, the message half of the text's bound in `|x|`): the next-message
function is unchanged when every received message is truncated to its first `m.eval |x|` bits.
Together with `Efficient` this is the text's PPT interactive machine — the activation is
computed in time polynomial in `|x| + |z| + rounds · m(|x|)` by truncating the messages first —
whereas `Efficient` alone is polynomial in the total message length (D8).

**Repair (run-3 audit P9-1):** added; the class `IP` requires it of the verifier. -/
def ReadsPrefix (S : Strategy) (m : PolyExpr) : Prop :=
  ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval x.length)))

/-- Under a message-prefix cap the next message depends only on the truncated history. -/
theorem ReadsPrefix.next_congr {S : Strategy} {m : PolyExpr} (h : S.ReadsPrefix m)
    {x z r : List Bool} {hist hist' : List (List Bool)}
    (he : hist.map (List.take (m.eval x.length)) = hist'.map (List.take (m.eval x.length))) :
    S.next x z r hist = S.next x z r hist' := by
  rw [h x z r hist, h x z r hist', he]

/-- The message-prefix cap is monotone: a cap `m` implies every pointwise larger cap `m'`
(`List.take_take`: truncating to `m'(|x|)` and then to `m(|x|) ≤ m'(|x|)` bits is truncating to
`m(|x|)` bits). -/
theorem ReadsPrefix.mono {S : Strategy} {m m' : PolyExpr} (h : S.ReadsPrefix m)
    (hle : ∀ n, m.eval n ≤ m'.eval n) : S.ReadsPrefix m' := by
  intro x z r hist
  refine h.next_congr ?_
  rw [List.map_map]
  refine List.map_congr_left fun msg _ => ?_
  simp only [Function.comp_apply, List.take_take, min_eq_left (hle _)]

end Strategy

/-! ### Executions -/

/-- Which party moves at move `k` (0-indexed): the verifier moves at the even positions when
it moves first, at the odd ones otherwise. -/
def moverIsV (vFirst : Bool) (k : ℕ) : Bool :=
  if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)

/-- With the verifier first, it moves at the even positions. -/
@[simp] theorem moverIsV_true (k : ℕ) : moverIsV true k = decide (k % 2 = 0) := rfl

/-- With the prover first, the verifier moves at the odd positions. -/
@[simp] theorem moverIsV_false (k : ℕ) : moverIsV false k = decide (k % 2 = 1) := rfl

/-- The messages received by `P` and by `V` after `k` moves of the execution
`P_{rP}(x, zP) ↔ V_{rV}(x, zV)` [PS10, §4.4, the execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)`]
(Def-115.a): at move `k` the active party applies its next-message function to the messages
it has received so far and the message is appended to the other party's received list. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := exec P V vFirst x zP zV rP rV k
    if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
    else (e.1, e.2 ++ [P.next x zP rP e.1])

/-- Before the first move nothing has been received. -/
@[simp] theorem exec_zero (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    exec P V vFirst x zP zV rP rV 0 = ([], []) := rfl

/-- One more move: the active party's message is appended to the other party's list. -/
theorem exec_succ (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV (k + 1) =
      (let e := exec P V vFirst x zP zV rP rV k
       if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
       else (e.1, e.2 ++ [P.next x zP rP e.1])) := rfl

/-- After `k` moves exactly `k` messages have been sent in total. -/
theorem exec_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    (exec P V vFirst x zP zV rP rV k).1.length + (exec P V vFirst x zP zV rP rV k).2.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ]
    split_ifs <;> simp only [List.length_append, List.length_singleton] <;> omega

/-! ### Views -/

/-- A party's view [PS10, §4.4] (Def-115.b): the common input, its auxiliary input, its random
tape and the messages it received. -/
structure View where
  /-- The common input. -/
  x : List Bool
  /-- The party's auxiliary input. -/
  z : List Bool
  /-- The party's random tape. -/
  r : List Bool
  /-- The messages the party received, in order. -/
  received : List (List Bool)

/-- The string encoding of a view, `⟨⟨x, z⟩, ⟨r, messages⟩⟩` (the sample handed to
distinguishers and produced by simulators in the zero-knowledge definitions). -/
def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))

/-- The output of a party on a view [PS10, §4.4, `out(v)`] (Def-115.d): its next-message
function on the complete history. -/
def Strategy.out (S : Strategy) (v : View) : List Bool := S.next v.x v.z v.r v.received

/-! ### Protocols -/

/-- A protocol [PS10, §4.4] (Def-114.b): a prover strategy, a verifier strategy, the number of
messages exchanged (an explicit polynomial in `|x|`) and the first mover (`true` = verifier
first, as in the graph non-isomorphism protocol; `false` = prover first, as in the graph
isomorphism and 3-colouring protocols). The verifier's verdict is its next-message function
on the complete history.

**Deviation (D8):** fixed number of messages `rounds.eval |x|`; a halting party sends `[]`.
If the verifier is the last mover (prover first with an even number of messages, or verifier
first with an odd number), its last message coincides with its verdict — both are `V.next` on
the same history (`outV_eq_getLast_of_moverIsV`) — so a verifier whose final message differs
from its verdict is not expressible; protocols are therefore stated so that the prover moves
last, or the verifier's last message is read as the verdict (the `n`-fold protocols)
(run-3 audit P9-3). -/
structure Protocol where
  /-- The prover's strategy. -/
  P : Strategy
  /-- The verifier's strategy. -/
  V : Strategy
  /-- The number of messages exchanged, as a polynomial in `|x|`. -/
  rounds : PolyExpr
  /-- Whether the verifier sends the first message. -/
  verifierFirst : Bool

namespace Protocol

/-- The joint coin space of an execution of `π` with the prover strategy `P'` on `x`: the
prover's and the verifier's random tapes at parameter `|x|` [PS10, §4.4, random executions]
(Def-116.a). -/
abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  P'.Coins x.length × π.V.Coins x.length

/-- The protocol with the verifier replaced by `V'` (the cheating verifier `V*` of the
zero-knowledge definitions), same prover, round count and first mover. -/
def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }

/-- The verifier of `π.withV V'` is `V'`. -/
@[simp] theorem withV_V (π : Protocol) (V' : Strategy) : (π.withV V').V = V' := rfl

/-- The prover of `π.withV V'` is the prover of `π`. -/
@[simp] theorem withV_P (π : Protocol) (V' : Strategy) : (π.withV V').P = π.P := rfl

/-- The round count of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_rounds (π : Protocol) (V' : Strategy) : (π.withV V').rounds = π.rounds := rfl

/-- The first mover of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_verifierFirst (π : Protocol) (V' : Strategy) :
    (π.withV V').verifierFirst = π.verifierFirst := rfl

/-- Replacing the verifier by itself changes nothing. -/
@[simp] theorem withV_self (π : Protocol) : π.withV π.V = π := by
  cases π
  rfl

/-- The transcript (messages received by `P'`, messages received by `V`) of the execution
`P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` with all `rounds.eval |x|` moves [PS10, §4.4] (Def-115.c). -/
def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)

/-- The transcript of the honest execution `P(x, y) ↔ V(x, z)` (Def-115.c). -/
def transcript (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    List (List Bool) × List (List Bool) :=
  π.transcriptWith π.P x y z r

/-- The verifier's output in `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `out_V`] (Def-115.d):
`V.next` on the complete history.

**Deviation (D8, run-3 audit P9-3):** when the verifier is the last mover this is also the
last message it sent (`outV_eq_getLast_of_moverIsV`); see `Protocol`. -/
def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
  π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2

/-- The honest prover's output in `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` (Def-115.d). -/
def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
  π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1

/-- The honest verifier's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_V`]
(Def-115.b). -/
def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩

/-- The honest prover's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_P`]
(Def-115.b). -/
def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩

/-- The execution `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` as the pair of views (the joint view)
[PS10, §4.4] (Def-115.a). -/
def execution (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View × View :=
  (π.viewP x y z r, π.viewV x y z r)

/-- The verifier's output is its output function on its view (Def-115.d). -/
theorem outV_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outV π.P x y z r = π.V.out (π.viewV x y z r) := rfl

/-- The prover's output is its output function on its view (Def-115.d). -/
theorem outP_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outP x y z r = π.P.out (π.viewP x y z r) := rfl

/-- The transcript is the pair of received-message components of the two views. -/
theorem transcript_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.transcript x y z r = ((π.viewP x y z r).received, (π.viewV x y z r).received) := rfl

/-- The verifier's output against `P'` only depends on `P'` through the transcript. -/
theorem outV_withV (π : Protocol) (V' P' : Strategy) (x y z : List Bool)
    (r : (π.withV V').ExecCoins P' x) :
    (π.withV V').outV P' x y z r =
      V'.next x z (List.ofFn r.2)
        (exec P' V' π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
          (π.rounds.eval x.length)).2 := rfl

/-- The verdict convention of D8 made explicit (run-3 audit P9-3): if the verifier makes the
last of the `k + 1` moves (`moverIsV verifierFirst k`), the last message it sent — the last
message `P'` received — is its verdict, because both are `V.next` on the messages `V` received
in the first `k` moves (`exec_succ`, `List.getLast?_concat`). -/
theorem outV_eq_getLast_of_moverIsV (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) {k : ℕ} (hk : π.rounds.eval x.length = k + 1)
    (hV : moverIsV π.verifierFirst k = true) :
    (π.transcriptWith P' x y z r).1.getLast? = some (π.outV P' x y z r) := by
  unfold outV transcriptWith
  rw [hk, exec_succ]
  simp [hV]

/-! ### Random executions -/

/-- A random execution is a sampler on the product of the two coin spaces [PS10, §4.4]
(Def-116.a): the probability of any event of the verifier's output is the average over the
prover's coins of its conditional probability over the verifier's coins (`uprob_prod`). -/
theorem uprob_outV_eq_uexp (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) =
      uexp (fun r₁ : P'.Coins x.length =>
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))) :=
  uprob_prod _

/-- A cheating prover may be taken deterministic: for every event of the verifier's output
there is a fixed prover random tape under which the event is at least as likely as on average
(the "without loss of generality `P*` is deterministic" remark behind the soundness clause of
[PS10, Definition 116.1]). -/
theorem exists_proverCoins_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    ∃ r₁ : P'.Coins x.length,
      uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) ≤
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂))) := by
  rw [uprob_outV_eq_uexp]
  set f : P'.Coins x.length → ℝ :=
    fun r₁ => uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))
  have hcard : (0 : ℝ) < Fintype.card (P'.Coins x.length) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : P'.Coins x.length, uexp f ≤ ∑ a, f a := by
    rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
  obtain ⟨a, -, ha⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨a, ha⟩

end Protocol

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive proof systems

The definitions of [PS10, §4.5] on top of the interaction model of `Interaction.lean`
(foundation decision D8): interactive proofs with negligible soundness error
[PS10, Definition 116.1], proofs with a stated soundness error `s(|x|)` [PS10, §4.5,
constant-error proofs], witness relations [PS10, Appendix B, Definition 191.11], and
interactive proofs with an efficient prover [PS10, Definition 119.5]. The sanity theorem
`npProtocol_interactiveProof` shows the definitions are satisfiable: the one-message protocol
in which the prover sends a witness (read by the verifier up to the relation's witness-length
bound) is an interactive proof with efficient prover for every polynomially decidable witness
relation, and `WitnessRelation.mem_IP`, `NP_subset_IP` place such languages in the class `IP`
([PS10, §4.5, the remark `NP ⊆ IP`]).

**Deviation (D8):** soundness is the literal `1 - ε(|x|) < Pr[out_V = 0]` with `out_V = 0`
read as the output string `[false]`, the negligible `ε` quantified before the instance, the
cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
every pair of random tapes. The verifier's efficiency is `Strategy.Efficient`, polynomial time
in `|x| + |z| + |messages|` (D8), so `InteractiveProof` alone does not bound the verifier's
work in `|x|` against an unbounded prover sending long messages; the class `IP` adds the
message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.InteractiveProof` — interactive proof system [PS10, Definition 116.1]
  (Def-116.1); `TCSlib.Cryptography.InteractiveProofErr` — with soundness error `s` (Def-117.a);
  `TCSlib.Cryptography.IP` — the class of languages with an interactive proof whose verifier
  reads a polynomial prefix of each message (Def-117.b).
* `TCSlib.Cryptography.WitnessRelation` — a witness relation for a language
  [PS10, Definition 191.11] (Def-191.11); `TCSlib.Cryptography.witnessLanguage`,
  `TCSlib.Cryptography.witnessSet` — the language `{x | ∃ y, R x y}` and the set `R_L(x)`.
* `TCSlib.Cryptography.EfficientProverProof`,
  `TCSlib.Cryptography.EfficientProverProofErr` — interactive proofs with efficient prover
  [PS10, Definition 119.5] (Def-119.5).
* `TCSlib.Cryptography.npProtocol` — the one-message protocol in which the prover sends a
  witness, read by the verifier up to a polynomial length bound.

## Main results

* `TCSlib.Cryptography.InteractiveProofErr.interactiveProof`,
  `TCSlib.Cryptography.InteractiveProof.exists_err` — a negligible soundness error gives an
  interactive proof and conversely.
* `TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt` — the acceptance form of
  soundness, `Pr[out_V = [true]] < ε(|x|)`.
* `TCSlib.Cryptography.WitnessRelation.mem_NP`,
  `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` — witness relations characterize
  `Complexity.NP` (the bridge to the certificate definition of `ClassNP/NP.lean`).
* `TCSlib.Cryptography.npProtocol_interactiveProof` — non-vacuity: sending a witness is an
  interactive proof with efficient prover; `TCSlib.Cryptography.npProtocol_readsPrefix`,
  `TCSlib.Cryptography.WitnessRelation.mem_IP`, `TCSlib.Cryptography.NP_subset_IP` — its
  verifier reads a polynomial prefix, hence `NP ⊆ IP` (Claim-117.c).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 116–120; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.1, NP via certificates; Chapter 8.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Interactive proofs -/

/-- An interactive proof system for `L` [PS10, Definition 116.1] (Def-116.1): the verifier is
efficient; completeness — for every `x ∈ L` there is an auxiliary input `y` such that for every
`z` the honest execution `P(x, y) ↔ V(x, z)` makes `V` output `1` with probability one;
soundness — there is a negligible `ε` such that for every `x ∉ L`, every (unbounded) prover
strategy `P'` and every `z`, `V` outputs `0` in `P'(x) ↔ V(x, z)` with probability greater than
`1 - ε(|x|)`.

**Deviation (D8):** `out_V = 0` is the literal output string `[false]` on the complete
history of the fixed-alternation execution; `P'` ranges over strategies with polynomial
random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is `uprob = 1`
(every pair of random tapes). The verifier is `Strategy.Efficient`, i.e. polynomial-time in
`|x| + |z| + |messages|` (D8), so this predicate alone does not bound the verifier's work in
`|x|` against an unbounded prover sending long messages; the class `IP` adds the
message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  /-- The verifier is a PPT strategy. -/
  efficientV : π.V.Efficient
  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness: against every prover strategy the verifier rejects with probability
  `> 1 - ε(|x|)` for a negligible `ε`. -/
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- An interactive proof system with soundness error `s` [PS10, §4.5, after Definition 116.1]
(Def-117.a): as `InteractiveProof` with `1 - s(|x|) ≤ Pr[out_V = [false]]` for the given
function `s` (for instance the constant `1/2` of the single-iteration graph-isomorphism
protocol).

**Deviation (D8):** as for `InteractiveProof` (literal `[false]`, provers with polynomial
tapes, `uprob = 1` completeness; verifier time in the total input length — the message-prefix
cap is added in `IP`, run-3 audit P9-1). -/
structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
  /-- The verifier is a PPT strategy. -/
  efficientV : π.V.Efficient
  /-- Completeness: some auxiliary input makes the honest verifier accept with probability one. -/
  complete : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness error `s`: the verifier rejects with probability at least `1 - s(|x|)`. -/
  sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- The class `IP` of languages with an interactive proof system [PS10, §4.5] (Def-117.b):
`L ∈ IP` iff some protocol `π` is an interactive proof for `L` whose verifier reads only a
polynomial prefix `m(|x|)` of each received message (`Strategy.ReadsPrefix`), as a verifier of
time complexity `t(|x|)` in the sense of the text necessarily does.

**Repair (run-3 audit P9-1):** the run-2 definition `∃ π, InteractiveProof π L` contained every
language `{x | ∃ y, T ⟨x, y⟩ = true}` with `T` polynomial-time on the pair and no bound on
`|y|` (all of RE, by computation-history checkers): under D8 the verifier's time is polynomial
in the total input including the messages, so an unbounded prover could hand it an arbitrarily
long certificate. With the cap the verifier's work is polynomial in `|x| + |z|`, as in the
text; `WitnessRelation.mem_IP` recovers `NP ⊆ IP`. -/
def IP : Set (Language Bool) :=
  {L | ∃ (π : Protocol) (m : PolyExpr), π.V.ReadsPrefix m ∧ InteractiveProof π L}

/-- A negligible soundness error gives an interactive proof: the strict clause holds with the
negligible function `ε n := s n + 2⁻¹ ^ n`. -/
theorem InteractiveProofErr.interactiveProof {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (hs : Negligible s) (h : InteractiveProofErr π L s) : InteractiveProof π L where
  efficientV := h.efficientV
  complete := h.complete
  sound := by
    refine ⟨fun n => s n + (2 : ℝ)⁻¹ ^ n, hs.add negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
    linarith [h.sound x hx P' z]

/-- An interactive proof has a negligible soundness error. -/
theorem InteractiveProof.exists_err {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧ InteractiveProofErr π L ε := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  exact ⟨ε, hε, h.efficientV, h.complete, fun x hx P' z => (hsound x hx P' z).le⟩

/-- Soundness in the acceptance form: for `x ∉ L` the verifier accepts (outputs `[true]`) with
probability less than `ε(|x|)` (the form the inventory records as equivalent; the event
`out_V = [true]` is contained in `out_V ≠ [false]`). -/
theorem InteractiveProof.exists_uprob_accept_lt {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
        uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) < ε x.length := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  refine ⟨ε, hε, fun x hx P' z => ?_⟩
  have h1 := hsound x hx P' z
  have h2 : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
    uprob_mono fun r hr => by simp [hr]
  rw [uprob_not] at h2
  linarith

/-! ### Witness relations -/

/-- A witness relation for `L` [PS10, Appendix B, Definition 191.11] (Def-191.11): `x ∈ L` iff
some `y` satisfies `R x y`; witnesses have polynomially bounded length; and the relation is
decidable in polynomial time on the pair `⟨x, y⟩`.

**Deviation:** the text's `R_L(x) = {y : (x, y) ∈ L}` is a typo for `∈ R_L`; the witness-length
bound is an explicit `PolyExpr` and the decider a polynomial-time string function
(`PolyTimeComputable`). -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  /-- `x ∈ L` iff `x` has a witness. -/
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  /-- Witnesses have length bounded by a polynomial in `|x|`. -/
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  /-- The relation is decidable in polynomial time on `⟨x, y⟩`. -/
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- The language of a relation, `{x | ∃ y, R x y}` [PS10, Definition 191.11]. -/
def witnessLanguage (R : List Bool → List Bool → Prop) : Language Bool := {x | ∃ y, R x y}

/-- The witness set `R_L(x) = {y | R x y}` [PS10, Definition 191.11]. -/
def witnessSet (R : List Bool → List Bool → Prop) (x : List Bool) : Set (List Bool) := {y | R x y}

/-- Membership in `witnessLanguage R` unfolds to the existence of a witness. -/
@[simp] theorem mem_witnessLanguage (R : List Bool → List Bool → Prop) (x : List Bool) :
    x ∈ witnessLanguage R ↔ ∃ y, R x y := Iff.rfl

/-- Membership in `witnessSet R x` unfolds to `R x y`. -/
@[simp] theorem mem_witnessSet (R : List Bool → List Bool → Prop) (x y : List Bool) :
    y ∈ witnessSet R x ↔ R x y := Iff.rfl

/-- A witness relation for `L` determines `L` as `witnessLanguage R`. -/
theorem WitnessRelation.eq_witnessLanguage {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L = witnessLanguage R :=
  Set.ext fun x => h.mem_iff x

/-- A language with a witness relation is in `NP` [PS10, Definition 191.11, the "iff" with
[AB09, Definition 2.1]].

**Proof sketch.** Use `Complexity.mem_NP_iff_exists_length_le` (the `pairEncode x u ∈ V`,
`|u| ≤ C(|x|+1)^c` form). From `h.bounded` take `p` and `C, c` with `p.eval n ≤ C(n+1)^c`
(`PolyExpr.eval_le`). From `h.decidable` take `T`; the verifier language is
`V := {z | T z = true}`, in `P` by `Complexity.mem_P_iff_polyTimeComputable` since
`[MultiTapeTM.indicator V z] = [T z]` (`funext`, `Bool.decide_eq_true`). The equivalence
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V` is `h.mem_iff`, the length bound and
the decider's specification. -/
theorem WitnessRelation.mem_NP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ NP := by
  rw [mem_NP_iff_exists_length_le]
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨C, c, hCc⟩ := p.eval_le
  obtain ⟨T, hT, hTR⟩ := h.decidable
  refine ⟨C, c, {z | T z = true}, mem_P_of_test hT, fun x => ?_⟩
  rw [h.mem_iff x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (hp x y hy).trans (hCc _), (hTR x y).2 hy⟩
  · rintro ⟨u, -, hu⟩
    exact ⟨u, (hTR x u).1 hu⟩

/-- Every `NP` language has a witness relation [PS10, Definition 191.11, converse direction].

**Proof sketch.** From `Complexity.mem_NP_iff_exists_length_le` take `C, c, V`; set
`R x y := y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V`. `mem_iff` is the
characterization; `bounded` is `PolyExpr.normal C c` (`PolyExpr.eval_normal`); `decidable`:
`T z := decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) && indicator V z`,
polynomial-time by `Complexity.polyTimeComputable_and`, `polyTimeComputable_lenLe` composed
with `pairEncode (unaryPoly (normal C c) ∘ pairFstD) pairSndD`, and
`mem_P_iff_polyTimeComputable`; on `pairEncode x y` the projections are `x` and `y`
(`pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem exists_witnessRelation_of_mem_NP {L : Language Bool} (h : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R := by
  obtain ⟨C, c, V, hV, hL⟩ := mem_NP_iff_exists_length_le.1 h
  refine ⟨fun x y => y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V, hL, ?_, ?_⟩
  · exact ⟨PolyExpr.normal C c, fun x y hy => by rw [PolyExpr.eval_normal]; exact hy.1⟩
  · refine ⟨fun z => decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) &&
      MultiTapeTM.indicator V z, ?_, ?_⟩
    · refine polyTimeComputable_and ?_ (test_of_mem_P hV)
      have hlen := polyTimeComputable_lenLe.comp
        (((polyTimeComputable_unaryPoly (PolyExpr.normal C c)).comp
          polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)
      convert hlen using 1
      funext z
      simp [PolyExpr.eval_normal]
    · intro x y
      simp [MultiTapeTM.indicator]

/-! ### Efficient provers -/

/-- An interactive proof for `L` with efficient prover with respect to the witness relation
`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is a PPT strategy
(the witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
(Definition 116.1 only asks for some auxiliary input). -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  /-- The prover is a PPT strategy. -/
  efficientP : π.P.Efficient
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- An interactive proof with soundness error `s` and efficient prover with respect to `R`
[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a). -/
structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
  /-- The prover is a PPT strategy. -/
  efficientP : π.P.Efficient
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- A negligible soundness error gives an interactive proof with efficient prover. -/
theorem EfficientProverProofErr.efficientProverProof {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {s : ℕ → ℝ} (hs : Negligible s)
    (h : EfficientProverProofErr π L R s) : EfficientProverProof π L R where
  toInteractiveProof := h.toInteractiveProofErr.interactiveProof hs
  efficientP := h.efficientP
  completeWitness := h.completeWitness

/-- An interactive proof with efficient prover has a negligible soundness error. -/
theorem EfficientProverProof.exists_err {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} (h : EfficientProverProof π L R) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ EfficientProverProofErr π L R ε := by
  obtain ⟨ε, hε, herr⟩ := h.toInteractiveProof.exists_err
  exact ⟨ε, hε, herr, h.efficientP, h.completeWitness⟩

/-! ### The trivial NP protocol -/

/-- The one-message protocol in which the prover sends its auxiliary input `y` and the
verifier accepts iff `T ⟨x, y'⟩`, where `y'` is the received message truncated to its first
`p(|x|)` bits [PS10, §4.5, "`NP ⊆ IP`": the certificate is sent in one round, and a
polynomial-time verifier reads at most polynomially many bits of it]: prover first, one
message, no coins.

**Repair (run-3 audit P9-1):** the witness-length bound `p : PolyExpr` is a parameter and the
verifier reads only the first `p(|x|)` bits of the message (`npProtocol_readsPrefix`), so that
the protocol witnesses `L ∈ IP` under the repaired class; the run-2 verifier read the whole
message. -/
def npProtocol (T : List Bool → Bool) (p : PolyExpr) : Protocol where
  P := ⟨fun _ y _ _ => y, .const 0⟩
  V := ⟨fun x _ _ hist => [T (pairEncode x ((hist.headD []).take (p.eval x.length)))], .const 0⟩
  rounds := .const 1
  verifierFirst := false

/-- In `npProtocol T p` the verifier's output against any prover `P'` is the verdict `T` on
`⟨x, m'⟩`, where `m'` is the first `p(|x|)` bits of the single message `P'` sends on the empty
history. -/
theorem npProtocol_outV (T : List Bool → Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (npProtocol T p).ExecCoins P' x) :
    (npProtocol T p).outV P' x y z r =
      [T (pairEncode x ((P'.next x y (List.ofFn r.1) []).take (p.eval x.length)))] := by
  simp [Protocol.outV, Protocol.transcriptWith, npProtocol, exec, moverIsV]

/-- The verifier of `npProtocol T p` reads only the first `p(|x|)` bits of the message
(`List.take_take`). -/
theorem npProtocol_readsPrefix (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).V.ReadsPrefix p := by
  intro x z r hist
  cases hist with
  | nil => rfl
  | cons m hist => simp [npProtocol, List.take_take]

/-- The verifier of `npProtocol T p` is efficient when `T` is polynomial-time: one activation of
the uniform machine computing `w ↦ [T ⟨x, m.take (p(|x|))⟩]` from the projections of the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩`.

**Proof sketch.** `x` and the first message `m` are fixed `pairFstD`/`pairSndD` projection
chains of the raw input `w` (`PolyTimeComputable.comp`); the truncation `m.take (p(|x|))` is
`Complexity.polyTimeComputable_pairTakePoly p` applied to `⟨x, m⟩`
(`PolyTimeComputable.pairEncode`), and `T` is applied to `⟨x, m.take (p(|x|))⟩` (`hT.comp`).
The uniform machine `NUPPT.ofPolyTimeUniform` of this function has the required next-message
function on every history (`NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`). -/
theorem npProtocol_efficientV (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z]) : (npProtocol T p).V.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp harg)
  have hm : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp harg)
  have htake : PolyTimeComputable fun w =>
      (pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
        (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length) := by
    convert (polyTimeComputable_pairTakePoly p).comp (hx.pairEncode hm) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF : PolyTimeComputable fun w =>
      [T (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))))
        ((pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
          (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length)))] :=
    hT.comp (hx.pairEncode htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput,
    Strategy.pairFstD_encodeMsgs]

/-- The prover of `npProtocol T p` is efficient: it copies the auxiliary input, the projection
`pairSndD ∘ pairFstD` of the argument of the layout. -/
theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).P.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hF : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp harg)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput]

/-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
`R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
`p(|x|)`, the one-message protocol in which the prover sends a witness is an interactive proof
for `L` with efficient prover with respect to `R` (the verifier rejects every `x ∉ L` with
probability one).

**Repair (run-3 audit P9-1):** the witness-length bound `p` with `hp` added (the verifier of
`npProtocol T p` reads only `p(|x|)` bits).

**Proof sketch.** The verifier's output is `[T ⟨x, m.take (p(|x|))⟩]` for the message `m` sent
(`npProtocol_outV`); the honest prover sends `y`, which the truncation leaves unchanged since
`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness: for `x ∈ L` take a witness `y`
(`hR.mem_iff`); then `T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
(`HardcoreBit.uprob_eq_one_of_forall`). Soundness with `ε n := 2⁻¹ ^ n`
(`negligible_two_pow_neg`; the literal clause is strict, so `ε = 0` is not admissible): for
`x ∉ L` no string — in particular no truncated message — is a witness, so `T ⟨x, ·⟩ = false`
and the verifier outputs `[false]` on every coin pair, with probability `1 > 1 - ε(|x|)`.
Efficiency of both parties: `npProtocol_efficientV`, `npProtocol_efficientP`. -/
theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List Bool → Prop}
    (hR : WitnessRelation L R) (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z])
    (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y)
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    EfficientProverProof (npProtocol T p) L R where
  efficientV := npProtocol_efficientV T p hT
  complete := by
    intro x hx
    obtain ⟨y, hy⟩ := (hR.mem_iff x).1 hx
    refine ⟨y, fun z => HardcoreBit.uprob_eq_one_of_forall fun r => ?_⟩
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
  sound := by
    refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
        (npProtocol T p).outV P' x [] z r = [false] := by
      intro r
      rw [npProtocol_outV]
      have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
        fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
      have hfalse :
          T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
        rw [← Bool.not_eq_true, hTR]
        exact hno
      rw [hfalse]
    rw [HardcoreBit.uprob_eq_one_of_forall hall]
    exact sub_lt_self _ (by positivity)
  efficientP := npProtocol_efficientP T p
  completeWitness := by
    intro x y hy z
    refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]

/-- Every language with a witness relation is in `IP` [PS10, §4.5, "`NP ⊆ IP`"] (Claim-117.c):
the one-message protocol `npProtocol T p`, with the relation's decider `T` and witness-length
bound `p`, is an interactive proof whose verifier reads only `p(|x|)` bits of the message
(`npProtocol_readsPrefix`, `npProtocol_interactiveProof`). -/
theorem WitnessRelation.mem_IP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ IP := by
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨T, hT, hTR⟩ := h.decidable
  exact ⟨npProtocol T p, p, npProtocol_readsPrefix T p,
    (npProtocol_interactiveProof h T p hT hTR hp).toInteractiveProof⟩

/-- `NP ⊆ IP` [PS10, §4.5] (Claim-117.c): every `NP` language has a witness relation
(`exists_witnessRelation_of_mem_NP`), hence an interactive proof with a prefix-reading
verifier (`WitnessRelation.mem_IP`). -/
theorem NP_subset_IP : NP ⊆ IP := fun _ h =>
  (Classical.choose_spec (exists_witnessRelation_of_mem_NP h)).mem_IP

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge: honest-verifier, general, statistical and perfect

The zero-knowledge notions of [PS10, §4.6] on top of the interaction model of
`Interaction.lean` (foundation decision D8): honest-verifier zero-knowledge
[PS10, Definition 121.1], zero-knowledge against every efficient verifier
[PS10, Definition 121.2], and the perfect and statistical variants (Def-122.a) through the
sup-over-test-sets closeness `StatClose` of `Asymptotic/Sampling.lean`, together with the
implications statistical ⇒ computational (`StatZK.zk`, `StatZK.hvzk`), general ⇒ honest-verifier
(`ZK.hvzk`), and the negligibility bookkeeping converting the chapter's per-vertex bounds
`2^{-n}`, `e^{-n}` into functions of the instance length `|x|` (Inf-4.4).

The simulator is a uniform `Complexity.NUPPT` run once at parameter `|x|` on `⟨x, z⟩`
(`Complexity.NUPPT.simulate`); its output is a word read as an encoded view
(`View.encode`: `⟨⟨x, z⟩, ⟨r, messages⟩⟩`), and the distinguisher is a non-uniform PPT run at
parameter `|x|` on the encoded view (`Complexity.NUPPT.distinguisherL`).

**Deviation (D8):** strict PPT simulators (the text's expected polynomial time is not
formalized; the rewinding simulators of the chapter are truncated and the theorems become
statistical); the auxiliary input of the verifier is bounded by an arbitrary polynomial
`Lz : PolyExpr` quantified after the simulator (the class a `t(|x|)`-time verifier can read,
and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the error bound is
a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
stated for a protocol and a witness relation without assuming the proof property, which the
theorems add separately.

## Main definitions

* `Complexity.NUPPT.simulate` — the simulator's output on `(x, z)`.
* `TCSlib.Cryptography.HVZK` — honest-verifier zero-knowledge [PS10, Definition 121.1]
  (Def-121.1).
* `TCSlib.Cryptography.ZK` — zero-knowledge [PS10, Definition 121.2] (Def-121.2).
* `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
  `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
  perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
  [Goldreich, *Foundations of Cryptography I*, Definition 4.3.1] (Def-122.a).

## Main results

* `TCSlib.Cryptography.StatZK.zk`, `TCSlib.Cryptography.StatZK.hvzk` — statistical
  zero-knowledge with negligible error implies zero-knowledge and honest-verifier
  zero-knowledge (`distAdv_le_of_statClose`).
* `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
* `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
  zero-knowledge is zero-knowledge; weakening the error.
* `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
  `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div` — `a^{-√(N/C)}` is negligible
  in `N` (Inf-4.4): the per-vertex bounds of the graph protocols are negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge, pp. 120–122.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge University
  Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Simulators -/

/-- The simulator's output on `(x, z)` [PS10, Definitions 121.1 and 121.2, `S(x, z)`]: one
activation of `S` at parameter `|x|` on `⟨x, z⟩`, a word read as an encoded view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) :
    List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- `simulate` unfolds to the typed activation at parameter `|x|`. -/
theorem _root_.Complexity.NUPPT.simulate_eq (S : NUPPT) (x z : List Bool)
    (r : S.Coins x.length) : S.simulate x z r = S.runAt x.length (pairEncode x z) r := rfl

/-! ### Honest-verifier and general zero-knowledge -/

/-- Honest-verifier zero-knowledge of `π` for the witness relation `R`
[PS10, Definition 121.1] (Def-121.1): there is a uniform PPT simulator `S` such that for every
auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a negligible `ε`
with, for all `x`, witnesses `y` of `x` and auxiliary inputs `z` of length `≤ Lz(|x|)`, the
advantage of `D` (at parameter `|x|`) between the honest verifier's view of
`P(x, y) ↔ V(x, z)` and `S(x, z)` at most `ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤
        ε x.length

/-- Zero-knowledge of `π` for the witness relation `R` [PS10, Definition 121.2] (Def-121.2):
for every efficient verifier strategy `V'` there is a uniform PPT simulator `S` such that for
every auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a
negligible `ε` with, for all `x`, witnesses `y` and auxiliary inputs `z` of length `≤ Lz(|x|)`,
the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- Statistical zero-knowledge of `π` for `R` with error `δ(|x|)` (Def-122.a, campaign
addition needed for the truncated simulators): for every efficient `V'` there is a uniform PPT
simulator whose output on `(x, z)` is `StatClose` (every test set, sup form) within `δ(|x|)`
to the view of `V'` in `P(x, y) ↔ V'(x, z)`, for all `x`, witnesses `y` and all auxiliary
inputs `z`.

**Deviation (D8):** strict PPT simulator; the bound is in `|x|`. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

/-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view. -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge with abort [Goldreich, Definition 4.3.1] (Def-122.a, the GMR form):
for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
of the view of `V'`: for every test set `T`,
`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]`. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins π.P x => T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

/-! ### Implications between the notions -/

/-- Statistical zero-knowledge with negligible error implies zero-knowledge
[PS10, §4.6, perfect/statistical ⇒ computational]: the same simulator works for every
distinguisher, with `ε := δ`, since a distinguisher's advantage between `δ`-close samplers is
at most `δ` (`distAdv_le_of_statClose`, [Gar26, Lemma 3.1]). -/
theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ =>
    distAdv_le_of_statClose _ _ (hclose x y z hR) _⟩⟩

/-- Statistical zero-knowledge with negligible error implies honest-verifier zero-knowledge
when the honest verifier is efficient: instantiate `V' := V` (`Protocol.withV_self`) and
apply `distAdv_le_of_statClose`. -/
theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  obtain ⟨S, hS, hclose⟩ := h π.V hV
  refine ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ => ?_⟩⟩
  have hc := hclose x y z hR
  rw [Protocol.withV_self] at hc
  exact distAdv_le_of_statClose _ _ hc _

/-- Zero-knowledge implies honest-verifier zero-knowledge when the honest verifier is
efficient [PS10, §4.6, after Definition 121.2]: instantiate `V' := V`. -/
theorem ZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} (hV : π.V.Efficient)
    (h : ZK π R) : HVZK π R := by
  obtain ⟨S, hS, hsim⟩ := h π.V hV
  refine ⟨S, hS, fun Lz D => ?_⟩
  obtain ⟨ε, hε, hadv⟩ := hsim Lz D
  refine ⟨ε, hε, fun x y z hR hz => ?_⟩
  have hc := hadv x y z hR hz
  rwa [Protocol.withV_self] at hc

/-- Weakening the statistical error. -/
theorem StatZK.mono {π : Protocol} {R : List Bool → List Bool → Prop} {δ δ' : ℕ → ℝ}
    (h : StatZK π R δ) (hle : ∀ n, δ n ≤ δ' n) : StatZK π R δ' := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun x y z hR => (hclose x y z hR).mono (hle _)⟩

/-- The zero function is negligible. -/
theorem negligible_const_zero : Negligible (fun _ => (0 : ℝ)) := fun c =>
  ⟨1, fun n hn => by
    rw [abs_zero]
    exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
theorem PerfectZK.statZK {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    StatZK π R (fun _ => 0) := h

/-- Perfect zero-knowledge implies zero-knowledge [PS10, §4.6]. -/
theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    ZK π R :=
  StatZK.zk negligible_const_zero h

/-! ### Negligibility in the instance length (Inf-4.4) -/

/-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
division) is negligible in `N` (Inf-4.4): the per-vertex error bounds `2^{-n}` and `e^{-n}` of
the graph protocols, whose instances have length `|x| ≥ n² / C`, are negligible in `|x|`.

**Proof sketch.** Fix `c`. Put `t := Nat.sqrt (N / C)`; then `N / C < (t + 1)²`
(`Nat.lt_succ_sqrt`), so `N < C (t + 1)² + C ≤ 2 C (t + 1)²` and
`N ^ c ≤ (2 C)^c (t + 1)^{2c}`. By `tendsto_pow_const_div_const_pow_of_one_lt`
(as in `negligible_two_pow_neg`), `(t + 1)^{2c} / a^{t+1} → 0`, so there is `t₀` with
`(2 C)^c · a · (t + 1)^{2c} < a^{t+1}` for `t ≥ t₀`, i.e. `(2C)^c (t+1)^{2c} < a^t`; and
`t ≥ t₀` as soon as `N ≥ C (t₀ + 1)²` (`Nat.le_sqrt`). Hence for such `N`,
`a⁻¹ ^ t = 1 / a^t < 1 / ((2C)^c (t+1)^{2c}) ≤ 1 / N^c`. -/
theorem negligible_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C) :
    Negligible fun N => a⁻¹ ^ Nat.sqrt (N / C) := by
  intro c
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCr : (0 : ℝ) < (C : ℝ) ^ c := by positivity
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) ^ c * a) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) ha
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max (C * t₀ * t₀) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNC : C * t₀ * t₀ ≤ N := le_of_max_le_left hN
  set t := Nat.sqrt (N / C) with ht_def
  -- `t₀ ≤ t` since `C t₀² ≤ N`
  have ht0 : t₀ ≤ t := by
    rw [ht_def, Nat.le_sqrt, Nat.le_div_iff_mul_le hC]
    calc t₀ * t₀ * C = C * t₀ * t₀ := by ring
      _ ≤ N := hNC
  -- `N < (t + 1)² C`
  have hNlt : N < (t + 1) * (t + 1) * C :=
    (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_sqrt (N / C))
  have hNltR : (N : ℝ) < ((t : ℝ) + 1) ^ 2 * C := by
    have := hNlt
    rw [← pow_two] at this
    exact_mod_cast this
  -- the limit at `t + 1`: `(t + 1)^{2c} C^c < a^t`
  have hlim := ht₀ (t + 1) (by omega)
  have hlim' : ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a) < a ^ (t + 1) := by
    have hapos : (0 : ℝ) < a ^ (t + 1) := pow_pos ha0 _
    rw [div_lt_iff₀ hapos] at hlim
    push_cast at hlim
    calc ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a)
        < 1 / ((C : ℝ) ^ c * a) * a ^ (t + 1) * ((C : ℝ) ^ c * a) := by
          gcongr
      _ = a ^ (t + 1) := by field_simp
  have hkey : ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c < a ^ t := by
    rw [pow_succ, ← mul_assoc] at hlim'
    exact lt_of_mul_lt_mul_right hlim' ha0.le
  -- `N^c ≤ (t + 1)^{2c} C^c`
  have hNpow : (N : ℝ) ^ c ≤ ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNltR.le c
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  show |a⁻¹ ^ t| < 1 / (N : ℝ) ^ c
  rw [abs_of_pos (pow_pos (inv_pos.mpr ha0) t), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt hNpos (hNpow.trans_lt hkey)

/-- `2^{-√(N / C)}` is negligible in `N` (Inf-4.4, the graph-isomorphism bound). -/
theorem negligible_two_pow_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => (2 : ℝ)⁻¹ ^ Nat.sqrt (N / C) :=
  negligible_inv_pow_sqrt_div one_lt_two hC

/-- `e^{-√(N / C)}` is negligible in `N` (Inf-4.4, the 3-colouring bound). -/
theorem negligible_exp_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => Real.exp (-(Nat.sqrt (N / C) : ℝ)) := by
  have h1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (negligible_inv_pow_sqrt_div h1 hC).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul, mul_one]

/-- A function bounded by `a^{-√(N / C)}` is negligible (Inf-4.4 in the form used by the
protocol theorems: a bound `a^{-n}` in the number of vertices `n ≥ √(|x| / C)` is a bound
`a^{-√(|x| / C)}` in the instance length). -/
theorem negligible_of_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C)
    {ν : ℕ → ℝ} (hν : ∀ N, |ν N| ≤ a⁻¹ ^ Nat.sqrt (N / C)) : Negligible ν :=
  (negligible_inv_pow_sqrt_div ha hC).mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans ha.le)) _)]
    exact hν N⟩

/-- A bound `a^{-n}` in a parameter `n ≥ √(N / C)` transfers to `a^{-√(N / C)}`
(monotonicity of `a⁻¹ ^ ·` for `a > 1`). -/
theorem inv_pow_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C N n : ℕ}
    (hn : Nat.sqrt (N / C) ≤ n) : a⁻¹ ^ n ≤ a⁻¹ ^ Nat.sqrt (N / C) :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans ha.le)) (inv_le_one_of_one_le₀ ha.le) hn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Commitment.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Commitment schemes and their construction from a one-way permutation

The material of [PS10, §4.7.1]: single-message commitment schemes [PS10, Definition 126.3]
(a deterministic polynomial-time `Com` with randomness polynomial `ℓ`; *binding*: distinct
values never commit to the same string; *hiding*: commitments to any two values of the same
length are computationally indistinguishable), multi-value hiding "by a simple hybrid
argument" (Claim-126.a), and the construction from a one-way permutation `f` with a hard-core
predicate `h` [PS10, Theorem 126.4]: `Com(b, r) = f(r) ‖ (b ⊕ h(r))` for one bit (Alg-127.a),
extended bitwise to `n`-bit values with independent randomness (`ℓ(n) = n²`). Binding
"directly follows from the construction" (Claim-127.b: `f` is injective and `⊕` cancels);
one-bit hiding is the predictor reduction of [PS10, Theorem 104.4] (Claim-127.c: a
distinguisher between `Com(0, ·)` and `Com(1, ·)` with advantage `ε` predicts `h(r)` from
`f(r)` with probability exactly `1/2 + ε/2`); `n`-bit hiding is the "show this!" hybrid over
the bits (Claim-127.d, Claim-126.a with single-bit values).

Two layers (foundation decision D2). The *concrete* layer reuses the frozen Garg development:
the one-bit scheme `Com(b, ·)` is `owpGen`/`owpGenNot` with `β := Unit`
(`Pseudorandom/GeneratorFromPermutation.lean`), its predictor is `owpPredictorSnoc` of
`Asymptotic/HardCore.lean`, and `predProb_owpPredictor_false/true` **are** Claim-127.c; the
coordinatewise hybrid lemma `exists_pairRed_ge` (new, concrete) generalises
`exists_multicopyRed_ge` and carries Claim-126.a and Claim-127.d. The *asymptotic* layer states
the frozen `Commitment` structure, multi-value hiding and Theorem 126.4 for `NUPPT`
distinguishers. The hiding fills do **not** sample the other coordinates of the hybrid: by
averaging over the reduction's coins (`CommitmentLemmas.exists_fixCoins`) a fixed choice of
the other commitments does at least as well, and the reduction machine merely splices the
challenge between two hard-wired strings (`CommitmentLemmas.exists_spliceRed`,
`exists_pairSpliceRed`) — the non-uniformity of [PS10, Definition 126.3] at work, so no
evaluator of `Com` is needed. The proof infrastructure (averaging, coin transport, tuple
splitting, the splice machines and the bitwise commitment loop `ComLoop` behind the
polynomial-time evaluator of Alg-127.a) is `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). In the string form `Com ⟨v, r⟩` the parameter is
`n = |v|`; the 3-colouring protocol pads its 2-bit colours to `n` bits.

## Main definitions

* `TCSlib.Cryptography.Commitment` — commitment scheme [PS10, Definition 126.3] (Def-126.3);
  `TCSlib.Cryptography.multiCom` — a vector of commitments as one string (Claim-126.a).
* `TCSlib.Cryptography.pairTuple`, `pairHybrid`, `pairRed` — coordinatewise products, their
  hybrids and the hybrid reduction (the concrete content of Claim-126.a and Claim-127.d).
* `TCSlib.Cryptography.bitCom` — the one-bit scheme `Com(b, r) = f(r) ‖ (b ⊕ h(r))`
  (Alg-127.a); `TCSlib.Cryptography.owpCom`, `owpComAt`, `owpComStr`, `owpComLen` — the
  `n`-bit scheme (typed, at a parameter, as the string function of `Commitment`; `ℓ(n) = n²`).
* `TCSlib.Cryptography.BitHiding` — hiding of the one-bit scheme against `NUPPT`s.

## Main results

* `TCSlib.Cryptography.exists_pairRed_ge` — the coordinatewise hybrid lemma (concrete);
  `TCSlib.Cryptography.Commitment.multiHiding` — multi-value hiding (Claim-126.a).
* `TCSlib.Cryptography.bitCom_inj`, `owpCom_inj`, `owpComStr_binding` — binding of
  Alg-127.a (Claim-127.b, proved).
* `TCSlib.Cryptography.exists_bitComPredictor` — single-bit hiding is the predictor
  reduction (Claim-127.c, concrete, proved); `HardCore.bitHiding` — its asymptotic form;
  `BitHiding.owpComStr_hides` — the bitwise hybrid (Claim-127.d).
* `TCSlib.Cryptography.owp_commitment` — **[PS10, Theorem 126.4]**: a one-way permutation
  with a hard-core predicate gives a commitment scheme; `exists_commitment_of_owp_hardCore` —
  the existential headline; `bitCom_false_eq_owpGenPRG` — `Com(0, ·)` is the generator of
  [PS10, Theorem 79.4]; `owpComStr_polyTimeComputable` — its `Com` is polynomial-time
  (the bitwise loop `CommitmentLemmas.ComLoop`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.3.3–3.3.4: Definition 78.3, Theorem 79.4;
  §3.5.2: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.2 (Construction 3.2, Theorem 3.2) and Lemma 3.3 (the
  multicopy hybrid argument).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Commitment schemes [PS10, Definition 126.3] -/

/-- A **commitment scheme** [PS10, Definition 126.3] (Def-126.3): a deterministic
polynomial-time string function `Com` (on the pair `⟨v, r⟩`) with a randomness polynomial `ℓ`
such that (1) *binding*: for all `n`, all distinct `v₀, v₁ ∈ {0,1}^n` and all
`r₀, r₁ ∈ {0,1}^{ℓ(n)}`, `Com(v₀, r₀) ≠ Com(v₁, r₁)`; (2) *hiding*: for every non-uniform PPT
`D` there is a negligible `ε` such that for every `n` and `v₀, v₁ ∈ {0,1}^n`, `D` (run at
parameter `n`) distinguishes `{r ← {0,1}^{ℓ(n)} : Com(v₀, r)}` from
`{r ← {0,1}^{ℓ(n)} : Com(v₁, r)}` with advantage at most `ε(n)`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). As printed, binding is unsatisfiable (`v₀ = v₁`,
`r₀ = r₁`); the string form's parameter is `n = |v|`, typed users supply `n` explicitly; the
distinguisher's verdict is the string `[true]` (`NUPPT.distinguisherL`, Deviation 4). -/
structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where
  /-- `Com` is computable in deterministic polynomial time. -/
  easy : PolyTimeComputable Com
  /-- Binding: distinct values of length `n` never commit to the same string. -/
  binding : ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
    r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  /-- Hiding: commitments to any two `n`-bit values are indistinguishable for every `NUPPT`. -/
  hides : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisherL n) ≤ ε n

/-- Binding in typed form [PS10, Definition 126.3 (1)]: distinct `n`-bit values with any
`ℓ(n)`-bit randomness commit to different strings (used by Lem-127.f). -/
theorem Commitment.binding_ofFn {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} {v₀ v₁ : Fin n → Bool} (hne : v₀ ≠ v₁)
    (r₀ r₁ : Fin (ℓ.eval n) → Bool) :
    Com (pairEncode (List.ofFn v₀) (List.ofFn r₀)) ≠
      Com (pairEncode (List.ofFn v₁) (List.ofFn r₁)) :=
  hC.binding n _ _ _ _ (List.length_ofFn) (List.length_ofFn) (List.length_ofFn)
    (List.length_ofFn) (fun h => hne (List.ofFn_injective h))

/-! ## The coordinatewise hybrid lemma (concrete content of Claim-126.a) -/

section Hybrids

variable {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] {t : ℕ}

/-- The coordinatewise product of a family of samplers: coordinate `i` is `X i` on the `i`-th
seed, all seeds independent (`copies t X` when all `X i` coincide). -/
def pairTuple (X : Fin t → σ → γ) : (Fin t → σ) → Fin t → γ :=
  fun s i => X i (s i)

/-- The `k`-th hybrid between the products of `X` and `Y`: coordinates `< k` are sampled from
`Y`, the others from `X` [PS10, Lemma 71.6, the hybrids `H_k` of Claim-126.a]. -/
def pairHybrid (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : ℕ) :
    (Fin t → σ) × (Fin t → τ) → Fin t → γ :=
  fun s i => if (i : ℕ) < k then Y i (s.2 i) else X i (s.1 i)

/-- The hybrid reduction at coordinate `k`: on a challenge `z` (a sample of `X k` or of `Y k`)
it samples coordinates `< k` from `Y`, coordinates `> k` from `X`, plants `z` at position `k`
and calls `D` once (the reduction of Claim-126.a). -/
def pairRed (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    γ → ((Fin t → σ) × (Fin t → τ)) × ρ → Bool :=
  fun z c => D (fun i => if (i : ℕ) < k then Y i (c.1.2 i) else if (i : ℕ) = k then z
    else X i (c.1.1 i)) c.2

/-- The zeroth hybrid is the product of `X`. -/
theorem acceptProb_pairHybrid_zero [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y 0) D = acceptProb (pairTuple X) D := by
  have h : pairHybrid X Y 0 = fun s => pairTuple X s.1 := by
    funext s i; simp [pairHybrid, pairTuple]
  rw [h, acceptProb_fst]

/-- The `t`-th hybrid is the product of `Y`. -/
theorem acceptProb_pairHybrid_self [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y t) D = acceptProb (pairTuple Y) D := by
  have h : pairHybrid X Y t = fun s => pairTuple Y s.2 := by
    funext s i; simp [pairHybrid, pairTuple, i.isLt]
  rw [h, acceptProb_snd]

/-- On a sample of `X k`, the reduction at `k` simulates the `k`-th hybrid for `D`.

**Proof sketch.** Position `k` holds a sample of `X k` in the `k`-th hybrid; overwriting the
ignored seed at position `k` with the challenge's seed leaves the seed tuple uniform
(`acceptProb_update`), as in `acceptProb_multicopyRed_left`. -/
theorem acceptProb_pairRed_left [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (X k) (pairRed X Y k D) = acceptProb (pairHybrid X Y k) D := by
  refine (acceptProb_bind (X k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ (acceptProb_update (ρ := ρ) k
    (fun u (s' : Fin t → τ) => pairHybrid X Y k (u, s')) D)
  congr 1
  funext w i
  simp only [pairHybrid, Function.update_apply, Fin.ext_iff]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le]

/-- On a sample of `Y k`, the reduction at `k` simulates the `(k + 1)`-th hybrid for `D`.

**Proof sketch.** As `acceptProb_pairRed_left`: position `k` holds a sample of `Y k` in the
`(k + 1)`-th hybrid (`acceptProb_update` after swapping the two seed vectors). -/
theorem acceptProb_pairRed_right [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (Y k) (pairRed X Y k D) = acceptProb (pairHybrid X Y (k + 1)) D := by
  let e : τ × ((Fin t → σ) × (Fin t → τ)) ≃ τ × ((Fin t → τ) × (Fin t → σ)) :=
    (Equiv.refl τ).prodCongr (Equiv.prodComm _ _)
  refine (acceptProb_bind (Y k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ ((acceptProb_comp_equiv e _ D).trans
    ((acceptProb_update (ρ := ρ) k
      (fun u (s : Fin t → σ) => pairHybrid X Y (k + 1) (s, u)) D).trans
    (acceptProb_comp_equiv (Equiv.prodComm _ _) (pairHybrid X Y (k + 1)) D)))
  congr 1
  funext w i
  simp only [e, pairHybrid, Function.update_apply, Fin.ext_iff, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, id]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt, Nat.lt_succ_of_lt hlt, hlt.ne]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le, not_lt.mpr (Nat.succ_le_of_lt hgt)]

/-- **The coordinatewise hybrid lemma** (concrete content of Claim-126.a and Claim-127.d;
[PS10, Lemma 71.6] as in [Gar26, Lemma 3.3]): if `D` distinguishes `(X_1(s_1), …, X_t(s_t))`
from `(Y_1(s_1), …, Y_t(s_t))` with advantage `ε` and `t ≥ 1`, then at some coordinate `k`
`pairRed X Y k D` distinguishes `X k` from `Y k` with advantage `≥ ε / t`
(`exists_multicopyRed_ge` is the case of equal pairs).

**Proof sketch.** `exists_hybrid_gap` on `k ↦ Pr[D(H_k) = 1]`; the ends are the two
products (`acceptProb_pairHybrid_zero/self`) and the reduction at `k` accepts `X k`, `Y k`
with the acceptance probabilities of `H_k`, `H_{k+1}` (`acceptProb_pairRed_left/right`). -/
theorem exists_pairRed_ge [Nonempty σ] [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (ht : 0 < t) (D : (Fin t → γ) → ρ → Bool) :
    ∃ k : Fin t, distAdv (pairTuple X) (pairTuple Y) D / t ≤
      distAdv (X k) (Y k) (pairRed X Y k D) := by
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (pairHybrid X Y i) D) ht
  refine ⟨⟨k, hk⟩, ?_⟩
  unfold distAdv
  rw [acceptProb_pairRed_left, acceptProb_pairRed_right, ← acceptProb_pairHybrid_zero X Y D,
    ← acceptProb_pairHybrid_self X Y D]
  exact hgap

end Hybrids

/-! ## Multi-value hiding (Claim-126.a) -/

/-- A vector of `q` commitments as one string: the right-nested pair encoding
(`Strategy.encodeMsgs`) of the list `Com(v_1, r_1), …, Com(v_q, r_q)` — the form in which the
3-colouring prover sends its commitments ([PS10, Protocol 127.5]). -/
def multiCom (Com : List Bool → List Bool) {q n m : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin m → Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i => Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))))

/-- The advice bound of the multi-value hiding reduction: `3 q(n) (2 C (2n + 3 + ℓ(n))^c + 2) + 2`,
where `C (|x|+1)^c` bounds `|Com x|` — the length of the pair `⟨pre_n, suf_n⟩` of the two
hard-wired strings of commitments (`CommitmentLemmas.length_encodeMsgs_le`). -/
private def multiAdvBound (ℓ q : PolyExpr) (C c : ℕ) : PolyExpr :=
  .add (.mul (.const 3) (.mul q (.add (.mul (.const 2) (.mul (.const C)
    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))) (.const 2)

/-- Unfolding the advice bound of the multi-value hiding reduction. -/
private theorem multiAdvBound_eval (ℓ q : PolyExpr) (C c n : ℕ) :
    (multiAdvBound ℓ q C c).eval n =
      3 * (q.eval n * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2)) + 2 := rfl

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-126.a**: at each `n` there are two strings `pre`, `suf`
of bounded length and two values `a, a' ∈ {0,1}^n` such that every pair of `q(n)`-vectors of
values is distinguished by `D` with advantage at most `q(n)` times the advantage of the
spliced distinguisher `z ↦ D(1^n, pre ++ ⟨z, suf⟩)` between `Com(a, ·)` and `Com(a', ·)`.

**Proof sketch.** For `t := q(n) = 0` both distributions coincide. Otherwise take a worst pair
`(v, v')` (`Finset.exists_max_image`); `multiCom` is `encodeMsgs ∘ List.ofFn ∘ pairTuple` of
`X i := r ↦ Com ⟨v i, r⟩`, `Y i := r ↦ Com ⟨v' i, r⟩`, so `exists_pairRed_ge` against
`D' := D ∘ encodeMsgs ∘ List.ofFn` gives a coordinate `k`; averaging over the reduction's seed
vectors (`CommitmentLemmas.exists_fixCoins`) fixes them to some `(c_X, c_Y)`, and with the tuple
`W` of fixed commitments the reduction at `k` is `z ↦ D'(update W k z)`, which is
`D(1^n, encodeMsgs (W|_{<k}) ++ ⟨z, encodeMsgs (W|_{>k})⟩)` by
`CommitmentLemmas.encodeMsgs_ofFn_update`; `a := v k`, `a' := v' k`. The length bound is
`CommitmentLemmas.length_encodeMsgs_le` with `|W i| ≤ C (2n + 3 + ℓ(n))^c`. -/
private theorem exists_multiRed_bound {Com : List Bool → List Bool} (ℓ q : PolyExpr) (D : NUPPT)
    {C c : ℕ} (hCc : ∀ x, (Com x).length ≤ C * (x.length + 1) ^ c) (n : ℕ) :
    ∃ (pre suf : List Bool) (a a' : Fin n → Bool),
      2 * pre.length + 2 + suf.length ≤ (multiAdvBound ℓ q C c).eval n ∧
      ∀ v v' : Fin (q.eval n) → Fin n → Bool,
        distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
          (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
          (D.distinguisherL n) ≤
        q.eval n * distAdv
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a) (List.ofFn r)))
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a') (List.ofFn r)))
          (fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c) := by
  rw [multiAdvBound_eval]
  set t := q.eval n with ht
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · refine ⟨[], [], fun _ => false, fun _ => false, by simp, fun v v' => ?_⟩
    have hvv : v = v' := funext fun i => absurd i.2 (by omega)
    rw [hvv]
    simp only [distAdv, sub_self, abs_zero]
    positivity
  set cm : (Fin t → Fin n → Bool) → Fin t → (Fin (ℓ.eval n) → Bool) → List Bool :=
    fun v i s => Com (pairEncode (List.ofFn (v i)) (List.ofFn s)) with hcm
  set D' : (Fin t → List Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (Strategy.encodeMsgs (List.ofFn w)) c with hD'
  have hadv : ∀ v v' : Fin t → Fin n → Bool,
      distAdv (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v' r) (D.distinguisherL n) =
      distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' := fun v v' => rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin t → Fin n → Bool) × (Fin t → Fin n → Bool) =>
      distAdv (pairTuple (cm p.1)) (pairTuple (cm p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (cm v) (cm v') htpos D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D')
  set W : Fin t → List Bool :=
    fun i => if (i : ℕ) < k then cm v' i (c₀.2 i) else cm v i (c₀.1 i) with hW
  set pre : List Bool := Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
    with hpre
  set suf : List Bool :=
    Strategy.encodeMsgs (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩) with hsuf
  have hred : ∀ z c, pairRed (cm v) (cm v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ pairEncode z suf) c := by
    intro z c
    have hTz : (fun i : Fin t => if (i : ℕ) < k then cm v' i (c₀.2 i)
        else if (i : ℕ) = k then z else cm v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, encodeMsgs_ofFn_update]
  have hWlen : ∀ i, (W i).length ≤ C * (2 * n + 3 + ℓ.eval n) ^ c := by
    intro i
    simp only [hW, hcm]
    split_ifs <;>
    · refine (hCc _).trans (le_of_eq ?_)
      rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
      ring_nf
  refine ⟨pre, suf, v k, v' k, ?_, fun v₀ v₁ => ?_⟩
  · have h1 := length_encodeMsgs_le (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    have h2 := length_encodeMsgs_le (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩)
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    rw [List.length_ofFn] at h1 h2
    have hk1 : (k : ℕ) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ k.2.le
    have hk2 : (t - k - 1) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ (by omega)
    simp only [hpre, hsuf]
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have ht' : (0 : ℝ) < t := Nat.cast_pos.2 htpos
    rw [div_le_iff₀ ht'] at hk
    have h1 : distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' ≤
        t * distAdv (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans (le_of_eq ?_)) (Nat.cast_nonneg t))
    rw [show (fun z c => pairRed (cm v) (cm v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c
      from funext fun z => funext fun c => hred z c]

/-- **Every commitment scheme is multi-value hiding** [PS10, p. 126, "it directly follows by
a simple hybrid argument that any commitment scheme is multi-value secure"] (Claim-126.a):
for a commitment scheme `(Com, ℓ)`, a polynomial `q` and a non-uniform PPT `D` there is a
negligible `ε` such that for every `n` and every two vectors `v, v'` of `q(n)` values of `n`
bits, `D` (at parameter `n`) distinguishes `(Com(v_i, r_i))_i` from `(Com(v'_i, r_i))_i`,
with independent uniform `r_i ∈ {0,1}^{ℓ(n)}`, with advantage at most `ε(n)`.

**Deviation:** the text does not state the notion; this is the analogue of multi-message
security [PS10, Definition 93.1], the vector encoded by `Strategy.encodeMsgs`, values after `ε`.

**Proof sketch.** Fix `D` and let `C (|x|+1)^c` bound `|Com x|` (`hC.easy.output_length_le`).
At each `n`, `exists_multiRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a coordinate `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` applied to `X i := r ↦ Com ⟨v_n i, r⟩`, `Y i := r ↦ Com ⟨v'_n i, r⟩`
against `D' := D.distinguisherL n ∘ encodeMsgs ∘ List.ofFn`, and — by averaging over the
reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the other
`q(n) − 1` commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ ⟨z, suf_n⟩)` for two
strings `pre_n`, `suf_n` of total length `≤ multiAdvBound` (`CommitmentLemmas.encodeMsgs_ofFn_update`,
`length_encodeMsgs_le`), and `ε_D(n) ≤ q(n) · distAdv (Com ⟨v_n k_n, ·⟩) (Com ⟨v'_n k_n, ·⟩) (that reduction)`.
The machine `B := CommitmentLemmas.exists_pairSpliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`);
by coin transport (`CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`) its advantage is the
reduction's, so `hC.hides B` gives `ε_D(n) ≤ q(n) ε_B(n)`, negligible by
`EnsembleLemmas.negligible_polyExpr_mul`; take `ε := q · ε_B`. -/
theorem Commitment.multiHiding {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) (q : PolyExpr) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v v' : Fin (q.eval n) → Fin n → Bool),
      distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨C, c, hCc⟩ := hC.easy.output_length_le
  choose pre suf a a' hlen hkey using exists_multiRed_bound ℓ q D hCc
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_pairSpliceRed D pre suf
    (multiAdvBound ℓ q C c) hlen
  obtain ⟨ε, hε, hεB⟩ := hC.hides B
  refine ⟨fun n => q.eval n * ε n, EnsembleLemmas.negligible_polyExpr_mul q hε, fun n v v' => ?_⟩
  refine (hkey n v v').trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hε' := hεB n (a n) (a' n)
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n),
    CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n)] at hε'

/-! ## The construction from a one-way permutation [PS10, Theorem 126.4] -/

/-- **The one-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a):
`Com(b, r) = f(r) ‖ (b ⊕ h(r))` for a permutation `f` of `{0,1}^n`, a predicate `h` and
randomness `r ∈ {0,1}^n` (`ℓ(n) = n`), an `(n + 1)`-bit string with the masked bit last
(`owpGen f h` / `owpGenNot f h` of the Garg layer up to the trivial `Unit` coordinate). -/
def bitCom {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (b : Bool) (r : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (f r) (xor b (h r))

/-- Unfolding: the first `n` bits of `Com(b, r)` are `f(r)`. -/
@[simp] theorem bitCom_castSucc {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) (i : Fin n) :
    bitCom f h b r i.castSucc = f r i := by
  simp [bitCom]

/-- Unfolding: the last bit of `Com(b, r)` is `b ⊕ h(r)`. -/
@[simp] theorem bitCom_last {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) :
    bitCom f h b r (Fin.last n) = xor b (h r) := by
  simp [bitCom]

/-- `Com(0, ·)` is `f(r) ‖ h(r)`. -/
theorem bitCom_false {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h false = fun r => Fin.snoc (f r) (h r) := by
  funext r; simp [bitCom]

/-- `Com(1, ·)` is `f(r) ‖ ¬h(r)`. -/
theorem bitCom_true {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h true = fun r => Fin.snoc (f r) (!h r) := by
  funext r; simp [bitCom]

/-- The commitment to `0` is the generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4]: the
hiding of Alg-127.a and the pseudorandomness of `owpGenPRG` rest on the same reduction. -/
theorem bitCom_false_eq_owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (r : Fin n → Bool) (i : Fin (n + 1)) :
    bitCom (P.f n) (h n) false r i = (owpGenPRG P h).G n r i := by
  simp [bitCom, owpGenPRG, PRG.oneBit]

/-- **Binding of the one-bit scheme** [PS10, proof of Theorem 126.4, "it directly follows from
the construction that `Com` is binding"] (Claim-127.b, single bit): `Com(b₀, r₀) = Com(b₁, r₁)`
forces `r₀ = r₁` (the first `n` bits are `f(r)` and `f` is injective) and then `b₀ = b₁`
(`⊕ h(r)` cancels). -/
theorem bitCom_inj {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    {b₀ b₁ : Bool} {r₀ r₁ : Fin n → Bool} (heq : bitCom f h b₀ r₀ = bitCom f h b₁ r₁) :
    b₀ = b₁ ∧ r₀ = r₁ := by
  have hf : f r₀ = f r₁ := by
    funext i
    have := congrFun heq i.castSucc
    simpa using this
  have hr : r₀ = r₁ := f.injective hf
  subst hr
  refine ⟨?_, rfl⟩
  have hb := congrFun heq (Fin.last n)
  simp only [bitCom_last] at hb
  cases b₀ <;> cases b₁ <;> cases h r₀ <;> simp_all

/-- **The `n`-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a): "a full-fledged
commitment scheme to a value `v ∈ {0,1}^n` can be obtained by individually committing to each
bit of `v`" — `Com(v, (r_i)_i) = (Com(v_i, r_i))_i`, `n` independent `n`-bit `r_i` (`ℓ(n) = n²`). -/
def owpCom (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v : Fin n → Bool)
    (r : Fin n → Fin n → Bool) : Fin n → Fin (n + 1) → Bool :=
  fun i => bitCom (P.f n) (h n) (v i) (r i)

/-- The typed `n`-bit scheme is the coordinatewise product of the one-bit schemes to the
bits of `v` (the form `exists_pairRed_ge` applies to). -/
theorem owpCom_eq_pairTuple (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (v : Fin n → Bool) : owpCom P h n v = pairTuple fun i => bitCom (P.f n) (h n) (v i) := rfl

/-- **Binding of the `n`-bit scheme** (Claim-127.b): equal commitment vectors have equal values
and equal randomness, coordinate by coordinate from `bitCom_inj`. -/
theorem owpCom_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ : Fin n → Bool} {r₀ r₁ : Fin n → Fin n → Bool}
    (heq : owpCom P h n v₀ r₀ = owpCom P h n v₁ r₁) : v₀ = v₁ ∧ r₀ = r₁ := by
  have hi := fun i => bitCom_inj (P.f n) (h n) (congrFun heq i)
  exact ⟨funext fun i => (hi i).1, funext fun i => (hi i).2⟩

/-- The `n`-bit scheme at an explicit parameter `n` on strings: the value is read as `n` bits,
the randomness as `n²` bits (`padFin`, total), the `n` commitments of `n + 1` bits are
concatenated into one `n(n+1)`-bit string (`FunFamily.blocks`). -/
def owpComAt (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v r : List Bool) :
    List Bool :=
  List.ofFn ((FunFamily.blocks n (n + 1)).symm
    (owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r))))

/-- **The string function `Com` of Alg-127.a**: on `⟨v, r⟩` it commits to the `|v|` bits of
`v` with the `|v|²` bits of `r` (`owpComAt` at `n = |v|`); the `Com` of `Commitment`. -/
def owpComStr (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (w : List Bool) : List Bool :=
  owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w)

/-- The randomness polynomial of Alg-127.a: `ℓ(n) = n · n`. -/
def owpComLen : PolyExpr := .mul .var .var

/-- `ℓ(n) = n²`. -/
@[simp] theorem owpComLen_eval (n : ℕ) : owpComLen.eval n = n * n := rfl

/-- Unfolding `owpComStr` on a well-formed pair. -/
theorem owpComStr_pairEncode (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (v r : List Bool) : owpComStr P h (pairEncode v r) = owpComAt P h v.length v r := by
  simp [owpComStr]

/-- Unfolding `owpComAt` on encoded typed arguments. -/
theorem owpComAt_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (n * n) → Bool) :
    owpComAt P h n (List.ofFn v) (List.ofFn r) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  simp [owpComAt, padFin_ofFn]

/-- The string scheme on encoded typed arguments is the encoded typed scheme (the bridge
between the `hides` clause and `owpCom`). -/
theorem owpComStr_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (owpComLen.eval n) → Bool) :
    owpComStr P h (pairEncode (List.ofFn v) (List.ofFn r)) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  rw [owpComStr_pairEncode, List.length_ofFn, owpComAt_ofFn]

/-- Two strings of length `n` with the same `n`-bit padding are equal. -/
private theorem padFin_inj {n : ℕ} {v₀ v₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (h : padFin n v₀ = padFin n v₁) : v₀ = v₁ := by
  refine List.ext_getElem (hv₀.trans hv₁.symm) fun i h₁ h₂ => ?_
  have := congrFun h ⟨i, hv₀ ▸ h₁⟩
  simpa [padFin, List.getD_eq_getElem, h₁, h₂] using this

/-- **Binding of `owpComAt`** (Claim-127.b, string form at a parameter): equal commitment
strings of two `n`-bit values force the values to be equal.

**Proof sketch.** `List.ofFn` and the block equivalence are injective, so the typed
commitment vectors agree; `owpCom_inj` gives equal padded values; strings of length `n` with
equal paddings are equal. -/
theorem owpComAt_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ r₀ r₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (heq : owpComAt P h n v₀ r₀ = owpComAt P h n v₁ r₁) : v₀ = v₁ := by
  have h1 := List.ofFn_injective heq
  have h2 := (FunFamily.blocks n (n + 1)).symm.injective h1
  exact padFin_inj hv₀ hv₁ (owpCom_inj P h h2).1

/-- **Binding of Alg-127.a** [PS10, proof of Theorem 126.4] (Claim-127.b): the binding clause
of `Commitment` for `owpComStr` — for all `n`, distinct `v₀, v₁ ∈ {0,1}^n` and any
`r₀, r₁ ∈ {0,1}^{n²}`, `Com ⟨v₀, r₀⟩ ≠ Com ⟨v₁, r₁⟩`. Only the injectivity of `f` is used. -/
theorem owpComStr_binding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) :
    ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
      r₀.length = owpComLen.eval n → r₁.length = owpComLen.eval n → v₀ ≠ v₁ →
      owpComStr P h (pairEncode v₀ r₀) ≠ owpComStr P h (pairEncode v₁ r₁) := by
  intro n v₀ v₁ r₀ r₁ hv₀ hv₁ _ _ hne heq
  rw [owpComStr_pairEncode, owpComStr_pairEncode, hv₀, hv₁] at heq
  exact hne (owpComAt_inj P h hv₀ hv₁ heq)

/-! ### Hiding of the one-bit scheme (Claim-127.c) -/

/-- **Single-bit hiding is the predictor reduction** [PS10, proof of Theorem 126.4, "hiding
follows using identically the same proof as in the proof of Theorem 104.4"] (Claim-127.c,
concrete): for every distinguisher `D` between `Com(0, ·) = f(r) ‖ h(r)` and
`Com(1, ·) = f(r) ‖ ¬h(r)` there is a sign `flip` such that `owpPredictorSnoc D flip` (one call
of `D` on `f(r) ‖ σ` for a fresh coin `σ`) predicts `h(r)` from `f(r)` with probability exactly
`1/2 + distAdv(Com(0), Com(1), D) / 2`. Only bijectivity of `f` is used [Gar26, Theorem 3.2].

**Proof sketch.** This is `predProb_owpPredictor_false`/`_true` with `β := Unit`: under the
bijection `(y, (), b) ↦ y ‖ b`, `owpGen f h'` is `Com(0, ·)` and `owpGenNot f h'` is
`Com(1, ·)` (`acceptProb_fst` removes the `Unit` seed coordinate), and the prediction
experiments correspond under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`); choose `flip`
by the sign of `Pr[D(Com(0)) = 1] - Pr[D(Com(1)) = 1]`. -/
theorem exists_bitComPredictor {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f h (owpPredictorSnoc D flip) =
      1 / 2 + distAdv (bitCom f h false) (bitCom f h true) D / 2 := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  have h1 : ∀ flip, predProb f h (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => h w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := fun flip => by
    unfold predProb
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h0 : acceptProb (owpGen f fun w : (Fin n → Bool) × Unit => h w.1) (fun z r => D (e z) r) =
      acceptProb (bitCom f h false) D := by
    rw [bitCom_false, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (h r)) D]
    rfl
  have h0' : acceptProb (owpGenNot f fun w : (Fin n → Bool) × Unit => h w.1)
      (fun z r => D (e z) r) = acceptProb (bitCom f h true) D := by
    rw [bitCom_true, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (!h r)) D]
    rfl
  rcases le_total 0 (acceptProb (bitCom f h false) D - acceptProb (bitCom f h true) D) with
    hs | hs
  · refine ⟨false, ?_⟩
    rw [h1, predProb_owpPredictor_false, h0, h0', distAdv, abs_of_nonneg hs]
  · refine ⟨true, ?_⟩
    rw [h1, predProb_owpPredictor_true, h0, h0', distAdv, abs_of_nonpos hs]
    ring

/-- **Hiding of the one-bit scheme against non-uniform PPTs**: for every `NUPPT` `D` there is
a negligible `ε` such that at every `n`, `D` (at parameter `n`, on the `(n+1)`-bit string)
distinguishes `Com(0, ·)` from `Com(1, ·)` with advantage `≤ ε(n)` [PS10, Def. 126.3 (2)]. -/
def BitHiding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
      (D.distinguisher n (n + 1)) ≤ ε n

/-- **A hard-core predicate makes the one-bit scheme hiding** [PS10, proof of Theorem 126.4,
via the proof of Theorem 104.4] (Claim-127.c, asymptotic): if `h` is hard-core for the
permutation family `f`, then `Com(b, r) = f(r) ‖ (b ⊕ h(r))` is hiding — every `NUPPT` has
negligible advantage between `Com(0, ·)` and `Com(1, ·)` (in fact `≤ 2 ε_h(n)` for the
predictor's bound `ε_h`).

**Deviation:** the text's proof goes through the prediction lemma [PS10, Lemma 73.8]; here the
reduction is the exact one of [Gar26, Theorem 3.2] (`exists_bitComPredictor`), with the sign
of the advantage as non-uniform advice.

**Proof sketch.** Fix `D : NUPPT`. At each `n`, `exists_bitComPredictor (P.f n) (h n)
(D.distinguisher n (n+1))` gives a sign `flip_n` (`Classical.choose`) with
`predProb (P.f n) (h n) (owpPredictorSnoc D' flip_n) = 1/2 + distAdv(Com(0), Com(1), D')/2`.
The predictor machine is `owpPredMachine D flip` of `Asymptotic/HardCoreLemmas.lean` (the
machine of Theorem 79.4: advice `⟨[flip_n], D.advice n⟩`, coins `1 + D.coins`; on `⟨1^n, y⟩` it
reads the first coin `σ`, calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining coins and
outputs `[xor (if D accepts then σ else !σ) flip_n]`), whose prediction probability is that
of `owpPredictorSnoc (D.distinguisher n (n+1)) (flip n)` (`owpPredMachine_predProb`). Then
`hh.hard A` (note `P.toFunFamily.outLen.eval n = n`) gives a negligible `ε_h` with
`1/2 + distAdv/2 ≤ 1/2 + ε_h n`, hence `distAdv ≤ 2 ε_h n`; take `ε := 2 ε_h`
(`Negligible.const_mul`). -/
theorem HardCore.bitHiding {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hh : HardCore P.toFunFamily h) : BitHiding P h := by
  intro D
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (D.distinguisher n (n + 1)) / 2 :=
    fun n => exists_bitComPredictor (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine ⟨fun n => 2 * ε n, hε.const_mul 2, fun n => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := rfl
  rw [← h3, hflip n] at h1
  linarith

/-! ### Hiding of the `n`-bit scheme (Claim-127.d) and Theorem 126.4 -/

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-127.d**: at each `n` there are two strings `pre`, `suf`
of total length `≤ 3n(n+1)` such that every pair of `n`-bit values is distinguished by `D`
with advantage at most `n` times the advantage of the spliced distinguisher
`z ↦ D(1^n, pre ++ z ++ suf)` between `Com(0, ·)` and `Com(1, ·)`.

**Proof sketch.** For `n = 0` there is one value. Otherwise `owpComStr_ofFn` and the seed
reindexing `acceptProb_comp_equiv (blocks n n)` turn the advantage into
`distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D'` with `bc v i := bitCom (f n) (h n) (v i)`
and `D' := D ∘ List.ofFn ∘ (blocks n (n+1)).symm`. Take a worst pair `(v, v')`
(`Finset.exists_max_image`), a bit position `k` from `exists_pairRed_ge`, and by averaging over
the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) a fixed choice `(c_X, c_Y)`;
with the tuple `W` of fixed one-bit commitments the reduction at `k` is `z ↦ D'(update W k z)`,
i.e. `D(1^n, pre ++ z ++ suf)` for the block strings before and after `k`
(`CommitmentLemmas.ofFn_blocks_symm_update`, lengths by `length_flatten_ofFn`). If
`v k = v' k` the advantage is `0`; otherwise the pair is `(Com(0), Com(1))` up to
`distAdv_comm`. -/
private theorem exists_bitRed_bound (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (D : NUPPT)
    (n : ℕ) :
    ∃ pre suf : List Bool, 2 * pre.length + 2 + suf.length ≤ 3 * (n * (n + 1)) + 2 ∧
      ∀ v₀ v₁ : Fin n → Bool,
        distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
          (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
          (D.distinguisherL n) ≤
        n * distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], [], by simp, fun v₀ v₁ => ?_⟩
    rw [Subsingleton.elim v₀ v₁]
    simp [distAdv]
  set D' : (Fin n → Fin (n + 1) → Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (List.ofFn ((FunFamily.blocks n (n + 1)).symm w)) c with hD'
  set bc : (Fin n → Bool) → Fin n → (Fin n → Bool) → Fin (n + 1) → Bool :=
    fun v i => bitCom (P.f n) (h n) (v i) with hbc
  have hadv : ∀ v₀ v₁ : Fin n → Bool,
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) = distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D' := by
    intro v₀ v₁
    simp only [owpComStr_ofFn]
    unfold distAdv
    rw [← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₀)) D',
      ← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₁)) D']
    rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      distAdv (pairTuple (bc p.1)) (pairTuple (bc p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (bc v) (bc v') hn D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D')
  set W : Fin n → Fin (n + 1) → Bool :=
    fun i => if (i : ℕ) < k then bc v' i (c₀.2 i) else bc v i (c₀.1 i) with hW
  set pre : List Bool := (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten
    with hpre
  set suf : List Bool :=
    (List.ofFn fun i : Fin (n - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten with hsuf
  have hred : ∀ z c, pairRed (bc v) (bc v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ List.ofFn z ++ suf) c := by
    intro z c
    have hTz : (fun i : Fin n => if (i : ℕ) < k then bc v' i (c₀.2 i)
        else if (i : ℕ) = k then z else bc v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, ofFn_blocks_symm_update]
  refine ⟨pre, suf, ?_, fun v₀ v₁ => ?_⟩
  · simp only [hpre, hsuf]
    rw [length_flatten_ofFn, length_flatten_ofFn]
    have h1 : (k : ℕ) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ k.2.le
    have h2 : (n - k - 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_le_iff₀ hn'] at hk
    have h1 : distAdv (pairTuple (bc v)) (pairTuple (bc v')) D' ≤
        n * distAdv (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans ?_) (Nat.cast_nonneg n))
    rw [show (fun z c => pairRed (bc v) (bc v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c
      from funext fun z => funext fun c => hred z c]
    simp only [hbc]
    cases v k <;> cases v' k
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · rw [distAdv_comm]
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _

/-- **Hiding of the bitwise scheme by the hybrid lemma** [PS10, proof of Theorem 126.4, "the
security of the full-fledged construction follows as a simple application of the
hybrid lemma (show this!)"] (Claim-127.d): if the one-bit scheme is hiding, the `n`-bit scheme
`owpComStr` satisfies the hiding clause of [PS10, Definition 126.3] — for every `NUPPT` `D`
there is a negligible `ε` with `distAdv(Com⟨v₀, ·⟩, Com⟨v₁, ·⟩, D) ≤ ε(n)` for all `n` and
`v₀, v₁ ∈ {0,1}^n` (the special case of Claim-126.a with `q = n` and single-bit values).

**Proof sketch.** Fix `D`. At each `n`, `exists_bitRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a bit position `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` (after `owpComStr_ofFn`, `distAdv_comp` and the seed reindexing
`acceptProb_comp_equiv (blocks n n)` have turned the two distributions into
`pairTuple (fun i => bitCom (f n) (h n) (v_n i))` and the same for `v'_n`), and — by averaging
over the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the
other `n − 1` one-bit commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ z ++ suf_n)`
for two block strings of total length `≤ 3n(n+1)` (`CommitmentLemmas.ofFn_blocks_symm_update`)
and `ε_D(n) ≤ n · distAdv (Com(0)) (Com(1)) (that reduction)` (if `v_n k_n = v'_n k_n` the
advantage is `0`, otherwise up to `distAdv_comm`). The machine
`B := CommitmentLemmas.exists_spliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`,
`NUPPT.exists_withAdvice`); by coin transport (`CommitmentLemmas.acceptProb_distinguisher_of_runAtL`)
its advantage is the reduction's, so `hBit B` gives `ε_D(n) ≤ n ε_B(n)`;
`EnsembleLemmas.negligible_polyExpr_mul` closes with `ε := n · ε_B`. No evaluator of `f` or `h`
is needed: the other commitments are hard-wired, not sampled. -/
theorem BitHiding.owpComStr_hides {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hBit : BitHiding P h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) ≤ ε n := by
  intro D
  choose pre suf hlen hkey using exists_bitRed_bound P h D
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_spliceRed D pre suf
    (.add (.mul (.const 3) (.mul .var (.add .var (.const 1)))) (.const 2))
    (fun n => by simpa using hlen n)
  obtain ⟨ε, hε, hεB⟩ := hBit B
  refine ⟨fun n => n * ε n, by simpa using EnsembleLemmas.negligible_polyExpr_mul .var hε,
    fun n v₀ v₁ => ?_⟩
  refine (hkey n v₀ v₁).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have hε' := hεB n
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _ (fun y => pre n ++ y ++ suf n)
    (hB n), CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _
    (fun y => pre n ++ y ++ suf n) (hB n)] at hε'

open CommitmentLemmas in
/-- **The string commitment is the output of the bitwise loop**: for evaluators `F`, `H` of
`f`, `h` on `⟨1^n, x⟩`, `owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w)` for every
string `w` (`n = |fst w|`).

**Proof sketch.** With `v := fst w`, `r := snd w`, `n := |v|` the loop runs from
`⟨1^n, ⟨v, padL (n²) r⟩⟩` for `|init w| + 1 ≥ n` rounds; round `i < n` emits
`F ⟨1^n, r_i⟩ ++ [v[i] ⊕ H ⟨1^n, r_i⟩]` with `r_i` the `i`-th block of `padFin (n²) r`
(`ComLoop.emit_init_of_lt`), which is `List.ofFn (bitCom (f n) (h n) (padFin n v i) r_i)` by
`hF`, `hH` and `ofFn_snoc_eq`, and rounds `i ≥ n` emit nothing (`ComLoop.emit_init_of_le`,
`CommitmentLemmas.flatMap_range_eq_of_nil`); the concatenation of the `n` block strings is
`List.ofFn ((blocks n (n+1)).symm (owpCom …))` (`EnsembleLemmas.ofFn_blocks_symm`), i.e.
`owpComAt P h n v r`. -/
private theorem owpComStr_eq_loopOut (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    {F H : List Bool → List Bool}
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x))
    (hHx : ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) (w : List Bool) :
    owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w) := by
  rw [ComLoop.init_eq]
  show owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w) = _
  generalize pairFstD w = v
  generalize pairSndD w = r
  unfold owpComAt ComLoop.loopOut
  set n := v.length with hn
  set T := owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r)) with hT
  set E : ℕ → List Bool :=
    fun i => ComLoop.emit F H (ComLoop.step^[i] (ComLoop.init (pairEncode v r))) with hE
  have hEi : ∀ i (hi : i < n), E i = List.ofFn (T ⟨i, hi⟩) := by
    intro i hi
    simp only [hE]
    rw [ComLoop.emit_init_of_lt F H hi, hFx, hHx, List.headD_cons, ← ofFn_snoc_eq]
    rfl
  have hb : FunFamily.blocks n (n + 1) = EnsembleLemmas.blocks n (n + 1) := rfl
  rw [hb, EnsembleLemmas.ofFn_blocks_symm T E hEi]
  refine (flatMap_range_eq_of_nil E ?_ fun i hi => ComLoop.emit_init_of_le F H hi).symm
  simp only [ComLoop.init, ComLoop.st, length_pairEncode, pairFstD_pairEncode]
  omega

/-- **`Com` of Alg-127.a is polynomial-time** [PS10, Definition 126.3, "a polynomial-time
machine `Com`"; Theorem 126.4]: if `f` and `h` have polynomial-time evaluators on `⟨1^n, x⟩`
(the efficiency clauses of [PS10, Definitions 27.3 and 78.3]), then `owpComStr` is
polynomial-time computable.

**Proof sketch.** On `w`, read `v := pairFstD w`, form `1^n := 1^{|v|}`
(`polyTimeComputable_unary`), pad/cut `pairSndD w` to `n²` bits
(`EnsembleLemmas.polyTimeComputable_padL`) — the initial state `ComLoop.init w` of the bitwise
commitment loop `CommitmentLemmas.ComLoop` — and run the loop `ComLoop.loopOut F H`
(`polyTimeComputable_iterateEmit`, state `⟨1^n, ⟨v.drop i, rest⟩⟩`: each round drops one value
bit and one `n`-bit block and emits `F ⟨1^n, r_i⟩ ++ [v_i ⊕ H ⟨1^n, r_i⟩]`, nothing once the
value bits are exhausted; `StateLoop.headBit_poly`, `StateLoop.xor_poly`,
`PolyTimeComputable.append`, `pairTakePoly/pairDropPoly`). The result equals `owpComStr P h w`
by `owpComStr_eq_loopOut` (`hF`, `hH`, `List.ofFn` of `(blocks n (n+1)).symm` being the
concatenation of the blocks, and `padFin` matching the padding). -/
theorem owpComStr_polyTimeComputable (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hF : P.toFunFamily.Easy)
    (hH : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) :
    PolyTimeComputable (owpComStr P h) := by
  obtain ⟨F, hF, hFx⟩ := hF
  obtain ⟨H, hH, hHx⟩ := hH
  convert (CommitmentLemmas.ComLoop.loopOut_poly F H hF hH).comp
    CommitmentLemmas.ComLoop.init_poly using 1
  funext w
  exact owpComStr_eq_loopOut P h hFx hHx w

/-- **Commitment schemes from one-way permutations** [PS10, Theorem 126.4]: if `f` is a
one-way permutation with a hard-core predicate `h`, then `Com(v, (r_i)_i) = (f(r_i) ‖
(v_i ⊕ h(r_i)))_i` (Alg-127.a, `ℓ(n) = n²`) is a commitment scheme: polynomial-time
(`owpComStr_polyTimeComputable`), binding (Claim-127.b, `owpComStr_binding`) and hiding
(Claim-127.c `HardCore.bitHiding` for one bit, Claim-127.d `BitHiding.owpComStr_hides` for `n`
bits).

**Deviation:** the text's hypothesis is "if one-way permutations exist"; its proof uses a
hard-core predicate `h` without stating it (source error 47: [PS10, Theorem 87.3] produces one
for `g(x, r) = (f(x), r)`, not for `f`) and a single permutation family `f` (as in
Theorem 79.4), not the collection of [PS10, Definition 55.1]. Both `OneWayPermutation P` and
`HardCore P.toFunFamily h` are hypotheses here; besides the hard-core property only
`P.toFunFamily.Easy` and the injectivity of `f` are used. -/
theorem owp_commitment (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) :
    Commitment (owpComStr P h) owpComLen where
  easy := owpComStr_polyTimeComputable P h hP.easy hh.easy
  binding := owpComStr_binding P h
  hides := hh.bitHiding.owpComStr_hides

/-- **[PS10, Theorem 126.4], existential form**: if there is a one-way permutation with a
hard-core predicate, then commitment schemes exist. -/
theorem exists_commitment_of_owp_hardCore
    (hex : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ := by
  obtain ⟨P, h, hP, hh⟩ := hex
  exact ⟨owpComStr P h, owpComLen, owp_commitment P h hP hh⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/NP.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
import TCSlib.Cryptography.ZeroKnowledge.NPLemmas
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge proofs for NP: Levin reductions and Theorem 124.1

Step 2 of [PS10, Theorem 124.1]: "to get a zero-knowledge proof `(P, V)` for any NP language
`L`, both `P` and `V` reduce the instance `x` into an instance `x' = f(x)` of graph
3-colouring, the prover additionally reduces the witness `y` to a witness `y' = w(x, y)` for
`x'`, and the parties execute the 3-colouring protocol on `x'`". The reduction must preserve
witnesses, i.e. be a *Levin reduction* (Def-124.a; the text says "Cook's reduction can be
applied to the witness", which Karp/Cook reductions do not provide — source error 47 of the
plan). Zero-knowledge proofs with efficient prover transfer along Levin reductions
(Claim-124.d), which gives [PS10, Theorem 124.1] in the plan's form (A): for every language
`L` with witness relation `R` and every Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)`,
the pulled-back 3-colouring protocol is a zero-knowledge proof with efficient prover for `L`,
given a commitment scheme (hence given a one-way permutation with a hard-core predicate,
[PS10, Theorem 126.4]). The "every language in NP" form is the corollary under the hypothesis
that `3COL` is NP-hard *with Levin reductions* (`LevinNPHard`); the string-level Levin
reduction from `3SAT` is not formalized (plan decision on Theorem 124.1, Claim-124.b/c
deferred).

**Deviations:**
* a Levin reduction is taken *length-regular* with `|f x| = p(|x|)` for a `PolyExpr p ≥ id`
  (every Levin reduction to `3COL` can be padded to this form by adding isolated vertices),
  which makes the coin and round polynomials of the pulled-back protocol `subst p` of the
  original ones and the error bounds `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
* the text's "execute protocol `(P, V)` on `x'`" is read as `(P', V')`; the hypothesis of a
  hard-core predicate for the one-way permutation is made explicit (as in Theorem 126.4).

**Proof infrastructure (run 4):** the transfer proofs use the sibling file
`TCSlib.Cryptography.ZeroKnowledge.NPLemmas` (namespace `LevinTransfer`): the execution
congruence `exec_congr`, the uniform coin projections `coinTrunc`/`UnifProj` with
`distAdv_eq_of_unifProj` (the padding of the random tapes is uniform and independent), the
verifier `liftVerifier V'` and the view re-encoder `postView` of the zero-knowledge transfer,
the machines `exists_liftSimulator`/`exists_liftDistinguisher`, and the strict monotonicity of
a length polynomial `p ≥ id` (`polyExpr_strictMono_of_le`, which gives the left inverse of
`p.eval` along which the distinguisher is re-parametrized).

**Run-3 repairs (audit P11-1, P11-2):** the transfer lemmas and both forms of Theorem 124.1
take the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (`L ⊆ witnessLanguage R`): no field of
`LevinReduction` relates `L` to `R` (with `R = ∅` the `witness` field is vacuous), and without
it the `complete` clause of the pulled-back proof is false. The "every language in NP" forms
keep the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` of the Levin reduction's
length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s` was vacuous with
`s = 1`; `one_sub_inv_add_half_pow_lt_one` shows the error is below `1`).

## Main definitions

* `TCSlib.Cryptography.LevinReduction` — Levin (witness-preserving) reductions (Def-124.a).
* `TCSlib.Cryptography.Strategy.pullback`, `TCSlib.Cryptography.Protocol.pullback` — the
  protocol for `L` obtained by reducing to `L'` and running a protocol for `L'`.
* `TCSlib.Cryptography.LevinNPHard` — NP-hardness with Levin reductions (the hypothesis of
  the "every language in NP" form).

## Main results

* `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.LevinReduction.trans`,
  `TCSlib.Cryptography.LevinReduction.polyTimeReducible` — sanity: Levin reductions compose
  and are Karp reductions (proved).
* `TCSlib.Cryptography.LevinReduction.efficientProverProof`,
  `TCSlib.Cryptography.LevinReduction.efficientProverProofErr`,
  `TCSlib.Cryptography.LevinReduction.zk` — interactive proofs with efficient prover and
  zero-knowledge transfer along Levin reductions (Claim-124.d).
* `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge proof for `L`;
  `TCSlib.Cryptography.zk_proof_of_owp_levinReduction` — the same from a one-way permutation
  with a hard-core predicate (Thm-124.1).
* `TCSlib.Cryptography.zk_proof_of_mem_NP`, `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` —
  the "every language in NP" form under `LevinNPHard L3COL R3COL`, with the explicit soundness
  error of the Levin reduction's length polynomial
  (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.7, Karp reductions; §2.3.3, Levin reductions.)
-/

namespace TCSlib.Cryptography

open Complexity Turing LevinTransfer

/-! ### Levin reductions (Def-124.a) -/

/-- A **Levin reduction** `(f, w)` from `(L, R)` to `(L', R')` [PS10, §4.7, Theorem 124.1,
step 2, "Cook's reduction can be applied to the witness"] (Def-124.a): `f` is a
polynomial-time Karp reduction (`x ∈ L ↔ f x ∈ L'`), `w` is polynomial-time on the pair
`⟨x, y⟩` and maps witnesses to witnesses (`R x y → R' (f x) (w x y)`), and `f` is
length-regular: `|f x| = p(|x|)` for the polynomial `p ≥ id`.

**Deviation:** the text never defines Levin reductions; length-regularity with `p ≥ id` is
assumed (achievable by padding) so that the pulled-back protocol's polynomials are `subst p`
of the original ones and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
structure LevinReduction (L L' : Language Bool) (R R' : List Bool → List Bool → Prop)
    (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Prop where
  /-- The instance map is polynomial-time. -/
  f_poly : PolyTimeComputable f
  /-- The witness map is polynomial-time on the pair `⟨x, y⟩`. -/
  w_poly : PolyTimeComputable fun z => w (pairFstD z) (pairSndD z)
  /-- `f` is a Karp reduction. -/
  mem_iff : ∀ x, x ∈ L ↔ f x ∈ L'
  /-- `w` maps witnesses of `x` to witnesses of `f x`. -/
  witness : ∀ x y, R x y → R' (f x) (w x y)
  /-- `f` is length-regular with length polynomial `p`. -/
  length_eq : ∀ x, (f x).length = p.eval x.length
  /-- The length polynomial dominates the identity. -/
  le_eval : ∀ N, N ≤ p.eval N

/-- A Levin reduction is a Karp reduction [AB09, Definition 2.7]. -/
theorem LevinReduction.polyTimeReducible {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) : PolyTimeReducible L L' :=
  ⟨f, h.f_poly, h.mem_iff⟩

/-- Sanity: the identity is a Levin reduction of `(L, R)` to itself. -/
theorem LevinReduction.refl (L : Language Bool) (R : List Bool → List Bool → Prop) :
    LevinReduction L L R R id (fun _ y => y) .var where
  f_poly := polyTimeComputable_id
  w_poly := polyTimeComputable_pairSndD
  mem_iff _ := Iff.rfl
  witness _ _ h := h
  length_eq _ := rfl
  le_eval _ := le_rfl

/-- Sanity: Levin reductions compose, with length polynomial `p'.subst p`.

**Proof sketch.** `f' ∘ f` by `PolyTimeComputable.comp`; the composed witness map
`⟨x, y⟩ ↦ w' (f x) (w x y)` is `w'` on the pair `⟨f x, w x y⟩` built by
`PolyTimeComputable.pairEncode` (`pairFstD_pairEncode`, `pairSndD_pairEncode`); membership
and witnesses by transitivity; lengths by `PolyExpr.eval_subst`. -/
theorem LevinReduction.trans {L L' L'' : Language Bool}
    {R R' R'' : List Bool → List Bool → Prop} {f f' : List Bool → List Bool}
    {w w' : List Bool → List Bool → List Bool} {p p' : PolyExpr}
    (h : LevinReduction L L' R R' f w p) (h' : LevinReduction L' L'' R' R'' f' w' p') :
    LevinReduction L L'' R R'' (f' ∘ f) (fun x y => w' (f x) (w x y)) (p'.subst p) where
  f_poly := h'.f_poly.comp h.f_poly
  w_poly := by
    have hfun : (fun z => w' (f (pairFstD z)) (w (pairFstD z) (pairSndD z))) =
        fun z => w' (pairFstD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z))))
          (pairSndD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z)))) := by
      funext z
      rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hfun]
    exact h'.w_poly.comp ((h.f_poly.comp polyTimeComputable_pairFstD).pairEncode h.w_poly)
  mem_iff x := (h.mem_iff x).trans (h'.mem_iff (f x))
  witness x y hxy := h'.witness _ _ (h.witness x y hxy)
  length_eq x := by
    rw [Function.comp_apply, h'.length_eq, h.length_eq, PolyExpr.eval_subst]
  le_eval N := by
    rw [PolyExpr.eval_subst]
    exact (h.le_eval N).trans (h'.le_eval _)

/-! ### Pulling a protocol back along a reduction -/

/-- The strategy that runs `S` on the reduced instance `f x` with the transformed auxiliary
input `g x z` [PS10, §4.7, Theorem 124.1, step 2]: `next x z r hist := S.next (f x) (g x z) r hist`,
coins `S.coins.subst p` (so that the tape at `|x|` has exactly `S.coinLen |f x|` bits when
`|f x| = p(|x|)`). -/
def Strategy.pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) (p : PolyExpr) : Strategy where
  next x z r hist := S.next (f x) (g x z) r hist
  coins := S.coins.subst p

/-- The pulled-back strategy's coin length at `|x|` is `S`'s at `|f x|` under length
regularity. -/
theorem Strategy.coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    (S.pullback f g p).coinLen x.length = S.coinLen (f x).length := by
  simp [Strategy.pullback, Strategy.coinLen, PolyExpr.eval_subst, hx]

/-- The protocol for `L` obtained from a protocol `π` for `L'` and a reduction `(f, w)`
[PS10, §4.7, Theorem 124.1, step 2]: `P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)`,
rounds `π.rounds.subst p`, same first mover (Claim-124.d, construction).

**Deviation:** "execute protocol `(P, V)` on `x'`" read as `(P', V')`. -/
def Protocol.pullback (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Protocol where
  P := π.P.pullback f w p
  V := π.V.pullback f (fun _ z => z) p
  rounds := π.rounds.subst p
  verifierFirst := π.verifierFirst

/-- Unfolding: the verifier's output in the pulled-back protocol against a prover `P'` is
`π.V.next` on the reduced instance after `π.rounds.eval (p |x|)` moves of `exec` with the
reduced inputs. -/
theorem Protocol.pullback_outV (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x y z r =
      π.V.next (f x) z (List.ofFn r.2)
        (exec P' (π.V.pullback f (fun _ z => z) p) π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn r.2) (π.rounds.eval (p.eval x.length))).2 := by
  simp [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Strategy.pullback,
    PolyExpr.eval_subst]

/-- A pulled-back strategy is efficient when the original is and `f`, `g` are
polynomial-time (on `⟨x, z⟩` for `g`): compose the machine of `S` with the FP function
`⟨⟨x, z⟩, msgs⟩ ↦ ⟨⟨f x, g x z⟩, msgs⟩` and re-parametrize `1^{|x|}` to `1^{p |x|}`
(`NUPPT.exists_reparam p`, `NUPPT.exists_comp`, `PolyExpr.eval_subst`, `hx`).

**Proof sketch.** From `hS` take the uniform `A` with `S.next x' z' r hist =
A.runAtL |x'| ⟨⟨x', z'⟩, encodeMsgs hist⟩ r`. `NUPPT.exists_comp A hpre polyTimeComputable_id`
with `pre := ⟨⟨f ∘ pairFstD ∘ pairFstD, g on the pair⟩, pairSndD⟩` (pairing calculus) gives
`B` with `B.runAtL m y r = A.runAtL m (pre y) r`; `NUPPT.exists_reparam B p` gives `C` with
`C.runAtL n y r = B.runAtL (p n) y r`, uniform, coins `A.coins.subst p = (S.pullback …).coins`;
on `n = |x|`, `p n = |f x|` (`hx`), so `C` computes the pulled-back next-message function
(`Strategy.ofNUPPT_next`, `pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem Strategy.pullback_efficient {S : Strategy} (hS : S.Efficient) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) {g : List Bool → List Bool → List Bool}
    (hg : PolyTimeComputable fun z => g (pairFstD z) (pairSndD z)) {p : PolyExpr}
    (hx : ∀ x, (f x).length = p.eval x.length) : (S.pullback f g p).Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hS
  have hpre : PolyTimeComputable fun y =>
      pairEncode (pairEncode (f (pairFstD (pairFstD y)))
        (g (pairFstD (pairFstD y)) (pairSndD (pairFstD y)))) (pairSndD y) :=
    ((hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
      (hg.comp polyTimeComputable_pairFstD)).pairEncode polyTimeComputable_pairSndD
  obtain ⟨B, hBc, -, hBadv, hB⟩ := A.exists_comp hpre polyTimeComputable_id
  obtain ⟨C, hCc, hCu, hC⟩ := B.exists_reparam p
  refine ⟨C, hCu fun n => by rw [hBadv]; exact hA n, ?_, fun x z r hist => ?_⟩
  · show S.coins.subst p = C.coins
    rw [hCc, hBc, hc]
  · rw [Strategy.ofNUPPT_next, hC, hB]
    show S.next (f x) (g x z) r hist = _
    rw [hnext, Strategy.ofNUPPT_next, ← hx x]
    simp only [id, pairFstD_pairEncode, pairSndD_pairEncode]

/-! ### Negligibility along polynomial reparametrization -/

/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
    Negligible fun N => μ (φ N) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ c
  refine ⟨max n₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)

/-! ### Executions of the pulled-back protocol -/

/-- The execution of two pulled-back strategies on `x` is the execution of the original
strategies on `f x` with the transformed auxiliary inputs and the same random tapes
(`LevinTransfer.exec_congr`; the pulled-back next-message functions are those of the
originals on the reduced inputs by definition). -/
private theorem exec_pullback (P V : Strategy) (f : List Bool → List Bool)
    (g g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k : ℕ) :
    exec (P.pullback f g p) (V.pullback f g' p) vFirst x zP zV rP rV k =
      exec P V vFirst (f x) (g x zP) (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The execution of an arbitrary prover `P'` against a pulled-back verifier on `x` is the
execution of the prover `⟨fun _ _ r hist => P'.next x [] r hist, const (P'.coinLen |x|)⟩`
(which hard-wires `x` and has `P'`'s random tape) against the original verifier on `f x`
(`LevinTransfer.exec_congr`). -/
private theorem exec_pullback_cheat (P' V : Strategy) (f : List Bool → List Bool)
    (g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zV rP rV : List Bool) (k : ℕ) :
    exec P' (V.pullback f g' p) vFirst x [] zV rP rV k =
      exec ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ V vFirst (f x)
        [] (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The coin length of a pulled-back strategy at `|x|` is at least (in fact equal to) the
original's at `|f x|` under length regularity — the form in which `LevinTransfer.coinTrunc`
casts the honest coins of the pulled-back protocol to those of `π` on `f x`. -/
private theorem coinLen_le_coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    S.coinLen (f x).length ≤ (S.pullback f g p).coinLen x.length :=
  (Strategy.coinLen_pullback S f g hx).ge

/-- **The honest execution of the pulled-back protocol is the honest execution of `π` on the
reduced instance:** the verifier's output in `(π.pullback f w p)` on `(x, y, z)` with coins
`r` is the output of `π` on `(f x, w x y, z)` with the coins cast along
`Strategy.coinLen_pullback` (`Protocol.pullback_outV`, `exec_pullback`,
`LevinTransfer.ofFn_coinTrunc_of_eq`, the move count `π.rounds (p |x|) = π.rounds |f x|`). -/
private theorem outV_pullback_honest (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (y z : List Bool)
    (r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x) :
    (π.pullback f w p).outV (π.pullback f w p).P x y z r =
      π.outV π.P (f x) (w x y) z
        (Prod.map (coinTrunc (coinLen_le_coinLen_pullback π.P f w hx))
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.P f w hx).symm,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback, ← hx]

/-- **A cheating prover for the pulled-back protocol is a cheating prover for `π`:** the
verifier's output in `(π.pullback f w p)` against `P'` on `x` with coins `r` is the output
of `π` on `f x` against the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist,
const (P'.coinLen |x|)⟩` (which hard-wires `x` and has `P'`'s random tape) with the verifier
coins cast along `Strategy.coinLen_pullback` (`exec_congr`). -/
private theorem outV_pullback_cheat (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (P' : Strategy) (z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x [] z r =
      π.outV ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ (f x) [] z
        (Prod.map (coinTrunc le_rfl)
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ rfl,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback_cheat, ← hx]

/-! ### Claim-124.d: zero-knowledge proofs transfer along Levin reductions -/

/-- **Interactive proofs with efficient prover transfer along Levin reductions, soundness
error `s ∘ p`** [PS10, §4.7, "it is easy to verify that the above protocol is a
zero-knowledge proof"] (Claim-124.d, proof half): if `π` is an interactive proof for `L'` with
efficient prover w.r.t. `R'` and soundness error `s`, `(f, w)` is a Levin reduction of
`(L, R)` to `(L', R')`, and every `x ∈ L` has an `R`-witness (`hLR`, i.e.
`L ⊆ witnessLanguage R`), then `π.pullback f w p` is an interactive proof for `L` with
efficient prover w.r.t. `R` and soundness error `N ↦ s (p N)`.

**Repair (run-3 audit P11-1):** the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` was added. No
field of `LevinReduction` relates `L` to `R` — with `R = ∅` the `witness` field is vacuous, so
a witness map that outputs non-witnesses is a valid Levin reduction — while the `complete`
clause of the conclusion needs the pulled-back honest prover, which runs `π.P` on `w x y`, to
hold a witness `y` with `R x y`; without `hLR` the statement is refutable (`npProtocol` for
the relation `|x| = |y|` pulled back along `id` and `w x y := ⟨x, x⟩`). Equivalent
alternative: state the lemma for `L := witnessLanguage R`.

**Proof sketch.** Efficiency of both parties: `Strategy.pullback_efficient` with `h.f_poly`,
`h.w_poly` (for `V` the map `g := fun _ z => z` is `polyTimeComputable_pairSndD`), `h.length_eq`.
Completeness for every witness: for `R x y`, `R' (f x) (w x y)` (`h.witness`), and the
execution of the pulled-back protocol on `(x, y, z)` with coins `r` is the execution of `π` on
`(f x, w x y, z)` with the coins cast along `Strategy.coinLen_pullback` (`outV_pullback_honest`:
`Protocol.pullback_outV` and `LevinTransfer.exec_congr` — the pulled-back next-message
functions are those of `π` on `(f x, w x y)` and `(f x, z)` by definition — with the move
count `π.rounds.eval (p |x|) = π.rounds.eval |f x|` by `h.length_eq`); the cast is a uniform
projection (`LevinTransfer.unifProj_coinTrunc`, `UnifProj.uprob_comp`), so
`hπ.completeWitness` gives probability one. Completeness:
`complete x hx := let ⟨y, hy⟩ := hLR x hx; ⟨y, completeWitness x y hy⟩`. Soundness: for
`x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol on `x` is the
prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩` for `π` on
`f x` with the same coins (`outV_pullback_cheat`, `P*.coinLen |f x| = P'.coinLen |x|`), and
`hπ.sound (f x) _ P* z` gives `1 - s |f x| ≤ Pr[out = [false]]`, i.e. `1 - s (p |x|)` by
`h.length_eq`. -/
theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} {s : ℕ → ℝ}
    (hπ : EfficientProverProofErr π L' R' s) :
    EfficientProverProofErr (π.pullback f w p) L R (fun N => s (p.eval N)) := by
  have hcompl : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x =>
        (π.pullback f w p).outV (π.pullback f w p).P x y z r = [true]) = 1 := by
    intro x y hxy z
    have hx := h.length_eq x
    have key := hπ.completeWitness (f x) (w x y) (h.witness x y hxy) z
    rw [← ((unifProj_coinTrunc (coinLen_le_coinLen_pullback π.P f w hx)).prod
      (unifProj_coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx))).uprob_comp
      (fun r' => π.outV π.P (f x) (w x y) z r' = [true])] at key
    rw [← key]
    congr 1
    funext r
    rw [outV_pullback_honest π f w hx]
  refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
    h.length_eq, fun x hx => ?_, fun x hx P' z => ?_⟩,
    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq, hcompl⟩
  · obtain ⟨y, hy⟩ := hLR x hx
    exact ⟨y, hcompl x y hy⟩
  · have hlen := h.length_eq x
    have hfx : f x ∉ L' := fun hfx => hx ((h.mem_iff x).2 hfx)
    have hU : UnifProj (Prod.map (coinTrunc le_rfl)
        (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hlen)) :
          (π.pullback f w p).ExecCoins P' x →
            π.ExecCoins ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩
              (f x)) :=
      (unifProj_coinTrunc _).prod (unifProj_coinTrunc _)
    have key := hπ.sound (f x) hfx
      ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ z
    rw [← hU.uprob_comp] at key
    refine le_of_eq_of_le (by rw [hlen]) (le_of_le_of_eq key ?_)
    congr 1
    funext r
    rw [outV_pullback_cheat π f w hlen]

/-- **Interactive proofs with efficient prover transfer along Levin reductions** (Claim-124.d,
proof half, negligible error): as `LevinReduction.efficientProverProofErr`, the soundness
error `ε (p N)` being negligible by `Negligible.comp_of_le` with `h.le_eval`
(`EfficientProverProof.exists_err`, `EfficientProverProofErr.efficientProverProof`).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`LevinReduction.efficientProverProofErr`). -/
theorem LevinReduction.efficientProverProof {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} (hπ : EfficientProverProof π L' R') :
    EfficientProverProof (π.pullback f w p) L R := by
  obtain ⟨ε, hε, herr⟩ := hπ.exists_err
  exact (h.efficientProverProofErr hLR herr).efficientProverProof (hε.comp_of_le _ h.le_eval)

/-- **Zero-knowledge transfers along Levin reductions** [PS10, §4.7, "it is easy to verify
that the above protocol is a zero-knowledge proof"] (Claim-124.d, zero-knowledge half): if `π`
is zero-knowledge for `R'` and `(f, w)` is a Levin reduction of `(L, R)` to `(L', R')`, then
`π.pullback f w p` is zero-knowledge for `R`.

**Proof sketch.** Let `V*` be an efficient verifier for the pulled-back protocol. The
verifier `V*' := LevinTransfer.liftVerifier V*` for `π`, `V*'.next x' z' r hist := V*.next
(pairFstD z') (pairSndD z') (r.take (V*.coinLen |pairFstD z'|)) hist` with coins `V*.coins`
(at `|x'| = p |x| ≥ |x|` the tape is long enough, `PolyExpr.eval_mono`, `h.le_eval`), recovers
`x` from its auxiliary input `z' = ⟨x, z⟩` and ignores `x'`; it is efficient
(`LevinTransfer.liftVerifier_efficient`, from `V*`'s machine with
`polyTimeComputable_pairTakePoly`). `hzk V*'` gives a uniform simulator `S'`; the simulator for
`V*` is `S` with `S.simulate x z r = post (S'.simulate (f x) ⟨x, z⟩ r)`, where
`post := LevinTransfer.postView V*.coins` re-encodes the view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` as
`⟨⟨x, z⟩, ⟨r'.take (V*.coinLen |x|), msgs⟩⟩` (`LevinTransfer.exists_liftSimulator`:
`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, then `NUPPT.exists_reparam p`; uniform,
coins `S'.coins.subst p`). For `Lz`, `D`: the distinguisher `D'` for `π` at parameter
`|x'| = p |x|` is `D` re-parametrized along the left inverse `φ N' := min (invFun p.eval N') N'`
of `p.eval` — well defined since `p ≥ id` is strictly increasing
(`LevinTransfer.polyExpr_strictMono_of_le`) — composed with `post`
(`LevinTransfer.exists_liftDistinguisher`: `NUPPT.exists_reparam_advice`, `NUPPT.exists_comp`);
auxiliary bound `Lz' := add (add (mul (const 2) var) (const 2)) Lz` (`|⟨x, z⟩| ≤ 2|x| + 2
+ Lz |x| ≤ Lz' |x'|`). `hzk V*' Lz' D'` gives `ε'`; on `R x y` (so `R' (f x) (w x y)`), `post` of
the view of `V*'` in `π` on `(f x, w x y, ⟨x, z⟩)` with coins `(r₁, r₂')` is the view of `V*` in
the pulled-back protocol with coins `(r₁, r₂'.take (V*.coinLen |x|))`
(`LevinTransfer.exec_congr`, `liftVerifier_next`, `postView_encode`), and `D'`'s verdict is
`D`'s on the re-encoded sample with truncated coins (`LevinTransfer.distinguisherL_lift`);
the truncations are uniform projections, so the two advantages coincide
(`LevinTransfer.distAdv_eq_of_unifProj`) and `distAdv ≤ ε' |f x| = ε' (p |x|)`;
`ε := ε' ∘ p.eval` is negligible by `Negligible.comp_of_le`. -/
theorem LevinReduction.zk {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) {π : Protocol} (hzk : ZK π R') :
    ZK (π.pullback f w p) R := by
  intro V' hV'
  obtain ⟨S', hS'u, hS'⟩ := hzk (liftVerifier V') (liftVerifier_efficient hV')
  obtain ⟨S, hSc, hSu, hS⟩ := exists_liftSimulator S' h.f_poly V'.coins p
  refine ⟨S, hSu hS'u, fun Lz D => ?_⟩
  -- the left inverse `φ` of the (strictly increasing) length polynomial
  have hmono := polyExpr_strictMono_of_le h.le_eval
  set φ : ℕ → ℕ := fun n => min (Function.invFun p.eval n) n with hφ_def
  have hφle : ∀ n, φ n ≤ n := fun n => min_le_right _ _
  have hφp : ∀ N, φ (p.eval N) = N := fun N => by
    simp only [hφ_def, Function.leftInverse_invFun hmono.injective N]
    exact min_eq_left (h.le_eval N)
  obtain ⟨D', hD'c, hD'⟩ := exists_liftDistinguisher D φ hφle V'.coins
  set Lz' : PolyExpr := .add (.add (.mul (.const 2) .var) (.const 2)) Lz with hLz'
  obtain ⟨ε', hε', hadv⟩ := hS' Lz' D'
  refine ⟨fun N => ε' (p.eval N), hε'.comp_of_le _ h.le_eval, fun x y z hxy hz => ?_⟩
  have hlen := h.length_eq x
  have hz' : (pairEncode x z).length ≤ Lz'.eval (f x).length := by
    rw [length_pairEncode, hlen, hLz']
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have h₁ := h.le_eval x.length
    have h₂ := Lz.eval_mono (h.le_eval x.length)
    omega
  have key := hadv (f x) (w x y) (pairEncode x z) (h.witness x y hxy) hz'
  -- coin-space bookkeeping
  have hxle : x.length ≤ (f x).length := by rw [hlen]; exact h.le_eval _
  have hφx : φ (f x).length = x.length := by rw [hlen]; exact hφp _
  have hDle : D.coinLen x.length ≤ D'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hD'c]
    exact D.coins.eval_mono hxle
  have hVle : V'.coinLen x.length ≤ (liftVerifier V').coinLen (f x).length := by
    rw [liftVerifier_coinLen]
    exact V'.coins.eval_mono hxle
  have hPeq : (π.P.pullback f w p).coinLen x.length = π.P.coinLen (f x).length :=
    Strategy.coinLen_pullback π.P f w hlen
  have hSeq : S.coinLen x.length = S'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hSc, PolyExpr.eval_subst, hlen]
  calc distAdv (fun r => (((π.pullback f w p).withV V').viewV x y z r).encode) (S.simulate x z)
        (D.distinguisherL x.length)
      = distAdv (fun r => ((π.withV (liftVerifier V')).viewV (f x) (w x y) (pairEncode x z) r).encode)
          (S'.simulate (f x) (pairEncode x z)) (D'.distinguisherL (f x).length) := by
        refine (distAdv_eq_of_unifProj ((unifProj_coinTrunc hPeq.le).prod (unifProj_coinTrunc hVle))
          (unifProj_coinTrunc hSeq.le) (unifProj_coinTrunc hDle) (fun r ρ => ?_)
          (fun r ρ => ?_)).symm
        · -- the view of `V*'` in `π` re-encodes to the view of `V'` in the pulled-back protocol
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [Protocol.viewV, Protocol.transcriptWith, Protocol.withV_P, Protocol.withV_V,
            Protocol.withV_rounds, Protocol.withV_verifierFirst, Protocol.pullback, Prod.map,
            postView_encode]
          rw [ofFn_coinTrunc_of_eq _ hPeq, ofFn_coinTrunc]
          simp only [PolyExpr.eval_subst, ← hlen, Strategy.coinLen]
          congr 2
          refine congrArg Prod.snd (exec_congr ?_ ?_ _ _)
          · intro _
            rfl
          · intro _
            exact liftVerifier_next V' _ x z _ _
        · -- the simulator for `V'` is `postView` of the simulator for `V*'`
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [NUPPT.simulate, NUPPT.runAt_eq, hS, pairFstD_pairEncode]
          rw [ofFn_coinTrunc_of_eq _ hSeq, ← hlen]
    _ ≤ ε' (f x).length := key
    _ = ε' (p.eval x.length) := by rw [hlen]

/-! ### Theorem 124.1 -/

/-- **[PS10, Theorem 124.1], form (A): a commitment scheme and a Levin reduction to `3COL`
give a zero-knowledge proof for `L`** (Thm-124.1): for a commitment scheme `(Com, ℓ)` and a
Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with `L ⊆ witnessLanguage R` (`hLR`),
the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
`R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`.

**Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
of scope); the reduction is an explicit hypothesis (the text's "Cook's reduction applied to
the witness" is a Levin reduction, never defined there).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added — the first and
third conjuncts are instances of `LevinReduction.efficientProverProofErr`, and without it
the reduction `id`, `w x y := []` of `(3COL, ∅)` to `(3COL, R_3COL)` refutes them on the
2-vertex one-edge graph (the pulled-back prover commits to the constant colouring
`decColoring n [] = 0` and opens two equal colours). -/
theorem zk_proof_of_levinReduction {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  ⟨h.efficientProverProof hLR (colRep_efficientProverProof hC), h.zk (col_zk hC),
    h.efficientProverProofErr hLR (col_efficientProverProofErr hC)⟩

/-- **[PS10, Theorem 124.1]: if one-way permutations (with a hard-core predicate) exist, every
language with a Levin reduction to `3COL` has a zero-knowledge proof** (Thm-124.1, headline):
for `L ⊆ witnessLanguage R` (`hLR`) there is a protocol that is an interactive proof for `L`
with efficient prover w.r.t. `R`, and a protocol that is zero-knowledge for `R` and an
interactive proof with efficient prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` —
the commitment scheme of [PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged
into `zk_proof_of_levinReduction`.

**Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`zk_proof_of_levinReduction`). -/
theorem zk_proof_of_owp_levinReduction
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
  exact ⟨⟨_, h1⟩, _, h2, h3⟩

/-- Sanity (run-3 audit P11-2): the soundness error `1 - 1/k + (1/2)^k` of the one-iteration
protocols is strictly below `1` for `k ≥ 1`, since `k < 2^k` (`Nat.lt_two_pow_self`). Hence
`EfficientProverProofErr π L R (fun N => 1 - 1/(p N) + (1/2)^{p N})` with `p N ≥ N ≥ 1`
asserts genuine soundness: the verifier rejects every `x ∉ L` with probability at least
`1/p(|x|) - 2^{-p(|x|)} > 0`. -/
theorem one_sub_inv_add_half_pow_lt_one {k : ℕ} (hk : 0 < k) :
    1 - 1 / (k : ℝ) + (1 / 2 : ℝ) ^ k < 1 := by
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hlt
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [one_div_pow]
  have h4 : 1 / (2 : ℝ) ^ k < 1 / (k : ℝ) := one_div_lt_one_div_of_lt hkpos h2
  linarith

/-- NP-hardness with Levin reductions [PS10, §4.7, Theorem 124.1, step 2, the implicit
hypothesis] (Claim-124.b/c as a hypothesis): every language with a witness relation Levin-reduces
to `(L', R')`. The string-level Levin reduction `3SAT → 3COL` that would establish
`LevinNPHard L3COL R3COL` is not formalized (plan decision on Theorem 124.1). -/
def LevinNPHard (L' : Language Bool) (R' : List Bool → List Bool → Prop) : Prop :=
  ∀ (L : Language Bool) (R : List Bool → List Bool → Prop), WitnessRelation L R →
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L' R R' f w p

/-- **[PS10, Theorem 124.1], "every language in NP"**, under NP-hardness of `3COL` with Levin
reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
`L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
for `R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`).

**Repair (run-3 audit P11-2):** the run-2 conclusion `∃ s, EfficientProverProofErr π L R s`
asserted no soundness (`s := 1` turns the clause into `0 ≤ uprob …`, so it followed from the
parties' efficiency and completeness alone); the explicit error of the Levin reduction's
length polynomial is kept, together with `∀ N, N ≤ p.eval N`, so that the error is below `1`
by the noticeable margin `1/p(N) - 2^{-p(N)}` (`one_sub_inv_add_half_pow_lt_one`). -/
theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool}
    {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
  obtain ⟨f, w, p, h⟩ := h3 L R hR
  obtain ⟨h1, h2, h3'⟩ := zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx
  exact ⟨R, hR, ⟨_, h1⟩, _, p, h.le_eval, h2, h3'⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof"**, under NP-hardness of `3COL` with Levin reductions and with the
hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
of the Levin reduction's length polynomial `p ≥ id`.

**Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). -/
theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  exact zk_proof_of_mem_NP h3 hC hL

end TCSlib.Cryptography
