## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03f1-pack.md =====

# Gate 03f1 ([PS10] ch. 2–4, discrete log, its hard-core bit, ElGamal): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/f1/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the discrete-log candidate (the assumption
and the collection), its hard-core bit, ElGamal, and the concrete samplers they use.
- **This pack gates fills.** Its files hold **21 `sorry`s**. By the user's ruling of 2026-11-05 they
  will be filled after this pack closes, discrete log first, because ch. 5–8 cites the DL candidate
  (Thm 142.3). A statement that cannot be proved as stated, or that is weaker than the source,
  must be found **now**, before anyone tries to fill it.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03f1-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs:
- §2.8 (book pp. 52–53);
- §3.4.1 (pp. 82–86);
- §3.11 (pp. 105–107);
- Claim 36.2 (p. 36);
- Claim 62.2 (p. 62).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also:
- For **every sorried declaration**, say whether it is (a) true as stated and provable from the
  hypotheses it carries, (b) true but stated more weakly than the source, or (c) false or
  unprovable as stated. For (c), give a counterexample or the missing hypothesis.
- The candidates are stated under an explicit hypothesis bundle for polynomial-time arithmetic
  (`Candidates/Arithmetic.lean`, decision D11; pack 03b audits the bundle itself). Say where a
  statement needs a field the bundle lacks.

Attempt at least **three adversarial instantiations**, for example:
- a group generator whose "generator" is the identity with non-negligible probability;
- a DDH instance whose exponents are not uniform;
- a hard-core-bit predictor that uses its advice to know the group.

Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | `Candidates/Arithmetic.lean` (pack 03b); the files of packs 03a–03d, which these statements use |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Asm-52.2, Thm-52.3, Claim-53.2, Claim-36.2, Claim-62.2; `inventory-ch3.md`: Constr-82.b, Lem-84.1 (with .0, .1, .3, .4, .5), Alg-84.2, Alg-85.a, Asm-105.1, NT-105.a, Claim-106.a, Claim-106.b, Alg-106.2, Claim-107.a, Thm-107.3, Def-107.b |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` (P8-1, the DDH ensembles, was a run-3a blocker: check its repair) |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the factoring-based candidates (pack 03f2) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/f1/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 333 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   43 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 24 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 9 use only the standard axioms, and
   15 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 21 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines;
- **admissions:** the 21 `sorry`s, listed by declaration:
  - `DiscreteLog`: 6;
  - `DiscreteLogHardcore`: 7;
  - `ElGamal`: 7;
  - `Concrete`: 1;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Candidates.ExpGroupGen` and
  `Candidates.DLAssumption`.

## Specific questions

1. **The DL assumption and collection (Asm 52.2, Thm 52.3).**
   - Is `DLAssumption` the source's assumption: the group (a safe-prime subgroup), the generator
     and the exponent sampled as stated, and inversion negligible for every n.u.p.p.t. adversary?
   - Is the validity bridge of `expCollection` (the generator output `dlDefaultIndex` below `n₀`, a
     run-3a repair) benign?
2. **The samplers** (`expSampler_spec`, `statClose_sampleBelowL`, `Concrete.lean`'s rejection
   sampler). Are the claimed closeness bounds negligible at the stated parameters, and are the
   specifications what the collection needs?
3. **The hard-core bit of DL (§3.4.1, Lem 84.1).**
   - Is the "half" predicate, with its inverter reduction (Algs 84.2 and 85.a), stated with the
     right advantage loss?
   - Lemma 84.1's generator is restricted to `p ≡ 3 (mod 4)` (open question 3 of Frederick's
     plan). Is that restriction declared, and is it benign?
4. **ElGamal (Asm 105.1, Alg 106.2, Thm 107.3).**
   - Is DDH stated on the right group with uniform exponents, and is P8-1's repair right?
   - Is the message space `G_q` handled as the source requires?
   - Is the encryption correct (`elGamal_correct`) for every message?
   - Is the security statement `elGamal_secure` the source's CPA security?
5. **Claim 107.a** (squaring a uniform unit is uniform on `G_q`, a generator unless it is `1`). Is
   `statClose_sq_generator` the claim, at the right distance?

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f1/replay.log =====

# closure of pack 03f1's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 333 modules, extracted from g03-replay.log
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
TCSlib/Cryptography/Asymptotic/OneWay rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 14s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 138s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 26s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 11s errors=0 sorry=1
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 12s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 11s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 10s errors=0 sorry=7
TCSlib/Cryptography/Foundations/Experiments rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 17s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/QuadraticResidues rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Units rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Generators rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0
TCSlib/Programs/Compat rc=0 3s errors=0 sorry=0
TCSlib/Programs/Util/List rc=0 9s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f1/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03f1's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.expF_injective: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.expCollection_sampleClose: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.expCollection_invProbAt_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.expCollection_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.dlCollection_oneWay: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.invProb_dlInverter_ge: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.fullDLCollection_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.fullDLCollection_hardCore: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.statClose_sq_generator: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.elGamal_correct: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.elGamal_secure: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.expSampler_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rejectBlocksL_spec: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.statClose_rejectBlocksL: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.listToNat_addStr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_subStr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.ddhExpo_statClose: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.statClose_sampleBelowL: propext,  sorryAx,  Classical.choice,  Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f1/admissions.txt =====

# declarations with `sorry` in pack 03f1's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib/Cryptography/Candidates/DiscreteLog.lean:488 TCSlib.Cryptography.Candidates.statClose_sampleBelowL
TCSlib/Cryptography/Candidates/DiscreteLog.lean:511 TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw
TCSlib/Cryptography/Candidates/DiscreteLog.lean:538 TCSlib.Cryptography.Candidates.expSampler_spec
TCSlib/Cryptography/Candidates/DiscreteLog.lean:606 TCSlib.Cryptography.Candidates.expCollection_sampleClose
TCSlib/Cryptography/Candidates/DiscreteLog.lean:623 TCSlib.Cryptography.Candidates.expCollection_invProbAt_le
TCSlib/Cryptography/Candidates/DiscreteLog.lean:635 TCSlib.Cryptography.Candidates.expCollection_oneWay
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:319 TCSlib.Cryptography.Candidates.dlBits_pow
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:357 TCSlib.Cryptography.Candidates.uprob_trial_ge
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:380 TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:408 TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:435 TCSlib.Cryptography.Candidates.invProb_dlInverter_ge
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:526 TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean:580 TCSlib.Cryptography.Candidates.fullDLCollection_hardCore
TCSlib/Cryptography/Candidates/ElGamal.lean:220 TCSlib.Cryptography.Candidates.statClose_sq_generator
TCSlib/Cryptography/Candidates/ElGamal.lean:515 TCSlib.Cryptography.Candidates.polyTimeComputable_egGenRaw
TCSlib/Cryptography/Candidates/ElGamal.lean:565 TCSlib.Cryptography.Candidates.polyTimeComputable_egEncRaw
TCSlib/Cryptography/Candidates/ElGamal.lean:626 TCSlib.Cryptography.Candidates.egDecStr_apply
TCSlib/Cryptography/Candidates/ElGamal.lean:662 TCSlib.Cryptography.Candidates.elGamal_correct
TCSlib/Cryptography/Candidates/ElGamal.lean:746 TCSlib.Cryptography.Candidates.polyTimeComputable_egGroupGenRaw
TCSlib/Cryptography/Candidates/ElGamal.lean:885 TCSlib.Cryptography.Candidates.elGamal_secure
TCSlib/Cryptography/Candidates/Concrete.lean:523 TCSlib.Cryptography.Candidates.statClose_rejectBlocksL

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f1/lint.log =====

# scripts/style_lint.py on pack 03f1's files, at a3c5fa8b72e50939822f22364647dc844a3914a0






0 findings in 5 files

## ===== TCSlib/Cryptography/Candidates/DiscreteLog.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm assumption and the discrete-logarithm collection

The discrete-logarithm material of [PS10, §2.8]: the *discrete-log assumption* for a family
of prime-order groups [PS10, Assumption 52.2] and the collection
`DL = {f_{q,g}(x) = g^x : Z_q → G_q}` with indices `(q, g)`, which is a collection of
one-way functions under that assumption [PS10, Theorem 52.3].

**The groups.** Following the text's own instantiation (p. 52, "one usually picks a prime of
the form `p = 2q + 1` … and then sets `G` to be the subgroup of squares in `Z_p^*`"), the
prime-order group `G_q` is the subgroup of squares of `Z_p^* = (ZMod p)ˣ` for a *safe prime*
`p = 2q + 1`. A group instance is the string index `⟨p, ⟨m, g⟩⟩` of three `n`-bit numerals:
the prime `p`, the order `m` of the group generated by `g` (the domain of the exponentiation
is `Z_m`), and the generator `g` (`ExpValid`: `orderOf g = m` in `Z_p`). The same index
format serves the full-group collection of `TCSlib.Cryptography.Candidates.DiscreteLogHardcore`
(`m = p − 1`, `g` a generator of `Z_p^*`, [PS10, Lemma 84.1]) and the El Gamal keys of
`TCSlib.Cryptography.Candidates.ElGamal`, so the exponentiation collection is built once,
generically over a validity predicate `V` on indices: `expCollection`.

**The sampler of instances.** The text samples `q ← Π_n; g ← Gen_{G_q}` and notes (p. 52–53)
that no efficient procedure for safe primes is known. Foundation decision D10 and the
deviation register (#15) replace the ideal sampler by an explicit *instance generator*
`ExpGroupGen V`: a PPT `Gen(1^n)` whose outputs, from a threshold `n₀` on, are valid indices
of three `n`-bit numerals. The assumption and the theorems are relative to the generator;
every statement about machines is conditional on the arithmetic bundle `ArithmeticFP` (D11).
Below the threshold the collection's own generator `expGen` outputs the fixed valid instance
`dlDefaultIndex = ⟨3, ⟨2, 2⟩⟩`, so that every generated index is valid and the sampler's
outputs decode at every parameter (`Collection.sample_spec`, run-3 audit P3-1); the
collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀ i, V i → ExpValid i`
as an argument.

**Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
the `1/q` term of Theorem 107.3) the prime must have full length `2^{n−1} ≤ p`. This is
demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
`Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
would require a deterministic polynomial-time construction of full-length primes of the
required form, which is not known (run-3 audit P8-2). The rejection sampler of numbers below
`m` (`sampleBelowL`) is within `(1/2)^n` of uniform (`statClose_sampleBelowL`, D10), the
closeness fact shared by the collection's domain sampler and the El Gamal samplers.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the adversary of Assumption 52.2 receives `⟨1^n, ⟨i, g^x⟩⟩`
with the whole index `i = ⟨p, ⟨q, g⟩⟩` (the text passes `g^x` only, source error 8), the
exponent `x ← Z_q` is ideal uniform in the experiment while the honest domain sampler is a
truncated rejection sampler within `2^{-n}` of uniform (D10), the answer is read as an
`n`-bit numeral (wrong length = failure, D5), "`Pr[…] < ε(n)` for a negligible `ε`" is
"`Pr[…]` is negligible", and the ideal "`q ← Π_n; g ← Gen_{G_q}`" is the law of the instance
generator. Theorem 52.3's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and `k` as `n`.

## Main definitions

* `TCSlib.Cryptography.Candidates.dlP`, `dlM`, `dlG`, `dlW`, `WellFormedIndex` — reading the
  index `⟨p, ⟨m, g⟩⟩`; `TCSlib.Cryptography.Candidates.ExpValid` — valid indices.
* `TCSlib.Cryptography.Candidates.expOrd`, `expEnc`, `expDec`, `expF`, `expEval` — the
  domain `Z_m`, its encoding, the function `x ↦ g^x mod p` and its evaluator.
* `TCSlib.Cryptography.Candidates.ExpGroupGen` — instance generators;
  `ExpGroupGen.dlProb`, `ExpGroupGen.DLHard` — the discrete-log experiment and hardness;
  `ExpGroupGen.FullLength`, `ExpGroupGen.FullLengthExcept` — full-length primes (on every
  coin string / except on a set of coins of probability `δ n`).
* `TCSlib.Cryptography.Candidates.sampleBelowL`, `expSampler`, `dlDefaultIndex`, `expGen`,
  `expCollection` — the exponentiation collection of an instance generator.
* `TCSlib.Cryptography.Candidates.SafePrimeValid`, `SafePrimeGen`,
  `TCSlib.Cryptography.Candidates.DLAssumption` — [PS10, Assumption 52.2];
  `TCSlib.Cryptography.Candidates.dlCollection` — the collection `DL` [PS10, Theorem 52.3].

## Main results

* `TCSlib.Cryptography.Candidates.expF_injective` — `x ↦ g^x` is injective on `Z_m` at a
  valid index (the remark after [PS10, Theorem 52.3]; Claim-53.2 of the inventory, proved).
* `TCSlib.Cryptography.Candidates.expEval_spec`, `expDec_expEnc` — the collection data
  (proved).
* `TCSlib.Cryptography.Candidates.statClose_sampleBelowL` — the rejection sampler of numbers
  below `m` is within `(1/2)^n` of uniform (D10);
  `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept` —
  full length on every coin string is the `δ = 0` case (proved).
* `TCSlib.Cryptography.Candidates.expCollection_invProbAt_le` — inverting the collection is
  the discrete-log experiment; `expCollection_sampleClose`, `expCollection_oneWay`.
* `TCSlib.Cryptography.Candidates.dlCollection_oneWay` — [PS10, Theorem 52.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.8: Definition 52.1, Assumption 52.2, Theorem 52.3 and the remarks on pp. 52–53.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Group instances `⟨p, ⟨m, g⟩⟩` -/

/-- The prime `p` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlP (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The group order `m` read from the index `⟨p, ⟨m, g⟩⟩` (the domain of the exponentiation
is `Z_m`; `m = q` for the prime-order groups, `m = p − 1` for `Z_p^*`). -/
def dlM (i : List Bool) : ℕ := listToNat (pairFstD (pairSndD i))

/-- The generator `g` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlG (i : List Bool) : ℕ := listToNat (pairSndD (pairSndD i))

/-- The numeral width of an index: the width of the numeral of `p` (all group elements are
encoded with this width). -/
def dlW (i : List Bool) : ℕ := (pairFstD i).length

/-- An index is *well formed at parameter `n`* when it is a pair `⟨a, ⟨b, c⟩⟩` of three
`n`-bit numerals (the text's "`p` of length `n`"). -/
def WellFormedIndex (n : ℕ) (i : List Bool) : Prop :=
  ∃ a b c : List Bool, i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n

/-- The width of a well-formed index is `n`. -/
theorem WellFormedIndex.dlW_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) : dlW i = n := by
  obtain ⟨a, b, c, rfl, ha, -, -⟩ := h
  simp [dlW, ha]

/-- A well-formed index at parameter `n` has length `5n + 4`. -/
theorem WellFormedIndex.length_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) :
    i.length = 5 * n + 4 := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h
  simp only [length_pairEncode, ha, hb, hc]
  ring

/-- `p < 2^{dlW i}`: the prime fits its numeral. -/
theorem dlP_lt_two_pow (i : List Bool) : dlP i < 2 ^ dlW i := listToNat_lt_two_pow _

/-- An index `⟨p, ⟨m, g⟩⟩` is *valid* when `p` is prime, `0 < m < p`, `0 < g < p`, and `g` has
order exactly `m` in `Z_p` (so `x ↦ g^x` is a bijection of `Z_m` onto the subgroup generated
by `g`, [PS10, Definition 52.1]). (Not efficiently decidable from the index — generators only
ever output valid indices.) -/
def ExpValid (i : List Bool) : Prop :=
  (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
    orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i

noncomputable instance : DecidablePred ExpValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The order of the domain at an index: `m` for a valid index and `1` otherwise (so that the
domain `Z_m` is always a finite group). -/
noncomputable def expOrd (i : List Bool) : ℕ := if ExpValid i then dlM i else 1

instance (i : List Bool) : NeZero (expOrd i) := by
  unfold expOrd
  split_ifs with h
  · exact ⟨h.2.1.ne'⟩
  · exact ⟨one_ne_zero⟩

/-- `expOrd` of a valid index is `m`. -/
theorem expOrd_of_valid {i : List Bool} (h : ExpValid i) : expOrd i = dlM i := if_pos h

/-- `expOrd` of an invalid index is `1`. -/
theorem expOrd_of_not_valid {i : List Bool} (h : ¬ ExpValid i) : expOrd i = 1 := if_neg h

/-- The order of the domain fits the numeral width: `expOrd i ≤ 2^{dlW i}`. -/
theorem expOrd_le_two_pow (i : List Bool) : expOrd i ≤ 2 ^ dlW i := by
  unfold expOrd
  split_ifs with h
  · exact (h.2.2.1.trans (dlP_lt_two_pow i)).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits the numeral width. -/
theorem val_lt_two_pow_dlW (i : List Bool) (x : ZMod (expOrd i)) : x.val < 2 ^ dlW i :=
  lt_of_lt_of_le (ZMod.val_lt x) (expOrd_le_two_pow i)

/-- `g` is coprime to `p` at a valid index (`0 < g < p` and `p` prime). -/
theorem coprime_dlG_dlP {i : List Bool} (h : ExpValid i) : Nat.Coprime (dlG i) (dlP i) :=
  ((Nat.Prime.coprime_iff_not_dvd h.1).2 (Nat.not_dvd_of_pos_of_lt h.2.2.2.1 h.2.2.2.2.1)).symm

/-- The generator `g` as a unit of `Z_p` at a valid index. -/
noncomputable def expUnit {i : List Bool} (h : ExpValid i) : (ZMod (dlP i))ˣ :=
  ZMod.unitOfCoprime (dlG i) (coprime_dlG_dlP h)

/-- The value of `expUnit` is `g mod p`. -/
theorem coe_expUnit {i : List Bool} (h : ExpValid i) :
    (expUnit h : ZMod (dlP i)) = ((dlG i : ℕ) : ZMod (dlP i)) := ZMod.coe_unitOfCoprime _ _

/-- The order of the unit `g` is `m` [PS10, Definition 52.1, "`g` is a generator"]. -/
theorem orderOf_expUnit {i : List Bool} (h : ExpValid i) : orderOf (expUnit h) = dlM i := by
  rw [← orderOf_units, coe_expUnit]
  exact h.2.2.2.2.2

/-! ## The domain `Z_m`, its encoding and the function `x ↦ g^x` -/

/-- The string encoding of `x ∈ Z_m`: its residue as a numeral of the index width. -/
noncomputable def expEnc (i : List Bool) (x : ZMod (expOrd i)) : List Bool := natToList (dlW i) x.val

/-- The decoder of `Z_m`: a numeral of the index width reading as a number below `m`. -/
noncomputable def expDec (i : List Bool) (w : List Bool) : Option (ZMod (expOrd i)) :=
  if w.length = dlW i ∧ listToNat w < expOrd i then some ((listToNat w : ℕ) : ZMod (expOrd i))
  else none

/-- Decoding inverts encoding (the clause `decD_encD` of `Collection`). -/
theorem expDec_expEnc (i : List Bool) (x : ZMod (expOrd i)) : expDec i (expEnc i x) = some x := by
  have hl : listToNat (expEnc i x) = x.val := listToNat_natToList (val_lt_two_pow_dlW i x)
  rw [expDec, if_pos ⟨by simp [expEnc], by rw [hl]; exact ZMod.val_lt x⟩, hl,
    ZMod.natCast_zmod_val]

/-- **The function `f_{q,g}(x) = g^x mod p`** [PS10, Theorem 52.3] as a string function on
`Z_m`: the numeral of `g^x mod p` of the index width (the evaluator `modExpStr` mirrored). -/
noncomputable def expF (i : List Bool) (x : ZMod (expOrd i)) : List Bool :=
  natToList (dlW i) (dlG i ^ x.val % dlP i)

/-- The evaluator of the exponentiation collection on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: one modular
exponentiation `modExpStr ⟨g, ⟨x, p⟩⟩` [PS10, Theorem 52.3, "it is easy to evaluate"]. -/
def expEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (pairSndD (pairFstD z)))
    (pairEncode (pairSndD z) (pairFstD (pairFstD z))))

/-- The evaluator computes `expF` on encoded elements. -/
theorem expEval_spec (i : List Bool) (x : ZMod (expOrd i)) :
    expEval (pairEncode i (expEnc i x)) = expF i x := by
  have hl : listToNat (natToList (dlW i) x.val) = x.val :=
    listToNat_natToList (val_lt_two_pow_dlW i x)
  simp only [expEval, expF, expEnc, dlG, dlP, dlW, pairFstD_pairEncode, pairSndD_pairEncode,
    modExpStr_pairEncode] at hl ⊢
  rw [hl]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_expEval (H : ArithmeticFP) : PolyTimeComputable expEval :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    polyTimeComputable_pairFstD)).pairEncode (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- **`x ↦ g^x` is injective on `Z_m`** at a valid index (the remark after
[PS10, Theorem 52.3]: "each function is a permutation"; Claim-53.2 of the inventory): since
`g` has order `m` in `Z_p`, `g^a = g^b` forces `a ≡ b (mod m)`.

**Proof sketch.** Both numerals have width `dlW i` and read as numbers below `p < 2^{dlW i}`
(`natToList_injOn`), so `g^a ≡ g^b (mod p)`; in the group of units, `pow_eq_pow_iff_modEq`
with `orderOf_expUnit` gives `a ≡ b (mod m)`, and `a, b < m`. -/
theorem expF_injective {i : List Bool} (h : ExpValid i) : Function.Injective (expF i) := by
  intro x y hxy
  have hlt : ∀ e : ℕ, dlG i ^ e % dlP i < 2 ^ dlW i :=
    fun e => (Nat.mod_lt _ h.1.pos).trans (dlP_lt_two_pow i)
  have h1 : dlG i ^ x.val % dlP i = dlG i ^ y.val % dlP i := natToList_injOn (hlt _) (hlt _) hxy
  have h2 : expUnit h ^ x.val = expUnit h ^ y.val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_expUnit, ← Nat.cast_pow,
      ← Nat.cast_pow, ← ZMod.natCast_mod, h1, ZMod.natCast_mod]
  have h3 := pow_eq_pow_iff_modEq.1 h2
  rw [orderOf_expUnit h] at h3
  have hx : x.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt x) (expOrd_of_valid h)
  have hy : y.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt y) (expOrd_of_valid h)
  apply ZMod.val_injective
  unfold Nat.ModEq at h3
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h3

/-! ## Instance generators and the discrete-log experiment -/

/-- An **instance generator** for exponentiation collections with validity predicate `V`:
a PPT `Gen(1^n)` whose outputs, from the threshold `n₀` on, satisfy `V` and are well-formed
indices of three `n`-bit numerals. The formal counterpart of the text's
"`q ← Π_n; g ← Gen_{G_q}`" [PS10, Assumption 52.2] and "pick a safe prime `p = 2q + 1` of
length `n`" [PS10, Algorithm 106.2]; the text itself notes (pp. 52–53) that no efficient
sampler of safe primes with generators is known, so the generator is a hypothesis object.

**Deviation:** the ideal samplers of the text are replaced by a PPT generator relative to
which the assumptions are stated (D10, deviations register #15); outputs below `n₀` are
unconstrained (the degenerate parameters). -/
structure ExpGroupGen (V : List Bool → Prop) where
  /-- The generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The threshold from which the outputs are valid. -/
  n₀ : ℕ
  /-- Outputs are valid from the threshold on. -/
  valid : ∀ n (r : gen.Coins n), n₀ ≤ n → V (gen.runAt n [] r)
  /-- Outputs are well-formed indices of `n`-bit numerals from the threshold on. -/
  wellFormed : ∀ n (r : gen.Coins n), n₀ ≤ n → WellFormedIndex n (gen.runAt n [] r)

namespace ExpGroupGen

variable {V : List Bool → Prop} (G : ExpGroupGen V)

/-- The generator outputs primes of *full length* `n` on **every** coin string: `2^{n-1} ≤ p`
at every generated index from `n₀` on (the text's "`p` of length `n`" read with a leading
`1`; `p < 2^n` already follows from `wellFormed`). Too strong as a hypothesis of a theorem
(see `FullLengthExcept`, run-3 audit P8-2): together with `valid` it asks for a deterministic
polynomial-time construction (run the generator on the all-zero coins) of a full-length prime
of the required form at every `n ≥ n₀`, which is not known. Kept as the deterministic
special case (`FullLength.fullLengthExcept`). -/
def FullLength : Prop :=
  ∀ n (r : G.gen.Coins n), G.n₀ ≤ n → 2 ^ (n - 1) ≤ dlP (G.gen.runAt n [] r)

/-- The generator outputs primes of full length `n` **except on a set of coins of probability
at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
rejection sampler, D10). Needed, with `Negligible δ`, where the proofs divide by `q` or
`p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
are discarded and contribute at most `δ n`. Whether safe primes (resp. primes `≡ 3 (mod 4)`
with a generator) of full length can be produced for every `n` except with negligible
probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
records this.

Repair (run-3 audit P8-2): replaces the hypothesis `G.FullLength` of
`fullDLCollection_hardCore` and `elGamal_secure`, which demanded `2^{n−1} ≤ p` on every coin
string and made `{G // G.FullLength}` not known to be inhabited for reasons unrelated to any
cryptographic assumption (contrary to D10 / deviation 15, strict PPT with `2^{-n}` failure). -/
def FullLengthExcept (δ : ℕ → ℝ) : Prop :=
  ∀ n, G.n₀ ≤ n → uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n

/-- **The discrete-log experiment** [PS10, Assumption 52.2]:
`Pr[i ← Gen(1^n); x ← Z_m : A(1^n, ⟨i, g^x⟩) = x]`, the average over the generator's coins
of the probability, over the ideal uniform `x ∈ Z_m` and the coins of `A`, that the answer of
`A` decodes to an `n`-bit numeral reading as `x`.

**Deviation:** `A` receives `1^n` and the index (the text's `A(g^x)`); ideal uniform `x`;
`n`-bit answers (module docstring). -/
noncomputable def dlProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : G.gen.Coins n =>
    uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
      ∃ x : Fin n → Bool,
        decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val

/-- **Discrete-log hardness relative to the generator**: every non-uniform PPT solves the
discrete-log experiment with negligible probability. The safe-prime instance is
[PS10, Assumption 52.2] (`DLAssumption`); the full-group instance is the assumption of
[PS10, Lemma 84.1] (`DiscreteLogHardcore`). -/
def DLHard : Prop := ∀ A : NUPPT, Negligible fun n => G.dlProb A n

/-- The discrete-log probability is nonnegative. -/
theorem dlProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ G.dlProb A n := by
  unfold dlProb uexp
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The discrete-log probability is at most one. -/
theorem dlProb_le_one (A : NUPPT) (n : ℕ) : G.dlProb A n ≤ 1 := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  unfold dlProb
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end ExpGroupGen

/-- Full length on every coin string is full length except on a set of probability `0`. -/
theorem ExpGroupGen.FullLength.fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : G.FullLengthExcept fun _ => 0 := by
  intro n hn
  have hz : uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) = 0 := by
    rw [← uprob_false (α := G.gen.Coins n)]
    exact OneWay.uprob_congr fun r => ⟨fun hlt => (not_le.mpr hlt (h n r hn)).elim, False.elim⟩
  exact hz.le

/-- A generator of full length on every coin string satisfies the hypothesis
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems (with `δ = 0`). -/
theorem ExpGroupGen.FullLength.exists_fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ := by
  refine ⟨fun _ => 0, fun c => ⟨1, fun n hn => ?_⟩, h.fullLengthExcept⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-! ## The exponentiation collection of an instance generator -/

/-- The fixed valid instance `⟨p, ⟨m, g⟩⟩ = ⟨3, ⟨2, 2⟩⟩` with `2`-bit numerals (`2` has order
`2` in `Z_3`): the index output by the collection's generator below the threshold `n₀` of the
instance generator, where the latter's outputs are unconstrained.

Repair (run-3 audit P3-1): `Collection.sample_spec` requires the sampler's outputs to decode
at *every* generated index, so the collection's generator must output valid indices at every
parameter. -/
def dlDefaultIndex : List Bool :=
  pairEncode (natToList 2 3) (pairEncode (natToList 2 2) (natToList 2 2))

/-- The default index is valid: `3` is prime, `0 < 2 < 3`, and `2` has order `2` in `Z_3`. -/
theorem expValid_dlDefaultIndex : ExpValid dlDefaultIndex := by
  have h3 : dlP dlDefaultIndex = 3 := by
    simp [dlP, dlDefaultIndex, listToNat_natToList (by norm_num : 3 < 2 ^ 2)]
  have h2 : dlM dlDefaultIndex = 2 := by
    simp [dlM, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  have hg : dlG dlDefaultIndex = 2 := by
    simp [dlG, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact Nat.prime_three
  · rw [h2]; norm_num
  · rw [h2, h3]; norm_num
  · rw [hg]; norm_num
  · rw [hg, h3]; norm_num
  · rw [hg, h2, h3]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)

/-- The string function of the collection's index generator on the raw layout
`⟨⟨⟨1^n, []⟩, α⟩, r⟩`: `⟨Gen(1^n; r), []⟩` (no trapdoor) from the threshold `n₀` on, and
`⟨dlDefaultIndex, []⟩` below it (where the instance generator's outputs are unconstrained;
run-3 audit P3-1). -/
def expGenFun {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  if G.n₀ ≤ (NUPPT.inParam z).length then
    pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
  else pairEncode dlDefaultIndex []

/-- The index generator's string function is polynomial-time: the threshold test compares
the length of `1^n` with the constant `1^{n₀}` (`polyTimeComputable_lenLe`), then
`polyTimeComputable_ite` between the instance generator's output and a constant. -/
theorem expGenFun_poly {V : List Bool → Prop} (G : ExpGroupGen V) : PolyTimeComputable (expGenFun G) := by
  have hp : PolyTimeComputable fun z => [decide (G.n₀ ≤ (NUPPT.inParam z).length)] := by
    have h := polyTimeComputable_lenLe.comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const (List.replicate G.n₀ true)))
    convert h using 1
    funext z
    simp [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]
  have hf : PolyTimeComputable fun z =>
      pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) [] :=
    (G.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)).pairEncode (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp hf (polyTimeComputable_const (pairEncode dlDefaultIndex []))
  convert h using 1
  funext z
  simp only [expGenFun, decide_eq_true_eq]

/-- The index generator of the collection: `Gen(1^n) = ⟨i, []⟩` with `i` the output of the
instance generator (from `n₀` on; `dlDefaultIndex` below), same coins. -/
noncomputable def expGen {V : List Bool → Prop} (G : ExpGroupGen V) : NUPPT :=
  NUPPT.ofPolyTimeUniform (expGenFun_poly G) G.gen.coins

/-- The activation of the collection's generator: `⟨Gen(1^n; r), []⟩` for `n ≥ n₀`,
`⟨dlDefaultIndex, []⟩` below. -/
theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n) :
    (expGen G).runAt n [] r =
      if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] r) [] else pairEncode dlDefaultIndex [] := by
  rw [NUPPT.runAt_eq]
  unfold expGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [expGenFun, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAt_eq G.gen_uniform]

/-- **Rejection sampling of a number below `m`** from a coin list: `T` trials, trial `t`
reading the first `k` bits of the `t`-th block of `B` bits as a number `v`, accepted iff
`v < m`; `none` if every trial is rejected. With `k` the bit length of `m` the acceptance rate
is `m / 2^k ≥ 1/2` [PS10, Theorem 52.3, "it is easy to sample the domain `D_i`"]. -/
def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- A sampled value is below `m`. -/
theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
    v < m := by
  unfold sampleBelowL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  exact ht ▸ hc

/-- **The rejection sampler is close to uniform** (D10; lemma C4 of the Chapter 2 inventory for
`sampleBelowL`): for `0 < m < 2^n`, `n` trials reading `k = Nat.size m` bits from each of `n`
blocks of `n` uniform coins, with the fallback `0`, output a number within statistical
distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
`expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
`ddhExpo`).

**Proof sketch.** `k ≤ n` by `Nat.size_le`, so trial `t < n` reads the first `k` bits of the
`t`-th block of `n` bits of `List.ofFn b` (`NumberTheory.chunk`; `List.drop`/`List.take` of
`List.ofFn`), and `sampleBelowL m k n n` is `firstHit (· < m)` of the numbers read from the
blocks (`List.findSome?` over `List.range n` versus `List.finRange n`; `listToNat` of the `k`
bits is `bitsToNat` of the block's prefix, `bitsToNat_eq_listToNat`). The map from the `n · n`
coins to the `n` prefixes is a product of coordinate projections, so it pushes the uniform
distribution to the uniform one on `Fin n → Fin k → Bool` (`StatClose.comp_pushesUniform`),
and reading bits is the bijection `bitsEquiv k` onto `Fin (2^k)`; `statClose_firstHit` with
`E = {x < m}` and `d = 0` gives closeness `(1 − m/2^k)^n ≤ (1/2)^n` (`Nat.lt_size_self`:
`m/2^k ≥ 1/2`), transported along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` by
`StatClose.comp_equiv_right` and `StatClose.map` (`Fin.val`), exactly as in
`statClose_rejectionSample`. -/
theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
    StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
      (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  sorry

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`: a number
below the order `m` read from the index, by rejection over `n` trials of `n`-bit blocks
(reading the bit length of `m` from each block), written as a numeral of the index width;
the fallback `0` on failure. -/
def expSampleRaw (z : List Bool) : List Bool :=
  natToList (dlW (NUPPT.inArg z))
    ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
      (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0)

/-- **The domain sampler is polynomial-time** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"] given the arithmetic bundle.

**Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
leading zeros stripped (requested shared primitive, as in the RSA sampler); the trial loop is
`Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
(`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
(`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
is padded to the index width (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_expSampleRaw (H : ArithmeticFP) : PolyTimeComputable expSampleRaw := by
  sorry

/-- **The domain sampler** of the exponentiation collection: a uniform `NUPPT` with `n · n`
coins. -/
noncomputable def expSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_expSampleRaw H) (.mul .var .var)

/-- The activation of the domain sampler on the index `i`. -/
theorem expSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool) (s : (expSampler H).Coins n) :
    (expSampler H).runAt n i s =
      natToList (dlW i) ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0) := by
  rw [NUPPT.runAt_eq]
  unfold expSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [expSampleRaw, NUPPT.inArg, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- **The domain sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is valid — `hV` with `G.valid` from `n₀` on, `expValid_dlDefaultIndex`
below (`expGen_runAt`) — so the domain is `Z_m` with `0 < m < p < 2^{dlW i}`
(`expOrd_of_valid`, `dlP_lt_two_pow`); the sampler outputs `natToList (dlW i) v` with `v < m`
(`expSampler_runAt`, `sampleBelowL_lt`, or the fallback `0`), which `expDec` reads back
(`length_natToList`, `listToNat_natToList`) as `x = (v : Z_m)` with `expEnc i x` the same
numeral (`ZMod.val_natCast`, `Nat.mod_eq_of_lt`); `expEval_spec` gives the evaluator clause.

**Proof sketch.** Case split on `G.n₀ ≤ n` in `expGen_runAt`, then the computation above. -/
theorem expSampler_spec {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expGen G).Coins n) (s : (expSampler H).Coins n) :
    ∃ x, expDec (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s) = some x ∧
      expEval (pairEncode (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s)) = expF _ x := by
  sorry

/-- **The exponentiation collection of an instance generator**: indices `⟨p, ⟨m, g⟩⟩`,
domains `D_i = Z_m` (valid indices; `Z_1` otherwise), `f_i(x) = g^x mod p`, the generator
`expGen G` (the instance generator from `n₀` on, `dlDefaultIndex` below), the sampler
`expSampler H` and the evaluator `expEval` (one modular exponentiation); the validity bridge
`hV` makes every generated index valid, so that the sampler's outputs decode
(`expSampler_spec`, run-3 audit P3-1). The collection `DL` of [PS10, Theorem 52.3] is the
safe-prime instance `dlCollection`; the full-group collection of [PS10, Lemma 84.1] is the
instance of `DiscreteLogHardcore`. -/
noncomputable def expCollection {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : Collection where
  D i := ZMod (expOrd i)
  encD := expEnc
  decD := expDec
  decD_encD := expDec_expEnc
  f := expF
  gen := expGen G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := expSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := expEval
  eval_poly := polyTimeComputable_expEval H
  eval_spec := expEval_spec
  sample_spec := expSampler_spec H G hV

/-- The index generated by the exponentiation collection from `n₀` on is the instance
generator's output. -/
theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : G.n₀ ≤ n) :
    (expCollection H G hV).index n r = G.gen.runAt n [] r := by
  show pairFstD ((expGen G).runAt n [] r) = _
  rw [expGen_runAt, if_pos hn, pairFstD_pairEncode]

/-- The index generated by the exponentiation collection below `n₀` is the default index. -/
theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : G.gen.Coins n) (hn : n < G.n₀) :
    (expCollection H G hV).index n r = dlDefaultIndex := by
  show pairFstD ((expGen G).runAt n [] r) = _
  rw [expGen_runAt, if_neg (not_le.mpr hn), pairFstD_pairEncode]

/-- The domain of the exponentiation collection at an index is `Z_{expOrd i}`. -/
theorem expCollection_D {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i = ZMod (expOrd i) := rfl

/-- **The domain sampler is close to uniform** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"]: the decoded output of `expSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_m`.

**Proof sketch.** Take `δ n := 1` for `n < n₀` and `δ n := (1/2)^n` for `n ≥ n₀`. At a
generated index `i` (`expCollection_index`, valid by `hV ∘ G.valid`, well formed with
`dlW i = n`) the sampler outputs `natToList n (sampleBelowL m k n n r).getD 0` with
`m = dlM i = expOrd i` (`expSampler_runAt`, `expOrd_of_valid`) and `k = Nat.size m ≤ n`
(`Nat.size_le`, `m < p < 2^n`): `n` trials each reading `k` uniform bits of a block of the
coins (`uprob_comp_equiv` on the block decomposition `NumberTheory.chunk`), accepted iff the
value is below `m`; `sampleBelowL` is `firstHit (· < m)` of the numbers read from the blocks
(`List.findSome?` over `List.range`), so `statClose_sampleBelowL` (`statClose_firstHit` on
`Fin (2^k)` transported along `bitsEquiv`) gives closeness `(1 - m/2^k)^n ≤ (1/2)^n`
(`Nat.lt_size_self`: `m/2^k ≥ 1/2`), and the decoder `expDec` reads the numeral back exactly
(`listToNat_natToList`, `StatClose.map`, `ZMod.natCast_zmod_val`). Negligibility by
`negligible_two_pow_neg` and `Negligible.mono`. -/
theorem expCollection_sampleClose {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (expCollection H G hV).SampleClose δ := by
  sorry

/-- **Inverting the collection is the discrete-log experiment** [PS10, proof of Theorem 52.3,
"the discrete log assumption implies that `f_{p,g}` is hard to invert"]: for `n ≥ n₀`, the
inversion probability of `A` against the exponentiation collection is at most its
discrete-log probability (the same machine, no reduction needed).

**Proof sketch.** Unfold both averages over the generator's coins (`OneWay.uexp_mono`) and
fix `r`; the index `i = Gen(1^n; r)` is valid and well formed (`hV`, `G.valid`,
`G.wellFormed`, `dlW i = n`). If `A`'s answer `w` decodes under `expDec` to `x'` with
`expF i x' = expF i x`, then `x' = x` (`expF_injective`), `w.length = n` and
`listToNat w = x.val`, so `decodeFin n w = some x''` with `bitsToNat x'' = listToNat w = x.val`
(`decodeFin`, `bitsToNat_eq_listToNat`, `List.ofFn_get`); `uprob_mono` with the coin types
identified (`expCollection_index`). -/
theorem expCollection_invProbAt_le {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) {n : ℕ} (hn : G.n₀ ≤ n) :
    (expCollection H G hV).invProbAt A n ≤ G.dlProb A n := by
  sorry

/-- **The exponentiation collection is one-way under discrete-log hardness** (the generic
form of [PS10, Theorem 52.3]).

**Proof sketch.** The sampling clause is `expCollection_sampleClose H G hV`. For the
hardness clause fix `A`: `expCollection_invProbAt_le H G hV A` bounds the inversion
probability by `G.dlProb A n` for `n ≥ n₀`, negligible by `hG A`; conclude by
`Negligible.mono` (`Collection.invProbAt_nonneg`, threshold `n₀`). -/
theorem expCollection_oneWay {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (hG : G.DLHard) : (expCollection H G hV).OneWay := by
  sorry

/-! ## Safe primes: the discrete-log assumption and the collection `DL` -/

/-- A **safe-prime instance** `⟨p, ⟨q, g⟩⟩`: a valid index whose order `q` is prime with
`p = 2q + 1`, so that `g` generates the subgroup of squares `G_q ≤ Z_p^*` of prime order `q`
[PS10, Assumption 52.2 and p. 52, "the subgroup of squares … has order `q` which is prime"]. -/
def SafePrimeValid (i : List Bool) : Prop :=
  ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1

/-- A safe-prime instance is a valid instance. -/
theorem SafePrimeValid.expValid {i : List Bool} (h : SafePrimeValid i) : ExpValid i := h.1

/-- **Safe-prime instance generators**: PPTs `Gen(1^n) = ⟨p, ⟨q, g⟩⟩` outputting safe primes
`p = 2q + 1` of length `n` with a generator `g` of the order-`q` subgroup of squares — the
formal "`q ← Π_n; g ← Gen_{G_q}`" of [PS10, Assumption 52.2] and the "`p ← Π̃_n; y ← Gen_q`"
of [PS10, Assumption 105.1]. -/
abbrev SafePrimeGen : Type 1 := ExpGroupGen SafePrimeValid

/-- **The discrete-log assumption** [PS10, Assumption 52.2] relative to a safe-prime instance
generator `G`: for every non-uniform PPT `A`,
`Pr[(p, q, g) ← Gen(1^n); x ← Z_q : A(1^n, ⟨⟨p, ⟨q, g⟩⟩, g^x⟩) = x]` is negligible.

**Deviation:** `A` receives `1^n` and the instance `(p, q, g)` (the text's `A(g^x)`, source
error 8); the group is the subgroup of squares of `Z_p^*` for a safe prime; the instance law
is the generator's (the text's ideal `q ← Π_n; g ← Gen_{G_q}` has no known efficient
sampler, p. 52); "`< ε(n)`" is "negligible" (module docstring). -/
def DLAssumption (G : SafePrimeGen) : Prop := G.DLHard

/-- Unfolding: the discrete-log assumption is the negligibility of every `dlProb`. -/
theorem dlAssumption_iff (G : SafePrimeGen) :
    DLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- **The collection `DL`** [PS10, Theorem 52.3]: indices `(q, g)` (with `p`), domains
`D_i = Z_q`, ranges `R_i = G_q`, `f_{q,g}(x) = g^x`, with the instance generator `G` as
`Gen`, the rejection sampler of `Z_q` and the modular-exponentiation evaluator.

**Deviation:** the text's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and the parameter `k` as `n`; the range `G_q` is encoded as residues modulo `p`
(`expF`). -/
noncomputable def dlCollection (H : ArithmeticFP) (G : SafePrimeGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- The index generated by `DL` from `n₀` on is the instance generator's output `⟨p, ⟨q, g⟩⟩`. -/
theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : G.gen.Coins n)
    (hn : G.n₀ ≤ n) : (dlCollection H G).index n r = G.gen.runAt n [] r :=
  expCollection_index H G _ n r hn

/-- **Theorem 52.3** [PS10, Theorem 52.3]: under the discrete-log assumption (and the
arithmetic hypotheses), `DL` is a collection of one-way functions.

**Deviation:** see `dlCollection` and the module docstring (instance generator, safe primes,
rejection-sampled domain).

**Proof sketch.** `expCollection_oneWay` with `hV := SafePrimeValid.expValid`: the sampler
is close to uniform (`expCollection_sampleClose`) and inverting the collection is the
discrete-log experiment (`expCollection_invProbAt_le`), negligible by `hDL`. -/
theorem dlCollection_oneWay (H : ArithmeticFP) (G : SafePrimeGen) (hDL : DLAssumption G) :
    (dlCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hard-core bit of the discrete logarithm

[PS10, §3.4.1]: under the discrete-log assumption, `half_{p−1}(x) = [x < (p−1)/2]` is a
hard-core predicate for the exponentiation `f_{p,g}(x) = g^x mod p` [PS10, Lemma 84.1], by the
bit-by-bit inversion of [PS10, Algorithm 84.2] with the randomized majority test of p. 85.

**The group.** The lemma, the algorithm and the proof work in the *full* group `Z_p^*` of
even order `p − 1` (the parity of the exponent is read off quadratic residuosity and
`g^{(p−1)/2} = −1`), not in the prime-order group of [PS10, Assumption 52.2]; the hypothesis is
therefore discrete-log hardness for the full-group collection (`FullDLAssumption`, the
exponentiation collection of `DiscreteLog` with `m = p − 1` and `g` a generator of `Z_p^*`),
restricted to primes `p ≡ 3 (mod 4)` so that the square roots of [PS10, Theorem 58.2] are one
modular exponentiation (decision log, open question 3).

**Two layers.** The *concrete* core (one prime `p`, one generator `g`, exact inequalities,
[Gar26]-style): the number theory behind the algorithm (`pow_half_eq_neg_one`,
`pow_mem_QR_iff`, `sq_eq_pow_two_mul_iff`, `neg_pow_eq`), the loop `dlLoop` of
Algorithm 84.2 with an oracle `O` (`dlBits` with the perfect half-oracle, `dlBits_pow`), the
majority test `majOracle` (p. 85) with its per-trial bound `uprob_trial_ge` and failure bound
`uprob_majOracle_ne_le`, the range reduction `shiftInverter` ("as we will show later", never
shown in the text) and the final inverter `dlInverter` with the bound
`invProb_dlInverter_ge`; the good-instance averaging `good_instances`. The *asymptotic*
wrapper `fullDLCollection_hardCore` packages the inverter as a non-uniform PPT.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
`Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of its own increment rule
(the counter `lo` counts *disagreements* `b_i ≠ half(r_i)`, so `noinc` is the typical event
on a low instance). Concretely: `dlLoop` follows line 11 literally (the root is kept iff `A`
answers `1` = lower half, negated on `0`); `half_m(x) := [2x < m]` is a harmless strict
variant of the text's `0 ≤ x ≤ m/2` (they differ at the single point `x = m/2`, probability
`1/(p−1)`; the strict form is *not* required by the halving invariant, since the boundary
exponent `(p−1)/2` only arises as the second root of `y = 1`, whose canonical root `dlRoot`
is `1`); the majority test `majOracle` votes on agreements and resolves the text's
inconsistency, with Chebyshev's inequality for pairwise independent trials and an explicit
number `ℓ` of trials (`HardcoreBit.uprob_majority_fails_le`, [PS10, Lemma 189.8] being
garbled); generators of `Z_p^*` are restricted to `p ≡ 3 (mod 4)`; the asymptotic form takes
`p` of full length `n` except on a negligible set of the generator's coins
(`ExpGroupGen.FullLengthExcept`, run-3 audit P8-2) and the arithmetic bundle `ArithmeticFP`.
(Run-3 audit P8-3: the run-2 text claimed line 11 inverted and the strict `half` necessary;
neither is the case.)

## Main definitions

* `TCSlib.Cryptography.Candidates.expo`, `halfBit`, `IsGenerator`, `dlog` — exponentiation
  `Z_{p−1} → Z_p^*`, the predicate `half_{p−1}`, generators and the discrete logarithm.
* `TCSlib.Cryptography.Candidates.dlRoot`, `dlLoop`, `dlQueries`, `dlBits` —
  [PS10, Algorithm 84.2] with an oracle and with the perfect half-oracle.
* `TCSlib.Cryptography.Candidates.majOracle` — the randomized majority test of p. 85;
  `shiftInverter`, `dlInverter` — the range reduction and the inverter `B`.
* `TCSlib.Cryptography.Candidates.FullGroupValid`, `FullGroupGen`, `FullDLAssumption`,
  `fullDLCollection`, `halfPred`, `halfStr` — the asymptotic setting.

## Main results

* `TCSlib.Cryptography.Candidates.pow_half_eq_neg_one`, `pow_mem_QR_iff`,
  `sq_eq_pow_two_mul_iff`, `neg_pow_eq` — the number theory of p. 85 (Lem-84.1.1).
* `TCSlib.Cryptography.Candidates.dlBits_pow` — correctness of Algorithm 84.2 with a perfect
  oracle; `dlLoop_eq_dlBits` — the noisy loop agrees whenever every query is answered correctly.
* `TCSlib.Cryptography.Candidates.uprob_trial_ge` (Lem-84.1.3), `uprob_majOracle_ne_le`
  (Alg-85.a), `invProb_shiftInverter_ge` (Lem-84.1.4), `good_instances` (Lem-84.1.5),
  `invProb_dlInverter_ge` — the concrete core of [PS10, Lemma 84.1].
* `TCSlib.Cryptography.Candidates.halfStr_spec` (Lem-84.1.0),
  `TCSlib.Cryptography.Candidates.fullDLCollection_hardCore` — [PS10, Lemma 84.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.1: Lemma 84.1, Algorithm 84.2 and pp. 85–86; §2.12 Theorem 58.2; Appendix A.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1 (majority votes and pairwise-independent trials).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Exponentiation in `Z_p^*`, the predicate `half_{p−1}`, generators -/

section Concrete

variable {p : ℕ} [hp : Fact p.Prime] [NeZero (p - 1)]

/-- **The exponentiation function** `f_{p,g}(x) = g^x mod p` on `Z_{p−1}` [PS10, Lemma 84.1]. -/
def expo (g : (ZMod p)ˣ) (x : ZMod (p - 1)) : (ZMod p)ˣ := g ^ x.val

/-- **The predicate `half_m`** [PS10, p. 84, "`half_n(x)` is equal to `1` if and only if
`0 ≤ x ≤ n/2`"]: `half_m(x) = 1` iff `2x < m` (lower half).

**Deviation:** strict inequality at the boundary (`x = m/2` counts as upper half), a harmless
variant of the text's `x ≤ m/2`: the two differ at the single point `x = m/2` (for `m = p − 1`
even), of probability `1/(p−1)` under a uniform exponent, and Algorithm 84.2 is correct with
either (the boundary exponent `(p−1)/2` only arises as the second root `−1` of `y = 1`, and
`dlRoot g 1 = 1`). Run-3 audit P8-3 (the run-2 docstring called the strict form necessary). -/
def halfBit (m : ℕ) (x : ZMod m) : Bool := decide (2 * x.val < m)

/-- `g` is a *generator* of `Z_p^*` [PS10, Definition 52.1]: every unit is a power of `g`. -/
def IsGenerator (g : (ZMod p)ˣ) : Prop := ∀ x, x ∈ Subgroup.zpowers g

omit [NeZero (p - 1)] in
/-- A generator of `Z_p^*` has order `p − 1`. -/
theorem IsGenerator.orderOf_eq {g : (ZMod p)ˣ} (hg : IsGenerator g) : orderOf g = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **Exponentiation by a generator is injective on `Z_{p−1}`** [PS10, Theorem 52.3 remark]. -/
theorem expo_injective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Injective (expo g) := by
  intro x y h
  have h1 := pow_eq_pow_iff_modEq.1 h
  rw [hg.orderOf_eq] at h1
  apply ZMod.val_injective
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h1

/-- **Exponentiation by a generator is a bijection `Z_{p−1} → Z_p^*`** (the discrete-log
collection is a collection of permutations, [PS10, p. 53]). -/
theorem expo_bijective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Bijective (expo g) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨expo_injective hg, by rw [ZMod.card, ZMod.card_units]⟩

/-- **The discrete logarithm** `dlog_g(y)`: the inverse of `expo g` (`Function.invFun`). -/
noncomputable def dlog (g : (ZMod p)ˣ) (y : (ZMod p)ˣ) : ZMod (p - 1) := Function.invFun (expo g) y

/-- `g^{dlog_g y} = y` for a generator `g`. -/
theorem expo_dlog {g : (ZMod p)ˣ} (hg : IsGenerator g) (y : (ZMod p)ˣ) : expo g (dlog g y) = y :=
  Function.invFun_eq ((expo_bijective hg).2 y)

/-- `dlog_g (g^x) = x` for a generator `g`. -/
theorem dlog_expo {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ZMod (p - 1)) : dlog g (expo g x) = x :=
  expo_injective hg (expo_dlog hg _)

/-! ### The number theory of p. 85 (Lem-84.1.1) -/

omit [NeZero (p - 1)] in
/-- For an odd prime, `(p − 1)/2 ≠ 0` and `2 · ((p − 1)/2) = p − 1`. -/
theorem two_mul_half (hp2 : p ≠ 2) : 2 * ((p - 1) / 2) = p - 1 ∧ 0 < (p - 1) / 2 := by
  have h2 := hp.out.two_le
  have hodd := hp.out.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  omega

omit [NeZero (p - 1)] in
/-- `−1 ≠ 1` in `Z_p^*` for an odd prime. -/
theorem neg_one_ne_one_units (hp2 : p ≠ 2) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  intro h
  exact ZMod.neg_one_ne_one (by simpa [Units.ext_iff] using h)

omit [NeZero (p - 1)] in
/-- **`g^{(p−1)/2} = −1` for a generator `g` of `Z_p^*`** [PS10, p. 85, "recall that
`g^{p/2} = −1 mod p`"].

**Proof sketch.** `(g^{(p−1)/2})² = g^{p−1} = 1`, so `g^{(p−1)/2} = ±1`
(`Units.sq_eq_sq_iff_eq_or_eq_neg`); `+1` would make the order of `g` divide `(p−1)/2 < p − 1`. -/
theorem pow_half_eq_neg_one (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) :
    g ^ ((p - 1) / 2) = -1 := by
  obtain ⟨h2, hpos⟩ := two_mul_half hp2
  have hsq : (g ^ ((p - 1) / 2)) ^ 2 = (1 : (ZMod p)ˣ) ^ 2 := by
    rw [← pow_mul, mul_comm, h2, ZMod.units_pow_card_sub_one_eq_one, one_pow]
  rcases Units.sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hg.orderOf_eq] at hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  · exact h

omit [NeZero (p - 1)] in
/-- **`g^e` is a square iff `e` is even** [PS10, p. 85, Algorithm 84.2 lines 3–7]: the parity
of the discrete logarithm is quadratic residuosity.

**Proof sketch.** Euler's criterion (`ZMod.euler_criterion_units`): `g^e ∈ QR_p` iff
`(g^e)^{(p−1)/2} = (g^{(p−1)/2})^e = (−1)^e = 1`, iff `e` is even (`−1 ≠ 1`). -/
theorem pow_mem_QR_iff (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (e : ℕ) :
    g ^ e ∈ QR p ↔ Even e := by
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := hp.out.two_le
    obtain ⟨k, hk⟩ := hp.out.eq_two_or_odd'.resolve_left hp2
    omega
  rw [mem_QR_iff, ZMod.euler_criterion_units, hhalf, ← pow_mul, mul_comm, pow_mul,
    pow_half_eq_neg_one hp2 hg]
  exact neg_one_pow_eq_one_iff_even (neg_one_ne_one_units hp2)

omit [NeZero (p - 1)] in
/-- **The square roots of `g^{2x}` are `g^x` and `−g^x`** [PS10, p. 85, "`y` has two square
roots: `g^x` and `g^{x + p/2}`"]. -/
theorem sq_eq_pow_two_mul_iff (g z : (ZMod p)ˣ) (x : ℕ) :
    z ^ 2 = g ^ (2 * x) ↔ z = g ^ x ∨ z = -(g ^ x) := by
  rw [mul_comm, pow_mul]
  exact Units.sq_eq_sq_iff_eq_or_eq_neg

omit [NeZero (p - 1)] in
/-- **`−g^x = g^{x + (p−1)/2}`** [PS10, p. 85]: the second root has the larger exponent. -/
theorem neg_pow_eq (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ℕ) :
    -(g ^ x) = g ^ (x + (p - 1) / 2) := by
  rw [pow_add, pow_half_eq_neg_one hp2 hg, mul_neg_one]

/-! ### Algorithm 84.2 -/

/-- **The root step of [PS10, Algorithm 84.2]** (lines 3–9): make `y` a square by dividing by
`g` if necessary, then take the square root `y^{(p+1)/4}` of [PS10, Theorem 58.2]
(`NumberTheory.sq_pow_div_four_succ`, valid for `p ≡ 3 (mod 4)`). -/
noncomputable def dlRoot (g y : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (if y ∈ QR p then y else y * g⁻¹) ^ (p / 4 + 1)

/-- **The loop of [PS10, Algorithm 84.2]** with an oracle `O` for `half_{p−1}` of the
discrete logarithm, answering with per-round coins `κ`: for `k` rounds, record the parity bit
(`1` iff `y` is a non-square), take the root `dlRoot g y`, keep it if the oracle says
"lower half" (`true`) and its negative otherwise, and recurse; the output is the exponent
rebuilt from its bits (least significant first).

The root selection is the text's line 11 read literally: "IF `b = 0` THEN `y_{k−1} ← −y_{k−1}`"
keeps the root exactly when `A` answers `1` (= lower half, `half`'s convention) and negates it
otherwise (run-3 audit P8-3: the run-2 docstring wrongly called this a deviation).

**Deviation:** `k` is an explicit round count (the text's `k = |p|` decremented to `0`). -/
noncomputable def dlLoop (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → ℕ
  | 0, _, _ => 0
  | k + 1, y, c =>
    2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
      (if y ∈ QR p then 0 else 1)

/-- The sequence of roots submitted to the oracle by `dlLoop` (round `j` queries the root
taken at round `j`); the union bound over rounds is stated on these queries. -/
noncomputable def dlQueries (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → Fin k → (ZMod p)ˣ
  | 0, _, _ => Fin.elim0
  | k + 1, y, c =>
    Fin.cons (dlRoot g y)
      (dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ))

/-- **The perfect oracle**: `half_{p−1}` of the discrete logarithm. -/
noncomputable def halfOracle (g y : (ZMod p)ˣ) : Bool := halfBit (p - 1) (dlog g y)

/-- **Algorithm 84.2 with a perfect oracle** [PS10, Algorithm 84.2, "let us first assume that
`A` is always correct"]: `k` rounds of `dlLoop` driven by `halfOracle`. -/
noncomputable def dlBits (g : (ZMod p)ˣ) (k : ℕ) (y : (ZMod p)ˣ) : ℕ :=
  dlLoop g (fun y (_ : Unit) => halfOracle g y) k y (fun _ => ())

omit [NeZero (p - 1)] in
/-- Unfolding: `dlLoop` at `k + 1`. -/
theorem dlLoop_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) :
    dlLoop g O (k + 1) y c =
      2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
        (if y ∈ QR p then 0 else 1) := rfl

omit [NeZero (p - 1)] in
/-- Unfolding: the first query of `dlQueries` is the root of the input. -/
theorem dlQueries_zero (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) : dlQueries g O (k + 1) y c 0 = dlRoot g y := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- Unfolding: the later queries of `dlQueries` are those of the recursive call. -/
theorem dlQueries_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) (j : Fin k) :
    dlQueries g O (k + 1) y c j.succ =
      dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) j := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- **The noisy loop agrees with the perfect one whenever every query is answered
correctly**: if `O` answers `half_{p−1}(dlog)` on each of its `k` queries, then
`dlLoop g O k y c = dlBits g k y`.

**Proof sketch.** Induction on `k` generalizing `y, c`: both loops query `dlRoot g y` first
(`dlQueries_zero`), the hypothesis at `0` makes them select the same root, and the hypothesis
at `j.succ` (`dlQueries_succ`) is the hypothesis of the recursive call. -/
theorem dlLoop_eq_dlBits (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    ∀ (k : ℕ) (y : (ZMod p)ˣ) (c : Fin k → κ),
      (∀ j, O (dlQueries g O k y c j) (c j) = halfOracle g (dlQueries g O k y c j)) →
        dlLoop g O k y c = dlBits g k y
  | 0, _, _, _ => rfl
  | k + 1, y, c, h => by
    have h0 := h 0
    rw [dlQueries_zero] at h0
    rw [dlLoop_succ, dlBits, dlLoop_succ, h0]
    congr 2
    rw [← dlBits]
    apply dlLoop_eq_dlBits g O k
    intro j
    have hj := h j.succ
    rw [dlQueries_succ, h0] at hj
    exact hj

omit [NeZero (p - 1)] in
/-- **Correctness of Algorithm 84.2 with a perfect oracle** [PS10, p. 85, "we can iteratively
divide, take square roots, and then choose the root with smaller discrete log until we
eventually end up at `1`"]: for `p ≡ 3 (mod 4)`, a generator `g` and `e < p − 1` with
`e < 2^k`, `dlBits g k (g^e) = e`.

**Proof sketch.** Induction on `k` generalizing `e`. At `k = 0`, `e = 0`. At `k + 1`: if `e`
is even, `g^e ∈ QR_p` (`pow_mem_QR_iff`) and `dlRoot g (g^e) = (g^e)^{(p+1)/4}` is a root of
`g^e = g^{2(e/2)}` (`sq_pow_div_four_succ`), hence `g^{e/2}` or `−g^{e/2} = g^{e/2 + (p−1)/2}`
(`sq_eq_pow_two_mul_iff`, `neg_pow_eq`); the perfect oracle answers `true` on `g^{e/2}`
(`dlog_expo`, `2(e/2) ≤ e < p − 1`) and `false` on the other root (its exponent
`e/2 + (p−1)/2 < p − 1` has `2 · (e/2 + (p−1)/2) ≥ p − 1`), so the kept root is `g^{e/2}`;
the recorded bit is `0`, the recursive call returns `e/2 < 2^k`, and `2(e/2) + 0 = e`. If `e`
is odd, `g^e ∉ QR_p`, the loop divides by `g` (`g^e · g⁻¹ = g^{e−1}`, even exponent) and the
same argument gives `2((e−1)/2) + 1 = e`. -/
theorem dlBits_pow (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) {k e : ℕ}
    (he : e < p - 1) (hk : e < 2 ^ k) : dlBits g k (g ^ e) = e := by
  sorry

/-! ### The majority test of p. 85 and the range reduction -/

/-- **The randomized majority test** replacing line 10 of Algorithm 84.2 [PS10, p. 85]: on
the root `y`, draw `ℓ` fresh `r_i ← Z_{p−1}` and coins for `A`, set `z_i = y · g^{r_i}`, and vote
"lower half" (`true`) for each `i` with `A(z_i) = half_{p−1}(r_i)`; decide by majority.

The text's counter `lo` is incremented when `(b_i = 0 ∧ r_i < p/2) ∨ (b_i = 1 ∧ r_i ≥ p/2)`,
i.e. on a *disagreement* `b_i ≠ half(r_i)`, and `b = 0` (upper half) is chosen when `lo > ℓ/2`:
voting on agreements and deciding "lower half" by majority is the same test. Its analysis on
p. 86 bounds `Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of this
increment rule (source error 27; run-3 audit P8-3) — `uprob_trial_ge` states the correct
direction.

**Deviation:** ties go to "upper half" (`HardcoreBit.majority`; the text gives `b = 1` on a
tie `lo = ℓ/2`). -/
def majOracle (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool) (ℓ : ℕ) :
    (ZMod p)ˣ → (Fin ℓ → ZMod (p - 1) × ρ) → Bool :=
  fun y c => HardcoreBit.majority fun i =>
    decide (A (y * g ^ (c i).1.val) (c i).2 = halfBit (p - 1) (c i).1)

/-- **One trial of the majority test is correct with probability at least `1/2 + ε/2`**
(Lem-84.1.3, [PS10, p. 86, "`Pr[noinc | low(y_{k−1})] ≤ 1/2 − ε + 2(ε/4) = 1/2 − ε/2`"]): if
`A` predicts `half_{p−1}` from `g^x` with probability at least `1/2 + ε` over uniform `x`, and
the exponent `e` of the root lies in `[0, s)` or in `[(p−1)/2, (p−1)/2 + s)` with
`4s ≤ ε(p−1)`, then a trial on `g^e` votes `half_{p−1}(e)` with probability at least `1/2 + ε/2`.

**Proof sketch.** The exponent of `z = g^e · g^r` is `e + r` in `Z_{p−1}` and `r ↦ e + r` is a
bijection (`HardcoreBit.pushesUniform_add_right`), so `Pr_{r, c}[A(z, c) = half(e + r)] =
predProb (expo g) half A ≥ 1/2 + ε` (`uprob_comp_equiv`). For `e < s`, `half(e + r) ≠ half(r)`
only for `r ∈ [(p−1)/2 − e, (p−1)/2) ∪ [p − 1 − e, p − 1)`, at most `2s` values, probability
`≤ 2s/(p−1) ≤ ε/2` (`uprob_eq_card_filter`, `Finset.card_le_card`); for `e` in the upper
window, `e = (p−1)/2 + e'` and `half(e + r) ≠ ¬half(r)` only on `2e' ≤ 2s` values. The union
bound `uprob_or_le` (through `uprob_not`) gives
`Pr[vote = half(e)] ≥ 1/2 + ε − ε/2`. -/
theorem uprob_trial_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A)
    {s : ℕ} (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    1 / 2 + ε / 2 ≤ uprob fun c : ZMod (p - 1) × ρ =>
      decide (A (g ^ e * g ^ c.1.val) c.2 = halfBit (p - 1) c.1) = halfBit (p - 1) (e : ZMod (p - 1)) := by
  sorry

/-- **The majority test fails with probability at most `1/(ε² ℓ)`** (Alg-85.a, [PS10, p. 86,
"by setting the number of samples `ℓ = (1/ε)²`, then by the corollary of the Chernoff bound …
`b` will be correct with probability very close to `1`"]) on a root `g^e` whose exponent lies
in the windows of `uprob_trial_ge`.

**Deviation:** Chebyshev's inequality for pairwise independent trials
(`HardcoreBit.uprob_majority_fails_le`, [PS10, Appendix A, p. 189]) with the explicit bound
`1/(4 (ε/2)² ℓ)`, instead of the garbled [PS10, Lemma 189.8].

**Proof sketch.** The `ℓ` votes are functions of the coordinates `c i` of a uniform tuple,
hence pairwise independent (`HardcoreBit.pairwiseUniform_eval`,
`PairwiseUniform.pairwiseIndep`) with the "correct vote" probability `≥ 1/2 + ε/2` each
(`uprob_trial_ge` transported by `pushesUniform_eval`); if the majority is wrong then at most
half of the votes are correct (`two_mul_card_le_of_majority_ne`), whose probability is
`≤ 1/(4 (ε/2)² ℓ) = 1/(ε² ℓ)`. -/
theorem uprob_majOracle_ne_le {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s : ℕ}
    (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {ℓ : ℕ} (hℓ : 0 < ℓ) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    uprob (fun c : Fin ℓ → ZMod (p - 1) × ρ =>
      majOracle g A ℓ (g ^ e) c ≠ halfBit (p - 1) (e : ZMod (p - 1))) ≤ 1 / (ε ^ 2 * ℓ) := by
  sorry

/-- **The range reduction** (Lem-84.1.4, [PS10, p. 85, "such an algorithm suffices to solve the
discrete log problem, since we can guess and map any instance into this range" — never
shown]): from a solver `B₀` for instances with exponent in `[0, s)`, the inverter that guesses
`t ← [0, T)`, runs `B₀` on `y · g^{−ts}` and returns `B₀(…) + ts`. -/
def shiftInverter (g : (ZMod p)ˣ) {ρ' : Type*} (B₀ : (ZMod p)ˣ → ρ' → ℕ) (s T : ℕ) :
    (ZMod p)ˣ → Fin T × ρ' → ZMod (p - 1) :=
  fun y c => ((B₀ (y * (g ^ (c.1.val * s))⁻¹) c.2 : ℕ) : ZMod (p - 1)) + ((c.1.val * s : ℕ) : ZMod (p - 1))

/-- **The range reduction succeeds with probability at least `(1 − δ)/T`** (Lem-84.1.4): if
`B₀` recovers every exponent `e' < s` from `g^{e'}` with probability at least `1 − δ`, and
`T s ≥ p − 1`, then `shiftInverter g B₀ s T` inverts `expo g` with probability at least
`(1 − δ)/T`.

**Proof sketch.** For `y = g^e` (`e < p − 1`) the guess `t = ⌊e/s⌋ < T` has probability `1/T`
(`pushesUniform_fst`, `uprob_eq_one_div_card`); then `y · g^{−ts} = g^{e − ts}` with
`e − ts < s`, and on `B₀`'s success the output is `(e − ts) + ts = e` in `Z_{p−1}`
(`Nat.cast_sub`, `Nat.div_add_mod`). `uprob_prod` over `(e, t)` and `uprob_mono` with the
event `t = ⌊e/s⌋ ∧ B₀ succeeds` (`OneWay.uprob_and_le_mul`-style product of the two
independent factors, `h (e % s)`). -/
theorem invProb_shiftInverter_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ' : Type*} [Fintype ρ']
    (B₀ : (ZMod p)ˣ → ρ' → ℕ) {s T : ℕ} (hs : 0 < s) (hT : p - 1 ≤ T * s) {δ : ℝ}
    (h : ∀ e' < s, 1 - δ ≤ uprob fun c : ρ' => B₀ (g ^ e') c = e') :
    (1 - δ) / T ≤ invProb (expo g) (shiftInverter g B₀ s T) := by
  sorry

/-- **The inverter `B` of [PS10, Lemma 84.1]**: the range reduction applied to the loop of
Algorithm 84.2 driven by the majority test with `ℓ` trials per round and `k` rounds. -/
noncomputable def dlInverter (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool)
    (s T ℓ k : ℕ) : (ZMod p)ˣ → Fin T × (Fin k → Fin ℓ → ZMod (p - 1) × ρ) → ZMod (p - 1) :=
  shiftInverter g (dlLoop g (majOracle g A ℓ) k) s T

/-- **The concrete core of [PS10, Lemma 84.1]**: for `p ≡ 3 (mod 4)` prime, a generator `g`
of `Z_p^*` and a predictor `A` of `half_{p−1}` from `g^x` with success at least `1/2 + ε`, the
inverter `dlInverter g A s T ℓ k` recovers the discrete logarithm of a uniform `g^x` with
probability at least `(1 − k/(ε² ℓ))/T`, for any window `0 < s` with `4s ≤ ε(p−1)`, `T s ≥ p − 1`
and `s ≤ 2^k` rounds. (With `s ≈ ε(p−1)/4`, `T ≈ 4/ε + 1`, `k = |p|` and `ℓ = 4|p|/ε²` this is
`≥ 3ε/20`.)

**Proof sketch.** `invProb_shiftInverter_ge` with `B₀ := dlLoop g (majOracle g A ℓ) k` and
`δ := k/(ε² ℓ)`: for `e' < s ≤ 2^k`, `dlBits g k (g^{e'}) = e'` (`dlBits_pow`), and
`dlLoop_eq_dlBits` reduces the failure of `B₀` to the failure of some round's majority vote on
its query (`uprob_exists_le` over the `k` rounds, `Fin.cons` bookkeeping). Along the correct
path the query of round `j` is `dlRoot` of `g^{e_j}` with `e_j = e'/2^j < s`, i.e. `g^{e_j/2}`
or `g^{e_j/2 + (p−1)/2}` (`sq_eq_pow_two_mul_iff`, `neg_pow_eq`), an instance of the windows of
`uprob_majOracle_ne_le`; the coins of round `j` are an independent uniform coordinate
(`pushesUniform_eval`), so each round fails with probability `≤ 1/(ε² ℓ)`. -/
theorem invProb_dlInverter_ge (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s T ℓ k : ℕ} (hs : 0 < s)
    (hs4 : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) (hT : p - 1 ≤ T * s) (hk : s ≤ 2 ^ k) (hℓ : 0 < ℓ) :
    (1 - k / (ε ^ 2 * ℓ)) / T ≤ invProb (expo g) (dlInverter g A s T ℓ k) := by
  sorry

end Concrete

/-- **Good instances** (Lem-84.1.5, missing in the text): if the predictor's success, averaged
over the instances `(p, g)` drawn by the generator, is at least `1/2 + ε`, then a set of
instances of probability at least `ε/2` has per-instance success at least `1/2 + ε/2`
(`HardcoreBit.half_le_uprob_threshold` with `c = 1/2`). The reduction fixes `(p, g)` from its
input, so the concrete lemma is applied on this set. -/
theorem good_instances {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℝ) (hq : ∀ i, q i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h : 1 / 2 + ε ≤ uexp q) :
    ε / 2 ≤ uprob fun i => 1 / 2 + ε / 2 ≤ q i :=
  HardcoreBit.half_le_uprob_threshold q hq (by norm_num) hε h

/-! ## The asymptotic form: the full-group collection and Lemma 84.1 -/

/-- A **full-group instance** `⟨p, ⟨p − 1, g⟩⟩`: a valid index whose order is `p − 1` (so `g`
generates `Z_p^*`, the setting of [PS10, Lemma 84.1 and Algorithm 84.2]) with `p ≡ 3 (mod 4)`
(square roots by [PS10, Theorem 58.2]).

**Deviation:** `p ≡ 3 (mod 4)` (decision log, open question 3). -/
def FullGroupValid (i : List Bool) : Prop := ExpValid i ∧ dlM i = dlP i - 1 ∧ dlP i % 4 = 3

/-- A full-group instance is a valid instance. -/
theorem FullGroupValid.expValid {i : List Bool} (h : FullGroupValid i) : ExpValid i := h.1

/-- **Full-group instance generators**: PPTs outputting primes `p ≡ 3 (mod 4)` of length `n`
with a generator of `Z_p^*` (the index set `{(p, g)}` of the collection of
[PS10, Lemma 84.1]). -/
abbrev FullGroupGen : Type 1 := ExpGroupGen FullGroupValid

/-- **The discrete-log assumption in `Z_p^*`** — the hypothesis of [PS10, Lemma 84.1] ("under
the DL assumption (52.2)"): every non-uniform PPT solves
`Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p − 1, g⟩⟩, g^x⟩) = x]` with negligible
probability.

**Deviation:** Assumption 52.2 is for prime-order groups; the lemma needs discrete-log
hardness for a uniform generator of the full group `Z_p^*` (source error 27), stated here
relative to a full-group instance generator. -/
def FullDLAssumption (G : FullGroupGen) : Prop := G.DLHard

/-- **The discrete-log collection in `Z_p^*`** [PS10, Lemma 84.1, "the exponentiation function
`f_{p,g}(x) = g^x mod p` from the discrete-log collection `DL`"]: domains `Z_{p−1}`,
`f_{p,g}(x) = g^x mod p`, the instance generator `G`. -/
noncomputable def fullDLCollection (H : ArithmeticFP) (G : FullGroupGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- The full-group collection is one-way under the full-group discrete-log assumption
([PS10, Theorem 52.3] for `Z_p^*`): `expCollection_oneWay`. -/
theorem fullDLCollection_oneWay (H : ArithmeticFP) (G : FullGroupGen) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

/-- **The predicate `half_{p−1}` on the collection**: `h_i(x) = [2x + 2 ≤ p]`, which is
`[2x < p − 1]` at every full-group index (`halfPred_eq`) and is computable from the numerals
of `p` and `x` at every string index (`halfStr_spec`). -/
noncomputable def halfPred (i : List Bool) (x : ZMod (expOrd i)) : Bool :=
  decide (2 * x.val + 2 ≤ dlP i)

/-- At a prime index `half_{p−1}(x) = [2x < p − 1]`, the predicate `halfBit (p − 1)` of the
concrete layer. -/
theorem halfPred_eq {i : List Bool} (h : ExpValid i) (x : ZMod (expOrd i)) :
    halfPred i x = decide (2 * x.val < dlP i - 1) := by
  have := h.1.two_le
  simp only [halfPred, decide_eq_decide]
  omega

/-- **The evaluator of `half_{p−1}`** on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: `[2x + 2 ≤ p]` on the numerals
(Lem-84.1.0, [PS10, p. 84, "it is easy to compute `half_{p−1}()` given `x`"]). -/
def halfStr (z : List Bool) : List Bool :=
  [decide (2 * listToNat (pairSndD z) + 2 ≤ listToNat (pairFstD (pairFstD z)))]

/-- The evaluator computes `halfPred` on encoded elements at every index (the efficiency
clause of `Collection.HardCore`). -/
theorem halfStr_spec (i : List Bool) (x : ZMod (expOrd i)) :
    halfStr (pairEncode i (expEnc i x)) = [halfPred i x] := by
  simp only [halfStr, halfPred, expEnc, dlP, pairFstD_pairEncode, pairSndD_pairEncode,
    listToNat_natToList (val_lt_two_pow_dlW i x)]

/-- **`half_{p−1}` is polynomial-time computable** (Lem-84.1.0) given the arithmetic bundle.

**Proof sketch.** `2x + 2 ≤ p ⟺ ¬ (p / 2 ≤ x)`: `p / 2` is the quotient of `divModStr ⟨p, 1 0⟩`
(`H.divMod` with the constant numeral of `2`, `polyTimeComputable_const`), the comparison is
`H.le` on `⟨p / 2, x⟩` (`polyTimeComputable_pairFstD`, `_pairSndD`, `.pairEncode`), and the
negation of a one-bit string is `polyTimeComputable_ite` on `polyTimeComputable_pairEq` with
`[true]`. -/
theorem polyTimeComputable_halfStr (H : ArithmeticFP) : PolyTimeComputable halfStr := by
  sorry

/-- **Lemma 84.1** [PS10, Lemma 84.1]: under the discrete-log assumption in `Z_p^*` (and the
arithmetic hypotheses), `half_{p−1}` is a hard-core predicate for the exponentiation
`f_{p,g}(x) = g^x mod p` of the discrete-log collection: for every non-uniform PPT `A` there is
a negligible `ε` with `Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p−1, g⟩⟩, g^x⟩) =
half_{p−1}(x)] ≤ 1/2 + ε(n)` for all `n`.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis is stated for the
complementary event of its own increment rule (module docstring, run-3 audit P8-3). Also:
`p ≡ 3 (mod 4)`; `p` of full length `n` except on a set of the generator's coins of negligible
probability `δ n` (`hbig`, `ExpGroupGen.FullLengthExcept`); the collection form of
Definition 78.3 (`Collection.HardCore`: `A` receives `1^n` and the index).

Repair (run-3 audit P8-2): the hypothesis `hbig : G.FullLength` (full length on every coin
string, not known to be satisfiable) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`; the
proof discards the short-prime coins, which contribute at most `δ n` to the good-instance set.

**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`.
*Hard:* by contradiction with `not_negligible_iff` (through the quantifier form
`Ensemble.indist_iff_exists_negligible`-style of `HardCore`): suppose `A : NUPPT` has
`1/2 + n^{-c} ≤ E_r[Pr_{x, ρ}[A(1^n, ⟨i, f_i x⟩) = half_i x]]` for infinitely many `n ≥ n₀`.
Set `ε := n^{-c}/2`. By `good_instances` (over the generator's coins `r`, index `i = Gen(1^n; r)`)
a set of coins of probability `≥ ε` has per-instance success `≥ 1/2 + ε`; removing the coins
with `p < 2^{n−1}` (probability `≤ δ n` by `hbig`, and `δ n ≤ ε/2` for large `n` since `δ` is
negligible) leaves a *good* set of probability `≥ ε/2` (`uprob_not`, `uprob_or_le`). At such an
index `i = ⟨p, ⟨p−1, g⟩⟩` (valid, `dlW i = n`, `p ≡ 3 (mod 4)`, `2^{n−1} ≤ p < 2^n` on the good
set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f_i x` is the numeral of
`expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
`orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
`Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).HardCore halfPred := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/ElGamal.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.Asymptotic.Ensembles
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The DDH assumption and El Gamal encryption

[PS10, §3.11]: the *decisional Diffie–Hellman assumption* in the order-`q` subgroup `G_q` of
`Z_p^*` for a safe prime `p = 2q + 1` [PS10, Assumption 105.1], the group facts behind it
(p. 106: `G_q` is the subgroup of squares, cyclic of prime order, every element `≠ 1`
generates, squaring is `2`-to-`1` onto it), the El Gamal public-key encryption scheme
[PS10, Algorithm 106.2] and its security under DDH [PS10, Theorem 107.3, "we leave the formal
proof as an exercise"].

**Instances and the two generators.** Safe primes come from a safe-prime instance generator
`G : SafePrimeGen` (`TCSlib.Cryptography.Candidates.DiscreteLog`; the text's "pick a safe
prime `p = 2q + 1` of length `n`"); El Gamal's `Gen` follows the text and draws its own
`h = g²` for a uniform unit `g` (the generator component of `G`'s output is ignored). The DDH
assumption is stated for the *derived* generator `egGroupGen H G`, which outputs the same
`(p, q)` and `h = g²`, replaced by the fixed generator `4 = 2²` on the event `g² = 1`
(probability `1/q`, Claim-107.a): the law of its `h` is the "`y ← Gen_q`" of
Assumption 105.1 up to this term, which is where the `1/q` of Theorem 107.3 comes from.

**Message space.** With arbitrary `m ∈ Z_p^*` the scheme is insecure under DDH on `G_q` (the
Legendre symbol of `c₂` reveals the coset of `m`, source error 28), so the message space is
`G_q`: `Enc` canonicalises its message (`egCanon`: a numeral not reading as an element of
`G_q` is encrypted as `1`). Since the message space depends on the key, security is stated
in the chosen-message form `GroupPKScheme.Secure`: the two messages are produced by a
non-uniform PPT *selector* `M(1^n, pk)`; the constant selectors (messages hard-wired as
advice) recover the quantifier form of [PS10, Definition 102.2] (`GroupPKScheme.Secure.const`).

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the DDH ensembles draw `(p, q, y)` from the instance
generator (the text's ideal `p ← Π̃_n; y ← Gen_q`) and the exponents `a, b, z ∈ Z_q` by
rejection from blocks of `n · n` seed coins, within `2^{-n}` of uniform at the generated
instance (`ddhExpo`, D10 — the inventory's recommendation for Assumption 105.1; equivalent to
the ideal-exponent form up to a negligible statistical term), encoded as
`⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` of `n`-bit numerals, length `15n + 14`; El Gamal's `Gen`
draws `g ← Z_p^*` by rejection (the text's `g ∈ Z_p` may be `0, ±1`, source error 28) and
`a, b ← Z_q` by the same rejection sampler (D10); `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩` carries `q`; `Dec`
is a deterministic string function; messages are canonicalised into `G_q`; security is the
chosen-message form; the safe prime has full length `n` except on a negligible set of the
generator's coins (`ExpGroupGen.FullLengthExcept`).

**Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
`Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — the two ensembles
then had different instance laws whenever `q` varies with the coins, and the threshold test
`[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every
randomized generator. The seeds are now product types (uniform coins for the generator, D6)
with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
(full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

## Main definitions

* `TCSlib.Cryptography.Candidates.ddhTuple`, `ddhLen`, `ddhExpo`, `ddhReal`, `ddhRandom`,
  `TCSlib.Cryptography.Candidates.DDHAssumption` — [PS10, Assumption 105.1].
* `TCSlib.Cryptography.Candidates.GroupPKScheme`, `GroupPKScheme.challenge`,
  `GroupPKScheme.Secure`, `constSelector` — public-key schemes with a key-dependent message
  space and their security (the form of [PS10, Definition 102.2] for `G_q`).
* `TCSlib.Cryptography.Candidates.egUnit`, `egCanon`, `egGenParts`, `egGen`, `egEncParts`,
  `egEnc`, `egDecStr`, `elGamal` — El Gamal [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.egSquareGen`, `egGroupParts`, `egGroupGen` — the derived
  safe-prime instance generator with `h = g²` (fallback `4`).

## Main results

* `TCSlib.Cryptography.Candidates.card_QR_safe`, `mem_QR_iff_pow_eq_one`,
  `orderOf_eq_of_mem_QR`, `zpowers_eq_QR`, `eq_QR_of_card`, `card_sqrt_safe`,
  `pushesUniform_sqTo_safe` — the group facts of p. 106 (NT-105.a, proved).
* `TCSlib.Cryptography.Candidates.uprob_sq_eq_one`, `statClose_of_uprob_ne`,
  `statClose_sq_generator` — the generator-versus-square term `1/q` (Claim-107.a).
* `TCSlib.Cryptography.Candidates.ddhExpo_statClose` — the DDH exponents are within `(1/2)^n`
  of uniform at a generated instance (D10).
* `TCSlib.Cryptography.Candidates.egSquareGen_valid` — the derived generator is valid
  (proved); `egGroupGen_runAt`, `egGen_runAt`, `egEnc_runAt`, `egDecStr_apply` — unfolding.
* `TCSlib.Cryptography.Candidates.elGamal_correct` — correctness of [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const` — constant messages.
* `TCSlib.Cryptography.Candidates.elGamal_secure` — [PS10, Theorem 107.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.11: Assumption 105.1, the remarks on p. 106, Algorithm 106.2, Theorem 107.3;
  §3.10: Definitions 102.1 and 102.2; §3.1: Definition 69.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage) and
  Lemma 3.2 (closure under post-processing).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The group `G_q` of a safe prime (NT-105.a, [PS10, p. 106]) -/

section SafePrime

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- A safe prime `p = 2q + 1` is odd. -/
theorem safe_ne_two (hpq : p = 2 * q + 1) : p ≠ 2 := by
  have := hq.out.two_le
  omega

/-- `5 ≤ p` for a safe prime `p = 2q + 1`. -/
theorem five_le_safe (hpq : p = 2 * q + 1) : 5 ≤ p := by
  have := hq.out.two_le
  omega

/-- `(p − 1)/2 = q` and `p/2 = q` for `p = 2q + 1`. -/
theorem safe_half (hpq : p = 2 * q + 1) : (p - 1) / 2 = q ∧ p / 2 = q := by omega

/-- **`|G_q| = q`** [PS10, p. 106, "`G` has a subgroup `G_q` of order `q`"]: the subgroup of
squares of `Z_p^*` has `(p − 1)/2 = q` elements (`NumberTheory.card_QR_prime`). -/
theorem card_QR_safe (hpq : p = 2 * q + 1) : Nat.card (QR p) = q := by
  rw [card_QR_prime (safe_ne_two hpq), (safe_half hpq).1]

/-- **`x ∈ G_q ↔ x^q = 1`** [PS10, p. 106, "the subgroup `G_q` consists of all of the squares
modulo `p`"]: Euler's criterion with `p/2 = q`. -/
theorem mem_QR_iff_pow_eq_one (hpq : p = 2 * q + 1) (x : (ZMod p)ˣ) : x ∈ QR p ↔ x ^ q = 1 := by
  rw [mem_QR_iff, ZMod.euler_criterion_units, (safe_half hpq).2]

/-- **Every element `≠ 1` of `G_q` has order `q`** [PS10, p. 106, "since `q` is prime, `G_q`
will be a cyclic group … every element is a generator"]. -/
theorem orderOf_eq_of_mem_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    orderOf x = q :=
  orderOf_eq_prime ((mem_QR_iff_pow_eq_one hpq x).1 hx) hx1

/-- **Every element `≠ 1` of `G_q` generates `G_q`** [PS10, p. 106]. -/
theorem zpowers_eq_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = QR p := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
  rw [Nat.card_zpowers, orderOf_eq_of_mem_QR hpq hx hx1, card_QR_safe hpq]

/-- **`G_q` is the unique subgroup of order `q`** of `Z_p^*` [PS10, p. 106]: a subgroup of
order `q` consists of `q`-th roots of unity, hence lies in `G_q`, and has its size. -/
theorem eq_QR_of_card (hpq : p = 2 * q + 1) (K : Subgroup (ZMod p)ˣ) (hK : Nat.card K = q) :
    K = QR p := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_QR_iff_pow_eq_one hpq]
    have h1 := pow_card_eq_one' (G := K) (x := ⟨x, hx⟩)
    rw [hK] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rw [hK, card_QR_safe hpq]

/-- **Squaring is `2`-to-`1` onto `G_q`** [PS10, p. 106, "choosing a generator involves simply
picking a random element `a ∈ G` and computing `a²`"]: every square has exactly two roots. -/
theorem card_sqrt_safe (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) :
    (univ.filter fun y : (ZMod p)ˣ => y ^ 2 = x).card = 2 :=
  card_sqrt_eq_two (safe_ne_two hpq) hx

/-- **The square of a uniform unit is a uniform element of `G_q`** (Claim-107.a, first part; inventory lemma
C5 of chapter 2). -/
theorem pushesUniform_sqTo_safe (hpq : p = 2 * q + 1) : HardcoreBit.PushesUniform (sqTo p) := by
  refine pushesUniform_of_card_fiber (sqTo p) (c := 2) (by norm_num) fun y => ?_
  rw [← card_sqrt_safe hpq y.2]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [Subtype.ext_iff, coe_sqTo]

/-- **`g² = 1` with probability `1/q`** for a uniform unit `g` (Claim-107.a): the two roots
`±1` among the `p − 1 = 2q` units. -/
theorem uprob_sq_eq_one (hpq : p = 2 * q + 1) :
    uprob (fun g : (ZMod p)ˣ => g ^ 2 = 1) = 1 / (q : ℝ) := by
  rw [uprob_eq_card_filter, card_sqrt_safe hpq (one_mem _), ZMod.card_units]
  have h : p - 1 = 2 * q := by omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [h]
  push_cast
  field_simp

end SafePrime

/-- **Two samplers on the same seeds are statistically close within the probability that they
differ**: `|Pr[T(X)] − Pr[T(Y)]| ≤ Pr[X ≠ Y]` (the device for the `1/q` term of
Theorem 107.3: the scheme's `h = g²` and the derived generator's `h` differ only on `g² = 1`). -/
theorem statClose_of_uprob_ne {σ γ : Type*} [Fintype σ] (X Y : σ → γ) :
    StatClose X Y (uprob fun s => X s ≠ Y s) := by
  intro T
  have key : ∀ (X Y : σ → γ), uprob (fun s => T (X s)) ≤
      uprob (fun s => T (Y s)) + uprob (fun s => X s ≠ Y s) := by
    intro X Y
    refine (uprob_mono fun s h => ?_).trans (uprob_or_le (fun s => T (Y s)) (fun s => X s ≠ Y s))
    by_cases hxy : X s = Y s
    · exact Or.inl (hxy ▸ h)
    · exact Or.inr hxy
  have h1 := key X Y
  have h2 := key Y X
  have hsymm : uprob (fun s => Y s ≠ X s) = uprob (fun s => X s ≠ Y s) :=
    OneWay.uprob_congr fun s => ne_comm
  rw [hsymm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The square of a uniform unit is within `1/q` of a uniform generator of `G_q`**
(Claim-107.a, missing in the text): the uniform element of `G_q` (`pushesUniform_sqTo_safe`)
and the uniform element of `G_q ∖ {1}` (the text's "`y ← Gen_q`") are within statistical
distance `1/q`.

**Proof sketch.** For a test set `S ⊆ G_q`, the two probabilities are `|S|/q` and
`|S ∖ {1}|/(q − 1)`; both lie between `|S ∖ {1}|/q` and `|S ∖ {1}|/q + 1/q`
(`uprob_eq_card_filter`, `card_QR_safe`, `Fintype.card_subtype_compl`); transport the first
along `pushesUniform_sqTo_safe` (`PushesUniform.uprob_eq`). -/
theorem statClose_sq_generator {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = 2 * q + 1) :
    StatClose (sqTo p) (fun y : {y : QR p // y ≠ 1} => (y : QR p)) (1 / (q : ℝ)) := by
  sorry

/-! ## The DDH assumption [PS10, Assumption 105.1] -/

/-- The DDH tuple `⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` at the instance `i` with exponents
`a, b, c ∈ Z_q` (the text's `(p, y, y^a, y^b, y^c)`), with `n`-bit numerals. -/
noncomputable def ddhTuple (i : List Bool) (a b c : ZMod (expOrd i)) : List Bool :=
  pairEncode i (pairEncode (expF i a) (pairEncode (expF i b) (expF i c)))

/-- The length `15n + 14` of a DDH tuple of `n`-bit numerals. -/
def ddhLen : PolyExpr := .add (.mul (.const 15) .var) (.const 14)

/-- `ddhLen.eval n = 15n + 14`. -/
@[simp] theorem eval_ddhLen (n : ℕ) : ddhLen.eval n = 15 * n + 14 := rfl

/-- A DDH tuple at a well-formed index has length exactly `15n + 14` (the padding of the
ensembles is lossless). -/
theorem length_ddhTuple {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) (a b c : ZMod (expOrd i)) :
    (ddhTuple i a b c).length = 15 * n + 14 := by
  have hw := h.dlW_eq
  simp only [ddhTuple, expF, length_pairEncode, length_natToList, h.length_eq, hw]
  ring

/-- **An exponent of `Z_{expOrd i}` from a block of `n · n` coins** by rejection: `n` trials of
`n`-bit blocks, each reading the bit length of `expOrd i` bits (`sampleBelowL`), with the
fallback `0` — the exponent sampler of El Gamal's `Gen` and `Enc` (`egGenParts`, `egEncParts`:
`sampleBelowL (dlM i) (Nat.size (dlM i)) n n` on an `n · n`-bit coin segment, the same numbers
at a valid index by `expOrd_of_valid`) on typed coins. Its law is within `(1/2)^n` of uniform
at a valid well-formed index (`ddhExpo_statClose`, D10).

Repair (run-3 audit P8-1): the exponents of the DDH ensembles are read from fixed-length coin
blocks instead of being ideal coordinates of a dependent-sum seed (module docstring). -/
noncomputable def ddhExpo (n : ℕ) (i : List Bool) (b : Fin (n * n) → Bool) : ZMod (expOrd i) :=
  (((sampleBelowL (expOrd i) (Nat.size (expOrd i)) n n (List.ofFn b)).getD 0 : ℕ) : ZMod (expOrd i))

/-- `((x : ℕ) : ZMod m) = x` for `x : ZMod m` read through `ZMod.finEquiv` (the identification
of the uniform `Fin m` with the uniform `ZMod m` used by `ddhExpo_statClose`). -/
private theorem natCast_val_finEquiv_symm {m : ℕ} [NeZero m] (t : ZMod m) :
    ((((ZMod.finEquiv m).symm t : Fin m) : ℕ) : ZMod m) = t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  exact ZMod.natCast_zmod_val t

/-- **The DDH exponents are close to uniform**: at a valid index of `n`-bit numerals,
`ddhExpo n i` is within statistical distance `(1/2)^n` of the uniform element of
`Z_{expOrd i}` (D10).

**Proof sketch.** `0 < expOrd i = dlM i < dlP i < 2^n` (`expOrd_of_valid`, `dlP_lt_two_pow`,
`WellFormedIndex.dlW_eq`), so `statClose_sampleBelowL` applies; map both samplers by
`Nat.cast : ℕ → ZMod (expOrd i)` (`StatClose.map`) and identify the image of the uniform
`Fin (expOrd i)` with the uniform `ZMod (expOrd i)` along `ZMod.finEquiv`
(`StatClose.comp_equiv_right`, `natCast_val_finEquiv_symm`). -/
theorem ddhExpo_statClose {n : ℕ} {i : List Bool} (hv : ExpValid i) (hw : WellFormedIndex n i) :
    StatClose (ddhExpo n i) (id : ZMod (expOrd i) → ZMod (expOrd i)) ((1 / 2 : ℝ) ^ n) := by
  have hm : 0 < expOrd i := NeZero.pos _
  have hmn : expOrd i < 2 ^ n := by
    rw [expOrd_of_valid hv, ← hw.dlW_eq]
    exact hv.2.2.1.trans (dlP_lt_two_pow i)
  have h := ((statClose_sampleBelowL hm hmn).map fun v : ℕ => (v : ZMod (expOrd i))).comp_equiv_right
    (ZMod.finEquiv (expOrd i)).symm.toEquiv
  have hY : (fun t : ZMod (expOrd i) =>
      ((((ZMod.finEquiv (expOrd i)).symm.toEquiv t : Fin (expOrd i)) : ℕ) : ZMod (expOrd i))) = id :=
    funext fun t => natCast_val_finEquiv_symm t
  rw [hY] at h
  exact h

/-- **The DDH ensemble** `{p ← Π̃_n; y ← Gen_q; a, b ← Z_q : (p, y, y^a, y^b, y^{ab})}` of
[PS10, Assumption 105.1]: a seed is the generator's coin string together with two blocks of
`n · n` coins from which the exponents `a, b ∈ Z_q` of the generated instance are read by
rejection (`ddhExpo`); the sample is the DDH tuple padded to `15n + 14` bits (exactly its
length from `n₀` on, `length_ddhTuple`). The seed type is a product of coin types, so the
uniform seed gives the generator uniform coins (D6) and is nonempty (`Ensemble.nonempty`,
run-3 audit P2-2, by instance resolution).

Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
depended on the fibre sizes and differed from `ddhRandom`'s (cubes), making `DDHAssumption`
false for every generator whose `q` varies with the coins. -/
noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1 * ddhExpo n (G.gen.runAt n [] z.1) z.2.2))

/-- **The random ensemble** `{p ← Π̃_n; y ← Gen_q; a, b, z ← Z_q : (p, y, y^a, y^b, y^z)}` of
[PS10, Assumption 105.1]: the generator's coins and three blocks of `n · n` coins for the
exponents `a, b, z` (`ddhExpo`); seeds nonempty by instance resolution (run-3 audit P2-2).

Repair (run-3 audit P8-1): product seeds instead of the dependent sum (see `ddhReal`). -/
noncomputable def ddhRandom (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.2))

/-- **The decisional Diffie–Hellman assumption** [PS10, Assumption 105.1] relative to a
safe-prime instance generator `G`: the ensembles `{(p, y, y^a, y^b, y^{ab})}` and
`{(p, y, y^a, y^b, y^z)}` are computationally indistinguishable (`Ensemble.Indist`,
[PS10, Definition 69.4]).

**Deviation:** the instance law is the generator's (the text's ideal `p ← Π̃_n; y ← Gen_q`);
the exponents are read from `n · n`-bit seed blocks by rejection, within `2^{-n}` of uniform
in `Z_q` (`ddhExpo`, D10; run-3 audit P8-1 — equivalent to the ideal-exponent form up to a
negligible statistical term); the tuple is a bit string of `15n + 14` bits; the
distinguisher receives `1^n` (D5). -/
def DDHAssumption (G : SafePrimeGen) : Prop := (ddhReal G).Indist (ddhRandom G)

/-! ## Public-key schemes with a key-dependent message space -/

/-- A **public-key encryption scheme with a key-dependent message space** (the shape of
[PS10, Definition 102.1] for El Gamal, whose messages are elements of the group `G_q`
determined by the public key): a PPT key generator `Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor
`Enc_pk(m)` activated on `⟨pk, m⟩`, and a deterministic polynomial-time decryptor on
`⟨sk, c⟩`. Correctness is stated per scheme (`elGamal_correct`), since it only holds for the
messages of the key's group.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message — here the message space is key-dependent and correctness is stated as a
separate theorem. -/
structure GroupPKScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec

namespace GroupPKScheme

/-- The challenge distribution `{(pk, sk) ← Gen(1^n); ⟨m₀, m₁⟩ ← M(1^n, pk) : ⟨pk, Enc_pk(m_b)⟩}`
for a message selector `M` and the bit `b` (the sampler over the coins of `Gen`, `M` and `Enc`). -/
def challenge (S : GroupPKScheme) (n : ℕ) (M : NUPPT) (b : Bool) :
    S.gen.Coins n × (M.Coins n × S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (if b then pairSndD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1)
        else pairFstD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1))) r.2.2)

/-- **Security with a key-dependent message space** (the form of [PS10, Definition 102.2]
used for El Gamal): for every non-uniform PPT message selector `M` and distinguisher `D` there
is a negligible `ε` with, for all `n`, advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀)⟩` and
`⟨pk, Enc_pk(m₁)⟩` for `⟨m₀, m₁⟩ ← M(1^n, pk)`.

**Deviation:** the text's "for all `m₀, m₁ ∈ {0,1}^n`" becomes "for all selectors `M`"
(the messages must lie in the group of the key, so they are functions of `pk`; constant
messages are the selectors returning their advice, `Secure.const`); `D` receives `1^n`. -/
def Secure (S : GroupPKScheme) : Prop :=
  ∀ M D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (S.challenge n M false) (S.challenge n M true) (D.distinguisherL n) ≤ ε n

end GroupPKScheme

/-- **The constant message selector**: the non-uniform PPT with no coins returning its advice
`⟨m₀(n), m₁(n)⟩` (length bounded by the syntactic polynomial `b`), whatever the public key. -/
noncomputable def constSelector (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) : NUPPT :=
  NUPPT.ofPolyTime NUPPT.polyTimeComputable_inAdvice (.const 0) b (fun n => pairEncode (m₀ n) (m₁ n)) hb

/-- The constant selector outputs `⟨m₀(n), m₁(n)⟩` on every input. -/
theorem constSelector_runAt (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) (pk : List Bool)
    (r : (constSelector m₀ m₁ b hb).Coins n) :
    (constSelector m₀ m₁ b hb).runAt n pk r = pairEncode (m₀ n) (m₁ n) := by
  rw [NUPPT.runAt_eq]
  unfold constSelector
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.inAdvice]

/-- The coins of the constant selector form a one-element type. -/
instance constSelector_unique (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) :
    Unique ((constSelector m₀ m₁ b hb).Coins n) :=
  haveI : IsEmpty (Fin ((constSelector m₀ m₁ b hb).coinLen n)) :=
    ⟨fun i => absurd i.2 (by simp [constSelector, NUPPT.coinLen])⟩
  Pi.uniqueOfIsEmpty _

/-- **Constant messages** (the quantifier form of [PS10, Definition 102.2]): a secure scheme
has, for every pair of message families `m₀, m₁` of polynomially bounded length and every
distinguisher `D`, a negligible `ε` with advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀(n))⟩`
and `⟨pk, Enc_pk(m₁(n))⟩`.

**Proof sketch.** Apply `h` to `constSelector m₀ m₁ b hb` and `D`; by `constSelector_runAt`
the challenge samplers are the constant-message samplers composed with the projection that
forgets the selector's (unique) coin, so `acceptProb_comp_equiv` with
`Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm` identifies the advantages. -/
theorem GroupPKScheme.Secure.const {S : GroupPKScheme} (h : S.Secure) (m₀ m₁ : ℕ → List Bool)
    (b : PolyExpr) (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      distAdv (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2))
        (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2))
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨ε, hε, hle⟩ := h (constSelector m₀ m₁ b hb) D
  refine ⟨ε, hε, fun n => le_of_eq_of_le ?_ (hle n)⟩
  let e : S.gen.Coins n × S.enc.Coins n ≃
      S.gen.Coins n × ((constSelector m₀ m₁ b hb).Coins n × S.enc.Coins n) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm
  unfold distAdv
  rw [← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) false),
    ← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) true)]
  have h0 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) false (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  have h1 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) true (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  rw [h0, h1]

/-! ## El Gamal [PS10, Algorithm 106.2] -/

/-- A uniform unit `g ∈ Z_p^*` by rejection: `1 + v` for `v` sampled below `p − 1`
(`sampleBelowL`, `n` trials of `n`-bit blocks); the fallback `g = 1` on failure.

**Deviation:** the text draws "a random element `g ∈ Z_p`" (possibly `0, ±1`, source
error 28). -/
def egUnit (n p : ℕ) (r : List Bool) : ℕ :=
  (sampleBelowL (p - 1) (Nat.size (p - 1)) n n r).getD 0 + 1

/-- `0 < egUnit n p r`. -/
theorem egUnit_pos (n p : ℕ) (r : List Bool) : 0 < egUnit n p r := Nat.succ_pos _

/-- `egUnit n p r < p` for `p ≥ 2`. -/
theorem egUnit_lt {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (r : List Bool) : egUnit n p r < p := by
  unfold egUnit
  match h : sampleBelowL (p - 1) (Nat.size (p - 1)) n n r with
  | some v => have := sampleBelowL_lt h; simp only [Option.getD_some]; omega
  | none => simp only [Option.getD_none]; omega

/-- **Canonicalisation of a message into `G_q`**: `m` itself when `0 < m < p` and `m^q ≡ 1
(mod p)` (i.e. `m ∈ G_q`, `mem_QR_iff_pow_eq_one`), and `1` otherwise.

**Deviation:** the message space is `G_q` (source error 28); a numeral outside it is
encrypted as the identity. -/
def egCanon (p q m : ℕ) : ℕ := if 0 < m ∧ m < p ∧ m ^ q % p = 1 then m else 1

/-- **The key material of El Gamal's `Gen`** [PS10, Algorithm 106.2] from the numerals `a, b`
of `p, q` and two coin segments: `g ← Z_p^*` (`egUnit`), `h = g² mod p`, `x ← Z_q`
(`sampleBelowL`), `pk = ⟨⟨p, ⟨q, h⟩⟩, h^x mod p⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, x⟩`.

**Deviation:** `pk` carries `q` and `sk` carries `q` (the text's `(p, h, a)`); the exponent
is sampled by rejection with the fallback `0`. -/
def egGenParts (n : ℕ) (a b r₁ r₂ : List Bool) : List Bool × List Bool :=
  (pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((egUnit n (listToNat a) r₁ ^ 2 % listToNat a) ^
        (sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0 % listToNat a)),
    pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0)))

/-- The coins of El Gamal's `Gen`: the instance generator's coins, then `n · n` coins for `g`
and `n · n` coins for `a`. -/
def egGenCoins (G : SafePrimeGen) : PolyExpr := .add G.gen.coins (.add (.mul .var .var) (.mul .var .var))

/-- The string function of El Gamal's `Gen` on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: run the
safe-prime generator on the first coin segment to get `⟨p, ⟨q, _⟩⟩`, then `egGenParts` on the
next two segments; output `⟨pk, sk⟩`. -/
def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  pairEncode
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).1
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).2

/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** Cut the coins at the unary lengths `1^{coins(n)}` and `1^{n·n}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
test `H.le` (the decrement `p − 1` and the bit length `Nat.size` are requested shared
primitives, as in the RSA generator); `h = g² mod p` and `h^x mod p` by `H.modExp`; the
numerals are padded to width `n` (`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGenRaw G) := by
  sorry

/-- **El Gamal's key generator** `Gen(1^n) = ⟨pk, sk⟩` as a uniform `NUPPT`. -/
noncomputable def egGen (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGenRaw H G) (egGenCoins G)

/-- The activation of `Gen`: `⟨pk, sk⟩ = egGenParts` on the safe-prime generator's output and
the coin segments. -/
theorem egGen_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : (egGen H G).Coins n) :
    (egGen H G).runAt n [] r =
      pairEncode
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).1
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).2 := by
  rw [NUPPT.runAt_eq]
  unfold egGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen]

/-- **The ciphertext of El Gamal's `Enc`** [PS10, Algorithm 106.2] on the public key
`pk = ⟨⟨p, ⟨q, h⟩⟩, A⟩` (`A = h^a`), the message numeral `m` and coins `r`: `b ← Z_q`
(`sampleBelowL`), output `⟨h^b mod p, A^b · m' mod p⟩` with `m' = egCanon p q m`. -/
def egEncParts (n : ℕ) (pk m r : List Bool) : List Bool :=
  pairEncode
    (natToList n (dlG (pairFstD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 % dlP (pairFstD pk)))
    (natToList n (listToNat (pairSndD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 *
        egCanon (dlP (pairFstD pk)) (dlM (pairFstD pk)) (listToNat m) % dlP (pairFstD pk)))

/-- The string function of `Enc` on the raw layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, α⟩, r⟩`. -/
def egEncRaw (z : List Bool) : List Bool :=
  egEncParts (NUPPT.inParam z).length (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z)

/-- **El Gamal's `Enc` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** The exponent `b` by the rejection loop (`polyTimeComputable_iterateFind`,
`H.le`); `h^b`, `A^b`, the membership test `m^q mod p = 1` (`H.modExp`, `polyTimeComputable_pairEq`,
`H.le` for `0 < m < p`, `polyTimeComputable_ite` for the canonicalisation); the product by
`H.mul` and the reduction modulo `p` by `H.divMod`; width-`n` padding by
`polyTimeComputable_unaryPoly`/`_blockMap`; pair. -/
theorem polyTimeComputable_egEncRaw (H : ArithmeticFP) : PolyTimeComputable egEncRaw := by
  sorry

/-- **El Gamal's encryptor** as a uniform `NUPPT` with `n · n` coins. -/
noncomputable def egEnc (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egEncRaw H) (.mul .var .var)

/-- The activation of `Enc` on `⟨pk, m⟩`. -/
theorem egEnc_runAt (H : ArithmeticFP) (n : ℕ) (pk m : List Bool) (r : (egEnc H).Coins n) :
    (egEnc H).runAt n (pairEncode pk m) r = egEncParts n pk m (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold egEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [egEncRaw, NUPPT.inParam, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

/-- **El Gamal's `Dec`** [PS10, Algorithm 106.2, `Dec_sk(c₁, c₂) = c₂ / c₁^a mod p`] as a
composition of the bundle's string functions on `⟨⟨⟨p, ⟨q, h⟩⟩, a⟩, ⟨c₁, c₂⟩⟩`:
`c₁^a mod p` (`modExpStr`), its inverse modulo `p` (`xgcdStr`, second component), the product
with `c₂` (`mulStr`) reduced modulo `p` (`divModStr`, second component). -/
def egDecStr (z : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (mulStr (pairEncode (pairSndD (pairSndD z))
      (pairSndD (xgcdStr (pairEncode
        (modExpStr (pairEncode (pairFstD (pairSndD z))
          (pairEncode (pairSndD (pairFstD z)) (pairFstD (pairFstD (pairFstD z))))))
        (pairFstD (pairFstD (pairFstD z))))))))
    (pairFstD (pairFstD (pairFstD z)))))

/-- Transport of polynomial-time computability along a pointwise equation (used to avoid
the unifier unfolding the arithmetic string functions when matching a composition chain
against a definition; integration note, run 2). -/
private theorem polyTimeComputable_of_forall_eq {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (h : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext h : f = g) ▸ hf

/-- **`Dec` is polynomial-time** given the arithmetic bundle (a composition of its functions).

The chain is assembled in composition form and transported to `egDecStr` pointwise
(`polyTimeComputable_of_forall_eq` with `Function.comp_apply`): matching the composition
directly against the unfolded definition makes the unifier unfold `xgcdStr`/`modExpStr`
and does not terminate in practice. -/
theorem polyTimeComputable_egDecStr (H : ArithmeticFP) : PolyTimeComputable egDecStr := by
  have hp := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have ha := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hexp := H.modExp.comp (hc₁.pairEncode (ha.pairEncode hp))
  have hinv := polyTimeComputable_pairSndD.comp (H.xgcd.comp (hexp.pairEncode hp))
  have hmul := H.mul.comp (hc₂.pairEncode hinv)
  refine polyTimeComputable_of_forall_eq
    (polyTimeComputable_pairSndD.comp (H.divMod.comp (hmul.pairEncode hp))) (fun z => ?_)
  simp only [Function.comp_apply, egDecStr]

/-- **Unfolding `Dec`**: on `⟨⟨⟨p, t⟩, a⟩, ⟨c₁, c₂⟩⟩` with `0 < p` it returns the numeral of
`c₂ · (c₁^a mod p)⁻¹ mod p` of the width of `p`'s numeral, the inverse being that of `Z_p`
(`ZMod.inv`).

**Proof sketch.** `modExpStr_pairEncode` gives the numeral `v` of `c₁^a mod p < p < 2^{|p|}`
(`listToNat_natToList`); `xgcdStr` returns the numeral of `(v : Z_p)⁻¹.val < p`; `mulStr_pairEncode`
gives the lossless product (`mul_lt_two_pow_add`); `divModStr`'s second component reduces it
modulo `p`. -/
theorem egDecStr_apply (pstr t a c₁ c₂ : List Bool) (hp : 0 < listToNat pstr) :
    egDecStr (pairEncode (pairEncode (pairEncode pstr t) a) (pairEncode c₁ c₂)) =
      natToList pstr.length (listToNat c₂ *
        (((listToNat c₁ ^ listToNat a % listToNat pstr : ℕ) : ZMod (listToNat pstr))⁻¹).val %
          listToNat pstr) := by
  sorry

/-- **El Gamal** [PS10, Algorithm 106.2] from a safe-prime instance generator `G` (used for
`(p, q)` only) and the arithmetic bundle: `Gen(1^n) = ⟨⟨⟨p, ⟨q, h⟩⟩, h^a⟩, ⟨⟨p, ⟨q, h⟩⟩, a⟩⟩` with
`h = g²` for `g ← Z_p^*` and `a ← Z_q`; `Enc_pk(m) = ⟨h^b, (h^a)^b · m⟩` for `b ← Z_q`;
`Dec_sk(c₁, c₂) = c₂ / c₁^a`.

**Deviation:** module docstring (rejection-sampled `g`, `a`, `b`; `q` in the keys;
canonicalised messages; the generator component of `G` is ignored). -/
noncomputable def elGamal (H : ArithmeticFP) (G : SafePrimeGen) : GroupPKScheme where
  gen := egGen H G
  enc := egEnc H
  dec := egDecStr
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_egDecStr H

/-- **Correctness of El Gamal** [PS10, Algorithm 106.2, "`Dec_sk(c) = c₂ / c₁^a mod p`"]: for
`n ≥ n₀`, every key pair and every message `m` of the key's group `G_q` (`egCanon p q m = m`),
`Dec_sk(Enc_pk(m))` decodes to the `n`-bit numeral of `m`.

**Proof sketch.** By `egGen_runAt` (the first coin segment has length `coinLen n`, so it is
`List.ofFn r'` for a typed `r'` and `G.valid`/`G.wellFormed` apply: `p = 2q + 1` prime,
`n`-bit numerals) the keys are `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, a⟩` with
`h = g² mod p`, `0 < h < p` (`egUnit_pos`, `egUnit_lt`, `Nat.Prime.dvd_of_dvd_pow`); by
`egEnc_runAt` the ciphertext is `⟨h^b mod p, (h^a mod p)^b · m mod p⟩` (`dlP`, `dlM`, `dlG`
read back by `listToNat_natToList`), and by `egDecStr_apply` the decryption is
`c₂ · ((h^b mod p)^a mod p)⁻¹ mod p`. In `Z_p` (units `h_u`, `m_u`):
`(h^a)^b · m · ((h^b)^a)⁻¹ = m` (`pow_mul`, `mul_comm`, `Units.mul_inv_cancel_right`,
`ZMod.natCast_mod`), so the result is the numeral of `m < p < 2^n` (`natToList n m`), decoded
by `decodeFin_ofFn`. -/
theorem elGamal_correct (H : ArithmeticFP) (G : SafePrimeGen) {n : ℕ} (hn : G.n₀ ≤ n)
    (rg : (egGen H G).Coins n) (re : (egEnc H).Coins n) (m : ℕ)
    (hm : egCanon (dlP (pairFstD (pairFstD ((egGen H G).runAt n [] rg))))
      (dlM (pairFstD (pairFstD ((egGen H G).runAt n [] rg)))) m = m) :
    decodeFin n (egDecStr (pairEncode (pairSndD ((egGen H G).runAt n [] rg))
      ((egEnc H).runAt n (pairEncode (pairFstD ((egGen H G).runAt n [] rg)) (natToList n m)) re))) =
      some (natToBits n m) := by
  sorry

/-! ## The derived instance generator and Theorem 107.3 -/

/-- The generator `h` of `G_q` derived from a unit `g`: `g² mod p`, replaced by `4 = 2²` when
`g² ≡ 1` (the text's `h = g²` with the degenerate case `h = 1` removed; Claim-107.a). -/
def egSquareGen (p g : ℕ) : ℕ := if g ^ 2 % p = 1 then 4 else g ^ 2 % p

/-- **The derived generator is a generator of `G_q`** (NT-105.a and Claim-107.a): for a safe
prime `p = 2q + 1` and `0 < g < p`, `h = egSquareGen p g` satisfies `0 < h < p` and
`orderOf (h : Z_p) = q`.

**Proof sketch.** Let `u` be the unit `g mod p`. If `g² mod p ≠ 1`, then `h = g² mod p` is the
value of `u² ∈ G_q` (`ZMod.natCast_mod`, `ZMod.coe_unitOfCoprime`), nonzero since `p ∤ g²`
(`Nat.Prime.dvd_of_dvd_pow`), different from `1` (`ZMod.val_natCast_of_lt`), of order `q`
(`orderOf_eq_of_mem_QR`, `sq_mem_QR`, `orderOf_units`). Otherwise `h = 4 = 2²` with `5 ≤ p`
(`five_le_safe`), the value of the square of the unit `2`, different from `1`, of order `q`
likewise. -/
theorem egSquareGen_valid {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p = 2 * q + 1)
    {g : ℕ} (hg0 : 0 < g) (hgp : g < p) :
    0 < egSquareGen p g ∧ egSquareGen p g < p ∧ orderOf ((egSquareGen p g : ℕ) : ZMod p) = q := by
  have h5 := five_le_safe hpq
  -- the order of the square of a unit `u` with `u² ≠ 1`
  have key : ∀ (u : (ZMod p)ˣ) (h : ℕ), ((h : ℕ) : ZMod p) = (u : ZMod p) ^ 2 → h < p → h ≠ 1 →
      orderOf ((h : ℕ) : ZMod p) = q := by
    intro u h hu hhp hh1
    have hne : u ^ 2 ≠ 1 := by
      intro h1
      apply hh1
      have h2 : ((h : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one, Nat.cast_one]
      have h3 := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt hhp, ZMod.val_natCast_of_lt (by omega)] at h3
    rw [hu, ← Units.val_pow_eq_pow_val, orderOf_units]
    exact orderOf_eq_of_mem_QR hpq (sq_mem_QR u) hne
  have hcop : Nat.Coprime g p :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hg0 hgp)).symm
  by_cases h1 : g ^ 2 % p = 1
  · have hval : egSquareGen p g = 4 := if_pos h1
    refine ⟨by rw [hval]; norm_num, by rw [hval]; omega, ?_⟩
    have hcop2 : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp.out).2 (by omega)
    rw [hval]
    refine key (ZMod.unitOfCoprime 2 hcop2) 4 ?_ (by omega) (by norm_num)
    rw [ZMod.coe_unitOfCoprime]
    norm_num
  · have hval : egSquareGen p g = g ^ 2 % p := if_neg h1
    have hlt : g ^ 2 % p < p := Nat.mod_lt _ hp.out.pos
    refine ⟨?_, by rw [hval]; exact hlt, ?_⟩
    · rw [hval]
      apply Nat.pos_of_ne_zero
      intro h0
      have hdvd : p ∣ g := hp.out.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0)
      exact absurd (Nat.le_of_dvd hg0 hdvd) (not_le.2 hgp)
    · rw [hval]
      refine key (ZMod.unitOfCoprime g hcop) (g ^ 2 % p) ?_ hlt h1
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_mod, Nat.cast_pow]

/-- The index `⟨p, ⟨q, h⟩⟩` of the derived generator from the numerals `a, b` of `p, q` and
the coin segment of `g`. -/
def egGroupParts (n : ℕ) (a b r₁ : List Bool) : List Bool :=
  pairEncode a (pairEncode b (natToList n (egSquareGen (listToNat a) (egUnit n (listToNat a) r₁))))

/-- The string function of the derived generator on `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: the safe-prime
generator on the first coin segment, then `egGroupParts` on the next `n · n` coins. -/
def egGroupGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  egGroupParts (NUPPT.inParam z).length
    (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
    (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
    (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
      ((NUPPT.inParam z).length * (NUPPT.inParam z).length))

/-- **The derived generator is polynomial-time** given the arithmetic bundle (the first two
steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1` by `H.modExp` and
`polyTimeComputable_pairEq` with the constant numeral of `4` on `polyTimeComputable_ite`). -/
theorem polyTimeComputable_egGroupGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGroupGenRaw G) := by
  sorry

/-- The machine of the derived generator: a uniform `NUPPT` with `G`'s coins plus `n · n`. -/
noncomputable def egGroupGenMachine (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGroupGenRaw H G) (.add G.gen.coins (.mul .var .var))

/-- The activation of the derived generator's machine. -/
theorem egGroupGenMachine_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    (egGroupGenMachine H G).runAt n [] r =
      egGroupParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
        (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
        (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n)) := by
  rw [NUPPT.runAt_eq]
  unfold egGroupGenMachine
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGroupGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen]

/-- A string of the right length is the encoding of a typed coin string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- The first coin segment of the derived generator is a coin string of `G.gen`. -/
private theorem exists_take_coins (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    ∃ r' : G.gen.Coins n, List.ofFn r' = (List.ofFn r).take (G.gen.coinLen n) := by
  apply exists_ofFn_eq
  simp only [List.length_take, List.length_ofFn, NUPPT.coinLen, egGroupGenMachine,
    NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add]
  omega

/-- **The derived generator outputs safe-prime instances** from `G.n₀` on: the index
`⟨p, ⟨q, egSquareGen p g⟩⟩` is valid.

**Proof sketch.** The first coin segment is a typed coin string of `G.gen` (`exists_take_coins`),
so `G.valid` and `G.wellFormed` give `⟨a, ⟨b, c⟩⟩` with `p = 2q + 1` prime; reading the output
back (`pairFstD_pairEncode`, `listToNat_natToList`) reduces the claim to `egSquareGen_valid`
with `0 < g < p` from `egUnit_pos`, `egUnit_lt`. -/
theorem egGroupGen_valid (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    SafePrimeValid ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  have hv := G.valid n r' hn
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := G.wellFormed n r' hn
  rw [ho] at hv ⊢
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  simp only [SafePrimeValid, ExpValid, dlP, dlM, dlG, pairFstD_pairEncode, pairSndD_pairEncode] at hv ⊢
  -- the occurrence of `p` inside the type `ZMod (dlP …)` is not reached by `simp`; `rw` abstracts it
  rw [pairFstD_pairEncode]
  haveI : Fact (listToNat a).Prime := ⟨hv.1.1⟩
  haveI : Fact (listToNat b).Prime := ⟨hv.2.1⟩
  have hpq := hv.2.2
  have hg0 := egUnit_pos n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  have hgp := egUnit_lt hv.1.1.two_le n (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  obtain ⟨hh0, hhp, hord⟩ := egSquareGen_valid hpq hg0 hgp
  have hlt : egSquareGen (listToNat a) (egUnit n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))) <
      2 ^ n := by
    have h2 : listToNat a < 2 ^ n := by
      rw [← ha]
      exact listToNat_lt_two_pow a
    exact hhp.trans h2
  rw [listToNat_natToList hlt]
  exact ⟨⟨hv.1.1, hv.1.2.1, hv.1.2.2.1, hh0, hhp, hord⟩, hv.2.1, hpq⟩

/-- **The derived generator outputs well-formed indices** from `G.n₀` on. -/
theorem egGroupGen_wellFormed (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    WellFormedIndex n ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := G.wellFormed n r' hn
  rw [ho]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  exact ⟨a, b, _, rfl, ha, hb, length_natToList _ _⟩

/-- **The derived safe-prime instance generator** of El Gamal: the same `(p, q)` as `G`,
`h = g²` for `g ← Z_p^*` with the fallback `4` on `g² = 1`. The DDH assumption of
Theorem 107.3 is relative to this generator; its `h` is the text's "`y ← Gen_q`" up to the
`1/q` term of Claim-107.a. -/
noncomputable def egGroupGen (H : ArithmeticFP) (G : SafePrimeGen) : SafePrimeGen where
  gen := egGroupGenMachine H G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  n₀ := G.n₀
  valid := egGroupGen_valid H G
  wellFormed := egGroupGen_wellFormed H G

/-- **Theorem 107.3** [PS10, Theorem 107.3]: if the DDH assumption holds (for the derived
generator) then El Gamal with message space `G_q` is secure, for safe primes of full length
except on a negligible set of the generator's coins (and under the arithmetic hypotheses).

**Deviation:** message space `G_q` and the chosen-message form of security (the text's
`m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
makes the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of probability
`δ n`; the text leaves the proof as an exercise and omits the generator-versus-square term.

Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b` (advice
`⟨M.advice n, ⟨D.advice n, [b]⟩⟩`, coins `M.coins + D.coins`): on a tuple `t`
(parsed by `pairFstD`/`pairSndD`, the last numeral cut to `n` bits by
`polyTimeComputable_pairTakePoly var`) with `t = ⟨i, ⟨A, ⟨B, Z⟩⟩⟩`, set `pk := ⟨i, A⟩`, run
`M(1^n, pk)` (`NUPPT.exists_seq`), take the `b`-th message, canonicalise it (`H.modExp`,
`H.le`, `polyTimeComputable_ite`), and output `D(1^n, ⟨pk, ⟨B, Z · m' mod p⟩⟩)` (`H.mul`,
`H.divMod`, `NUPPT.exists_comp`). *Hybrid 1* (the square-versus-generator event): the coins of
`challenge n M b` — `G`'s coins, the `n · n`-bit segments of `g` and `a` (`egGen_runAt`), `M`'s
coins and the `n · n` coins of `Enc` for `b'` (`egEnc_runAt`) — are in bijection with the seeds
`(r', (e₁, e₂))` of `ddhReal (egGroupGen H G)` together with `D_b`'s coins
(`acceptProb_comp_equiv`), `r'` being `G`'s coins followed by the segment of `g`
(`egGroupGenMachine_runAt`). Under this bijection the two experiments run `D` on the *same*
string unless `g² ≡ 1 (mod p)`: `ddhExpo` is the very sampler `sampleBelowL q (Nat.size q) n n`
of `egGenParts`/`egEncParts` (`expOrd_of_valid` at the valid index), `h^{(ab' mod q)} = h^{ab'}`
since `h` has order `q` (`egSquareGen_valid`), and `egSquareGen p g = g² mod p` unless
`g² ≡ 1`. Hence `|Pr[D(challenge b)] − Pr[D_b(ddhReal)]| ≤ Pr[g² ≡ 1]` (`uprob_mono`,
`statClose_of_uprob_ne`); `egUnit` is within `(1/2)^n` of the uniform unit
(`statClose_sampleBelowL` with `m = p − 1`, `StatClose.map`), so `Pr[g² ≡ 1] ≤ 1/q + (1/2)^n`
(`uprob_sq_eq_one`, `card_sqrt_safe`), and `hbig` gives, for `n ≥ n₀`, a set of `G`'s coins of
probability `≤ δ n` outside which `2^{n−1} ≤ p = 2q + 1` and `1/q ≤ 8 (1/2)^n`; altogether the
hybrid-1 gap is at most `9 (1/2)^n + δ n =: η n`. *Hybrid 2* (DDH): `hDDH D_b` through
`Ensemble.indist_iff_exists_negligible` gives `ε_b` with
`|Pr[D_b(ddhReal)] − Pr[D_b(ddhRandom)]| ≤ ε_b n`. *Hybrid 3* (the two random worlds coincide
up to the exponent sampler): in `ddhRandom`, `Z = h^z` with `z = ddhExpo n i e₃` independent
of the rest; replacing `z` by an ideal uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`,
`StatClose.abs_uprob_sub_le_prod`) in each world, and for ideal `z` and a fixed rest,
`z ↦ h^z · m'_b` is a bijection of `G_q` for `m'_b ∈ G_q` (`expF_injective`, `card_QR_safe`,
`Equiv.mulRight`, or `HardcoreBit.pushesUniform_add_right` on the exponent `z + dlog m'_b`), so
`uprob_prod` and `uprob_comp_equiv` give `|Pr[D_0(ddhRandom)] − Pr[D_1(ddhRandom)]| ≤ 2 (1/2)^n`.
Hence the advantage is at most `2 η n + ε_0 n + ε_1 n + 2 (1/2)^n` for `n ≥ n₀` (and `≤ 1`
below), negligible by `negligible_two_pow_neg`, `Negligible.const_mul`, `Negligible.add`,
`Negligible.mono`. -/
theorem elGamal_secure (H : ArithmeticFP) (G : SafePrimeGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ)
    (hDDH : DDHAssumption (egGroupGen H G)) : (elGamal H G).Secure := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/Concrete.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.OneWayFunctions.Amplification
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Cryptography.NumberTheory.Units
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Candidates.Arithmetic
import Mathlib.Logic.Equiv.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete lemmas for the factoring-based candidates

The concrete-layer content of the reductions of [PS10, §2.3–§2.4, §2.7] (Theorems 33.5,
36.3, 51.1), stated as exact inequalities at one security parameter in the style of
[Gar26] and consumed by `TCSlib.Cryptography.Candidates.Factoring`:

* *conditioning* (lemma C1 of the chapter 2 inventory): the probability of an event on the
  uniform subtype `{a // E a}` is `Pr[E ∧ S] / Pr[E]`, and is at least
  `1 - (1 - Pr[S]) / δ` when `Pr[E] ≥ δ` — the step of [PS10, Theorem 33.5] turning an
  inverter of `f_mult` on uniform pairs into a factorer on uniform *prime* pairs;
* the *diagonal*: a uniform pair of elements of a finite type coincides with probability
  `1 / |γ|` (the switch from `Π_n × Π_n` to pairs of distinct primes);
* *random-position planting with a good set* (lemma C3): the one-call reduction of
  [PS10, Algorithm 37.4] (plant the challenge at a uniform position of a fresh tuple,
  `OneWay.yaoTry`) inverts `f` on a uniform *good* input with probability at least
  `(μ - (1 - Pr[G])^m) / m`, `μ` the success of the inverter of the direct product
  `prodFun f m` — the mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the
  bad set replaced by the complement of the good set;
* the *tail bound* `(1 - 1/a)^{a k} ≤ e^{-k}` (lemma C8) and its instance
  `(1 - 1/(4n²))^{4n³} ≤ e^{-n}` [PS10, Claim 36.2], with `e^{-n} ≤ 2^{-n}`;
* the *prime-pair density* on `n`-bit strings and the identification of the uniform subtype
  of prime pairs with `Π_n × Π_n` (`primesPairEquiv`);
* the type `DistinctPrimes n` of pairs of distinct primes of `Π_n` (the restriction `p ≠ q`
  of the decision log "Rabin/RSA scope") with its string encoding, its `NeZero`/`Fact`
  instances and `Φ(pq) = (p−1)(q−1)` (moved here from `RSA.lean`, run-3 audit P7-6);
* *block rejection sampling* on coin lists (`rejectBlocksL`, run-3 audit P7-6): the one
  sampler behind the honest samplers of `Z_N^*`, `Z*_{Φ(N)}` and the restricted prime classes
  of [PS10, §2.9–§2.12], with its closeness lemma `statClose_rejectBlocksL` (lemma C4 on
  coin lists).

## Main definitions

* `TCSlib.Cryptography.Candidates.primesPairEquiv` — prime pairs of `n`-bit strings as
  `Π_n × Π_n`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes` — pairs of distinct primes of `Π_n` (the
  index distribution of the factoring assumption and of the RSA/Rabin moduli), with
  `DistinctPrimes.default`, `encodeDistinctPrimes`, `decodeDistinctPrimes`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL` — block rejection sampling on a coin list.

## Main results

* `TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype`,
  `TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype` (C1),
  `TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add`,
  `TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq` — conditioning on an event.
* `TCSlib.Cryptography.Candidates.uprob_diag` — the diagonal of a uniform pair.
* `TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant` (C3) — random-position
  planting with a good set [PS10, Algorithm 37.4, Theorem 36.3].
* `TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg` (C8),
  `TCSlib.Cryptography.Candidates.claim_36_2` [PS10, Claim 36.2],
  `TCSlib.Cryptography.Candidates.exp_neg_le_half_pow`.
* `TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits`,
  `TCSlib.Cryptography.Candidates.one_div_card_primes_le` — density facts in the forms
  the reductions use.
* `TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt` — the encoding of distinct
  prime pairs is lossless; `Π_n` has no two distinct primes for `n < 2`.
* `TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul`,
  `TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient` — `Φ(pq) = (p−1)(q−1) ≥ 2`.
* `TCSlib.Cryptography.Candidates.rejectBlocksL_spec`,
  `TCSlib.Cryptography.Candidates.statClose_rejectBlocksL` — accepted values satisfy the
  test; the total sampler is within `(1 − Pr[E])^T` of uniform on `E`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.1–§2.3.2, Theorem 33.5, Algorithm 33.6; §2.4.2, Claim 36.2, Theorem 36.3,
  Algorithm 37.4; §2.7, Theorem 51.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1 and Figure 2.2: planting at a uniform
  position).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing Finset TCSlib.Cryptography.OneWay NumberTheory

/-! ## Conditioning on an event (lemma C1) -/

section Conditioning

variable {α ρ : Type*} [Fintype α] [Fintype ρ]

/-- **Conditioning, multiplicative form**: `Pr[E ∧ S] = Pr[E] · Pr[S | E]`, where `Pr[S | E]`
is the probability of `S` under the uniform distribution on the subtype `{a // E a}`
(lemma C1 of the chapter 2 inventory, [PS10, proof of Theorem 33.5]: "`A'` feeds `A` a
uniformly distributed input … and replaces `xy` with `z` if both are prime"). -/
theorem uprob_and_eq_mul_subtype (E S : α → Prop) [DecidablePred E] :
    uprob (fun a => E a ∧ S a) = uprob E * uprob (fun z : {a // E a} => S z.1) := by
  unfold uprob
  rw [← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter E S)]
  rcases (Fintype.card {a // E a}).eq_zero_or_pos with h0 | hpos
  · haveI : IsEmpty {a // E a} := Fintype.card_eq_zero_iff.mp h0
    have h1 : Nat.card {z : {a // E a} // S z.1} = 0 := Nat.card_of_isEmpty
    have h2 : Nat.card {a // E a} = 0 := Nat.card_of_isEmpty
    rw [h1, h2]
    simp
  · rw [Nat.card_eq_fintype_card (α := {a // E a})]
    have hc : (Fintype.card {a // E a} : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- **Conditioning, lower bound** (lemma C1, [PS10, proof of Theorem 33.5, the union
bound]): if `Pr[E] ≥ δ > 0` then `Pr[S | E] ≥ 1 - (1 - Pr[S]) / δ`. With `Pr[E] ≥ 1/(4n²)`
and `1 - Pr[S] ≤ 1/(8(n+1)²)` this gives `Pr[S | E] ≥ 1/2`.

**Proof sketch.** `Pr[S] ≤ Pr[E ∧ S] + Pr[¬E] = Pr[E]·Pr[S | E] + 1 - Pr[E]`, so
`Pr[E]·(1 - Pr[S | E]) ≤ 1 - Pr[S]`; divide by `Pr[E] ≥ δ`. -/
theorem one_sub_div_le_uprob_subtype (E S : α → Prop) [DecidablePred E] {δ : ℝ} (hδ : 0 < δ)
    (hE : δ ≤ uprob E) : 1 - (1 - uprob S) / δ ≤ uprob (fun z : {a // E a} => S z.1) := by
  haveI : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : uprob E = 0 := by
      unfold uprob
      simp
    linarith
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  rw [uprob_not, hES] at hsplit
  have hEpos : 0 < uprob E := lt_of_lt_of_le hδ hE
  have h1 : 1 - uprob (fun z : {a // E a} => S z.1) ≤ (1 - uprob S) / uprob E := by
    rw [le_div_iff₀ hEpos]
    nlinarith
  have h2 : (1 - uprob S) / uprob E ≤ (1 - uprob S) / δ :=
    div_le_div_of_nonneg_left (by linarith [uprob_le_one S]) hδ hE
  linarith

/-- **Dropping a conditioning**: `Pr[S] ≤ Pr[S | E] + Pr[¬E]` (the switch from the uniform
pair of primes `Π_n × Π_n` to the uniform pair of *distinct* primes, whose complement — the
diagonal — has probability `1/|Π_n|`). -/
theorem uprob_le_uprob_subtype_add (E S : α → Prop) [DecidablePred E] :
    uprob S ≤ uprob (fun z : {a // E a} => S z.1) + uprob (fun a => ¬ E a) := by
  have hES := uprob_and_eq_mul_subtype E S
  have hsplit : uprob S ≤ uprob (fun a => E a ∧ S a) + uprob (fun a => ¬ E a) := by
    refine (uprob_mono ?_).trans (uprob_or_le _ _)
    intro a ha
    by_cases hEa : E a
    · exact Or.inl ⟨hEa, ha⟩
    · exact Or.inr hEa
  have h1 : uprob (fun a => E a ∧ S a) ≤ uprob (fun z : {a // E a} => S z.1) := by
    rw [hES]
    exact mul_le_of_le_one_left (uprob_nonneg _) (uprob_le_one _)
  linarith

/-- Conditioning on the first coordinate of a product: the uniform subtype `{a // E a}` with
independent auxiliary coins `ρ` is the uniform subtype of pairs whose first coordinate
satisfies `E` (relabelling by `Equiv.prodSubtypeFstEquivSubtypeProd`). -/
theorem uprob_subtype_prod_eq (E : α → Prop) [DecidablePred E] (S : α × ρ → Prop) :
    uprob (fun z : {a // E a} × ρ => S (z.1.1, z.2)) =
      uprob (fun z : {w : α × ρ // E w.1} => S z.1) :=
  uprob_comp_equiv (Equiv.prodSubtypeFstEquivSubtypeProd (p := E)).symm fun z => S z.1

/-- **The diagonal**: a uniform pair of elements of a nonempty finite type consists of equal
elements with probability `1 / |γ|`. -/
theorem uprob_diag {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ] :
    uprob (fun z : γ × γ => z.2 = z.1) = 1 / Fintype.card γ := by
  rw [uprob_prod]
  simp only [uprob_eq_one_div_card]
  exact uexp_const _

end Conditioning

/-! ## Random-position planting with a good set (lemma C3) -/

section Planting

variable {α β ρ : Type*} [Fintype α] [Fintype ρ] {m : ℕ}

/-- **Random-position planting with a good set** (lemma C3 of the chapter 2 inventory; the
concrete content of [PS10, Theorem 36.3] with the one-call reduction of
[PS10, Algorithm 37.4] planting the challenge at a *uniform* position): if `B` inverts the
direct product `prodFun f m` with probability `μ`, then either every coordinate of the
uniform tuple is outside the good set `G` (probability `(1 - Pr[G])^m`) or the one-call
reduction `yaoTry f B` (plant `f x` at the uniform position `i` of a fresh tuple, call `B`,
return the `i`-th answer) inverts `f(x)` for a uniform `x` lying in `G`:
`μ ≤ (1 - Pr[G])^m + m · Pr_{x, i, xs, r}[x ∈ G ∧ f(yaoTry f B (f x) (i, xs, r)) = f x]`.
Mirror of `OneWay.invProb_prodFun_le` [Gar26, Theorem 2.1] with the bad set replaced by
`¬G`.

**Deviation:** [PS10, Algorithm 37.4] plants at the first prime pair and tests primality;
planting at a uniform position needs no primality test (the text's exercise, p. 37).

**Proof sketch.** Success of `B` on `(xs, r)` means that every `xs i` is outside `G` or that
some position `i` has `xs i ∈ G` and the `i`-th answer inverts `f (xs i)`
(`uprob_mono`, `uprob_or_le`, `uprob_exists_le`). The first event has probability
`(1 - Pr[G])^m` (`uprob_fst`, `OneWay.uprob_pi_forall`, `uprob_not`). For fixed `i`, planting
a fresh uniform `x` at position `i` leaves the tuple uniform (`OneWay.uprob_update`,
`OneWay.prodFun_update`), which rewrites the `i`-th event as the planted experiment; summing
over `i` makes the position uniform (`OneWay.sum_uprob_eq_card_mul`), and a relabelling of
the coin space finishes. -/
theorem invProb_prodFun_le_plant [Nonempty α] [Nonempty ρ] (f : α → β)
    (B : (Fin m → β) → ρ → (Fin m → α)) (G : α → Prop) :
    invProb (prodFun f m) B ≤ (1 - uprob G) ^ m +
      m * uprob (fun z : α × (Fin m × ((Fin m → α) × ρ)) =>
        G z.1 ∧ f (yaoTry f B (f z.1) z.2) = f z.1) := by
  classical
  unfold invProb
  calc uprob (fun z : (Fin m → α) × ρ =>
        prodFun f m (B (prodFun f m z.1) z.2) = prodFun f m z.1)
      ≤ uprob (fun z : (Fin m → α) × ρ => (∀ i, ¬ G (z.1 i)) ∨
          ∃ i ∈ (univ : Finset (Fin m)),
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) := by
        apply uprob_mono
        rintro ⟨xs, r⟩ h
        by_cases hall : ∀ i, ¬ G (xs i)
        · exact Or.inl hall
        · push_neg at hall
          obtain ⟨i, hi⟩ := hall
          exact Or.inr ⟨i, mem_univ _, hi, congrFun h i⟩
    _ ≤ uprob (fun z : (Fin m → α) × ρ => ∀ i, ¬ G (z.1 i)) +
          ∑ i, uprob (fun z : (Fin m → α) × ρ =>
            G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) :=
        (uprob_or_le _ _).trans (add_le_add_left (uprob_exists_le _ _) _)
    _ ≤ _ := by
        apply add_le_add
        · rw [uprob_fst (fun xs : Fin m → α => ∀ i, ¬ G (xs i)),
            uprob_pi_forall (ι := Fin m) (fun x => ¬ G x), uprob_not, Fintype.card_fin]
        · have hplant : ∀ i, uprob (fun z : (Fin m → α) × ρ =>
              G (z.1 i) ∧ f (B (prodFun f m z.1) z.2 i) = f (z.1 i)) =
              uprob (fun z : α × ((Fin m → α) × ρ) =>
                G z.1 ∧ f (yaoTry f B (f z.1) (i, z.2)) = f z.1) := by
            intro i
            rw [← uprob_update i (fun xs r =>
              G (xs i) ∧ f (B (prodFun f m xs) r i) = f (xs i))]
            apply uprob_congr
            rintro ⟨x, xs, r⟩
            simp [yaoTry, prodFun_update]
          simp only [hplant]
          rw [sum_uprob_eq_card_mul, Fintype.card_fin]
          let e : α × (Fin m × ((Fin m → α) × ρ)) ≃ Fin m × (α × ((Fin m → α) × ρ)) :=
            { toFun := fun z => (z.2.1, (z.1, z.2.2))
              invFun := fun z => (z.2.1, (z.1, z.2.2))
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          rw [← uprob_comp_equiv e]
          exact le_rfl

end Planting

/-! ## Tail bounds (lemma C8, Claim 36.2) -/

/-- **Tail bound** (lemma C8 of the chapter 2 inventory): `(1 - 1/a)^{a·k} ≤ e^{-k}` for
`a ≥ 1` (the inequality `1 - t ≤ e^{-t}` raised to the power `a·k`,
`Real.one_sub_div_pow_le_exp_neg`). -/
theorem one_sub_one_div_pow_le_exp_neg (a k : ℕ) (ha : 0 < a) :
    (1 - 1 / (a : ℝ)) ^ (a * k) ≤ Real.exp (-(k : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := a * k) (t := (k : ℝ))
    (by push_cast; nlinarith [(by exact_mod_cast ha : (1 : ℝ) ≤ a), (by exact_mod_cast hk : (0 : ℝ) < k)])
  have heq : (1 - (k : ℝ) / ((a * k : ℕ) : ℝ)) = 1 - 1 / (a : ℝ) := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- **Claim 36.2** [PS10, (36.2)]: `(1 - 1/(4n²))^{4n³} = ((1 - 1/(4n²))^{4n²})^n ≤ e^{-n}`:
with `4n³` pairs of random `n`-bit numbers, the probability that none of them is a pair of
primes is at most `e^{-n}` (given the density `1/(4n²)` of prime pairs). -/
theorem claim_36_2 (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ Real.exp (-(n : ℝ)) := by
  have h := one_sub_one_div_pow_le_exp_neg (4 * n ^ 2) n (by positivity)
  have hexp : 4 * n ^ 2 * n = 4 * n ^ 3 := by ring
  rw [hexp] at h
  push_cast at h
  exact h

/-- `e^{-n} ≤ (1/2)^n` (the negligible form of the tail bounds, `negligible_two_pow_neg`). -/
theorem exp_neg_le_half_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h1]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have := Real.add_one_le_exp (1 : ℝ)
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- **Claim 36.2, negligible form**: `(1 - 1/(4n²))^{4n³} ≤ 2^{-n}`. -/
theorem claim_36_2_half_pow (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (4 * (n : ℝ) ^ 2)) ^ (4 * n ^ 3) ≤ (1 / 2 : ℝ) ^ n :=
  (claim_36_2 n hn).trans (exp_neg_le_half_pow n)

/-! ## Prime pairs of bit strings -/

/-- **Prime-pair density on bit strings** [PS10, proof of Theorem 33.5]: for `n ≥ 2`, a
uniform pair of `n`-bit strings reads (`bitsToNat`) as a pair of primes with probability at
least `1/(4n²)` (`NumberTheory.one_div_le_uprob_prime_pair` transported along
`bitsEquiv`). -/
theorem one_div_le_uprob_prime_pair_bits (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : (Fin n → Bool) × (Fin n → Bool) =>
        (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime) := by
  have h := one_div_le_uprob_prime_pair n hn
  rw [← uprob_comp_equiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n))] at h
  simpa using h

/-- The uniform subtype of prime pairs of `n`-bit strings is `Π_n × Π_n`: read each string as
a number (`bitsEquiv`) and split the conjunction (`Equiv.subtypeProdEquivProd`). -/
noncomputable def primesPairEquiv (n : ℕ) :
    {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime} ≃
      Primes n × Primes n :=
  (Equiv.subtypeEquiv (Equiv.prodCongr (bitsEquiv n) (bitsEquiv n)) (fun z => by simp)).trans
    Equiv.subtypeProdEquivProd

/-- The components of `primesPairEquiv` are the numbers read from the two strings. -/
@[simp] theorem primesPairEquiv_apply_val (n : ℕ)
    (z : {z : (Fin n → Bool) × (Fin n → Bool) // (bitsToNat z.1).Prime ∧ (bitsToNat z.2).Prime}) :
    ((primesPairEquiv n z).1.1 : ℕ) = bitsToNat z.1.1 ∧
      ((primesPairEquiv n z).2.1 : ℕ) = bitsToNat z.1.2 := by
  simp [primesPairEquiv, Equiv.subtypeProdEquivProd]

/-- `1/|Π_n| ≤ 2n/2^n` for `n ≥ 2` (`NumberTheory.two_pow_le_two_mul_card_primes`): the
probability that two independent uniform primes coincide is negligible. -/
theorem one_div_card_primes_le (n : ℕ) (hn : 2 ≤ n) :
    1 / (Fintype.card (Primes n) : ℝ) ≤ 2 * n / 2 ^ n := by
  have h := two_pow_le_two_mul_card_primes n hn
  have h' : (2 : ℝ) ^ n ≤ 2 * n * Fintype.card (Primes n) := by exact_mod_cast h
  have hpos : (0 : ℝ) < Fintype.card (Primes n) := by
    have : 0 < Fintype.card (Primes n) := by
      by_contra h0
      push_neg at h0
      have : Fintype.card (Primes n) = 0 := by omega
      rw [this, mul_zero] at h
      exact absurd h (not_le.mpr (Nat.two_pow_pos n))
    exact_mod_cast this
  rw [div_le_div_iff₀ hpos (by positivity), one_mul]
  linarith

/-! ## Pairs of distinct primes -/

/-- Pairs of **distinct** primes of `Π_n`: the index distribution of the factoring
assumption and of the RSA/Rabin moduli `N = pq` (decision log "Rabin/RSA scope": `p ≠ q`). -/
abbrev DistinctPrimes (n : ℕ) : Type := {z : Primes n × Primes n // (z.1.1 : ℕ) ≠ z.2.1}

namespace DistinctPrimes

variable {n : ℕ}

/-- The first prime `p`. -/
def p (z : DistinctPrimes n) : ℕ := z.1.1.1

/-- The second prime `q`. -/
def q (z : DistinctPrimes n) : ℕ := z.1.2.1

/-- `p` is prime. -/
theorem p_prime (z : DistinctPrimes n) : z.p.Prime := z.1.1.2

/-- `q` is prime. -/
theorem q_prime (z : DistinctPrimes n) : z.q.Prime := z.1.2.2

/-- `p < 2^n`. -/
theorem p_lt (z : DistinctPrimes n) : z.p < 2 ^ n := z.1.1.1.2

/-- `q < 2^n`. -/
theorem q_lt (z : DistinctPrimes n) : z.q < 2 ^ n := z.1.2.1.2

/-- `p ≠ q`. -/
theorem p_ne_q (z : DistinctPrimes n) : z.p ≠ z.q := z.2

/-- The modulus `N = pq < 2^{2n}`. -/
theorem mul_lt (z : DistinctPrimes n) : z.p * z.q < 2 ^ (2 * n) := by
  rw [two_mul]; exact mul_lt_two_pow_add z.p_lt z.q_lt

/-! ### Instances and the totient (moved from `RSA.lean`, run-3 audit P7-6) -/

/-- The modulus `pq` is nonzero. -/
instance neZero_mul (z : DistinctPrimes n) : NeZero (z.p * z.q) :=
  ⟨mul_ne_zero z.p_prime.ne_zero z.q_prime.ne_zero⟩

/-- `Φ(pq)` is nonzero. -/
instance neZero_totient (z : DistinctPrimes n) : NeZero (Nat.totient (z.p * z.q)) :=
  ⟨(Nat.totient_pos.2 (NeZero.pos _)).ne'⟩

/-- `p` is prime (as a `Fact`). -/
instance fact_p_prime (z : DistinctPrimes n) : Fact z.p.Prime := ⟨z.p_prime⟩

/-- `q` is prime (as a `Fact`). -/
instance fact_q_prime (z : DistinctPrimes n) : Fact z.q.Prime := ⟨z.q_prime⟩

/-- `Φ(pq) = (p−1)(q−1)` for a pair of distinct primes [PS10, p. 47]. -/
theorem totient_mul (z : DistinctPrimes n) : Nat.totient (z.p * z.q) = (z.p - 1) * (z.q - 1) :=
  totient_prime_mul_prime z.p_prime z.q_prime z.p_ne_q

/-- `Φ(pq) ≥ 2`: one of two distinct primes is at least `3`. -/
theorem one_lt_totient (z : DistinctPrimes n) : 1 < Nat.totient (z.p * z.q) := by
  rw [z.totient_mul]
  have hp := z.p_prime.two_le
  have hq := z.q_prime.two_le
  have hne := z.p_ne_q
  rcases Nat.lt_or_ge 2 z.p with h | h
  · calc 1 < 2 * 1 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)
  · have h2 : z.p = 2 := by omega
    have h3 : 3 ≤ z.q := by omega
    calc 1 < 1 * 2 := by norm_num
      _ ≤ (z.p - 1) * (z.q - 1) := Nat.mul_le_mul (by omega) (by omega)

/-- A pair of distinct primes is determined by `(p, q)`. -/
theorem ext {z w : DistinctPrimes n} (hp : z.p = w.p) (hq : z.q = w.q) : z = w := by
  rcases z with ⟨⟨⟨⟨p, hp'⟩, hpp⟩, ⟨⟨q, hq'⟩, hqq⟩⟩, hne⟩
  rcases w with ⟨⟨⟨⟨p', _⟩, _⟩, ⟨⟨q', _⟩, _⟩⟩, _⟩
  simp only [DistinctPrimes.p, DistinctPrimes.q] at hp hq
  subst hp hq
  rfl

/-- `Π_n` has no two distinct primes for `n < 2`. -/
theorem isEmpty_of_lt (hn : n < 2) : IsEmpty (DistinctPrimes n) := by
  refine ⟨fun z => ?_⟩
  have h1 := z.p_prime.two_le
  have h2 := z.q_prime.two_le
  have h3 := z.p_lt
  have h4 := z.q_lt
  have h5 := z.p_ne_q
  interval_cases n <;> omega

/-- The pair `(2, 3)` for `n ≥ 2` (the default element of the collection's domain). -/
def default (hn : 2 ≤ n) : DistinctPrimes n :=
  ⟨(⟨⟨2, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_two⟩,
    ⟨⟨3, lt_of_lt_of_le (by norm_num) ((Nat.pow_le_pow_right (by norm_num) hn).trans_eq' rfl)⟩,
      Nat.prime_three⟩), (by norm_num : (2 : ℕ) ≠ 3)⟩

end DistinctPrimes

/-! ### Encoding pairs of distinct primes -/

/-- Decode `⟨a, b⟩` as a pair of distinct primes of `Π_m`: both components must be `m`-bit
strings (`decodeFin`) reading as distinct primes; anything else is a failure. -/
def decodeDistinctPrimes (m : ℕ) (w : List Bool) : Option (DistinctPrimes m) :=
  match decodeFin m (pairFstD w), decodeFin m (pairSndD w) with
  | some a, some b =>
    if h : (bitsToNat a).Prime ∧ (bitsToNat b).Prime ∧ bitsToNat a ≠ bitsToNat b then
      some ⟨(⟨⟨bitsToNat a, bitsToNat_lt a⟩, h.1⟩, ⟨⟨bitsToNat b, bitsToNat_lt b⟩, h.2.1⟩), h.2.2⟩
    else none
  | _, _ => none

/-- Encode a pair of distinct primes of `Π_m` as `⟨p, q⟩` with `m`-bit numerals. -/
def encodeDistinctPrimes (m : ℕ) (z : DistinctPrimes m) : List Bool :=
  pairEncode (natToList m z.p) (natToList m z.q)

/-- Decoding inverts encoding. -/
theorem decodeDistinctPrimes_encode (m : ℕ) (z : DistinctPrimes m) :
    decodeDistinctPrimes m (encodeDistinctPrimes m z) = some z := by
  unfold decodeDistinctPrimes encodeDistinctPrimes natToList
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, decodeFin_ofFn,
    bitsToNat_natToBits z.p_lt, bitsToNat_natToBits z.q_lt]
  rw [dif_pos ⟨z.p_prime, z.q_prime, z.p_ne_q⟩]
  congr 1

/-! ## Block rejection sampling on coin lists (run-3 audit P7-6) -/

/-- **Block rejection sampling** on a coin list, the common shape of the honest samplers of
the candidates [PS10, Theorem 53.2 (`Z_N^*`, `Z*_{Φ(N)}`), Theorem 61.7, Theorem 63.10 (Blum
primes), Theorem 52.3 (`Z_q`)]: `T` trials, trial `t` reading the first `k` bits of the
`t`-th block of `B` bits of `r` as a number `v` (`listToNat`), accepted iff `E v`; `none` if
every trial is rejected. With `k ≤ B` and `r` uniform, the `T` values are independent and
uniform below `2^k`, so the output is `firstHit E` on `Fin (2^k)` (`statClose_rejectBlocksL`).
Repair (run-3 audit P7-6): the one sampler behind `sampleUnitL` (RSA, Rabin) and
`samplePrimePL` (Rabin); `sampleBelowL` (discrete log) has the same shape. -/
def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
bits, `listToNat_lt_two_pow`). -/
theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
    (h : rejectBlocksL E k B T r = some v) : E v ∧ v < 2 ^ k := by
  unfold rejectBlocksL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  subst ht
  refine ⟨hc, lt_of_lt_of_le (listToNat_lt_two_pow _) ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _)

/-- **Block rejection sampling is close to uniform on `E`** (lemma C4 of the chapter 2
inventory on coin lists; the sampling clauses of [PS10, Theorems 52.3, 53.2, 61.7, 63.10]):
for `k ≤ B`, a uniform coin string of `T · B` bits and a default `d < 2^k` with `E d`, the
total sampler `(rejectBlocksL E k B T r).getD d` is within `(1 − Pr_{v < 2^k}[E v])^T` of the
uniform element of `{v < 2^k | E v}`. Repair (run-3 audit P7-6): stated once here instead of
in each consumer.

**Proof sketch.** For `r = List.ofFn r'`, `(r.drop (t·B)).take k = List.ofFn (π_t r')` where
`π_t r'` is the `k`-bit prefix of block `t` (`List.ext_get`, `List.getElem_take`,
`List.getElem_drop`, `List.getElem_ofFn`; the length is `k` since `t < T` and `k ≤ B`), so
`rejectBlocksL E k B T r = (firstHit (fun x : Fin (2^k) => E x) (fun t => bitsEquiv k (π_t r'))).map Fin.val`
(`List.map_coe_finRange`, `List.findSome?_map`, `bitsToNat_eq_listToNat`, `bitsEquiv_val`) and
`(·).getD d = Fin.val ((firstHit …).getD ⟨d, hdk⟩)` (`Option.getD_map`). The map
`r' ↦ (π_t r')_t` from `Fin (T·B) → Bool` to `Fin T → Fin k → Bool` pushes the uniform
distribution to the uniform one — it is the first projection of a splitting equivalence
`(Fin (T·B) → Bool) ≃ (Fin T → Fin k → Bool) × (Fin T → Fin (B − k) → Bool)` (`uprob_comp_equiv`,
`uprob_fst`; alternatively `pushesUniform_of_card_fiber`) — as does
`Equiv.piCongrRight (fun _ => bitsEquiv k)`; conclude from `statClose_firstHit` (default
`⟨d, hdk⟩`, `hd`) by `StatClose.comp_pushesUniform` and `StatClose.map Fin.val`. -/
theorem statClose_rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (hkB : k ≤ B)
    {d : ℕ} (hd : E d) (hdk : d < 2 ^ k) :
    StatClose (fun r : Fin (T * B) → Bool => (rejectBlocksL E k B T (List.ofFn r)).getD d)
      (fun e : {v : Fin (2 ^ k) // E (v : ℕ)} => ((e : Fin (2 ^ k)) : ℕ))
      ((1 - uprob fun v : Fin (2 ^ k) => E (v : ℕ)) ^ T) := by
  sorry

end TCSlib.Cryptography.Candidates

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
