## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03h-pack.md =====

# Gate 03h ([PS10] ch. 2–4, ch. 2 results and the universal one-way function): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/h/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the statements of ch. 2's main results proved in their own files: Yao's amplification (Thm 35.1's proof) and its lemmas, the collections theorem's proof (Thm 42.2), and the universal one-way function of §2.13.
- **This pack gates fills.** Its files hold **2 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03h-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.4.3 (book pp. 36–40), §2.5 (pp. 41–42) and §2.13 (pp. 63–65).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a universal function whose enumeration misses machines of some code length;
- an amplification whose repetition count is not polynomial;
- a padding that changes the input distribution.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{OneWayLemmas, OneWayYao, CollectionsLemmas, Universal, UniversalLemmas, UniversalPadding}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | pack 03b's files (one-wayness, collections); the machine layer (`Complexity/Randomized/`, and `Complexity/TuringMachine/` from `main`) |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11 (`CanonizerExp`, ratified as an explicit hypothesis, with its open problem); §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Thm-35.1 (proof), Claim-38.2, Thm-42.2 (proof), Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the definitions of pack 03b |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/h/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 69 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   19 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 9 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 6 use only the standard axioms, and
   3 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 2 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 6 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines (`audits/pass-shelat/Checks.lean`);
- admissions: the 2 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **Yao's amplification.** Are the lemmas of `OneWayYao` stated at the parameters the proof
   of Thm 35.1 needs (the number of rounds, and `statClose_roundSample` and `statClose_sampleAll`)?
2. **Thm 42.2's proof** (`CollectionsLemmas`). Are both directions' auxiliary statements right?
3. **The universal OWF (Thm 63.1, Lem 64.3).**
   - Is `theorem_63_1` stated under `CanonizerExp` as an explicit hypothesis?
   - Is the open-problem stub `exists_canonizerExp` (sorried) correctly labelled? Is it true?
   - Is `exists_linearTime_gStr` (sorried, a machine construction) true as stated, with the right
     linear-time bound?
4. **Sorried statements.** Give both a sorry verdict (a / b / c).

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/h/replay.log =====

# closure of pack 03h's files at a3c5fa8b72e50939822f22364647dc844a3914a0: 69 modules, extracted from g03-replay.log
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
TCSlib/Complexity/TuringMachine/Universal rc=0 53s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalBlock rc=0 18s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalInterpreter rc=0 17s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalStartup rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 14s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 138s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 26s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Universal rc=0 18s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 12s errors=0 sorry=1
TCSlib/Cryptography/Foundations/Experiments rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/OutputLength rc=0 5s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 6s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 6s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/h/axioms.log =====

# headline axiom prints (audits/pass-shelat/Checks.lean) for declarations in pack 03h's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib.Cryptography.fUniversal_easy: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.lemma_64_3: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.claim_65_1: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.claim_65_2: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.claim_65_2_cond: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.fUniversal_hard: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.fUniversal_weakOneWay: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.theorem_63_1: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_canonizerExp: propext, sorryAx, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/h/admissions.txt =====

# declarations with `sorry` in pack 03h's files, at a3c5fa8b72e50939822f22364647dc844a3914a0
TCSlib/Cryptography/Asymptotic/Universal.lean:294 TCSlib.Cryptography.exists_canonizerExp
TCSlib/Cryptography/Asymptotic/UniversalPadding.lean:163 TCSlib.Cryptography.PadQuad.exists_linearTime_gStr

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/h/lint.log =====

# scripts/style_lint.py on pack 03h's files, at a3c5fa8b72e50939822f22364647dc844a3914a0







0 findings in 6 files

## ===== TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the one-way function theorems

The machine-level and list-level infrastructure behind the fills of
`TCSlib.Cryptography.Asymptotic.OneWay` ([PS10, Theorems 35.1 and 35.2]): the file is
imported by `OneWay.lean`, so it cannot mention `FunFamily`; every statement is about strings,
`Fin`-indexed tuples (blocks through `finProdFinEquiv`), the concrete experiments of
`TCSlib.Cryptography.Foundations.Experiments` and the machine calculus of
`TCSlib.Complexity.Randomized`.

* **Blocks of a string.** A string of `q·ℓ` bits is `q` consecutive blocks of `ℓ` bits; block `i`
  of `x : Fin (q·ℓ) → Bool` is `fun j => x (finProdFinEquiv (i, j))` (the `blocks` bijection of
  `OneWay.lean` unfolds to this), and `ofFn_block_eq_take_drop` reads it off `List.ofFn x` by
  `drop`/`take`.
* **Planting** (`invProbOpt_prodFun_le_yaoTryOpt`): the `Option`-valued form of
  `OneWay.invProb_prodFun_le_yaoTry` — planting a challenge at a fixed position of a fresh tuple
  inverts `f` at least as often as the given inverter inverts the direct product.
* **Bridges** between the `List.find?` of `Complexity.polyTimeComputable_iterateFind` and the
  `foldr`/`findSome?` of `OneWay.yaoInverter` and `rejectionSample`.
* **Statistical closeness of products** over `Fin N` (`statClose_pi`): the `T + 1` rounds of
  rejection-sampled positions of Algorithm 38.5 are within `(T + 1)·δ` of uniform.
* **Sub-machines** of Algorithm 38.5 as `PolyTimeComputable` functions with clean
  specifications: the blockwise evaluator `exists_prodEval` (the honest evaluator of the direct
  product and of the fresh tuple `(f(x₁), …, f(x_m))`), the capped binary-to-unary converter
  `exists_unaryOf`, and the rejection sampler of the position `exists_posMachine`.

## Main definitions

* `TCSlib.Cryptography.OneWay.bitListToNat` — a bit string read as a number, most significant bit
  first (the list form of `bitsToNat`).
* `TCSlib.Cryptography.OneWay.padTrue` — pad or truncate a string to `ℓ` bits with `true`.

## Main results

* `TCSlib.Cryptography.OneWay.invProbOpt_prodFun_le_yaoTryOpt` — one-call planting, `Option` form.
* `TCSlib.Cryptography.OneWay.statClose_pi` — closeness of `Fin N`-indexed products.
* `TCSlib.Cryptography.OneWay.exists_prodEval`, `exists_unaryOf`, `exists_posMachine` — the
  sub-machines of [PS10, Algorithm 38.5].
* `TCSlib.Cryptography.OneWay.foldr_ite_eq_find?`, `findSome?_eq_bind_find?`,
  `find?_range_eq_map_find?_finRange` — loop bridges.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4: Theorems 35.1, 35.2 and Algorithm 38.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography.OneWay

open Complexity Turing Finset

/-! ### Blocks of a string -/

/-- Block `i` of `x : Fin (q * ℓ) → Bool` (positions `ℓ·i, …, ℓ·i + ℓ - 1`) is the `ℓ`-bit window
of `List.ofFn x` after `i·ℓ` bits. -/
theorem ofFn_block_eq_take_drop {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    List.ofFn (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) =
      ((List.ofFn x).drop (i * ℓ)).take ℓ := by
  have hle : i * ℓ + ℓ ≤ q * ℓ := by
    have : (i + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ i.2
    rwa [Nat.add_mul, Nat.one_mul] at this
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
  congr 1
  ext
  simp only [finProdFinEquiv_apply_val]
  ring

/-- The window of `ℓ` bits after `i·ℓ` bits of `List.ofFn x` has exactly `ℓ` bits. -/
theorem length_take_drop_block {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    (((List.ofFn x).drop (i * ℓ)).take ℓ).length = ℓ := by
  rw [← ofFn_block_eq_take_drop, List.length_ofFn]

/-- The concatenation of two chunks indexed by `Fin 2`. -/
theorem flatten_ofFn_two (g : Fin 2 → List Bool) : (List.ofFn g).flatten = g 0 ++ g 1 := by
  simp [List.ofFn_succ]

/-- Reading the first `m` coordinates of a tuple is taking the first `m` bits of its encoding. -/
theorem ofFn_castLE_eq_take {m k : ℕ} (h : m ≤ k) (a : Fin k → Bool) :
    List.ofFn (fun j : Fin m => a (Fin.castLE h j)) = (List.ofFn a).take m := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp

/-- Pad with `true` or truncate a string to exactly `ℓ` bits (the convention of the block
extraction of Algorithm 38.5: a malformed answer of the given inverter is padded). -/
def padTrue (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i true

/-- The encoding of `padTrue ℓ w` is `w` padded with `1^ℓ` and cut to `ℓ` bits. -/
theorem ofFn_padTrue (ℓ : ℕ) (w : List Bool) :
    List.ofFn (padTrue ℓ w) = (w ++ List.replicate ℓ true).take ℓ := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, padTrue, List.getElem_take]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < w.length
  · rw [List.getElem_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
  · rw [List.getElem_append_right (not_lt.1 hj), List.getElem_replicate,
      List.getElem?_eq_none (not_lt.1 hj), Option.getD_none]

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padTrue_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padTrue ℓ (List.ofFn x) = x := by
  funext i
  simp [padTrue]

/-- Padding the tail of the encoding of a `q·ℓ`-bit tuple after `i·ℓ` bits gives block `i`. -/
theorem padTrue_drop_ofFn {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    padTrue ℓ ((List.ofFn x).drop (i * ℓ)) = fun j => x (finProdFinEquiv (i, j)) := by
  apply List.ofFn_injective
  rw [ofFn_padTrue, ofFn_block_eq_take_drop]
  have h := length_take_drop_block x i
  rw [List.length_take] at h
  rw [List.take_append_of_le_length (by omega)]

/-- A bit string read as a number, most significant bit first: the list form of `bitsToNat`
(`bitsToNat b = bitListToNat (List.ofFn b)` by definition). -/
def bitListToNat (l : List Bool) : ℕ := l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- `bitsToNat` is `bitListToNat` of the encoding. -/
theorem bitsToNat_eq_bitListToNat {k : ℕ} (b : Fin k → Bool) : bitsToNat b = bitListToNat (List.ofFn b) :=
  rfl

/-- Reading one more bit: `bitListToNat (l ++ [c]) = 2 · bitListToNat l + c`. -/
theorem bitListToNat_append_singleton (l : List Bool) (c : Bool) :
    bitListToNat (l ++ [c]) = 2 * bitListToNat l + (if c then 1 else 0) := by
  simp [bitListToNat, List.foldl_append]

/-- Prefix values are monotone: the number read from a prefix is at most the number read from
the whole string.

**Proof sketch.** Induction on the string: reading the remaining bits after a prefix of value
`a` gives `a · 2^{rest} + value(rest)`, so a longer suffix can only increase the value
(`Nat.pow_le_pow_right`). -/
theorem bitListToNat_take_le (l : List Bool) : ∀ i, bitListToNat (l.take i) ≤ bitListToNat l := by
  intro i
  induction l generalizing i with
  | nil => simp [bitListToNat]
  | cons c l ih =>
    cases i with
    | zero => simp [bitListToNat]
    | succ i =>
      rw [List.take_succ_cons]
      have key : ∀ (m : List Bool) (a : ℕ),
          m.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
            a * 2 ^ m.length + m.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
        intro m
        induction m with
        | nil => simp
        | cons d m ihm =>
          intro a
          rw [List.foldl_cons, List.foldl_cons, ihm, ihm (2 * 0 + _), List.length_cons, pow_succ]
          ring
      simp only [bitListToNat, List.foldl_cons] at ih ⊢
      rw [key (l.take i), key l]
      have h1 := ih i
      have h2 : (l.take i).length ≤ l.length := List.length_take_le' _ _
      have h3 : 2 ^ (l.take i).length ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) h2
      have h4 : 0 ≤ (if c then 1 else 0 : ℕ) := Nat.zero_le _
      nlinarith [Nat.mul_le_mul_left (2 * 0 + (if c then 1 else 0)) h3]

/-! ### Planting, `Option` form -/

/-- **One-call planting, `Option` form** (the `invProbOpt` variant of
`OneWay.invProb_prodFun_le_yaoTry`, anticipated by the proof sketch of [PS10, Theorem 35.2]):
for a possibly failing inverter `B` of the direct product and a fixed position `i`, the
inverter that samples a fresh tuple, plants the challenge at position `i`, calls `B` and returns
the `i`-th component of its answer inverts `f` at least as often as `B` inverts `prodFun f q`.

**Proof sketch.** As `invProb_prodFun_le_yaoTry`: the planted tuple is uniform
(`OneWay.uprob_update`, `prodFun_update`), and an inverse of the whole tuple inverts every
coordinate (`uprob_mono`). -/
theorem invProbOpt_prodFun_le_yaoTryOpt {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → Option (Fin q → α)) (i : Fin q) :
    invProbOpt (prodFun f q) B ≤
      invProbOpt f fun y (c : (Fin q → α) × ρ) =>
        (B (Function.update (prodFun f q c.1) i y) c.2).map fun xs => xs i := by
  unfold invProbOpt
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r =>
    ∃ x', (B (prodFun f q xs) r).map (fun xs => xs i) = some x' ∧ f x' = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  refine le_trans ?_ (le_of_eq h.symm)
  apply uprob_mono
  rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
  exact ⟨xs' i, by simp [hxs'], congrFun hf i⟩

/-! ### Loop bridges -/

/-- The `foldr` of `OneWay.yaoInverter` returns the value at the first element satisfying the
test, or the default (`Option.elim` of the `List.find?`). -/
theorem foldr_ite_eq_find? {ι γ : Type*} (P : ι → Prop) [DecidablePred P] (v : ι → γ) (d : γ) :
    ∀ l : List ι, l.foldr (fun t acc => if P t then v t else acc) d =
      (l.find? (fun t => decide (P t))).elim d v := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.foldr_cons, List.find?_cons, ih]
    by_cases h : P t <;> simp [h]

/-- `findSome?` is `find?` of the successful indices followed by the function. -/
theorem findSome?_eq_bind_find? {ι γ : Type*} (f : ι → Option γ) :
    ∀ l : List ι, l.findSome? f = (l.find? fun t => (f t).isSome).bind f := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases hf : f t <;> simp [hf, ih]

/-- A search over `List.range N` with a test that agrees with `p` below `n ≤ N` and fails from
`n` on is the search over `List.finRange n`. -/
theorem find?_range_eq_map_find?_finRange {n N : ℕ} (hN : n ≤ N) (p : Fin n → Bool) (p' : ℕ → Bool)
    (hp : ∀ (t : ℕ) (h : t < n), p' t = p ⟨t, h⟩) (hp' : ∀ t, n ≤ t → p' t = false) :
    (List.range N).find? p' = ((List.finRange n).find? p).map Fin.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction d with
  | zero =>
    rw [Nat.add_zero, ← List.map_coe_finRange, List.find?_map]
    congr 2
    funext t
    exact hp t.1 t.2
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.find?_append, ih (Nat.le_add_right n d)]
    have : [n + d].find? p' = none := by simp [hp' (n + d) (Nat.le_add_right n d)]
    rw [this, Option.or_none]

/-! ### The direct product's evaluator -/

/-- The concatenation of `R` chunks of which only the first `Q ≤ R` are nonempty is the
concatenation of the first `Q`. -/
theorem flatMap_range_ite_eq_flatten_ofFn (E : ℕ → List Bool) {Q R : ℕ} (h : Q ≤ R) :
    (List.range R).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
  have base : (List.range Q).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
    rw [List.ofFn_eq_map, List.flatMap_def, ← List.map_coe_finRange, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp]
    rw [if_neg (not_le.2 t.2)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simpa using base
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.flatMap_append]
    have : [Q + d].flatMap (fun i => if Q ≤ i then [] else E i) = [] := by
      simp [Nat.le_add_right Q d]
    rw [this, List.append_nil]
    exact ih (Nat.le_add_right Q d)

/-! ### Statistical closeness of `Fin N`-indexed products -/

/-- **Closeness of products over `Fin N`:** if `X` is `δ`-close to `Y` then `N` independent
copies are `N·δ`-close (the `T + 1` rounds of rejection-sampled positions of
[PS10, Algorithm 38.5] are within `(T + 1)·δ` of uniform).

**Proof sketch.** Induction on `N`. For `N = 0` both samplers are constant. For `N + 1`,
split off the first coordinate with `Fin.consEquiv`: the pair sampler is `StatClose.prod` of
one copy and `N` copies (`δ + N·δ`), post-processed by `Fin.cons` (`StatClose.map`) and
re-indexed by the bijection on both sides (`StatClose.comp_equiv_left/right`);
`Fin.cons (c 0) (Fin.tail c) = c` identifies the samplers. -/
theorem statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (N : ℕ) :
    StatClose (fun c : Fin N → σ => fun t => X (c t)) (fun c : Fin N → τ => fun t => Y (c t))
      (N * δ) := by
  induction N with
  | zero =>
    intro T
    have hX : ∀ c : Fin 0 → σ, (fun t => X (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    have hY : ∀ c : Fin 0 → τ, (fun t => Y (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    simp only [hX, hY, Nat.cast_zero, zero_mul]
    by_cases hT : T (fun t : Fin 0 => t.elim0)
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | succ N ih =>
    have hp := ((h.prod ih).map (fun p : γ × (Fin N → γ) => (Fin.cons p.1 p.2 : Fin (N + 1) → γ)))
    have hp2 := (hp.comp_equiv_left (Fin.consEquiv (fun _ => σ)).symm).comp_equiv_right
      (Fin.consEquiv (fun _ => τ)).symm
    have keyX : ∀ c : Fin (N + 1) → σ,
        (Fin.cons (X (c 0)) (fun t => X (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => X (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail]
    have keyY : ∀ c : Fin (N + 1) → τ,
        (Fin.cons (Y (c 0)) (fun t => Y (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => Y (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail]
    have hδ : ((N + 1 : ℕ) : ℝ) * δ = δ + N * δ := by push_cast; ring
    rw [hδ]
    convert hp2 using 1
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyX c).symm
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyY c).symm

/-! ### Unary multiplication at the FP level -/

/-- The FP form of the unary-multiplication machine: `⟨u, v⟩ ↦ 1^{|u|·|v|}` (with the total
projections, so `[]` on malformed words). -/
theorem polyTimeComputable_unaryMulPair :
    PolyTimeComputable fun z => List.replicate ((pairFstD z).length * (pairSndD z).length) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have h : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p =>
    obtain ⟨u, v⟩ := p
    have := eq_pairEncode_of_pairDecode z u v hz
    subst this
    simp

/-! ### The blockwise evaluator -/

namespace ProdEval

/-- The parameter slot `u` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def u (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- The unary round counter `cnt` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def cnt (w : List Bool) : List Bool := pairSndD (pairFstD w)

/-- The unread input `rest` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def rest (w : List Bool) : List Bool := pairSndD w

/-- The initial state word `⟨⟨u, []⟩, x⟩` of the input `⟨u, x⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairEncode (pairFstD z) []) (pairSndD z)

/-- One round: add a token to the counter and drop one block of `inLen(|u|)` bits. -/
def step (inLen : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode (pairEncode (u w) (true :: cnt w)) ((rest w).drop (inLen.eval (u w).length))

/-- The emission of a round: `F ⟨u, next block⟩` while fewer than `q(|u|)` rounds have run,
`[]` afterwards. -/
def emit (F : List Bool → List Bool) (inLen q : PolyExpr) (w : List Bool) : List Bool :=
  if q.eval (u w).length ≤ (cnt w).length then []
  else F (pairEncode (u w) ((rest w).take (inLen.eval (u w).length)))

/-- The parameter slot is polynomial-time. -/
theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The counter is polynomial-time. -/
theorem cnt_poly : PolyTimeComputable cnt :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread input is polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_const [])).pairEncode
    polyTimeComputable_pairSndD

/-- Dropping the current block is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`
on `⟨u, rest⟩`). -/
theorem drop_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).drop (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairDropPoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- Reading the current block is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly`
on `⟨u, rest⟩`). -/
theorem take_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).take (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairTakePoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- The step is polynomial-time. -/
theorem step_poly (inLen : PolyExpr) : PolyTimeComputable (step inLen) :=
  (u_poly.pairEncode ((StateLoop.cons_poly true).comp cnt_poly)).pairEncode (drop_poly inLen)

/-- The emission is polynomial-time (`StateLoop.lenLe_comp` against `1^{q(|u|)}`,
`Complexity.polyTimeComputable_ite`). -/
theorem emit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (inLen q : PolyExpr) :
    PolyTimeComputable (emit F inLen q) := by
  have htest : PolyTimeComputable fun w => [decide (q.eval (u w).length ≤ (cnt w).length)] := by
    convert StateLoop.lenLe_comp cnt_poly (StateLoop.unaryPoly_comp q u_poly) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [])
    (hF.comp (u_poly.pairEncode (take_poly inLen))) using 1
  funext w
  by_cases h : q.eval (u w).length ≤ (cnt w).length <;> simp [emit, h]

/-- The orbit of an arbitrary word after `i + 1` rounds: the parameter is retained, the counter
has grown by `i + 1` tokens and `(i + 1)` blocks have been dropped. -/
theorem iterate_step_succ (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    (step inLen)^[i + 1] w =
      pairEncode (pairEncode (u w) (List.replicate (i + 1) true ++ cnt w))
        ((rest w).drop ((i + 1) * inLen.eval (u w).length)) := by
  induction i with
  | zero => simp [step]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, u, cnt, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
    congr 2
    ring

/-- The orbit of an arbitrary word `w` stays within `4|w| + 2i + 6` after `i` rounds. -/
theorem length_iterate_step_le (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    ((step inLen)^[i] w).length ≤ 4 * w.length + 2 * i + 6 := by
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [iterate_step_succ, length_pairEncode, length_pairEncode, List.length_append,
      List.length_replicate]
    have h1 := StateLoop.length_pairFstD_add_pairSndD_le w
    have h2 := StateLoop.length_pairFstD_add_pairSndD_le (pairFstD w)
    have h3 : ((rest w).drop ((i + 1) * inLen.eval (u w).length)).length =
        (rest w).length - (i + 1) * inLen.eval (u w).length := List.length_drop
    simp only [u, cnt, rest] at h2 h3 ⊢
    omega

/-- The orbit on a genuine input `⟨⟨1^n, []⟩, x⟩`: `⟨⟨1^n, 1^i⟩, x.drop (i·inLen(n))⟩`. -/
theorem iterate_step_start (inLen : PolyExpr) (n : ℕ) (x : List Bool) (i : ℕ) :
    (step inLen)^[i] (start (pairEncode (List.replicate n true) x)) =
      pairEncode (pairEncode (List.replicate n true) (List.replicate i true))
        (x.drop (i * inLen.eval n)) := by
  cases i with
  | zero => simp [start]
  | succ i =>
    rw [iterate_step_succ]
    simp [start, u, cnt, rest]

end ProdEval

/-- **The blockwise evaluator** (the honest evaluator of the direct product of
[PS10, Theorem 35.1], and the evaluation of the fresh tuple of Algorithm 38.5): from a
polynomial-time `F` and syntactic lengths `inLen`, `q`, a polynomial-time `F'` with
`F' ⟨1^n, x⟩ = F ⟨1^n, x₀⟩ ++ ⋯ ++ F ⟨1^n, x_{q(n)-1}⟩` on every `q(n)·inLen(n)`-bit `x`
(`x_i` its `i`-th block).

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word
`⟨⟨1^n, cnt⟩, rest⟩` (`ProdEval`): each round emits `F ⟨1^n, rest.take (inLen n)⟩` while the
unary counter is shorter than `1^{q(n)}` and `[]` afterwards, then drops `inLen n` bits and adds
a token (`ProdEval.iterate_step_start`); the orbit of every word is bounded by
`4|w| + 2q(|w|) + 6` (`ProdEval.length_iterate_step_le`). `q` is evaluated at the length of the
state word `≥ n`, so at least `q(n)` rounds emit (`PolyExpr.eval_mono`); the concatenation
of the first `q(n)` emissions is the target by `flatMap_range_ite_eq_flatten_ofFn` and
`ofFn_block_eq_take_drop`. -/
theorem exists_prodEval {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (inLen q : PolyExpr) :
    ∃ F' : List Bool → List Bool, PolyTimeComputable F' ∧
      ∀ (n : ℕ) (x : Fin (q.eval n * inLen.eval n) → Bool),
        F' (pairEncode (List.replicate n true) (List.ofFn x)) =
          (List.ofFn fun i : Fin (q.eval n) =>
            F (pairEncode (List.replicate n true)
              (List.ofFn fun j : Fin (inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ q.eval w.length →
      ((ProdEval.step inLen)^[i] w).length ≤
        (PolyExpr.add (.mul (.const 4) .var) (.add (.mul (.const 2) q) (.const 6))).eval w.length := by
    intro w i hi
    have := ProdEval.length_iterate_step_le inLen w i
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hloop := polyTimeComputable_iterateEmit (ProdEval.step_poly inLen)
    (ProdEval.emit_poly hF inLen q) q _ horbit
  refine ⟨_, hloop.comp ProdEval.start_poly, fun n x => ?_⟩
  simp only [Function.comp_apply]
  have hlen : n ≤ (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length := by
    simp only [ProdEval.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_replicate]
    omega
  have hQle : q.eval n ≤
      q.eval (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length + 1 :=
    (q.eval_mono hlen).trans (Nat.le_succ _)
  have hemit : ∀ i, ProdEval.emit F inLen q
      ((ProdEval.step inLen)^[i] (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x)))) =
      if q.eval n ≤ i then []
      else F (pairEncode (List.replicate n true)
        (((List.ofFn x).drop (i * inLen.eval n)).take (inLen.eval n))) := by
    intro i
    rw [ProdEval.iterate_step_start]
    simp [ProdEval.emit, ProdEval.u, ProdEval.cnt, ProdEval.rest]
  simp only [hemit]
  rw [flatMap_range_ite_eq_flatten_ofFn _ hQle]
  congr 2
  funext i
  rw [ofFn_block_eq_take_drop]

/-! ### The capped binary-to-unary converter -/

namespace UnaryOf

/-- The pad `1^L` of the state word `⟨pad, ⟨rest, acc⟩⟩`: the cap on the accumulator. -/
def pad (w : List Bool) : List Bool := pairFstD w

/-- The unread bits of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def rest (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary accumulator of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def acc (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The accumulator doubled, plus the next bit: `1^{2a + bit}`. -/
def dbl (w : List Bool) : List Bool :=
  acc w ++ acc w ++ (if (rest w).headD false then [true] else [])

/-- The doubled accumulator, capped at the pad (so that the orbit of every word is bounded). -/
def capped (w : List Bool) : List Bool :=
  if (dbl w).length ≤ (pad w).length then dbl w else pad w

/-- One round: read one bit if any remain, else stay. -/
def step (w : List Bool) : List Bool :=
  if rest w = [] then w else pairEncode (pad w) (pairEncode (rest w).tail (capped w))

/-- The initial state `⟨pad, ⟨b, []⟩⟩` of the input `⟨pad, b⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The pad is polynomial-time. -/
theorem pad_poly : PolyTimeComputable pad := polyTimeComputable_pairFstD

/-- The unread bits are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The accumulator is polynomial-time. -/
theorem acc_poly : PolyTimeComputable acc :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Doubling is polynomial-time. -/
theorem dbl_poly : PolyTimeComputable dbl := by
  have hbit : PolyTimeComputable fun w => [(rest w).headD false] :=
    StateLoop.headBit_poly.comp rest_poly
  exact (acc_poly.append acc_poly).append
    (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const []))

/-- Capping is polynomial-time. -/
theorem capped_poly : PolyTimeComputable capped := by
  convert polyTimeComputable_ite (StateLoop.lenLe_comp pad_poly dbl_poly) dbl_poly pad_poly using 1
  funext w
  simp [capped]

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp rest_poly) polyTimeComputable_id
    (pad_poly.pairEncode ((StateLoop.tail_poly.comp rest_poly).pairEncode capped_poly)) using 1
  funext w
  simp [step]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The capped accumulator never exceeds the pad. -/
theorem length_capped_le (w : List Bool) : (capped w).length ≤ (pad w).length := by
  unfold capped
  split_ifs with h
  · exact h
  · exact le_rfl

/-- The unread bits of any word are no longer than the word. -/
theorem length_rest_le (w : List Bool) : (rest w).length ≤ w.length := by
  have h1 := length_pairFstD_le (pairSndD w)
  have h2 := StateLoop.length_pairFstD_add_pairSndD_le w
  unfold rest
  omega

/-- The orbit invariant on arbitrary words: the orbit point is the start word or a state word
`⟨pad w, ⟨r, a⟩⟩` with `|r| ≤ |w|` and `|a| ≤ |pad w|`. -/
def Inv (w w' : List Bool) : Prop :=
  w' = w ∨ ∃ r a : List Bool,
    w' = pairEncode (pad w) (pairEncode r a) ∧ r.length ≤ w.length ∧ a.length ≤ (pad w).length

/-- The invariant is preserved by the step. -/
theorem inv_step (w w' : List Bool) (h : Inv w w') : Inv w (step w') := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · unfold step
    split_ifs with h0
    · exact Or.inl rfl
    · refine Or.inr ⟨(rest w').tail, capped w', rfl, ?_, length_capped_le w'⟩
      have := List.length_tail (l := rest w')
      have := length_rest_le w'
      omega
  · have hpad : pad (pairEncode (pad w) (pairEncode r a)) = pad w := by simp [pad]
    have hrest : rest (pairEncode (pad w) (pairEncode r a)) = r := by simp [rest]
    unfold step
    split_ifs with h0
    · exact Or.inr ⟨r, a, rfl, hr, ha⟩
    · refine Or.inr ⟨r.tail, capped (pairEncode (pad w) (pairEncode r a)), ?_, ?_, ?_⟩
      · rw [hpad, hrest]
      · have := List.length_tail (l := r)
        omega
      · have := length_capped_le (pairEncode (pad w) (pairEncode r a))
        rwa [hpad] at this

/-- A word satisfying the invariant has length at most `5|w| + 4`. -/
theorem length_le_of_inv {w w' : List Bool} (h : Inv w w') : w'.length ≤ 5 * w.length + 4 := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · omega
  · have := length_pairFstD_le w
    simp only [length_pairEncode, pad] at *
    omega

/-- The whole orbit satisfies the invariant. -/
theorem inv_iterate (w : List Bool) (i : ℕ) : Inv w (step^[i] w) := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step w _ ih

/-- The orbit of every word stays within `5|w| + 4`. -/
theorem length_iterate_le (w : List Bool) (i : ℕ) : (step^[i] w).length ≤ 5 * w.length + 4 :=
  length_le_of_inv (inv_iterate w i)

/-- The orbit on a genuine input `⟨p, b⟩` with `bitListToNat b ≤ |p|`: after `i` rounds the state
is `⟨p, ⟨b.drop i, 1^{bitListToNat (b.take i)}⟩⟩`.

**Proof sketch.** Induction on `i`. While bits remain (`List.drop_eq_getElem_cons`), the step
doubles the accumulator and adds the bit `b[i]`, giving `1^{bitListToNat (b.take (i + 1))}`
(`List.take_append_getElem`, `bitListToNat_append_singleton`); the cap never fires because
`bitListToNat (b.take (i + 1)) ≤ bitListToNat b ≤ |p|` (`bitListToNat_take_le`). Once the bits are
exhausted the step is the identity and `b.take (i + 1) = b.take i`. -/
theorem iterate_start (p b : List Bool) (hb : bitListToNat b ≤ p.length) (i : ℕ) :
    step^[i] (start (pairEncode p b)) =
      pairEncode p (pairEncode (b.drop i) (List.replicate (bitListToNat (b.take i)) true)) := by
  induction i with
  | zero => simp [start, bitListToNat]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : i < b.length
    · have hdrop := List.drop_eq_getElem_cons hi
      have hdbl : dbl (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        simp only [dbl, acc, rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop, List.headD_cons]
        rw [← List.take_append_getElem hi, bitListToNat_append_singleton, two_mul, List.replicate_add,
          List.replicate_add]
        cases hbi : b[i] <;> simp
      have hcap : capped (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        unfold capped
        rw [hdbl, if_pos]
        rw [List.length_replicate]
        simp only [pad, pairFstD_pairEncode]
        exact (bitListToNat_take_le b (i + 1)).trans hb
      have hne : rest (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) ≠ [] := by
        simp only [rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop]
        exact List.cons_ne_nil _ _
      unfold step
      rw [if_neg hne, hcap]
      simp only [pad, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop]
    · have hle : b.length ≤ i := not_lt.1 hi
      have h1 : b.drop i = [] := List.drop_eq_nil_of_le hle
      have h2 : b.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h3 : b.take (i + 1) = b.take i := by
        rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
      rw [h2, h3]
      unfold step
      rw [if_pos (by simp [rest, h1]), h1]

end UnaryOf

/-- **The capped binary-to-unary converter**: a polynomial-time `U` with
`U ⟨p, b⟩ = 1^{bitListToNat b}` whenever `bitListToNat b ≤ |p|` (the pad `p` bounds the output; the
rejection sampler of Algorithm 38.5 reads each `k`-bit trial as a number below `2^k ≤ 2m`).

**Proof sketch.** `Complexity.polyTimeComputable_iterate` with `R := var` on the state word
`⟨p, ⟨rest, acc⟩⟩` (`UnaryOf`): each round doubles the unary accumulator and adds the next
bit, capped at the pad so that the orbit of every word stays within `5|w| + 4`
(`UnaryOf.length_iterate_le`); on a genuine input the cap never fires
(`UnaryOf.iterate_start`), and after `|b|` rounds the state is `⟨p, ⟨[], 1^{bitListToNat b}⟩⟩`. -/
theorem exists_unaryOf : ∃ U : List Bool → List Bool, PolyTimeComputable U ∧
    ∀ p b : List Bool, bitListToNat b ≤ p.length → U (pairEncode p b) = List.replicate (bitListToNat b) true := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval w.length →
      (UnaryOf.step^[i] w).length ≤ (PolyExpr.add (.mul (.const 5) .var) (.const 4)).eval w.length := by
    intro w i _
    simpa using UnaryOf.length_iterate_le w i
  have hiter := polyTimeComputable_iterate UnaryOf.step_poly .var _ horbit
  refine ⟨_, UnaryOf.acc_poly.comp (hiter.comp UnaryOf.start_poly), fun p b hb => ?_⟩
  simp only [Function.comp_apply, PolyExpr.eval_var]
  rw [UnaryOf.iterate_start p b hb]
  have hlen : b.length ≤ (UnaryOf.start (pairEncode p b)).length := by
    simp only [UnaryOf.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_nil]
    omega
  rw [List.drop_eq_nil_of_le hlen, List.take_of_length_le hlen]
  simp [UnaryOf.acc]

/-! ### The rejection sampler of the position -/

namespace PosLoop

/-- The trial length `1^k` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def ukk (v : List Bool) : List Bool := pairFstD (pairFstD v)

/-- The range `1^m` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def uM (v : List Bool) : List Bool := pairSndD (pairFstD v)

/-- The unread trials of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def rest (v : List Bool) : List Bool := pairSndD v

/-- One round: drop one trial of `k` bits. -/
def step (v : List Bool) : List Bool := pairEncode (pairFstD v) ((rest v).drop (ukk v).length)

/-- The current trial: the next `k` bits. -/
def trial (v : List Bool) : List Bool := (rest v).take (ukk v).length

/-- The current trial as a unary number, through the converter `U` with pad `1^{2m}`. -/
def unum (U : List Bool → List Bool) (v : List Bool) : List Bool :=
  U (pairEncode (uM v ++ uM v) (trial v))

/-- The acceptance test: a full trial remains and its value is below `m`. -/
def acc (U : List Bool → List Bool) (v : List Bool) : Bool :=
  decide ((ukk v).length ≤ (rest v).length) && !decide ((uM v).length ≤ (unum U v).length)

/-- The trial length is polynomial-time. -/
theorem ukk_poly : PolyTimeComputable ukk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The range is polynomial-time. -/
theorem uM_poly : PolyTimeComputable uM := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread trials are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at `var`). -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_pairDropPoly .var).comp (ukk_poly.pairEncode rest_poly)) using 1
  funext v
  simp [step]

/-- The current trial is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` at `var`). -/
theorem trial_poly : PolyTimeComputable trial := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ukk_poly.pairEncode rest_poly) using 1
  funext v
  simp [trial]

/-- The unary value of the trial is polynomial-time. -/
theorem unum_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable (unum U) :=
  hU.comp ((uM_poly.append uM_poly).pairEncode trial_poly)

/-- The acceptance test is polynomial-time. -/
theorem acc_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable fun v => [acc U v] :=
  polyTimeComputable_and (StateLoop.lenLe_comp rest_poly ukk_poly)
    (StateLoop.not_poly (StateLoop.lenLe_comp (unum_poly hU) uM_poly))

/-- Re-pairing the first component of a word with a shorter second component does not lengthen a
pair, and gives a word of length `2` on a non-pair. -/
theorem length_pairEncode_pairFstD_le (v s : List Bool) (hs : s.length ≤ (pairSndD v).length) :
    (pairEncode (pairFstD v) s).length ≤ max v.length 2 := by
  cases hv : pairDecode v with
  | none =>
    simp only [pairFstD, pairSndD, hv, Option.map_none, Option.getD_none, List.length_nil,
      nonpos_iff_eq_zero, List.length_eq_zero_iff] at hs ⊢
    subst hs
    simp [length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have := eq_pairEncode_of_pairDecode v a b hv
    subst this
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hs ⊢
    rw [length_pairEncode, length_pairEncode]
    omega

/-- The orbit of every word stays within `|v| + 2`. -/
theorem length_iterate_le (v : List Bool) (t : ℕ) : (step^[t] v).length ≤ v.length + 2 := by
  have key : ∀ t, (step^[t] v).length ≤ max v.length 2 := by
    intro t
    induction t with
    | zero => exact le_max_left _ _
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine (length_pairEncode_pairFstD_le _ _
        (by rw [List.length_drop]; exact Nat.sub_le _ _)).trans ?_
      exact max_le (ih.trans (le_refl _)) (le_max_right _ _)
  exact (key t).trans (by omega)

/-- The orbit on a genuine input: after `t` rounds, `t` trials have been dropped. -/
theorem iterate_step_start (kk M : ℕ) (L : List Bool) (t : ℕ) :
    step^[t] (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) L) =
      pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (L.drop (t * kk)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, rest, ukk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
      List.drop_drop]
    congr 2
    ring

end PosLoop

/-- A trial succeeds iff its value is below `m`. -/
theorem isSome_uniformFromBits {m k : ℕ} (b : Fin k → Bool) :
    (uniformFromBits m k b).isSome = decide (bitsToNat b < m) := by
  unfold uniformFromBits
  split_ifs with h <;> simp [h]

/-- **The position sampler** [PS10, Algorithm 38.5, "`i ← [m]`", by rejection (D10)]: a
polynomial-time `Pm` with `Pm ⟨⟨1^k, 1^m⟩, trials⟩ = 1^i` where `i` is the output of
`rejectionSample m k n` on the `n` trials of `k` bits encoded in `trials` (`0` on failure),
for `0 < m`, `0 < k` and `2^k ≤ 2m`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateFind` with `R := var` on the state word
`⟨⟨1^k, 1^m⟩, rest⟩` (`PosLoop`): each round drops one trial; the test accepts when a full
trial remains and its unary value (`exists_unaryOf` with pad `1^{2m}`, valid since the value is
below `2^k ≤ 2m`) is shorter than `1^m`; the payload is that unary value. The orbit of every
word is bounded by `|v| + 2` (`PosLoop.length_iterate_le`). On a genuine input the test at
round `t < n` is `bitsToNat (trial t) < m` and fails from round `n` on (no full trial remains),
so the loop's `find?` is the `find?` over `finRange n` (`find?_range_eq_map_find?_finRange`),
which is the `findSome?` of `rejectionSample` (`findSome?_eq_bind_find?`,
`isSome_uniformFromBits`). -/
theorem exists_posMachine : ∃ Pm : List Bool → List Bool, PolyTimeComputable Pm ∧
    ∀ (M kk n : ℕ) (hM : 0 < M), 0 < kk → 2 ^ kk ≤ 2 * M → ∀ pb' : Fin (n * kk) → Bool,
      Pm (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')) =
        List.replicate
          ((rejectionSample M kk n fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true := by
  obtain ⟨U, hU, hUspec⟩ := exists_unaryOf
  have horbit : ∀ (v : List Bool) (t : ℕ), t ≤ PolyExpr.var.eval v.length →
      (PosLoop.step^[t] v).length ≤ (PolyExpr.add .var (.const 2)).eval v.length := by
    intro v t _
    simpa using PosLoop.length_iterate_le v t
  have hfind := polyTimeComputable_iterateFind PosLoop.step_poly (PosLoop.acc_poly hU)
    (PosLoop.unum_poly hU) .var _ horbit
  refine ⟨_, hfind, fun M kk n hM hkk h2 pb' => ?_⟩
  have hunum : ∀ t : Fin n, PosLoop.unum U (PosLoop.step^[(t : ℕ)]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      List.replicate (bitsToNat fun j => pb' (finProdFinEquiv (t, j))) true := by
    intro t
    rw [PosLoop.iterate_step_start]
    simp only [PosLoop.unum, PosLoop.uM, PosLoop.trial, PosLoop.rest, PosLoop.ukk,
      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    rw [← ofFn_block_eq_take_drop pb' t, hUspec]
    · rfl
    · rw [List.length_append, List.length_replicate]
      have := bitsToNat_lt fun j => pb' (finProdFinEquiv (t, j))
      rw [bitsToNat_eq_bitListToNat] at this
      omega
  have hacc : ∀ t : ℕ, PosLoop.acc U (PosLoop.step^[t]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      if h : t < n then decide (bitsToNat (fun j => pb' (finProdFinEquiv (⟨t, h⟩, j))) < M)
      else false := by
    intro t
    split_ifs with h
    · have := hunum ⟨t, h⟩
      simp only at this
      unfold PosLoop.acc
      rw [this, PosLoop.iterate_step_start]
      simp only [PosLoop.ukk, PosLoop.uM, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.length_drop, List.length_ofFn]
      have hmul : (t + 1) * kk ≤ n * kk := Nat.mul_le_mul_right kk h
      rw [Nat.add_mul, Nat.one_mul] at hmul
      have h1 : kk ≤ n * kk - t * kk := by omega
      simp [h1, ← decide_not]
    · unfold PosLoop.acc
      rw [PosLoop.iterate_step_start]
      have hmul : n * kk ≤ t * kk := Nat.mul_le_mul_right kk (not_lt.1 h)
      simp only [PosLoop.ukk, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.drop_eq_nil_of_le (List.length_ofFn.trans_le hmul),
        List.length_nil]
      simp [Nat.pos_iff_ne_zero.1 hkk]
  have hR : n ≤ PolyExpr.var.eval
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')).length + 1 := by
    have := Nat.le_mul_of_pos_right n hkk
    simp only [PolyExpr.eval_var, length_pairEncode, List.length_replicate, List.length_ofFn]
    omega
  rw [find?_range_eq_map_find?_finRange hR
    (fun t : Fin n => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)) _
    (fun t h => by rw [hacc, dif_pos h]) (fun t h => by rw [hacc, dif_neg (not_lt.2 h)])]
  have hrs : rejectionSample M kk n (fun t j => pb' (finProdFinEquiv (t, j))) =
      ((List.finRange n).find? fun t => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)).bind
        fun t => uniformFromBits M kk fun j => pb' (finProdFinEquiv (t, j)) := by
    unfold rejectionSample
    rw [findSome?_eq_bind_find?]
    congr 2
    funext t
    exact isSome_uniformFromBits _
  rw [hrs]
  cases hf : (List.finRange n).find? fun t =>
      decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M) with
  | none => simp
  | some t =>
    have ht : bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M := by
      simpa using List.find?_some hf
    simp only [Option.map_some, Option.bind_some]
    rw [hunum]
    unfold uniformFromBits
    rw [dif_pos ht]
    rfl

end TCSlib.Cryptography.OneWay

## ===== TCSlib/Cryptography/Asymptotic/OneWayYao.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Yao reduction machine

The machine of [PS10, Algorithm 38.5] behind Theorem 35.1 (`weak_to_strong` in
`TCSlib.Cryptography.Asymptotic.OneWay`, which imports this file): given an inverter `A'` of the
direct product `f'(x₁, …, x_m) = (f(x₁), …, f(x_m))`, the reduction repeats `T + 1` times —
sample a position `i ← [m]` by rejection (D10), sample `m` fresh inputs, evaluate `f` on them,
plant the challenge `y` at block `i`, call `A'`, and test whether block `i` of the answer is a
preimage of `y` — and returns the first success. The machine is
`Complexity.polyTimeComputable_iterateFind` on the raw input `⟨⟨⟨1^n, y⟩, ⟨α', 1^k⟩⟩, r⟩` (the
coins `r` are consumed one round at a time), its round is an FP composition of the
sub-machines of `TCSlib.Cryptography.Asymptotic.OneWayLemmas`, and the main theorem
`exists_yaoReduction` identifies its inverter with the concrete `OneWay.yaoInverter` of
[Gar26, Figure 2.2] up to the statistical term `(T + 1)·2^{-n}` of the rejection-sampled
positions (`statClose_pi`, `statClose_rejectionSample`).

The file is generic over the lengths `inLen`, `outLen`, the block count `m`, the round count
`T` (all `PolyExpr`) and the function `f` with its evaluator `Fe`; `OneWay.lean` instantiates it
with a `FunFamily`.

## Main definitions

* `TCSlib.Cryptography.OneWay.blocksE` — the block bijection (the `blocks` of `OneWay.lean`).
* `TCSlib.Cryptography.OneWay.kkOf` — the trial length `⌊log₂ m⌋ + 1` of the position sampler.
* `TCSlib.Cryptography.OneWay.YaoMachine.Data`, `YaoMachine.acc`, `YaoMachine.ans`,
  `YaoMachine.g`, `YaoMachine.yaoRaw'` — the round of Algorithm 38.5 and the repeated machine.
* `TCSlib.Cryptography.OneWay.yaoB` — the total inverter of the direct product read off `A'`.

## Main results

* `TCSlib.Cryptography.OneWay.ofFn_blocksE_symm_update` — planting a block is splicing.
* `TCSlib.Cryptography.OneWay.exists_yaoReduction` — the reduction machine and its bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4: Theorem 35.1 and Algorithm 38.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography.OneWay

open Complexity Turing Finset

/-! ### The block bijection -/

/-- A string of `q·ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`); the `FunFamily.blocks` of `OneWay.lean`, repeated here
because this file is imported by it. -/
def blocksE (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Block `i`, position `j` of `x` is position `ℓ·i + j`. -/
theorem blocksE_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    blocksE q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksE` reads block `k.divNat`, position `k.modNat`. -/
theorem blocksE_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocksE q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocksE_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocksE q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocksE_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- **Planting is splicing:** the encoding of the tuple `t` with block `p` replaced by `v` is the
encoding of `t` with the `ℓ` bits after `p·ℓ` replaced by the encoding of `v`
[PS10, Algorithm 38.5, "`(f(x₁), …, y, …, f(x_m))`"].

**Proof sketch.** Both sides have length `q·ℓ`; compare position `i`: below `p·ℓ` and from
`p·ℓ + ℓ` on, both read block `i / ℓ ≠ p` of `t` (`Function.update_of_ne`), and in between both
read position `i - p·ℓ` of `v` (`Function.update_self`, `Nat.div_add_mod`). -/
theorem ofFn_blocksE_symm_update {q ℓ : ℕ} (t : Fin q → Fin ℓ → Bool) (p : Fin q)
    (v : Fin ℓ → Bool) :
    List.ofFn ((blocksE q ℓ).symm (Function.update t p v)) =
      (List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ) ++ List.ofFn v ++
        (List.ofFn ((blocksE q ℓ).symm t)).drop (p * ℓ + ℓ) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp at h₁
  have hle : p * ℓ + ℓ ≤ q * ℓ := by
    have : (p + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ p.2
    rwa [Nat.add_mul, Nat.one_mul] at this
  have hLlen : (List.ofFn ((blocksE q ℓ).symm t)).length = q * ℓ := List.length_ofFn
  have hT : ((List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ)).length = p * ℓ := by
    rw [List.length_take, hLlen]; omega
  have hV : (List.ofFn v).length = ℓ := List.length_ofFn
  have hTV : ((List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ) ++ List.ofFn v).length = p * ℓ + ℓ := by
    rw [List.length_append, hT, hV]
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_append, List.length_drop, hT, hV, hLlen, List.length_ofFn]
    omega
  rw [List.getElem_ofFn, blocksE_symm_apply, Function.update_apply]
  rw [List.length_ofFn] at h₁
  have hdiv : ((⟨i, h₁⟩ : Fin (q * ℓ)).divNat : ℕ) = i / ℓ := Fin.coe_divNat _
  have hmod : ((⟨i, h₁⟩ : Fin (q * ℓ)).modNat : ℕ) = i % ℓ := Fin.coe_modNat _
  have hdm := Nat.div_add_mod i ℓ
  rcases lt_or_ge i (p * ℓ) with hA | hA
  · -- below the planted block: block `i / ℓ < p`
    have hq : i / ℓ < p := (Nat.div_lt_iff_lt_mul hℓ).2 hA
    rw [if_neg (by rw [Fin.ext_iff, hdiv]; omega)]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem_take, List.getElem_ofFn, blocksE_symm_apply]
  · rcases lt_or_ge i (p * ℓ + ℓ) with hB | hB
    · -- the planted block
      have hlo : p ≤ i / ℓ := (Nat.le_div_iff_mul_le hℓ).2 hA
      have hhi : i / ℓ < p + 1 :=
        (Nat.div_lt_iff_lt_mul hℓ).2 (by rw [Nat.add_mul, Nat.one_mul]; exact hB)
      have hq : i / ℓ = p := by omega
      rw [if_pos (by rw [Fin.ext_iff, hdiv]; exact hq)]
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega),
        List.getElem_ofFn]
      congr 1
      rw [Fin.ext_iff, hmod]
      simp only [hT]
      rw [hq, Nat.mul_comm] at hdm
      omega
    · -- above the planted block: block `i / ℓ > p`
      have hq : p + 1 ≤ i / ℓ :=
        (Nat.le_div_iff_mul_le hℓ).2 (by rw [Nat.add_mul, Nat.one_mul]; exact hB)
      rw [if_neg (by rw [Fin.ext_iff, hdiv]; omega)]
      rw [List.getElem_append_right (by omega), List.getElem_drop, List.getElem_ofFn,
        blocksE_symm_apply]
      congr 1 <;> (apply Fin.ext; simp only [Fin.coe_divNat, Fin.coe_modNat]; congr 1; omega)

/-! ### The trial length of the position sampler -/

/-- The trial length `⌊log₂ m⌋ + 1` of the rejection sampler of `i ← [m]`: the least `k` with
`m < 2^k`, so that `2^k ≤ 2m` and every trial succeeds with probability at least `1/2`
(D10, [PS10, Theorem 35.1]). -/
def kkOf (M : ℕ) : ℕ := Nat.log 2 M + 1

/-- The trial length is positive. -/
theorem kkOf_pos (M : ℕ) : 0 < kkOf M := Nat.succ_pos _

/-- `m < 2^{kkOf m}`. -/
theorem lt_two_pow_kkOf (M : ℕ) : M < 2 ^ kkOf M := Nat.lt_pow_succ_log_self one_lt_two M

/-- `2^{kkOf m} ≤ 2m` for `0 < m`. -/
theorem two_pow_kkOf_le (M : ℕ) (hM : 0 < M) : 2 ^ kkOf M ≤ 2 * M := by
  rw [kkOf, pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hM.ne')

/-- `kkOf m ≤ m` for `0 < m`. -/
theorem kkOf_le (M : ℕ) (hM : 0 < M) : kkOf M ≤ M :=
  Nat.log_lt_of_lt_pow hM.ne' Nat.lt_two_pow_self

/-- `kkOf m ≤ m + 1`. -/
theorem kkOf_le_succ (M : ℕ) : kkOf M ≤ M + 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [kkOf]
  · exact (kkOf_le M hM).trans (Nat.le_succ M)

/-! ### The round of Algorithm 38.5 -/

namespace YaoMachine

/-- The data of the reduction: the evaluator `Fe` of `f` (on `⟨1^n, x⟩`), the blockwise
evaluator `F'` (`exists_prodEval`), the position sampler `Pm` (`exists_posMachine`), the
lengths `inLen`, `outLen`, the block count `m` and the given inverter `A'`. -/
structure Data where
  /-- The evaluator of `f` on `⟨1^n, x⟩`. -/
  Fe : List Bool → List Bool
  /-- The blockwise evaluator on `⟨1^n, x₁ ⋯ x_m⟩`. -/
  F' : List Bool → List Bool
  /-- The position sampler on `⟨⟨1^k, 1^m⟩, trials⟩`. -/
  Pm : List Bool → List Bool
  /-- The input length of `f`. -/
  inLen : PolyExpr
  /-- The output length of `f`. -/
  outLen : PolyExpr
  /-- The number of blocks. -/
  m : PolyExpr
  /-- The given inverter of the direct product. -/
  A' : NUPPT

variable (D : Data)

/-- The coins of one round: `n·m(n)` position bits (of which `n·k` are read), `m(n)·inLen(n)`
bits of fresh inputs, and the coins of `A'`. -/
def ρP : PolyExpr := .add (.mul .var D.m) (.add (.mul D.m D.inLen) D.A'.coins)

/-- The advice of `A'`, read off the advice slot `⟨α', 1^k⟩`. -/
def alpha1 (w : List Bool) : List Bool := pairFstD (NUPPT.inAdvice w)

/-- The trial length `1^k`, read off the advice slot `⟨α', 1^k⟩`. -/
def ukk (w : List Bool) : List Bool := pairSndD (NUPPT.inAdvice w)

/-- The block count in unary, `1^{m(n)}`. -/
def uM (w : List Bool) : List Bool := List.replicate (D.m.eval (NUPPT.inParam w).length) true

/-- The coins of the current round: the first `ρ(n)` remaining coins. -/
def rc (w : List Bool) : List Bool :=
  (NUPPT.inCoins w).take ((ρP D).eval (NUPPT.inParam w).length)

/-- `1^{n·k}`: the number of position bits read. -/
def nkk (w : List Bool) : List Bool :=
  List.replicate ((NUPPT.inParam w).length * (ukk w).length) true

/-- The position bits of the round. -/
def posBits (w : List Bool) : List Bool := (rc D w).take (nkk w).length

/-- The sampled position in unary, `1^i`. -/
def ipos (w : List Bool) : List Bool :=
  D.Pm (pairEncode (pairEncode (ukk w) (uM D w)) (posBits D w))

/-- The fresh inputs `x₁ ⋯ x_m` of the round. -/
def xs (w : List Bool) : List Bool :=
  ((rc D w).drop ((PolyExpr.mul .var D.m).eval (NUPPT.inParam w).length)).take
    ((PolyExpr.mul D.m D.inLen).eval (NUPPT.inParam w).length)

/-- The coins handed to `A'`. -/
def rcoins (w : List Bool) : List Bool :=
  (rc D w).drop ((PolyExpr.add (.mul .var D.m) (.mul D.m D.inLen)).eval (NUPPT.inParam w).length)

/-- The tuple `f(x₁) ⋯ f(x_m)`. -/
def ys (w : List Bool) : List Bool := D.F' (pairEncode (NUPPT.inParam w) (xs D w))

/-- `1^{outLen(n)}`. -/
def uOut (w : List Bool) : List Bool := List.replicate (D.outLen.eval (NUPPT.inParam w).length) true

/-- `1^{i·outLen(n)}`: the offset of block `i` of the tuple. -/
def off (w : List Bool) : List Bool :=
  List.replicate ((ipos D w).length * (uOut D w).length) true

/-- The planted tuple `(f(x₁), …, y, …, f(x_m))`. -/
def planted (w : List Bool) : List Bool :=
  (ys D w).take (off D w).length ++ NUPPT.inArg w ++ (ys D w).drop (off D w ++ uOut D w).length

/-- The answer of `A'` on the planted tuple. -/
def zOut (w : List Bool) : List Bool :=
  D.A'.output (NUPPT.layout (NUPPT.inParam w) (planted D w) (alpha1 w) (rcoins D w))

/-- `1^{inLen(n)}`. -/
def uIn (w : List Bool) : List Bool := List.replicate (D.inLen.eval (NUPPT.inParam w).length) true

/-- `1^{i·inLen(n)}`: the offset of block `i` of the answer. -/
def offIn (w : List Bool) : List Bool :=
  List.replicate ((ipos D w).length * (uIn D w).length) true

/-- Block `i` of the answer, padded with `true` to `inLen(n)` bits. -/
def ans (w : List Bool) : List Bool :=
  ((zOut D w).drop (offIn D w).length ++ uIn D w).take (D.inLen.eval (NUPPT.inParam w).length)

/-- The test `f(z_i) = y`. -/
def test (w : List Bool) : Bool :=
  decide (D.Fe (pairEncode (NUPPT.inParam w) (ans D w)) = NUPPT.inArg w)

/-- The acceptance test of a round: a full round of coins remains and the test succeeds. -/
def acc (w : List Bool) : Bool :=
  decide ((ρP D).eval (NUPPT.inParam w).length ≤ (NUPPT.inCoins w).length) && test D w

/-- The step: drop one round of coins. -/
def g (w : List Bool) : List Bool :=
  pairEncode (pairFstD w) ((NUPPT.inCoins w).drop ((ρP D).eval (NUPPT.inParam w).length))

/-- The repeated machine: `T(|x|) + 1` rounds, the answer of the first successful one. -/
def yaoRaw (T : PolyExpr) (x : List Bool) : List Bool :=
  match (List.range (T.eval x.length + 1)).find? (fun i => acc D ((g D)^[i] x)) with
  | some i => ans D ((g D)^[i] x)
  | none => []

/-- The repeated machine with the default answer `1^{inLen(n)}` on exhaustion. -/
def yaoRaw' (T : PolyExpr) (x : List Bool) : List Bool :=
  if yaoRaw D T x = [] then uIn D x else yaoRaw D T x

section Poly

variable {D}
variable (hFe : PolyTimeComputable D.Fe) (hF' : PolyTimeComputable D.F') (hPm : PolyTimeComputable D.Pm)

/-- The advice of `A'` is polynomial-time. -/
theorem alpha1_poly : PolyTimeComputable alpha1 :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice

/-- The trial length is polynomial-time. -/
theorem ukk_poly : PolyTimeComputable ukk :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice

/-- The unary block count is polynomial-time. -/
theorem uM_poly : PolyTimeComputable (uM D) :=
  StateLoop.unaryPoly_comp D.m NUPPT.polyTimeComputable_inParam

/-- The round coins are polynomial-time. -/
theorem rc_poly : PolyTimeComputable (rc D) := by
  convert (polyTimeComputable_pairTakePoly (ρP D)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
  funext w
  simp [rc]

/-- `1^{n·k}` is polynomial-time. -/
theorem nkk_poly : PolyTimeComputable nkk := by
  convert polyTimeComputable_unaryMulPair.comp
    (NUPPT.polyTimeComputable_inParam.pairEncode ukk_poly) using 1
  funext w
  simp [nkk]

/-- The position bits are polynomial-time. -/
theorem posBits_poly : PolyTimeComputable (posBits D) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (nkk_poly.pairEncode (rc_poly (D := D))) using 1
  funext w
  simp [posBits]

include hPm in
/-- The position is polynomial-time. -/
theorem ipos_poly : PolyTimeComputable (ipos D) :=
  hPm.comp ((ukk_poly.pairEncode uM_poly).pairEncode posBits_poly)

/-- The fresh inputs are polynomial-time. -/
theorem xs_poly : PolyTimeComputable (xs D) := by
  convert (polyTimeComputable_pairTakePoly (.mul D.m D.inLen)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairDropPoly (.mul .var D.m)).comp
        (NUPPT.polyTimeComputable_inParam.pairEncode (rc_poly (D := D))))) using 1
  funext w
  simp [xs]

/-- The coins handed to `A'` are polynomial-time. -/
theorem rcoins_poly : PolyTimeComputable (rcoins D) := by
  convert (polyTimeComputable_pairDropPoly (.add (.mul .var D.m) (.mul D.m D.inLen))).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode (rc_poly (D := D))) using 1
  funext w
  simp [rcoins]

include hF' in
/-- The tuple is polynomial-time. -/
theorem ys_poly : PolyTimeComputable (ys D) :=
  hF'.comp (NUPPT.polyTimeComputable_inParam.pairEncode xs_poly)

/-- `1^{outLen(n)}` is polynomial-time. -/
theorem uOut_poly : PolyTimeComputable (uOut D) :=
  StateLoop.unaryPoly_comp D.outLen NUPPT.polyTimeComputable_inParam

include hPm in
/-- The offset is polynomial-time. -/
theorem off_poly : PolyTimeComputable (off D) := by
  convert polyTimeComputable_unaryMulPair.comp
    ((ipos_poly hPm).pairEncode (uOut_poly (D := D))) using 1
  funext w
  simp [off]

include hF' hPm in
/-- The planted tuple is polynomial-time. -/
theorem planted_poly : PolyTimeComputable (planted D) := by
  convert (((polyTimeComputable_pairTakePoly .var).comp
      ((off_poly hPm).pairEncode (ys_poly hF'))).append NUPPT.polyTimeComputable_inArg).append
    ((polyTimeComputable_pairDropPoly .var).comp
      (((off_poly hPm).append (uOut_poly (D := D))).pairEncode (ys_poly hF'))) using 1
  funext w
  simp [planted]

include hF' hPm in
/-- The answer of `A'` is polynomial-time. -/
theorem zOut_poly : PolyTimeComputable (zOut D) :=
  D.A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam (planted_poly hF' hPm)
      alpha1_poly rcoins_poly)

/-- `1^{inLen(n)}` is polynomial-time. -/
theorem uIn_poly : PolyTimeComputable (uIn D) :=
  StateLoop.unaryPoly_comp D.inLen NUPPT.polyTimeComputable_inParam

include hPm in
/-- The answer offset is polynomial-time. -/
theorem offIn_poly : PolyTimeComputable (offIn D) := by
  convert polyTimeComputable_unaryMulPair.comp
    ((ipos_poly hPm).pairEncode (uIn_poly (D := D))) using 1
  funext w
  simp [offIn]

include hF' hPm in
/-- The padded answer block is polynomial-time. -/
theorem ans_poly : PolyTimeComputable (ans D) := by
  convert (polyTimeComputable_pairTakePoly D.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (((polyTimeComputable_pairDropPoly .var).comp
        ((offIn_poly hPm).pairEncode (zOut_poly hF' hPm))).append (uIn_poly (D := D)))) using 1
  funext w
  simp [ans]

include hFe hF' hPm in
/-- The test is polynomial-time (`Complexity.polyTimeComputable_pairEq`). -/
theorem test_poly : PolyTimeComputable fun w => [test D w] := by
  convert polyTimeComputable_pairEq.comp
    ((hFe.comp (NUPPT.polyTimeComputable_inParam.pairEncode (ans_poly hF' hPm))).pairEncode
      NUPPT.polyTimeComputable_inArg) using 1
  funext w
  simp [test]

include hFe hF' hPm in
/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun w => [acc D w] := by
  convert polyTimeComputable_and
    (StateLoop.lenLe_comp NUPPT.polyTimeComputable_inCoins
      (StateLoop.unaryPoly_comp (ρP D) NUPPT.polyTimeComputable_inParam))
    (test_poly hFe hF' hPm) using 1
  funext w
  simp [acc]

/-- The step is polynomial-time. -/
theorem g_poly : PolyTimeComputable (g D) := by
  convert polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairDropPoly (ρP D)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)) using 1
  funext w
  simp [g]

/-- The orbit of every word under the step stays within `|w| + 2`. -/
theorem length_g_iterate_le (w : List Bool) (i : ℕ) : ((g D)^[i] w).length ≤ w.length + 2 := by
  have key : ∀ i, ((g D)^[i] w).length ≤ max w.length 2 := by
    intro i
    induction i with
    | zero => exact le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      refine (PosLoop.length_pairEncode_pairFstD_le _ _
        (by rw [List.length_drop]; exact Nat.sub_le _ _)).trans ?_
      exact max_le ih (le_max_right _ _)
  exact (key i).trans (by omega)

include hFe hF' hPm in
/-- The repeated machine is polynomial-time (`Complexity.polyTimeComputable_iterateFind`). -/
theorem yaoRaw_poly (T : PolyExpr) : PolyTimeComputable (yaoRaw D T) :=
  polyTimeComputable_iterateFind g_poly (acc_poly hFe hF' hPm) (ans_poly hF' hPm) T
    (.add .var (.const 2)) fun w i _ => by simpa using length_g_iterate_le w i

include hFe hF' hPm in
/-- The repeated machine with default is polynomial-time. -/
theorem yaoRaw'_poly (T : PolyExpr) : PolyTimeComputable (yaoRaw' D T) := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp (yaoRaw_poly hFe hF' hPm T))
    (uIn_poly (D := D)) (yaoRaw_poly hFe hF' hPm T) using 1
  funext w
  simp [yaoRaw']

end Poly

/-- The orbit on a raw input: after `i` rounds, `i·ρ(n)` coins have been dropped. -/
theorem iterate_g_layout (u y α r : List Bool) (i : ℕ) :
    (g D)^[i] (NUPPT.layout u y α r) =
      NUPPT.layout u y α (r.drop (i * (ρP D).eval u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [g, NUPPT.layout, NUPPT.inCoins, NUPPT.inParam, pairFstD_pairEncode,
      pairSndD_pairEncode, List.drop_drop]
    congr 2
    ring

end YaoMachine

/-! ### The typed coins of a round -/

/-- The coins of one round as a triple: `n·m` position bits, `m·k` bits of fresh inputs, and the
`c` coins of `A'`. -/
def roundEquiv (n M k c : ℕ) :
    (Fin (n * M) → Bool) × ((Fin (M * k) → Bool) × (Fin c → Bool)) ≃
      (Fin (n * M + (M * k + c)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (Fin.appendEquiv (M * k) c)).trans
    (Fin.appendEquiv (n * M) (M * k + c))

/-- The encoding of a round's coins is the concatenation of the three parts. -/
theorem ofFn_roundEquiv (n M k c : ℕ) (a : Fin (n * M) → Bool) (b : Fin (M * k) → Bool)
    (c' : Fin c → Bool) :
    List.ofFn (roundEquiv n M k c (a, (b, c'))) = List.ofFn a ++ (List.ofFn b ++ List.ofFn c') := by
  show List.ofFn (Fin.append a (Fin.append b c')) = _
  simp only [List.ofFn_fin_append]

/-- The `n` trials of `kk` bits read from the first `n·kk` position bits. -/
def pbOf {n M kk : ℕ} (h : n * kk ≤ n * M) (a : Fin (n * M) → Bool) : Fin n → Fin kk → Bool :=
  fun t j => a (Fin.castLE h (finProdFinEquiv (t, j)))

/-- The rejection-sampled position (`0` on failure). -/
def posOf {n M kk : ℕ} (hM : 0 < M) (h : n * kk ≤ n * M) (a : Fin (n * M) → Bool) : Fin M :=
  (rejectionSample M kk n (pbOf h a)).getD ⟨0, hM⟩

/-- Reading the trials pushes uniform position bits to uniform trials (a restriction to the
first `n·kk` coordinates followed by the block bijection).

**Proof sketch.** The restriction is the first projection of the bijection
`(Fin (n·m) → Bool) ≃ (Fin (n·kk) → Bool) × (Fin (n·m − n·kk) → Bool)` (`Fin.appendEquiv`,
`finCongr`), which pushes uniform to uniform (`HardcoreBit.pushesUniform_fst`); the block
bijection is a bijection. -/
theorem pushesUniform_pbOf {n M kk : ℕ} (h : n * kk ≤ n * M) :
    HardcoreBit.PushesUniform (pbOf (M := M) h) := by
  have hsum : n * M = n * kk + (n * M - n * kk) := by omega
  let e₁ : (Fin (n * M) → Bool) ≃ (Fin (n * kk) → Bool) × (Fin (n * M - n * kk) → Bool) :=
    (Equiv.arrowCongr (finCongr hsum) (Equiv.refl Bool)).trans (Fin.appendEquiv _ _).symm
  have h₁ : HardcoreBit.PushesUniform fun a : Fin (n * M) → Bool => (e₁ a).1 :=
    (HardcoreBit.pushesUniform_equiv e₁).comp HardcoreBit.pushesUniform_fst
  have h₂ := h₁.comp (HardcoreBit.pushesUniform_equiv (blocksE n kk))
  convert h₂ using 1

/-- The typed coins of a round read off the raw round coins: the position by rejection, the
fresh inputs as `m` blocks of `k` bits, and the coins of `A'`. -/
def roundSample (n M k c kk : ℕ) (hM : 0 < M) (h : n * kk ≤ n * M)
    (rc : Fin (n * M + (M * k + c)) → Bool) : Fin M × (Fin M → Fin k → Bool) × (Fin c → Bool) :=
  (posOf hM h ((roundEquiv n M k c).symm rc).1,
    blocksE M k ((roundEquiv n M k c).symm rc).2.1, ((roundEquiv n M k c).symm rc).2.2)

/-- The typed coins of a round are within `(1 − m/2^{kk})^n` of uniform
(`statClose_rejectionSample` for the position, bijections for the rest). -/
theorem statClose_roundSample (n M k c kk : ℕ) (hM : 0 < M) (hMk : M ≤ 2 ^ kk)
    (h : n * kk ≤ n * M) :
    StatClose (roundSample n M k c kk hM h) id ((1 - (M : ℝ) / 2 ^ kk) ^ n + 0) := by
  have hpos : StatClose (posOf (n := n) (kk := kk) hM h) (id : Fin M → Fin M)
      ((1 - (M : ℝ) / 2 ^ kk) ^ n) :=
    (statClose_rejectionSample M kk n hM hMk ⟨0, hM⟩).comp_pushesUniform (pushesUniform_pbOf h)
  have hbij : StatClose (Equiv.prodCongr (blocksE M k) (Equiv.refl (Fin c → Bool)))
      (id : (Fin M → Fin k → Bool) × (Fin c → Bool) → _) 0 :=
    statClose_of_pushesUniform (HardcoreBit.pushesUniform_equiv _)
  have hprod := (hpos.prod hbij).comp_equiv_left (roundEquiv n M k c).symm
  convert hprod using 1

/-- The total inverter of the direct product read off `A'`: on the tuple `ys` with coins `r`,
block `j` of `A'`'s answer, padded with `true` to `inLen(n)` bits (`padTrue`); when the answer
has the right length this is exactly `A'`'s inverse, so it inverts at least as often as `A'`
[PS10, Algorithm 38.5, "`z_i`"]. -/
def yaoB (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ) :
    (Fin (m.eval n) → Fin (outLen.eval n) → Bool) → A'.Coins n →
      (Fin (m.eval n) → Fin (inLen.eval n) → Bool) :=
  fun ys r j => padTrue (inLen.eval n)
    ((A'.runAt n (List.ofFn ((blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop
      (j * inLen.eval n))

namespace YaoMachine

variable (D : Data)

/-- The advice of the reduction: `⟨A'.advice n, 1^{kkOf (m n)}⟩`. -/
def adv (n : ℕ) : List Bool :=
  pairEncode (D.A'.advice n) (List.replicate (kkOf (D.m.eval n)) true)

/-- The advice bound `2·adv' + 2 + (m + 1)`. -/
def advP : PolyExpr := .add (.add (.mul (.const 2) D.A'.adv) (.const 2)) (.add D.m (.const 1))

/-- The advice is bounded by `advP`. -/
theorem adv_length (n : ℕ) : (adv D n).length ≤ (advP D).eval n := by
  simp only [adv, advP, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const]
  have := D.A'.advice_length n
  have := kkOf_le_succ (D.m.eval n)
  omega

/-- The number of coins of a round, `ρ(n) = n·m + (m·inLen + coins_{A'})`, in the form of
`roundEquiv`. -/
theorem ρP_eval (n : ℕ) :
    (ρP D).eval n = n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n) := rfl

/-- `n·kkOf m ≤ n·m` for `0 < m`. -/
theorem nkk_le (n M : ℕ) (hM : 0 < M) : n * kkOf M ≤ n * M := Nat.mul_le_mul_left n (kkOf_le M hM)

section Round

variable {D}
variable (n : ℕ) (hM : 0 < D.m.eval n)
  (f : (Fin (D.inLen.eval n) → Bool) → (Fin (D.outLen.eval n) → Bool))
  (hFe : ∀ a : Fin (D.inLen.eval n) → Bool,
    D.Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f a))
  (hF' : ∀ x : Fin (D.m.eval n * D.inLen.eval n) → Bool,
    D.F' (pairEncode (List.replicate n true) (List.ofFn x)) =
      (List.ofFn fun i : Fin (D.m.eval n) => D.Fe (pairEncode (List.replicate n true)
        (List.ofFn fun j : Fin (D.inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten)
  (hPm : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
    D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
      (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
      List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
        fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true)
  (y : Fin (D.outLen.eval n) → Bool)
  (rc : Fin ((ρP D).eval n) → Bool)
  (rest' : List Bool)

include hFe hF' hPm in
/-- **The round identity:** on the state word of a round whose coins start with `rc`, the padded
answer block is the encoding of `OneWay.yaoTry` on the typed coins `roundSample rc`.

**Proof sketch.** Unfold the FP round on the layout: the projections return the slots, the
coin cuts return the three parts of `rc` (`ofFn_roundEquiv`, `List.take_left'`,
`List.drop_left'`), the position sampler returns `1^i` (`hPm`, `ofFn_castLE_eq_take`), the
blockwise evaluator returns the tuple `(f(x₁), …, f(x_m))` (`hF'`, `hFe`, `ofFn_blocksE_symm`),
planting is splicing (`ofFn_blocksE_symm_update`), `A'.output` on the layout is `A'.runAt`, and
the padded block is `padTrue` (`ofFn_padTrue`). -/
theorem ans_layout :
    ans D (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn rc ++ rest')) =
      List.ofFn (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y
        (roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
          (nkk_le n _ hM) rc)) := by
  obtain ⟨⟨a, b, c'⟩, rfl⟩ : ∃ p, roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) p = rc :=
    ⟨_, Equiv.apply_symm_apply _ rc⟩
  simp only [roundSample, Equiv.symm_apply_apply]
  set w := NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n)
    (List.ofFn (roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (a, b, c')) ++ rest')
    with hw
  have hu : NUPPT.inParam w = List.replicate n true := by simp [hw]
  have hy : NUPPT.inArg w = List.ofFn y := by simp [hw]
  have hα : NUPPT.inAdvice w = adv D n := by simp [hw]
  have hcoins : NUPPT.inCoins w =
      List.ofFn (roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (a, b, c')) ++ rest' := by
    simp [hw]
  have halpha : alpha1 w = D.A'.advice n := by simp [alpha1, hα, adv]
  have hukk : ukk w = List.replicate (kkOf (D.m.eval n)) true := by simp [ukk, hα, adv]
  have huM : uM D w = List.replicate (D.m.eval n) true := by simp [uM, hu]
  have hrc : rc D w = List.ofFn a ++ (List.ofFn b ++ List.ofFn c') := by
    simp only [YaoMachine.rc, hcoins, hu, List.length_replicate, ρP_eval]
    rw [List.take_left' (by simp), ofFn_roundEquiv]
  have hnkk : nkk w = List.replicate (n * kkOf (D.m.eval n)) true := by
    simp [nkk, hu, hukk]
  have hposBits : posBits D w =
      List.ofFn fun j : Fin (n * kkOf (D.m.eval n)) => a (Fin.castLE (nkk_le n _ hM) j) := by
    simp only [posBits, hrc, hnkk, List.length_replicate]
    rw [List.take_append_of_le_length (by simpa using nkk_le n _ hM), ← ofFn_castLE_eq_take]
  have hipos : ipos D w = List.replicate (posOf hM (nkk_le n _ hM) a).val true := by
    simp only [ipos, hukk, huM, hposBits]
    exact hPm _
  have hxs : xs D w = List.ofFn b := by
    simp only [xs, hrc, hu, PolyExpr.eval_mul, PolyExpr.eval_var, List.length_replicate]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]
  have hrcoins : rcoins D w = List.ofFn c' := by
    simp only [rcoins, hrc, hu, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var,
      List.length_replicate]
    rw [← List.append_assoc, List.drop_left' (by simp)]
  have hys : ys D w = List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))) := by
    simp only [ys, hu, hxs]
    rw [hF' b, ofFn_blocksE_symm]
    congr 2
    funext i
    rw [hFe]
    rfl
  have huOut : uOut D w = List.replicate (D.outLen.eval n) true := by simp [uOut, hu]
  have hoff : off D w = List.replicate ((posOf hM (nkk_le n _ hM) a).val * D.outLen.eval n) true := by
    simp [off, hipos, huOut]
  have hplanted : planted D w = List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (Function.update (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))
        (posOf hM (nkk_le n _ hM) a) y)) := by
    rw [ofFn_blocksE_symm_update]
    simp only [planted, hoff, huOut, hys, hy, List.length_replicate, List.length_append]
  have hz : zOut D w = D.A'.runAt n (List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (Function.update (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))
        (posOf hM (nkk_le n _ hM) a) y))) c' := by
    simp only [zOut, hu, hplanted, halpha, hrcoins]
    rfl
  have huIn : uIn D w = List.replicate (D.inLen.eval n) true := by simp [uIn, hu]
  have hoffIn : offIn D w =
      List.replicate ((posOf hM (nkk_le n _ hM) a).val * D.inLen.eval n) true := by
    simp [offIn, hipos, huIn]
  simp only [ans, hoffIn, huIn, hz, hu, List.length_replicate]
  rw [yaoTry]
  simp only [yaoB]
  rw [ofFn_padTrue]

include hFe hF' hPm in
/-- **The round test:** on the state word of a round, the test is `f(z_i) = y`. -/
theorem test_layout :
    test D (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn rc ++ rest')) =
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y
        (roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
          (nkk_le n _ hM) rc)) = y) := by
  rw [test, ans_layout n hM f hFe hF' hPm y rc rest']
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout]
  rw [hFe]
  simp [List.ofFn_injective.eq_iff]

end Round

end YaoMachine

/-- `OneWay.yaoInverter` returns the first successful try, found by `List.find?`
(`foldr_ite_eq_find?`). -/
theorem yaoInverter_eq_find? {α β ρ : Type*} [DecidableEq β] {q : ℕ} (inst : Inhabited α)
    (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (T : ℕ) (y : β)
    (cs : Fin T → Fin q × (Fin q → α) × ρ) :
    @yaoInverter α β ρ _ q inst f B T y cs =
      ((List.finRange T).find? (fun t => decide (f (yaoTry f B y (cs t)) = y))).elim
        (@default α inst) (fun t => yaoTry f B y (cs t)) := by
  unfold yaoInverter
  have h := foldr_ite_eq_find? (fun t => f (yaoTry f B y (cs t)) = y)
    (fun t => yaoTry f B y (cs t)) (@default α inst) (List.finRange T)
  convert h

namespace YaoMachine

variable (D : Data)

section Loop

variable {D}
variable (T : PolyExpr) (n : ℕ) (hM : 0 < D.m.eval n)

/-- The typed coins of all `T(n) + 1` rounds, read off the coin string. -/
def sampleAll (r : Fin ((T.eval n + 1) * (ρP D).eval n) → Bool) :
    Fin (T.eval n + 1) →
      Fin (D.m.eval n) × (Fin (D.m.eval n) → Fin (D.inLen.eval n) → Bool) × D.A'.Coins n :=
  fun i => roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
    (nkk_le n _ hM) (blocksE (T.eval n + 1) ((ρP D).eval n) r i)

/-- **The coins of all rounds are close to uniform:** within `(T(n) + 1)·(1 − m/2^{kk})^n`
(`statClose_roundSample`, `statClose_pi`, the block bijection on the coin string). -/
theorem statClose_sampleAll :
    StatClose (sampleAll T n hM) id
      (((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0)) :=
  (statClose_pi (statClose_roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n)
    (kkOf (D.m.eval n)) hM (lt_two_pow_kkOf _).le (nkk_le n _ hM)) (T.eval n + 1)).comp_equiv_left
    (blocksE (T.eval n + 1) ((ρP D).eval n))

variable (hn : 1 ≤ n)
  (f : (Fin (D.inLen.eval n) → Bool) → (Fin (D.outLen.eval n) → Bool))
  (hFe : ∀ a : Fin (D.inLen.eval n) → Bool,
    D.Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f a))
  (hF' : ∀ x : Fin (D.m.eval n * D.inLen.eval n) → Bool,
    D.F' (pairEncode (List.replicate n true) (List.ofFn x)) =
      (List.ofFn fun i : Fin (D.m.eval n) => D.Fe (pairEncode (List.replicate n true)
        (List.ofFn fun j : Fin (D.inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten)
  (hPm : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
    D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
      (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
      List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
        fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true)

include hn hFe hF' hPm in
/-- **The loop identity:** on the raw input `⟨⟨⟨1^n, y⟩, ⟨α', 1^k⟩⟩, r⟩` the repeated machine
returns the encoding of `OneWay.yaoInverter` with the default `1^{inLen(n)}` on the typed coins
`sampleAll r`.

**Proof sketch.** Round `i` runs on the layout with the first `i·ρ(n)` coins dropped
(`iterate_g_layout`); for `i ≤ T(n)` the remaining coins start with block `i` of `r`
(`ofFn_block_eq_take_drop`), so the round test is `f(z_i) = y` (`test_layout`) and the payload is
`yaoTry` on `sampleAll r i` (`ans_layout`); from round `T(n) + 1` on no coins remain and the test
fails. The loop's `find?` over `List.range (T(|x|) + 1) ⊇ [0, T(n)]` is the `find?` over
`finRange (T(n) + 1)` (`find?_range_eq_map_find?_finRange`), which is `yaoInverter`
(`yaoInverter_eq_find?`); on exhaustion both return `1^{inLen(n)}`. -/
theorem yaoRaw'_layout (y : Fin (D.outLen.eval n) → Bool)
    (r : Fin ((T.eval n + 1) * (ρP D).eval n) → Bool) :
    yaoRaw' D T (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn r)) =
      List.ofFn (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ f (yaoB D.inLen D.outLen D.m D.A' n)
        (T.eval n + 1) y (sampleAll T n hM r)) := by
  set x₀ := NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn r) with hx₀
  have hρpos : 0 < (ρP D).eval n := by
    rw [ρP_eval]
    have := Nat.mul_pos hn hM
    omega
  have hstate : ∀ i, (g D)^[i] x₀ = NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n)
      ((List.ofFn r).drop (i * (ρP D).eval n)) := by
    intro i
    rw [hx₀, iterate_g_layout]
    simp only [List.length_replicate]
  have hblock : ∀ (i : ℕ) (h : i < T.eval n + 1), (List.ofFn r).drop (i * (ρP D).eval n) =
      List.ofFn (blocksE (T.eval n + 1) ((ρP D).eval n) r ⟨i, h⟩) ++
        ((List.ofFn r).drop (i * (ρP D).eval n)).drop ((ρP D).eval n) := by
    intro i h
    conv_lhs => rw [← List.take_append_drop ((ρP D).eval n) ((List.ofFn r).drop (i * (ρP D).eval n))]
    congr 1
    exact (ofFn_block_eq_take_drop r ⟨i, h⟩).symm
  have hacc : ∀ i : ℕ, acc D ((g D)^[i] x₀) =
      if h : i < T.eval n + 1 then
        decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r ⟨i, h⟩)) = y)
      else false := by
    intro i
    rw [hstate]
    split_ifs with h
    · rw [hblock i h]
      unfold acc
      rw [test_layout n hM f hFe hF' hPm y _ _]
      simp only [NUPPT.inParam_layout, NUPPT.inCoins_layout, List.length_replicate,
        List.length_append, List.length_ofFn]
      simp [sampleAll]
    · have hdrop : (List.ofFn r).drop (i * (ρP D).eval n) = [] := by
        apply List.drop_eq_nil_of_le
        rw [List.length_ofFn]
        exact Nat.mul_le_mul_right _ (not_lt.1 h)
      rw [hdrop]
      unfold acc
      simp only [NUPPT.inParam_layout, NUPPT.inCoins_layout, List.length_replicate,
        List.length_nil]
      simp [hρpos.ne']
  have hout : ∀ i : Fin (T.eval n + 1), ans D ((g D)^[i] x₀) =
      List.ofFn (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r i)) := by
    intro i
    rw [hstate, hblock i.1 i.2]
    exact ans_layout n hM f hFe hF' hPm y _ _
  have hR : T.eval n + 1 ≤ T.eval x₀.length + 1 := by
    have : n ≤ x₀.length := by
      simp only [hx₀, NUPPT.layout, length_pairEncode, List.length_replicate]
      omega
    exact Nat.succ_le_succ (T.eval_mono this)
  have hfind := find?_range_eq_map_find?_finRange hR
    (fun t : Fin (T.eval n + 1) =>
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r t)) = y))
    (fun i => acc D ((g D)^[i] x₀))
    (fun t h => by show acc D ((g D)^[t] x₀) = _; rw [hacc, dif_pos h])
    (fun t h => by show acc D ((g D)^[t] x₀) = _; rw [hacc, dif_neg (not_lt.2 h)])
  rw [yaoInverter_eq_find? ⟨fun _ => true⟩]
  unfold yaoRaw' yaoRaw
  rw [hfind]
  have huIn : uIn D x₀ = List.replicate (D.inLen.eval n) true := by simp [uIn, hx₀]
  cases hf : (List.finRange (T.eval n + 1)).find? fun t =>
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r t)) = y) with
  | none =>
    simp only [Option.map_none, Option.elim_none]
    simp [huIn, List.ofFn_const]
  | some t =>
    simp only [Option.map_some, Option.elim_some]
    rw [hout t]
    split_ifs with h0
    · have hk : D.inLen.eval n = 0 := by simpa using congrArg List.length h0
      rw [huIn, h0, hk]
      rfl
    · rfl

end Loop

end YaoMachine

/-- **The Yao reduction machine** [PS10, Algorithm 38.5]: for lengths `inLen`, `outLen`, a block
count `m` (positive at every `n ≥ 1`), a round count `T`, a function `f` with a polynomial-time
evaluator `Fe` on `⟨1^n, x⟩`, and any `NUPPT` `A'`, there is an `NUPPT` `A` whose inversion
probability against `f` at every `n ≥ 1` is at least that of the concrete
`OneWay.yaoInverter (f n) (yaoB … n) (T(n) + 1)` [Gar26, Figure 2.2] minus the statistical
term `(T(n) + 1)·2^{-n}` of the rejection-sampled positions (D10).

**Proof sketch.** `A := NUPPT.ofPolyTime` of `YaoMachine.yaoRaw'` (polynomial-time by
`YaoMachine.yaoRaw'_poly`, from `exists_prodEval`, `exists_posMachine` and
`Complexity.polyTimeComputable_iterateFind`) with coins `(T + 1)·ρ`, `ρ = n·m + m·inLen + coins_{A'}`,
and advice `⟨A'.advice n, 1^{kkOf (m n)}⟩` (bounded by `YaoMachine.advP`). At `n ≥ 1`,
`YaoMachine.yaoRaw'_layout` identifies `A`'s inverter with `some (yaoInverter … y (sampleAll r))`
(`decodeFin_ofFn`), so `A`'s inversion probability is the success probability of `yaoInverter`
on the sampled coins; `YaoMachine.statClose_sampleAll` and `StatClose.abs_uprob_sub_le_prod`
move it to uniform coins at the cost of `(T + 1)·(1 − m/2^{kk})^n ≤ (T + 1)·2^{-n}`
(`uprob_rejectionSample_none_le_half_pow`). -/
theorem exists_yaoReduction (inLen outLen m T : PolyExpr)
    (f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool))
    {Fe : List Bool → List Bool} (hFe : PolyTimeComputable Fe)
    (hFe_spec : ∀ n (a : Fin (inLen.eval n) → Bool),
      Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f n a))
    (A' : NUPPT) (hm : ∀ n, 1 ≤ n → 0 < m.eval n) :
    ∃ A : NUPPT, ∀ n, 1 ≤ n →
      invProb (f n) (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1)) - (T.eval n + 1) * (1 / 2 : ℝ) ^ n ≤
        invProbOpt (f n) (A.inverter n (inLen.eval n) (outLen.eval n)) := by
  obtain ⟨F', hF', hF'spec⟩ := exists_prodEval hFe inLen m
  obtain ⟨Pm, hPm, hPmspec⟩ := exists_posMachine
  let D : YaoMachine.Data := ⟨Fe, F', Pm, inLen, outLen, m, A'⟩
  let A : NUPPT := NUPPT.ofPolyTime (YaoMachine.yaoRaw'_poly (D := D) hFe hF' hPm T)
    (.mul (.add T (.const 1)) (YaoMachine.ρP D)) (YaoMachine.advP D) (YaoMachine.adv D)
    (YaoMachine.adv_length D)
  refine ⟨A, fun n hn => ?_⟩
  have hM : 0 < D.m.eval n := hm n hn
  have hPm' : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
      D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
        (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
        List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
          fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true :=
    fun pb' => hPmspec (D.m.eval n) (kkOf (D.m.eval n)) n hM (kkOf_pos _) (two_pow_kkOf_le _ hM) pb'
  -- the functional identity
  have hrun : ∀ (y : Fin (outLen.eval n) → Bool) (r : A.Coins n),
      A.runAt n (List.ofFn y) r =
        List.ofFn (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) y (YaoMachine.sampleAll T n hM r)) := by
    intro y r
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime _ _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    exact YaoMachine.yaoRaw'_layout T n hM hn (f n) (hFe_spec n) (hF'spec n) hPm' y r
  have hinv : ∀ (y : Fin (outLen.eval n) → Bool) (r : A.Coins n),
      A.inverter n (inLen.eval n) (outLen.eval n) y r =
        some (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) y (YaoMachine.sampleAll T n hM r)) := by
    intro y r
    simp only [NUPPT.inverter, hrun, decodeFin_ofFn]
  -- the statistical switch
  have hS := YaoMachine.statClose_sampleAll T n hM
  have hδ : (1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    have h1 := uprob_rejectionSample_none (D.m.eval n) (kkOf (D.m.eval n)) n hM
      (lt_two_pow_kkOf _).le
    have h2 := uprob_rejectionSample_none_le_half_pow (D.m.eval n) (kkOf (D.m.eval n)) n hM
      (lt_two_pow_kkOf _).le (two_pow_kkOf_le _ hM)
    rwa [h1] at h2
  have hS' : StatClose (fun r : A.Coins n => YaoMachine.sampleAll T n hM r) id
      (((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0)) := hS
  have key := hS'.abs_uprob_sub_le_prod fun cs (x : Fin (inLen.eval n) → Bool) =>
    f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
      (T.eval n + 1) (f n x) cs) = f n x
  have hL : invProbOpt (f n) (A.inverter n (inLen.eval n) (outLen.eval n)) =
      uprob fun z : A.Coins n × (Fin (inLen.eval n) → Bool) =>
        f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) (f n z.2) (YaoMachine.sampleAll T n hM z.1)) = f n z.2 := by
    unfold invProbOpt
    rw [← uprob_comp_equiv (Equiv.prodComm (A.Coins n) (Fin (inLen.eval n) → Bool))]
    congr 1
    funext z
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hinv, Option.some.injEq,
      exists_eq_left']
  have hR : invProb (f n) (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
      (T.eval n + 1)) =
      uprob fun z : (Fin (T.eval n + 1) →
          Fin (m.eval n) × (Fin (m.eval n) → Fin (inLen.eval n) → Bool) × A'.Coins n) ×
          (Fin (inLen.eval n) → Bool) =>
        f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) (f n z.2) (id z.1)) = f n z.2 := by
    unfold invProb
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    congr 1
  have hδ' : ((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0) ≤
      (T.eval n + 1) * (1 / 2 : ℝ) ^ n := by
    rw [add_zero]
    push_cast
    exact mul_le_mul_of_nonneg_left hδ (by positivity)
  have hkey := (abs_le.1 key).1
  linarith [hL, hR, hkey, hδ']

end TCSlib.Cryptography.OneWay

## ===== TCSlib/Cryptography/Asymptotic/CollectionsLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Padding and coin-splitting lemmas for the collection and universal constructions

Proof infrastructure shared by `TCSlib.Cryptography.Asymptotic.Collections`
([PS10, Theorem 42.2 ⇒]) and `TCSlib.Cryptography.Asymptotic.Universal`
([PS10, Theorem 63.1]): the polynomial-time *padding evaluator*
`padStr p u w = (w ++ 0^{p(|u|)}).take (p(|u|))`, which is the string form of the typed
output `padFin (p n) w` of a function family at parameter `n` read off `1^n`
(`ofFn_padFin_eq_padStr`).

Every FP fact here is an instance of the pairing calculus of
`TCSlib.Complexity.ClassNP.PolyTimePairing`, the unary evaluator
`Complexity.polyTimeComputable_unaryPoly`, the typed cut
`Complexity.polyTimeComputable_pairTakePoly` and the bitwise xor
`Complexity.polyTimeComputable_pairXor` (zeros are `1^m ⊕ 1^m`).

## Main definitions

* `TCSlib.Cryptography.padStr` — the string padded with `false` (or truncated) to
  `p(|u|)` bits.

## Main results

* `TCSlib.Cryptography.polyTimeComputable_padStr` — the padding evaluator is
  polynomial-time on `⟨u, w⟩`.
* `TCSlib.Cryptography.ofFn_padFin_eq_take`, `TCSlib.Cryptography.ofFn_padFin_eq_padStr`,
  `TCSlib.Cryptography.padStr_of_length_le` — the encoding of a padded typed string is the
  padded string.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5 Theorem 42.2; §2.13 Algorithm 64.2.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Zeros and the padding evaluator -/

/-- The bitwise xor of `1^m` with itself is `0^m`. -/
theorem zipWith_xor_replicate_true (m : ℕ) :
    List.zipWith xor (List.replicate m true) (List.replicate m true) = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m _ => simp [List.replicate_succ]

/-- `z ↦ 0^{p(|fst z|)}` is polynomial-time: the unary evaluator of `p` on the first
component, xored with itself (`Complexity.polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_zerosPoly (p : PolyExpr) :
    PolyTimeComputable fun z => List.replicate (p.eval (pairFstD z).length) false := by
  have hu : PolyTimeComputable fun z => List.replicate (p.eval (pairFstD z).length) true :=
    (polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD
  have h := polyTimeComputable_pairXor.comp (hu.pairEncode hu)
  convert h using 1
  funext z
  simp

/-- The string `w` padded with `false` (or truncated) to `p(|u|)` bits: the string form of
the typed output `padFin (p n) w` at the parameter `n = |u|` read off `u = 1^n`
(`ofFn_padFin_eq_padStr`). -/
def padStr (p : PolyExpr) (u w : List Bool) : List Bool :=
  (w ++ List.replicate (p.eval u.length) false).take (p.eval u.length)

/-- **The padding evaluator is polynomial-time** on `⟨u, w⟩`: append the zeros
`polyTimeComputable_zerosPoly` and keep the first `p(|u|)` bits
(`Complexity.polyTimeComputable_pairTakePoly` on `⟨u, w ++ 0^{p(|u|)}⟩`). -/
theorem polyTimeComputable_padStr (p : PolyExpr) :
    PolyTimeComputable fun z => padStr p (pairFstD z) (pairSndD z) := by
  have hbody : PolyTimeComputable fun z =>
      pairSndD z ++ List.replicate (p.eval (pairFstD z).length) false :=
    polyTimeComputable_pairSndD.append (polyTimeComputable_zerosPoly p)
  have h := (polyTimeComputable_pairTakePoly p).comp (polyTimeComputable_pairFstD.pairEncode hbody)
  convert h using 1
  funext z
  simp [padStr]

/-- The padded reading of a string: `List.ofFn (padFin ℓ w)` is `(w ++ 0^ℓ).take ℓ`. -/
theorem ofFn_padFin_eq_take (ℓ : ℕ) (w : List Bool) :
    List.ofFn (padFin ℓ w) = (w ++ List.replicate ℓ false).take ℓ := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_append, List.length_replicate]
    omega
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_take,
      List.getElem_append]
    simp only [padFin, List.getD_eq_getElem?_getD]
    split_ifs with h₃
    · simp [List.getElem?_eq_getElem h₃]
    · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h₃)]

/-- The encoding of the typed padding at parameter `|u|` is the padding evaluator. -/
theorem ofFn_padFin_eq_padStr (p : PolyExpr) (u w : List Bool) :
    List.ofFn (padFin (p.eval u.length) w) = padStr p u w :=
  ofFn_padFin_eq_take _ _

/-- The padding of a string shorter than the target length appends zeros only. -/
theorem padStr_of_length_le (p : PolyExpr) (u w : List Bool) (hw : w.length ≤ p.eval u.length) :
    padStr p u w = w ++ List.replicate (p.eval u.length - w.length) false := by
  unfold padStr
  rw [List.take_append, List.take_of_length_le hw, List.take_replicate]
  congr 2
  omega

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Universal.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import TCSlib.Cryptography.Asymptotic.UniversalPadding
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Levin's universal one-way function

The universal one-way function of [PS10, §2.13]: `f_universal` interprets its input `y` as a
machine–input pair `⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, runs `M` on `x` for a cubic number of
steps through the clocked universal machine `Turing.timed_universal_concrete`, and outputs
`⟨M, M(x)⟩` (or `⟨M, ⊥⟩` on timeout). [PS10, Theorem 63.1] says that `f_universal` is one-way
as soon as *some* one-way function exists; the proof shows weak one-wayness with `q(n) = n³`
through [PS10, Lemma 64.3] (a strong one-way function computable in quadratic time, by
padding) and the two counting claims of [PS10, p. 65] (`PickG`, the union bound), then applies
Yao's amplification [PS10, Theorem 35.1] (`weak_to_strong`).

**Deviation (source error, DESIGN §7, error 1):** [PS10, Algorithm 64.2] outputs `M(x)` only;
an inverter may then answer `⟨M', x'⟩` with `M' ≠ M_g`, which yields no preimage under `M_g`,
and the proof of Theorem 63.1 is invalid. The corrected function outputs `⟨M, M(x)⟩` (Levin's
definition). The budget `|y|³` becomes `(|y| + 1)³` (error 19); the timeout symbol `⊥` is
`[false]`, distinct from every successful answer `true :: M(x)` (`Turing.timed_universal`).

**Deviation (encoding of machines):** the text "assumes a standard way to encode Turing
machines with appropriate padding"; here the encoding is an arbitrary effective scheme
`c : Turing.EffectiveMachineCode` ([AB09, §1.4], `decode_encode_pad`), and the clocked
simulation costs the code-dependent coefficient of `Turing.timed_universal_concrete`, which
includes `c.canonizerTime |M|`. The theorems assume a canonizer at most exponential in the code
length (`CanonizerExp c`), so that the coefficient is polynomial in `n` for codes of length
`⌊log₂ n⌋`; no bound on the canonizer of `Turing.exists_effectiveMachineCode` is available,
so the headlines `fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay` and
`theorem_63_1` are **conditional** on this hypothesis — ratified by the run-3 audit (P3-4) as
an explicit hypothesis in the manner of the arithmetic bundle `Candidates.ArithmeticFP`
(plan D11); the open problem of exhibiting a scheme with such a canonizer is the sorried
`exists_canonizerExp`.

**Deviation (typed domains, D5):** `fUniversal c` is `FunFamily.ofString` of the string
function with the output-length polynomial `univOutLen` (outputs padded with `false`, never
truncated by `length_fUniversalStr_le`); the `g'` of Lemma 64.3 is a family with `inLen = var`
computable by a coded machine on the bare input (`FunFamily.QuadraticCode`).

## Main definitions

* `TCSlib.Cryptography.clockedAnswer`, `TCSlib.Cryptography.univCoeff` — the answer and the
  coefficient of the clocked universal simulation.
* `TCSlib.Cryptography.univCode`, `TCSlib.Cryptography.univArg`,
  `TCSlib.Cryptography.fUniversalStr`, `TCSlib.Cryptography.univOutLen`,
  `TCSlib.Cryptography.fUniversal` — `f_universal` [PS10, Algorithm 64.2], corrected.
* `TCSlib.Cryptography.CanonizerExp` — the hypothesis on the encoding scheme;
  `TCSlib.Cryptography.FunFamily.QuadraticCode` — computable by a coded machine in time
  `c₀ (|x| + 1)²` [PS10, Lemma 64.3].

## Main results

* `TCSlib.Cryptography.exists_univ_computes` — the clocked universal machine computes
  `clockedAnswer` (repackaging of `Turing.timed_universal_concrete`); the serialization-length
  facts it needs live in `TCSlib.Cryptography.Asymptotic.UniversalLemmas`;
  `TCSlib.Cryptography.exists_univCoeff_le` — its coefficient is polynomial on codes of
  length `⌊log₂ n⌋` under `CanonizerExp`; `TCSlib.Cryptography.exists_canonizerExp` — the
  open problem that some scheme satisfies `CanonizerExp` (sorried, run-3 audit P3-4).
* `TCSlib.Cryptography.fUniversal_easy` — `f_universal` is polynomial-time computable
  [PS10, Algorithm 64.2, "computable in time `O(|y|³)`"] (proved; the evaluator is assembled
  from `polyTimeComputable_univCode`, `polyTimeComputable_univArg`,
  `polyTimeComputable_clockedAnswer` and `polyTimeComputable_fUniversalStr`, with the generic
  padding and splitting lemmas of `TCSlib.Cryptography.Asymptotic.CollectionsLemmas` and
  `TCSlib.Cryptography.Asymptotic.UniversalLemmas`).
* `TCSlib.Cryptography.lemma_64_3` — a strong one-way function computable in quadratic time
  [PS10, Lemma 64.3] (from `PadQuad.exists_family` of
  `TCSlib.Cryptography.Asymptotic.UniversalPadding`; one machine admission remains, see the
  fill note).
* `TCSlib.Cryptography.claim_65_1`, `claim_65_2`, `claim_65_2_cond` — `PickG` and the union
  bound [PS10, p. 65].
* `TCSlib.Cryptography.fUniversal_hard`, `TCSlib.Cryptography.fUniversal_weakOneWay`,
  `TCSlib.Cryptography.theorem_63_1` — `f_universal` is weakly one-way with `q(n) = n³`, hence
  (after amplification) strongly one-way [PS10, Theorem 63.1] (`fUniversal_hard` and
  `fUniversal_weakOneWay` are proved from the hypothesis of `lemma_64_3`; `theorem_63_1`
  depends on `lemma_64_3`, which is sorried, see its fill note).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13: Theorem 63.1, Algorithm 64.2, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding) and Exercise 2.4.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4: encodings of machines, universal simulation.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The clocked universal simulation -/

/-- The answer of the clocked simulation of the coded machine `c.decode α` on the input `x`
with the budget `t`: `true :: output` if the machine has halted within `t` steps (deadline
included), `[false]` (the `⊥` of [PS10, Algorithm 64.2]) otherwise — the output convention of
`Turing.timed_universal`. -/
def clockedAnswer (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  if ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none then
    true :: ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output
  else [false]

/-- The code-dependent coefficient of the quadratic time bound of the clocked universal
simulation, as displayed in `Turing.timed_universal_concrete` (startup part
`3|α| + canonizerTime |α| + |serialize| + 2|bits numStates| + 2 q₀ + 16`, then
`Turing.universalBlockBound c α + 14`). -/
def univCoeff (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
    universalBlockBound c α + 14

/-- If the coded machine computes `out` from `x` within `t` steps, the clocked answer is
`true :: out`. -/
theorem clockedAnswer_eq_cons_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (h : (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = true :: out := by
  obtain ⟨hs, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  have hs' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none := hs
  have ho' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output = out := ho
  unfold clockedAnswer
  rw [if_pos hs', ho']

/-- If the coded machine does not halt on `x` within `t` steps, the clocked answer is the
timeout symbol `[false]`. -/
theorem clockedAnswer_eq_false_of_not_computesInTime (c : EffectiveMachineCode)
    {α x : List Bool} {t : ℕ} (h : ∀ out, ¬ (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = [false] := by
  have hs : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
    intro hs
    exact h _ ((FinTM.computesInTime_iff (c.decode α).toFinTM _ _ _).mpr ⟨hs, rfl⟩)
  unfold clockedAnswer
  rw [if_neg hs]

/-- The clocked answer has at most `t + 1` bits (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem length_clockedAnswer_le (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (clockedAnswer c α x t).length ≤ t + 1 := by
  unfold clockedAnswer
  split_ifs
  · simp only [List.length_cons]
    exact Nat.add_le_add_right ((c.decode α).tm.output_length_le x t) 1
  · simp

/-- **The clocked universal machine** [AB09, §1.4.1; `Turing.timed_universal_concrete`]: one
machine `U` which, on `⟨⟨bits t, α⟩, x⟩`, outputs `clockedAnswer c α x t` within
`univCoeff c α · (t + 1)²` steps, for every code `α`, input `x` and budget `t`.

**Proof sketch.** The simulator of `Turing.timed_universal_concrete c`: success clause with
`clockedAnswer_eq_cons_of_computesInTime`, or timeout clause with
`clockedAnswer_eq_false_of_not_computesInTime`. -/
theorem exists_univ_computes (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (clockedAnswer c α x t)
        (univCoeff c α * (t + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  by_cases h : ∃ out, (c.decode α).toFinTM.ComputesInTime x out t
  · obtain ⟨out, hout⟩ := h
    rw [clockedAnswer_eq_cons_of_computesInTime c hout]
    exact (hU α x t).1 out hout
  · push_neg at h
    rw [clockedAnswer_eq_false_of_not_computesInTime c h]
    exact (hU α x t).2 h

/-! ## Algorithm 64.2: the universal function -/

/-- The code field of `y`: its first `⌊log₂ |y|⌋` bits ("interpret `y` as `⟨M, x⟩` where
`|M| = log |y|`", [PS10, Algorithm 64.2]). -/
def univCode (y : List Bool) : List Bool := y.take (Nat.log 2 y.length)

/-- The argument field of `y`: the bits after the first `⌊log₂ |y|⌋` [PS10, Algorithm 64.2]. -/
def univArg (y : List Bool) : List Bool := y.drop (Nat.log 2 y.length)

/-- The code field has exactly `⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univCode (y : List Bool) : (univCode y).length = Nat.log 2 y.length := by
  simp [univCode, Nat.log_le_self]

/-- The argument field has `|y| - ⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univArg (y : List Bool) : (univArg y).length = y.length - Nat.log 2 y.length := by
  simp [univArg]

/-- The code field of `α ++ x` is `α` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univCode_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univCode (α ++ x) = α := by
  simp only [univCode, List.length_append, ← hα]
  exact List.take_left

/-- The argument field of `α ++ x` is `x` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univArg_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univArg (α ++ x) = x := by
  simp only [univArg, List.length_append, ← hα]
  exact List.drop_left

/-- **`f_universal` as a string function** [PS10, Algorithm 64.2, corrected]: interpret `y` as
`⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, run `M` on `x` for `(|y| + 1)³` steps, and output `⟨M, M(x)⟩`
(`M(x)` prefixed by `true`) if `M` halts, `⟨M, ⊥⟩` (`⊥ = [false]`) otherwise.

**Deviation:** the output carries the code `M` (DESIGN §7, error 1); budget `(|y| + 1)³`
(error 19); machines are decoded by the effective scheme `c`. -/
def fUniversalStr (c : EffectiveMachineCode) (y : List Bool) : List Bool :=
  pairEncode (univCode y) (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))

/-- The output-length polynomial of `f_universal`: `2n + 3 + (n + 1)³`, a bound on
`|⟨M, answer⟩| = 2|M| + 2 + |answer| ≤ 2⌊log₂ n⌋ + 2 + (n + 1)³ + 1`. -/
def univOutLen : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.const 3)) (.pow (.add .var (.const 1)) 3)

/-- `univOutLen` evaluates to `2n + 3 + (n + 1)³`. -/
@[simp] theorem eval_univOutLen (n : ℕ) : univOutLen.eval n = 2 * n + 3 + (n + 1) ^ 3 := rfl

/-- The output of `f_universal` on `y` has at most `univOutLen |y|` bits (so the family
`fUniversal` pads and never truncates). -/
theorem length_fUniversalStr_le (c : EffectiveMachineCode) (y : List Bool) :
    (fUniversalStr c y).length ≤ univOutLen.eval y.length := by
  simp only [fUniversalStr, length_pairEncode, length_univCode, eval_univOutLen]
  have h₁ := length_clockedAnswer_le c (univCode y) (univArg y) ((y.length + 1) ^ 3)
  have h₂ := Nat.log_le_self 2 y.length
  omega

/-- On a well-formed `y = α ++ x` (`|α| = ⌊log₂ |y|⌋`) whose coded machine computes `out`
from `x` within the budget, `f_universal (y) = ⟨α, true :: out⟩`: the evaluation step
"`f_universal (⟨M_g, x⟩) = ⟨M_g, g(x)⟩`" of the proof of [PS10, Theorem 63.1]. -/
theorem fUniversalStr_append_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (hα : α.length = Nat.log 2 (α.length + x.length))
    (h : (c.decode α).toFinTM.ComputesInTime x out t) (ht : t ≤ (α.length + x.length + 1) ^ 3) :
    fUniversalStr c (α ++ x) = pairEncode α (true :: out) := by
  simp only [fUniversalStr, univCode_append hα, univArg_append hα, List.length_append]
  rw [clockedAnswer_eq_cons_of_computesInTime c (h.mono ht)]

/-- **`f_universal` as a function family** [PS10, Algorithm 64.2]: parameter = input length,
output length `univOutLen` (the string output padded with `false`, never truncated by
`length_fUniversalStr_le`). -/
def fUniversal (c : EffectiveMachineCode) : FunFamily :=
  FunFamily.ofString (fUniversalStr c) univOutLen

/-- The padded reading of a string: `List.ofFn (fun i : Fin p => w.getD i false)` is
`(w ++ 0^p).take p` (the encoding of `FunFamily.ofString`'s output). -/
theorem ofFn_getD_eq_take (w : List Bool) (p : ℕ) :
    List.ofFn (fun i : Fin p => w.getD i false) = (w ++ List.replicate p false).take p :=
  ofFn_padFin_eq_take p w

/-- The encoding of `fUniversal c` at parameter `n` is the string output padded with `false`
to `univOutLen n` bits. -/
theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ) (x : Fin n → Bool) :
    List.ofFn ((fUniversal c).f n x) =
      (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take
        (univOutLen.eval n) :=
  ofFn_getD_eq_take _ _

/-! ## The encoding hypothesis and the polynomial coefficient -/

/-- The canonizer of the encoding scheme `c` runs in time at most exponential in the code
length: `canonizerTime k ≤ A · 2^{B k}`. For codes of length `⌊log₂ n⌋` the coefficient
`univCoeff` of the clocked simulation is then polynomial in `n` (`exists_univCoeff_le`), which
is what makes `f_universal` polynomial-time computable.

**Deviation:** [PS10] assumes a standard encoding with an implicit efficient universal
simulation; here the simulation cost of the arbitrary effective scheme `c` is made explicit
through this hypothesis (no bound is known for `Turing.exists_effectiveMachineCode`). -/
def CanonizerExp (c : EffectiveMachineCode) : Prop :=
  ∃ A B : ℕ, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)

/-- **Open problem (run-3 audit P3-4): some effective encoding scheme has a canonizer at most
exponential in the code length.** The standard encodings have polynomial canonizers (parse and
re-serialize), so the hypothesis `CanonizerExp c` of `theorem_63_1` is mathematically harmless
and is accepted as an explicit hypothesis (plan D11, like `Candidates.ArithmeticFP`); but the
only scheme in the library, `Turing.exists_effectiveMachineCode`, carries a `canonizerTime`
defined as a finite maximum of halting times with no bound, so no instance is available and the
headlines of this file are conditional. This statement records the gap.

**Proof sketch.** Build a scheme in the `Build/` style: keep the serialization
`Turing.CodeTM.serialize` and the parser `Turing.codeDecode` of
`TCSlib.Complexity.TuringMachine.MathlibBridge`, and implement the canonizer as an explicit
finite machine performing the parse of the `9 · (numStates + 1)` fixed-format records (with the
up-front minimum-length guard) followed by re-serialization — the superseded composition route
described in `MathlibBridge` — through the combinators of
`TCSlib.Complexity.TuringMachine.Composition` and the primitives of
`TCSlib.Complexity.TuringMachine.Build`; its running time is polynomial in the code length,
in particular `≤ A · 2^{B k}`. -/
theorem exists_canonizerExp : ∃ c : EffectiveMachineCode, CanonizerExp c := by
  sorry

/-- **The coefficient is polynomial on codes of logarithmic length.** If `c` has an
exponential canonizer, there is a syntactic polynomial `p` with
`univCoeff c α ≤ p(n)` for every `n` and every code `α` of length `⌊log₂ n⌋`.

**Proof sketch.** With `A, B` from `CanonizerExp c` and `k = |α| = ⌊log₂ n⌋`:
`canonizerTime k ≤ A · 2^{Bk} = A (2^k)^B ≤ A (n + 1)^B` (`Nat.pow_log_le_self`, `pow_mul`);
`|serialize| ≤ canonizerTime k` (`length_serialize_decode_le`); `numStates + 1 ≤ |serialize|`
(`numStates_add_one_le_length_serialize`), so `|bits numStates| ≤ numStates`
(`Turing.length_bits_le_self`) and `q₀.val ≤ numStates` are below `|serialize|`;
`Turing.universalBlockBound c α = 3|serialize| + 5(numStates + 1) + 20`; and `3k ≤ 3n`
(`Nat.log_le_self`). Collecting, `univCoeff c α ≤ 3n + 14 A (n + 1)^B + 60`. -/
theorem exists_univCoeff_le (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    ∃ p : PolyExpr, ∀ (n : ℕ) (α : List Bool), α.length = Nat.log 2 n →
      univCoeff c α ≤ p.eval n := by
  obtain ⟨A, B, hAB⟩ := hc
  refine ⟨.add (.add (.mul (.const 3) .var)
    (.mul (.const 14) (.mul (.const A) (.pow (.add .var (.const 1)) B)))) (.const 60),
    fun n α hα => ?_⟩
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_pow]
  have h2k : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  have hT : c.canonizerTime α.length ≤ A * (n + 1) ^ B := by
    calc c.canonizerTime α.length ≤ A * 2 ^ (B * α.length) := hAB _
      _ = A * (2 ^ Nat.log 2 n) ^ B := by rw [hα, mul_comm B, pow_mul]
      _ ≤ A * (n + 1) ^ B := Nat.mul_le_mul_left A (Nat.pow_le_pow_left h2k B)
  have hS := length_serialize_decode_le c α
  have hN := numStates_add_one_le_length_serialize (c.decode α)
  have hb := length_bits_le_self (c.decode α).numStates
  have hq := (c.decode α).tm.q₀.isLt
  have hk : α.length ≤ n := hα ▸ Nat.log_le_self 2 n
  simp only [univCoeff, universalBlockBound]
  omega

/-! ## The evaluator machine of `f_universal` -/

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- **The code field is polynomial-time**: the typed cut `polyTimeComputable_pairTakePoly var`
on `⟨(bits |y|).tail, y⟩` keeps the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univCode : PolyTimeComputable univCode := by
  have h := ptc_comp (polyTimeComputable_pairTakePoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univCode, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- **The argument field is polynomial-time**: the typed cut `polyTimeComputable_pairDropPoly var`
on `⟨(bits |y|).tail, y⟩` drops the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univArg : PolyTimeComputable univArg := by
  have h := ptc_comp (polyTimeComputable_pairDropPoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univArg, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- The input `⟨⟨bits ((|y| + 1)³), univCode y⟩, univArg y⟩` of the clocked universal machine
is polynomial-time in `y`. -/
theorem polyTimeComputable_univInput :
    PolyTimeComputable fun y : List Bool =>
      pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y) :=
  (polyTimeComputable_univBudget.pairEncode polyTimeComputable_univCode).pairEncode
    polyTimeComputable_univArg

/-- **The clocked simulation is polynomial-time** for a scheme with an exponential
canonizer: `y ↦ clockedAnswer c (univCode y) (univArg y) ((|y| + 1)³)`.

**Proof sketch.** `Turing.FinTM.exists_comp_on_image` with the machine of
`polyTimeComputable_univInput` (time `C (n + 1)^d`) and the universal machine `U` of
`exists_univ_computes c`, which on the image maps `⟨⟨bits t, univCode y⟩, univArg y⟩` to the
clocked answer within `univCoeff c (univCode y) · (t + 1)² ≤ p(|y|) · ((|y| + 1)³ + 1)²`
(`exists_univCoeff_le` at `n := |y|`, `length_univCode`, `ComputesInTime.mono`); the total
`2 C (n + 1)^d + p(n)((n + 1)³ + 1)² + 2` is a syntactic polynomial, majorised in normal form
by `PolyExpr.eval_le`. -/
theorem polyTimeComputable_clockedAnswer (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable fun y : List Bool =>
      clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3) := by
  obtain ⟨M, C, d, hM⟩ := polyTimeComputable_univInput
  obtain ⟨U, hU⟩ := exists_univ_computes c
  obtain ⟨p, hp⟩ := exists_univCoeff_le c hc
  have hU' : ∀ y : List Bool, U.ComputesInTime
      (pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y))
      (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))
      (p.eval y.length * ((y.length + 1) ^ 3 + 1) ^ 2) := fun y =>
    (hU _ _ _).mono (Nat.mul_le_mul_right _ (hp y.length _ (length_univCode y)))
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M U _ _ (fun n => C * (n + 1) ^ d)
    (fun n => p.eval n * ((n + 1) ^ 3 + 1) ^ 2) hM hU'
  obtain ⟨C', c', hC'⟩ := PolyExpr.eval_le (.add (.add (.mul (.const 2) (.normal C d))
    (.mul p (.pow (.add (.pow (.add .var (.const 1)) 3) (.const 1)) 2))) (.const 2))
  refine ⟨N, C', c', fun y => (hN y).mono ?_⟩
  have h := hC' y.length
  simpa [PolyExpr.eval_normal] using h

/-- **`f_universal` as a string function is polynomial-time** for a scheme with an
exponential canonizer: `⟨univCode y, clockedAnswer …⟩` by `PolyTimeComputable.pairEncode`. -/
theorem polyTimeComputable_fUniversalStr (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable (fUniversalStr c) :=
  polyTimeComputable_univCode.pairEncode (polyTimeComputable_clockedAnswer c hc)

/-- **`f_universal` is easy to compute** [PS10, Algorithm 64.2: "clearly `f_universal` is
computable in time `O(|y|³)`"]: for a scheme with an exponential canonizer, `fUniversal c` is
`Easy`.

**Deviation:** the evaluator is a deterministic polynomial-time machine on `⟨1^n, y⟩` (D3); the
time is `p(n) · ((n+1)³ + 1)²` with the coefficient polynomial `p` of `exists_univCoeff_le`,
not the text's `O(|y|³)` (the simulation overhead of `Turing.timed_universal_concrete` is
quadratic in the budget).

**Proof sketch.** The evaluator on `z = ⟨1^n, y⟩` (`y := pairSndD z`) is built in the FP
calculus of `ClassNP/PolyTimePairing.lean` plus one timed composition: (1) *the split at
`⌊log₂ |y|⌋`:* `Nat.bits |y|` (`Turing.FinTM.computesFunInTime_lengthBits`) has
`⌊log₂ |y|⌋ + 1` bits; its tail (`List.drop 1`, linear) paired with `y` and split by
`Turing.FinTM.computesFunInTime_pairSplitAt` gives `⟨univCode y, univArg y⟩`; (2) *the budget*
`Nat.bits ((|y| + 1)³)` by `Turing.FinTM.computesFunInTime_polyBits 1 3`; (3) *the universal
input* `g y := ⟨⟨bits t, univCode y⟩, univArg y⟩` by `PolyTimeComputable.pairEncode`; (4) *the
simulation:* `Turing.FinTM.exists_comp_on_image` with `M` computing `g` in time `T₁` and `U`
from `exists_univ_computes c` computing `clockedAnswer c (univCode y) (univArg y) t` on the image
within `T₂ |z| := p(|z|) · ((|z| + 1)³ + 1)²`, where `univCoeff c (univCode y) ≤ p(|y|) ≤ p(|z|)`
by `exists_univCoeff_le` (at `n := |y|`, `length_univCode`) and `PolyExpr.eval_mono`; (5) *the
output* `pairEncode (univCode y) answer` by `PolyTimeComputable.pairEncode`, which is
`fUniversalStr c y`; (6) *the padding* `(w ++ 0^{p(n)}).take (p(n))` with
`0^{p(n)} = zipWith xor 1^{p(n)} 1^{p(n)}` (`Complexity.polyTimeComputable_unaryPoly univOutLen`
on `1^n = pairFstD z`, `Complexity.polyTimeComputable_pairXor`), `PolyTimeComputable.append`,
`Complexity.polyTimeComputable_pairTakePoly univOutLen` on `⟨1^n, w ++ 0^{p(n)}⟩`. Correctness
on `advInput n (List.ofFn x)` is `ofFn_fUniversal_f` with `List.length_ofFn`,
`Turing.pairDecode_pairEncode` and `List.length_replicate`. -/
theorem fUniversal_easy (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    (fUniversal c).Easy := by
  have hF : PolyTimeComputable fun z =>
      padStr univOutLen (pairFstD z) (fUniversalStr c (pairSndD z)) := by
    have h := ptc_comp (polyTimeComputable_padStr univOutLen)
      (polyTimeComputable_pairFstD.pairEncode
        (ptc_comp (polyTimeComputable_fUniversalStr c hc) polyTimeComputable_pairSndD))
    convert h using 1
    funext z
    simp
  refine ⟨_, hF, fun n x => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [ofFn_fUniversal_f]
  simp [padStr]

/-! ## Lemma 64.3: a strong one-way function computable in quadratic time -/

/-- `𝓕` is *computable in quadratic time by a coded machine*: some `Turing.CodeTM` (one work
tape, binary alphabet — the machines the universal machine interprets) computes
`f n x` from the bare input `x` within `c₀ (|x| + 1)²` steps. This is "`g'` is computable in
time `O(n²)`" of [PS10, Lemma 64.3], at the level of the coded machines of
[PS10, Algorithm 64.2]. -/
def FunFamily.QuadraticCode (𝓕 : FunFamily) : Prop :=
  ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓕.f n x))
      (c₀ * (𝓕.inLen.eval n + 1) ^ 2)

/-- **Strong one-way functions computable in quadratic time** [PS10, Lemma 64.3]: if there is
a strong one-way function, there is a strong one-way function `g'` with parameter = input
length (`inLen = var`) computable by a coded machine in time `c₀ (n + 1)²` on the bare input.

**Deviation:** the text defines `g'(⟨a, b⟩) = ⟨a, g(b)⟩` on lengths `m = n^c` only and
leaves the recovery of `n` from `m` implicit; the formal `g'` is defined at every length `m`
with the parameter `ν(m) := max {n : P(n) ≤ m}` recovered from the input length, and the
output `a ++ g_{ν m}(b)` is padded with `false` to the syntactic length `2·var` (which it never
exceeds from `P(0)` on; truncated at the finitely many smaller `m`).

Repair (run-3 audit P3-3): the sketch's family is `𝓖 := ⟨var, mul (const 2) var, g'⟩`, not
`⟨var, add var outLen, g'⟩` — padding to `m + outLen(m)` bits is not computable within the
quadratic one-tape budget when `deg outLen ≥ 2`; the raw output has at most `2m` bits. The
"non-constant input length" sub-lemma is unnecessary (`P` is strictly increasing because of its
summand `n`). Statement unchanged.

**Proof sketch.** Let `𝓕` be strong one-way with input length `ℓ := 𝓕.inLen`, evaluator `F`
(`h.easy`) within `C(k + 1)^c`, and `T_F(n) := C(2n + 3 + ℓ(n))^c` its time on `⟨1^n, x⟩`.
*Padding:* `P(n) := ℓ(n) + T_F(n) + n`, strictly increasing (its summand `n`), so
`ν(m) := max {n : P(n) ≤ m}` (`0` below `P(0)`) is well defined, `P(ν m) ≤ m < P(ν m + 1)` for
`m ≥ P(0)`, and `ν` is unbounded; `g'_m(y) := y.take (m - ℓ(ν m)) ++ F ⟨1^{ν m}, y.drop (m - ℓ(ν m))⟩`
padded with `false` to `2m` bits (`𝓖 := ⟨var, mul (const 2) var, g'⟩`): for `m ≥ P(0)` the raw
output has `(m − ℓ(ν m)) + |F ⟨1^{ν m}, b⟩| ≤ m + T_F(ν m) ≤ m + P(ν m) ≤ 2m` bits, an
evaluator's output being no longer than its running time (`PolyTimeComputable.output_length_le`,
as in `Collection.exists_outLenBound`), so the padding is lossless (`ofFn_padFin_of_le`).
*Hardness:* an inverter `A'` of `𝓖` with `1/m^d ≤ invProbAt A' m` infinitely often
(`not_negligible_iff`) gives an inverter of `𝓕` at `n := ν(m)` by `OneWay.invProb_pad_le`
[Gar26, Lemma 2.3] (`OneWay.pad`, `OneWay.padInverter`): sample the padding `a` from the
coins (`NUPPT.exists_split`), call `A'` at the length `m < P(n + 1)` hard-wired as advice
(`NUPPT.exists_reparam_advice` with the majorant `P.subst (add var (const 1))`), project the
`b`-part (`NUPPT.exists_comp`). Two inputs `a ++ b`, `a' ++ b'` of length `m` with equal padded
outputs have equal raw outputs (both raw outputs have length `(m − ℓ(n)) + outLen(n)`, so the
zero-padding to `2m` bits is injective on them, `List.append` of equal-length prefixes), hence
`a' = a` and `f_n(b') = f_n(b)`; `1/m^d ≥ 1/P(n+1)^d` and `not_negligible_iff` contradict
`h.hard`. *Quadratic time:* a multi-tape machine computing `g'` in linear time `O(m)` — the
parameter `1^{ν m}` by incremental unary counting (the powers `(n+1)^j`, `j ≤ deg P`, kept on
`deg P` tapes and updated by the binomial identity, total cost
`∑_{n ≤ ν m} O((n+1)^{deg P - 1}) = O(m)`), then `1^{ℓ(ν m)}`
(`Turing.FinTM.computesFunInTime_polyUnary`, cost `O(P(ν m)) = O(m)`), the split and the copy
(`pairSplitAt`, `pairConcat`), the call of `F` (cost `T_F(ν m) ≤ m`), the padding to `2m` bits
(`O(m)` steps); then `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine
within `c (O(m) + 1)² = O(m²)` and `Turing.exists_codeTM` a `CodeTM` with the same runs.
Sub-obligations: the identification of `g'` with `OneWay.pad`, and the linear-time
parameter-recovery machine (the only new machine; `Turing.FinTM.computesFunInTime_splitSolve`
solves the same length equation in time `(m+1)^{e+2}`, too slow for a quadratic one-tape
bound).

**Fill note (run 4).** Proved in `TCSlib.Cryptography.Asymptotic.UniversalPadding`
(`PadQuad.exists_family`: the padded family `PadQuad.family` with `ν m = max {n : n^d ≤ m}`,
its one-wayness `PadQuad.strongOneWay` and `PadQuad.quadraticCode_of_linear`) **modulo one
machine admission**, `PadQuad.exists_linearTime_gStr`: a *linear-time multitape* evaluator of
the padded function (`one_work_tape_binary` squares the time, so quadratic one-tape time needs
linear multitape time). No assembly of the timed catalogue is output-linear for the parameter
recovery `1^m ↦ 1^{ν m}`: `computesFunInTime_polyUnary C e` costs `(n+1)^{e+1}` for an output of
length `C(n+1)^e`, `computesFunInTime_comp` evaluates the second bound at the *time* of the
first stage (only `exists_comp_on_image` avoids this), `pairMapSnd` charges the whole pair, and
the loop combinators charge rounds × maximal round cost; the missing primitive is a bespoke
linear-time unary root (or an output-linear binary-to-unary converter), see the construction
sketch of `PadQuad.exists_linearTime_gStr`. -/
theorem lemma_64_3 (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode :=
  PadQuad.exists_family h

/-! ## Claims 65.1 and 65.2: the counting steps -/

/-- **`PickG`** [PS10, p. 65, Claim 65.1 of the inventory]: for a uniform `y ∈ {0,1}^n` and any
fixed code `code` of `⌊log₂ n⌋` bits (the description of `M_g` padded to that length), the
first `⌊log₂ n⌋` bits of `y` equal `code` with probability `2^{-⌊log₂ n⌋} ≥ 1/n`.

**Proof sketch.** Split `y` as `(prefix, rest)` by `Fin.appendEquiv` (`uprob_comp_equiv`); the
event is a point event on the first component (`uprob_fst`, `OneWay.uprob_eq_one_div_card`),
of probability `1/2^k`, and `2^k ≤ n` (`Nat.pow_log_le_self`). -/
theorem claim_65_1 (n : ℕ) (hn : n ≠ 0) (code : Fin (Nat.log 2 n) → Bool) :
    1 / (n : ℝ) ≤ uprob fun y : Fin n → Bool =>
      (List.ofFn y).take (Nat.log 2 n) = List.ofFn code := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have hP : (fun z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) =>
      (List.ofFn (e z)).take (Nat.log 2 n) = List.ofFn code) = fun z => z.1 = code := by
    funext z
    have h1 : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
    rw [h1, List.take_left' (List.length_ofFn (f := z.1)), List.ofFn_inj]
  rw [hP, uprob_fst (fun a : Fin (Nat.log 2 n) → Bool => a = code), OneWay.uprob_eq_one_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  have hpos : (0 : ℝ) < ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le hpos h2

/-- **The union bound** [PS10, p. 65, the displayed inequalities]: if `A` inverts with
probability more than `1 - 1/n³` (`Invert`) and the code field is `M_g` with probability at
least `1/n` (`PickG`), then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + (1 - 1/n)`, i.e.
`Pr[Invert ∧ PickG] ≥ 1/n - 1/n³` (which is `≥ 1/n³` for `n ≥ 2`, the text's bound).

**Proof sketch.** `uprob_or_le` on the complements and `uprob_not`. -/
theorem claim_65_2 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Invert PickG : Ω → Prop) (n : ℕ)
    (hI : 1 - 1 / (n : ℝ) ^ 3 < uprob Invert) (hP : 1 / (n : ℝ) ≤ uprob PickG) :
    1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 ≤ uprob fun w => Invert w ∧ PickG w := by
  have h1 : uprob (fun w => ¬ (Invert w ∧ PickG w)) ≤
      uprob (fun w => ¬ Invert w) + uprob (fun w => ¬ PickG w) := by
    calc uprob (fun w => ¬ (Invert w ∧ PickG w))
        = uprob (fun w => ¬ Invert w ∨ ¬ PickG w) := by
          congr 1
          funext w
          exact propext not_and_or
      _ ≤ _ := uprob_or_le _ _
  rw [uprob_not, uprob_not, uprob_not] at h1
  linarith

/-- The probability of an event on the fibre over a fixed first coordinate is at most
`|α|` times its probability on the product: `Pr_b[E(a, b)] ≤ |α| · Pr_{(a', b)}[E]`
(Fubini, `uprob_prod`, one term of the average). -/
theorem uprob_fiber_le_card_mul {α β : Type*} [Fintype α] [Fintype β] (E : α × β → Prop)
    (a : α) : uprob (fun b => E (a, b)) ≤ Fintype.card α * uprob E := by
  haveI : Nonempty α := ⟨a⟩
  rw [uprob_prod, uexp]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard]
  exact Finset.single_le_sum (f := fun a' => uprob fun b => E (a', b))
    (fun a' _ => uprob_nonneg _) (Finset.mem_univ a)

/-- **The conditional form of the union bound** (the form the reduction of
[PS10, Theorem 63.1] uses): if `Invert` has probability at least `1 - 1/n³` on the product
`α × β` with `|α| ≤ n` (the code field, `|α| = 2^{⌊log₂ n⌋}`), then conditioned on the code
field being `a` — i.e. on the fibre — `Invert` has probability at least `1 - 1/n²`.

**Proof sketch.** `uprob_fiber_le_card_mul` for the complement: `Pr_b[¬Invert(a, b)] ≤ |α| ·
Pr[¬Invert] ≤ n · (1/n³) = 1/n²`, then `uprob_not`. -/
theorem claim_65_2_cond {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (Invert : α × β → Prop) (a : α) (n : ℕ) (hn : 0 < n) (hα : Fintype.card α ≤ n)
    (hI : 1 - 1 / (n : ℝ) ^ 3 ≤ uprob Invert) :
    1 - 1 / (n : ℝ) ^ 2 ≤ uprob fun b => Invert (a, b) := by
  haveI : Nonempty α := ⟨a⟩
  have h1 := uprob_fiber_le_card_mul (fun z => ¬ Invert z) a
  rw [uprob_not, uprob_not] at h1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have h2 : (Fintype.card α : ℝ) * (1 - uprob Invert) ≤ n * (1 / (n : ℝ) ^ 3) :=
    mul_le_mul hcard (by linarith) (by linarith [uprob_le_one Invert]) (by positivity)
  have h3 : (n : ℝ) * (1 / (n : ℝ) ^ 3) = 1 / (n : ℝ) ^ 2 := by
    field_simp
  linarith

/-! ## Theorem 63.1: the universal one-way function -/

/-! ### The reduction of Theorem 63.1 -/

/-- **Evaluation on the fibre of the code field** [PS10, Theorem 63.1,
"`f_universal(⟨M_g, x⟩) = ⟨M_g, g(x)⟩`"]: for a code of `⌊log₂ n⌋` bits decoding to the
quadratic machine `M_g` of `g` and an argument `x` of `n − ⌊log₂ n⌋` bits,
`fUniversalStr c (code ++ x) = ⟨code, true :: g(x)⟩`.

**Proof sketch.** `fUniversalStr_append_of_computesInTime` with `|code| + |x| = n`: the code
field is `code` (its length is `⌊log₂ n⌋`), the decoded machine is `M_g` (`hdec`), which
computes `g(x)` within `c₀ (|x| + 1)² ≤ (n + 1)³` (`quadratic_le_cubic`). -/
private theorem fUniversalStr_ofFn_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) :
    fUniversalStr c (List.ofFn y) = pairEncode code (true :: List.ofFn (g _ x)) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hsum : code.length + (List.ofFn x).length = n := by
    rw [hcode, List.length_ofFn]
    omega
  have hα : code.length = Nat.log 2 (code.length + (List.ofFn x).length) := by
    rw [hsum, hcode]
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g _ x))
      (c₀ * ((n - Nat.log 2 n) + 1) ^ 2) := by
    rw [hdec]
    exact hMg _ x
  rw [hy]
  exact fUniversalStr_append_of_computesInTime c hα hM
    (by rw [hsum]; exact quadratic_le_cubic (by omega) hc₀)

/-- The padded encoding of `f_universal (code ++ x)` is the padding evaluator on
`⟨code, true :: g(x)⟩`: the pre-processing of the reduction produces exactly the challenge
`A` expects (`ofFn_fUniversal_f`, `fUniversalStr_ofFn_eq`). -/
private theorem padStr_eq_ofFn_fUniversal_f (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) :
    padStr univOutLen (List.replicate n true) (pairEncode code (true :: List.ofFn (g _ x))) =
      List.ofFn ((fUniversal c).f n y) := by
  rw [ofFn_fUniversal_f, fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y hy, padStr,
    List.length_replicate]

/-- **Inverses on the fibre** [PS10, Theorem 63.1, "`A` outputs `⟨M_g, x'⟩` with
`g(x') = g(x)`"]: if `y'` has the same `f_universal`-value as `y = code ++ x` (code of
`⌊log₂ n⌋` bits decoding to `M_g`), then the argument field of `y'` is some `x'` with
`g(x') = g(x)`.

**Proof sketch.** Both padded outputs are `⟨·, ·⟩ ++ 0^*` with first components of
`⌊log₂ n⌋` bits (`length_univCode`), so `pairEncode_append_eq` gives `univCode y' = code` and
equal padded answers; the answer on `y'` is `clockedAnswer c code x' ((n+1)³) = true :: g(x')`
(`clockedAnswer_eq_cons_of_computesInTime`, budget `quadratic_le_cubic`), and the two
`g`-values have the same length, so they agree (`List.append_inj_left`, `List.ofFn_injective`). -/
private theorem exists_preimage_of_fUniversal_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y y' : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) (h : (fUniversal c).f n y' = (fUniversal c).f n y) :
    ∃ x' : Fin (n - Nat.log 2 n) → Bool, List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  obtain ⟨x', hx'⟩ := exists_ofFn_eq_of_length (m := n - Nat.log 2 n)
    (w := univArg (List.ofFn y')) (by simp)
  refine ⟨x', hx', ?_⟩
  have h1 := congrArg List.ofFn h
  rw [ofFn_fUniversal_f, ofFn_fUniversal_f,
    take_append_replicate_of_le (by simpa using length_fUniversalStr_le c (List.ofFn y')),
    take_append_replicate_of_le (by simpa using length_fUniversalStr_le c (List.ofFn y)),
    fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y hy] at h1
  unfold fUniversalStr at h1
  simp only [List.length_ofFn] at h1
  obtain ⟨hcd, hans⟩ := pairEncode_append_eq (by simp [hcode]) h1
  rw [hcd, ← hx'] at hans
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x') (List.ofFn (g _ x'))
      ((n + 1) ^ 3) := by
    rw [hdec]
    exact (hMg _ x').mono (quadratic_le_cubic (by omega) hc₀)
  rw [clockedAnswer_eq_cons_of_computesInTime c hM, List.cons_append, List.cons_append] at hans
  exact List.ofFn_injective (List.append_inj_left (List.tail_eq_of_cons_eq hans) (by simp))

/-- **The reduction wins on the fibre** [PS10, Theorem 63.1, the displayed bound
`Pr[Invert ∧ PickG]`]: if `A` inverts `f_universal` at parameter `n` with probability more
than `1 − 1/n³`, and `B` at parameter `m = n − ⌊log₂ n⌋` runs `A` on the padded
`⟨code, true :: y⟩` and returns the argument field of its answer, then `B` inverts `g` at `m`
with probability at least `1 − 1/n²`.

**Proof sketch.** Split `{0,1}^n ≃ {0,1}^{⌊log₂ n⌋} × {0,1}^m` (`Fin.appendEquiv`); the
inversion event of `A` on the product has probability `invProbAt A n`
(`invProbAt_eq_uprob`, `uprob_comp_equiv`), so `claim_65_2_cond` with
`2^{⌊log₂ n⌋} ≤ n` (`OneWay.card_log_bits_le`) gives probability `≥ 1 − 1/n²` on the fibre of
the code. On that fibre `B`'s challenge is `A`'s (`padStr_eq_ofFn_fUniversal_f`), `B`'s coins
are `A`'s followed by unread coins (`uprob_comp_equiv`, `uprob_fst`), and `A`'s success gives
`B`'s by `exists_preimage_of_fUniversal_eq` (`uprob_mono`). -/
private theorem invProbAt_reduction_ge (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    (A B : NUPPT) {n : ℕ} (hn : 2 ≤ n) {code : List Bool} (hcode : code.length = Nat.log 2 n)
    (hdec : c.decode code = Mg) (hc₀ : c₀ ≤ n + 1)
    (hBc : A.coinLen n ≤ B.coinLen (n - Nat.log 2 n))
    (hB : ∀ y (r : List Bool), B.runAtL (n - Nat.log 2 n) y r =
      univArg (A.runAtL n (padStr univOutLen (List.replicate n true) (pairEncode code (true :: y)))
        (r.take (A.coinLen n))))
    (hA : 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n) :
    1 - 1 / (n : ℝ) ^ 2 ≤ (⟨.var, L, g⟩ : FunFamily).invProbAt B (n - Nat.log 2 n) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  have hofn : ∀ z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool),
      List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
    intro z
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
  obtain ⟨cf, hcf⟩ := exists_ofFn_eq_of_length (m := Nat.log 2 n) hcode
  let Invert : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) → Prop :=
    fun w => ∃ y', A.runAt n (List.ofFn ((fUniversal c).f n (e (w.1, w.2.1)))) w.2.2 = List.ofFn y' ∧
      (fUniversal c).f n y' = (fUniversal c).f n (e (w.1, w.2.1))
  have hInv : uprob Invert = (fUniversal c).invProbAt A n := by
    rw [FunFamily.invProbAt_eq_uprob]
    let e' : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ≃
        (Fin ((fUniversal c).inLen.eval n) → Bool) × A.Coins n :=
      (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr e (Equiv.refl _))
    rw [← uprob_comp_equiv e']
    exact OneWay.uprob_congr fun w => Iff.rfl
  have hfib := claim_65_2_cond Invert cf n (by omega) (OneWay.card_log_bits_le (by omega))
    (by rw [hInv]; exact hA.le)
  rw [FunFamily.invProbAt_eq_uprob]
  have hlen : B.coinLen (n - Nat.log 2 n) =
      A.coinLen n + (B.coinLen (n - Nat.log 2 n) - A.coinLen n) := by omega
  let e₂ : ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ×
      (Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool) ≃
      (Fin (n - Nat.log 2 n) → Bool) × B.Coins (n - Nat.log 2 n) :=
    (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))))
  rw [← uprob_comp_equiv e₂]
  refine hfib.trans ?_
  rw [← uprob_fst (β := Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool)
    (fun b : (Fin (n - Nat.log 2 n) → Bool) × A.Coins n => Invert (cf, b))]
  refine uprob_mono fun w hw => ?_
  obtain ⟨y', hy', hfy'⟩ := hw
  have hcoins : List.ofFn (e₂ w).2 = List.ofFn w.1.2 ++ List.ofFn w.2 := by
    show List.ofFn ((Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))
      (Fin.appendEquiv _ _ (w.1.2, w.2))) = _
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm (Fin.append w.1.2 w.2)).symm
  have hy : List.ofFn (e (cf, w.1.1)) = code ++ List.ofFn w.1.1 := by rw [hofn, hcf]
  show ∃ x', B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 = List.ofFn x' ∧
    g _ x' = g _ w.1.1
  have hBrun : B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 =
      univArg (List.ofFn y') := by
    rw [NUPPT.runAt_eq, hB, hcoins, List.take_left' (List.length_ofFn (f := w.1.2)), ← NUPPT.runAt_eq,
      padStr_eq_ofFn_fUniversal_f c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) hy, hy']
  obtain ⟨x', hx', hgx'⟩ :=
    exists_preimage_of_fUniversal_eq c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) y' hy hfy'
  exact ⟨x', by rw [hBrun, hx'], hgx'⟩

/-- **`f_universal` is hard to invert with `q(n) = n³`** [PS10, Theorem 63.1, proof of weak
one-wayness]: for a scheme `c` with an exponential canonizer, if some strong one-way function
`𝓖` with `inLen = var` is computable in quadratic time by a coded machine (the output of
`lemma_64_3`), every non-uniform PPT inverts `fUniversal c` with probability at most
`1 - 1/n³` for all large `n`.

**Deviation:** the hypothesis is the conclusion of Lemma 64.3 (`theorem_63_1` composes the
two); `q(n) = n³` is literal; `Invert` is `invProbAt_eq_uprob`'s event with the inverse
decoded as an `n`-bit string (D5).

**Proof sketch.** Let `M_g, c₀` be the coded machine of `hG.2.2`, `α₀ := c.encode M_g`, and
suppose `A` inverts with probability `> 1 - 1/n³` for infinitely many `n`. Fix such an
`n ≥ max c₀ 2^{|α₀|+1}`, `k := ⌊log₂ n⌋ ≥ |α₀|`, `m := n - k`, `code := α₀ ++ 1^{k - |α₀|}`
(`c.decode code = M_g` by `Turing.MachineCode.decode_encode_pad`). *Evaluation on `PickG`:*
for `y = code ++ x`, `|x| = m`, `fUniversalStr_append_of_computesInTime` with `hG.2.2` at `m`
and `c₀ (m + 1)² ≤ (n + 1)³` gives `fUniversalStr c y = pairEncode code (true :: ofFn (g m x))`,
`ofFn_fUniversal_f` the padded encoding. *Conditioning:* split `{0,1}^n ≃ {0,1}^k × {0,1}^m`
(`Fin.appendEquiv`, `uprob_comp_equiv`, as in `claim_65_1`); `claim_65_2_cond` with
`2^k ≤ n` (`OneWay.card_log_bits_le`) gives `Pr_{x, r}[Invert(code ++ x, r)] ≥ 1 - 1/n²`.
*Inverses on the fibre:* an answer `y' = code' ++ x'` with equal padded outputs has
`code' = code` (the first `2k + 2` bits are the doubled code and the separator,
`Turing.pairEncode`, `List.take` of `ofFn_fUniversal_f`), then
`ofFn (g m x') = ofFn (g m x)` (equal lengths `1 + outLen m`), so `g m x' = g m x`
(`List.ofFn_injective`). *The reduction `B`* for `𝓖` at parameter `m`: advice `⟨1^n, code⟩`
with `n ≤ 2(m + 1)` (`2⌊log₂ n⌋ ≤ n + 2`), by `NUPPT.exists_reparam_advice A φ
(mul (const 2) (add var (const 1)))` with `φ m := n` on the infinitely many `m = n - ⌊log₂ n⌋`
with `n` good (`0` elsewhere; fibres of `n ↦ n - ⌊log₂ n⌋` have at most two elements),
composed (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`) with the pre-processing
`z ↦ (pairEncode code (true :: z) ++ 0^{univOutLen n}).take (univOutLen n)` and the
post-processing `univArg` (the split of `fUniversal_easy` (1)); extra coins unread
(`List.take`, `uprob_fst` on `Fin.appendEquiv`). *Functional identity:*
`B.inverter m _ _ (g m x) r = some x'` iff `A.runAt n (ofFn ((fUniversal c).f n (code ++ x))) r'
= ofFn (code ++ x')` (`NUPPT.inverter_eq_some_iff`, `decodeFin_ofFn`, `univArg_append`), so
`𝓖.invProbAt B m ≥ 1 - 1/n² ≥ 1/2` (`invProbAt_eq_uprob`, `uprob_mono`). *Conclusion:* for
infinitely many `m` (unbounded, `m ≥ n/2`), so `fun m => 𝓖.invProbAt B m` is not negligible
(`not_negligible_iff` with `c = 1`), contradicting `hG.2.1.hard B`. -/
theorem fUniversal_hard (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) (A : NUPPT) :
    ∃ n₀, ∀ n ≥ n₀, (fUniversal c).invProbAt A n ≤ 1 - 1 / (n : ℝ) ^ 3 := by
  classical
  obtain ⟨⟨ℓ, L, g⟩, hℓ, hsow, Mg, c₀, hMg⟩ := hG
  dsimp only at hℓ
  subst hℓ
  by_contra hcon
  push_neg at hcon
  -- the good parameters, the code of `M_g` padded to `⌊log₂ n⌋` bits, the parameter change
  set α₀ := c.encode Mg with hα₀
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ α₀.length = K := ⟨_, rfl⟩
  set N₀ := K + c₀ + 4 with hN₀
  let good : ℕ → Prop := fun n => N₀ ≤ n ∧ 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n
  let φ : ℕ → ℕ := fun m => if h : ∃ n, good n ∧ n - Nat.log 2 n = m then h.choose else 0
  have hφ : ∀ m, φ m ≤ (PolyExpr.mul (.const 2) .var).eval m := by
    intro m
    simp only [φ, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    split_ifs with h
    · have h1 := h.choose_spec.2
      have h2 := two_mul_log_two_le h.choose
      omega
    · exact Nat.zero_le _
  have hφ_spec : ∀ m, (∃ n, good n ∧ n - Nat.log 2 n = m) →
      good (φ m) ∧ φ m - Nat.log 2 (φ m) = m := by
    intro m h
    simp only [φ, dif_pos h]
    exact h.choose_spec
  let code : ℕ → List Bool := fun n => α₀ ++ List.replicate (Nat.log 2 n - α₀.length) true
  have hcode_len : ∀ n, N₀ ≤ n → (code n).length = Nat.log 2 n := by
    intro n hn
    have : α₀.length ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by rw [hK]; omega)
    simp only [code, List.length_append, List.length_replicate]
    omega
  have hcode_dec : ∀ n, c.decode (code n) = Mg := fun n => c.decode_encode_pad Mg _
  have hcode_le : ∀ n, (code n).length ≤ α₀.length + n := by
    intro n
    have := Nat.log_le_self 2 n
    simp only [code, List.length_append, List.length_replicate]
    omega
  -- the reduction `B`
  let β : ℕ → List Bool := fun m => pairEncode (List.replicate (φ m) true) (code (φ m))
  have hβ : ∀ m, (β m).length ≤
      (PolyExpr.add (.add (.mul (.const 6) .var) (.const 2)) (.const α₀.length)).eval m := by
    intro m
    have h1 := hφ m
    have h2 := hcode_le (φ m)
    simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var] at h1
    simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hpre : PolyTimeComputable fun w => padStr univOutLen (pairFstD (pairFstD w))
      (pairEncode (pairSndD (pairFstD w)) (true :: pairSndD w)) := by
    have h := ptc_comp (polyTimeComputable_padStr univOutLen)
      ((ptc_comp polyTimeComputable_pairFstD polyTimeComputable_pairFstD).pairEncode
        ((ptc_comp polyTimeComputable_pairSndD polyTimeComputable_pairFstD).pairEncode
          (ptc_comp (StateLoop.cons_poly true) polyTimeComputable_pairSndD)))
    convert h using 1
    funext w
    simp
  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_pre_post φ _ hφ β _ hβ hpre polyTimeComputable_univArg
  have hB' : ∀ m y r, B.runAtL m y r = univArg (A.runAtL (φ m)
      (padStr univOutLen (List.replicate (φ m) true) (pairEncode (code (φ m)) (true :: y)))
      (r.take (A.coinLen (φ m)))) := by
    intro m y r
    rw [hB]
    simp [β]
  -- `B` inverts `g` with probability `≥ 1/2` infinitely often, contradicting its one-wayness
  refine (not_negligible_iff.mpr ⟨1, fun m₀ => ?_⟩) (hsow.hard B)
  obtain ⟨n, hn, hgood⟩ := hcon (max (2 * m₀) N₀)
  have hNn : N₀ ≤ n := le_of_max_le_right hn
  have hmn : 2 * m₀ ≤ n := le_of_max_le_left hn
  have hgoodn : good n := ⟨hNn, hgood⟩
  obtain ⟨hgood', hφm⟩ := hφ_spec (n - Nat.log 2 n) ⟨n, hgoodn, rfl⟩
  have hlog := two_mul_log_two_le n
  have hm₀ : m₀ ≤ n - Nat.log 2 n := by omega
  refine ⟨n - Nat.log 2 n, hm₀, ?_⟩
  have hn'N : N₀ ≤ φ (n - Nat.log 2 n) := hgood'.1
  have hcoins : A.coinLen (φ (n - Nat.log 2 n)) ≤
      B.coinLen (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) := by
    rw [hφm]
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
    exact A.coins.eval_mono (hφ _)
  have hrun : ∀ y (r : List Bool),
      B.runAtL (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) y r =
      univArg (A.runAtL (φ (n - Nat.log 2 n)) (padStr univOutLen
        (List.replicate (φ (n - Nat.log 2 n)) true)
        (pairEncode (code (φ (n - Nat.log 2 n))) (true :: y)))
        (r.take (A.coinLen (φ (n - Nat.log 2 n))))) := by
    intro y r
    rw [hφm]
    exact hB' _ y r
  have hkey := invProbAt_reduction_ge c g Mg c₀ hMg A B (n := φ (n - Nat.log 2 n)) (by omega)
    (hcode_len _ hn'N) (hcode_dec _) (by omega) hcoins hrun hgood'.2
  rw [hφm] at hkey
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  refine le_trans ?_ hkey
  have hm2 : (2 : ℝ) ≤ ((n - Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - Nat.log 2 n by omega)
  have hn2 : (2 : ℝ) ≤ ((φ (n - Nat.log 2 n) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ φ (n - Nat.log 2 n) by omega)
  have h1 : 1 / ((n - Nat.log 2 n : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2
  have h2 : 1 / ((φ (n - Nat.log 2 n) : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  simp only [pow_one]
  linarith

/-- **`f_universal` is weakly one-way** [PS10, Theorem 63.1, "we claim that this function is
weakly one-way"] with the polynomial `q(n) = (n + 1)³`, for a scheme with an exponential
canonizer, given a quadratic-time strong one-way function (`lemma_64_3`).

**Deviation:** `WeakOneWay` requires `0 < q(n)` at every `n`, so the text's `q(n) = n³` is
replaced by `(n + 1)³ ≥ n³` (the bound `1 - 1/n³ ≤ 1 - 1/(n+1)³` of `fUniversal_hard` is the
stronger one).

**Proof sketch.** `fUniversal_easy` and `fUniversal_hard`; `1/(n+1)³ ≤ 1/n³` for `n ≥ 1`
(`one_div_le_one_div_of_le`), and at `n = 0` the bound `1 - 1/1 = 0` is only needed for
`n ≥ max n₀ 1`. -/
theorem fUniversal_weakOneWay (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) :
    (fUniversal c).WeakOneWay := by
  refine ⟨fUniversal_easy c hc, PolyExpr.normal 1 3, fun n => by simp [PolyExpr.eval_normal],
    fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := fUniversal_hard c hc hG A
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / ((n : ℝ) + 1) ^ 3 ≤ 1 / (n : ℝ) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  simp only [PolyExpr.eval_normal, Nat.cast_one, Nat.cast_pow, Nat.cast_add, one_mul]
  linarith

/-- **The universal one-way function** [PS10, Theorem 63.1]: if there exists a (strong)
one-way function, then `f_universal` (for a scheme with an exponential canonizer) is weakly
one-way, and its direct product `(fUniversal c).prod q` is strongly one-way for some
polynomial `q` (hardness amplification, [PS10, Theorem 35.1], `weak_to_strong`).

**Deviation:** the output of `f_universal` carries the machine description (DESIGN §7,
error 1); "hardness amplification from §2.3" of the text is §2.4 (error 19); the scheme
hypothesis `CanonizerExp c`; the strong one-way function is the amplified product.

**Proof sketch.** `lemma_64_3`, `fUniversal_weakOneWay`, `weak_to_strong`. -/
theorem theorem_63_1 (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    (fUniversal c).WeakOneWay ∧ ∃ q : PolyExpr, FunFamily.StrongOneWay ((fUniversal c).prod q) :=
  have hw := fUniversal_weakOneWay c hc (lemma_64_3 h)
  ⟨hw, weak_to_strong hw⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/UniversalLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Infrastructure for the hardness of the universal one-way function

Generic lemmas used by the proof of [PS10, Theorem 63.1] in
`TCSlib.Cryptography.Asymptotic.Universal` (`fUniversal_hard`): the closure lemma
`Complexity.NUPPT.exists_reparam_pre_post` (a parameter change `m ↦ φ m` together with an
advice-dependent polynomial-time pre-processing and a polynomial-time post-processing — the
shape of the reduction "`B(1^m, y)` runs `A(1^n, ⟨M_g, y⟩ padded)` and strips the code field"),
the arithmetic fact `2 ⌊log₂ n⌋ ≤ n` behind the majorant `n ≤ 2(n − ⌊log₂ n⌋)` of the
reparametrisation, and two list facts: zero-padded pairs with first components of equal length
agree on their first components (the step "an answer `⟨M', x'⟩` with equal padded output has
`M' = M_g`"), and a string of length `m` is the encoding of some `m`-bit string.

## Main definitions

None: this file is proof infrastructure for `TCSlib.Cryptography.Asymptotic.Universal`.

## Main results

* `Complexity.NUPPT.exists_reparam_pre_post`, `Complexity.NUPPT.exists_reparam_pre_post_adv` —
  reparametrisation with pre- and post-processing (the latter with the advice visible to the
  post-processing).
* `TCSlib.Cryptography.length_tail_bits`, `TCSlib.Cryptography.polyTimeComputable_logMarker`,
  `TCSlib.Cryptography.polyTimeComputable_univBudget` — the split marker `(bits |y|).tail` of
  `⌊log₂ |y|⌋` bits and the binary budget `bits ((|y| + 1)³)` are polynomial-time.
* `TCSlib.Cryptography.length_serialize_decode_le`,
  `TCSlib.Cryptography.numStates_add_one_le_length_serialize` (with `length_signBits`,
  `two_le_length_actionBits`, `length_le_length_flatMap`) — the serialization of a decoded
  code is bounded by the canonizer's time and bounds the number of states (used by
  `exists_univCoeff_le`).
* `TCSlib.Cryptography.two_mul_log_two_le` — `2 ⌊log₂ n⌋ ≤ n`;
  `TCSlib.Cryptography.quadratic_le_cubic` — `c₀ (m + 1)² ≤ (n + 1)³` for `m ≤ n`, `c₀ ≤ n + 1`.
* `TCSlib.Cryptography.pairEncode_append_eq` — zero-padded pairs with equal-length first
  components agree on the first component and on the padded second components.
* `TCSlib.Cryptography.exists_ofFn_eq_of_length`, `TCSlib.Cryptography.take_append_replicate_of_le`
  — encoding and padding facts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13, Theorem 63.1.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-! ## The closure lemma -/

/-- **Parameter change with advice-dependent pre-processing and post-processing**
[PS10, §2.1, implicit; the reduction of Theorem 63.1]: for an `NUPPT` `A`, a map `φ : ℕ → ℕ`
majorised by the syntactic polynomial `p`, an advice family `β m` of length `≤ b m`, and
polynomial-time `pre`, `post`, there is an `NUPPT` `B` with coins `A.coins.subst p` such that
`B(1^m, y; r) = post (A(1^{φ m}, pre ⟨β m, y⟩; r.take (A.coins (φ m))))` — extra coins are unread.

**Proof sketch.** Advice `⟨⟨1^{φ m}, A.advice (φ m)⟩, β m⟩`, of length
`≤ 4 p(m) + 6 + 2 A.adv(p(m)) + b(m)` (`length_pairEncode`, `hφ`, `advice_length`,
`PolyExpr.eval_mono`). The raw function reads `w := 1^{φ m}`, `α := A.advice (φ m)` and `β m`
from the advice slot, pairs `β m` with the argument slot and applies `pre`, cuts the coins to
`A.coins.eval |w|` bits (`polyTimeComputable_pairTakePoly A.coins` on `⟨w, inCoins z⟩`), runs
`A.output` on `layout w (pre ⟨β m, y⟩) α coins'` and applies `post`; the equation is
`NUPPT.runAtL_ofPolyTime` plus the projection identities of the layout. -/
theorem _root_.Complexity.NUPPT.exists_reparam_pre_post (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ ∀ m y r, B.runAtL m y r =
      post (A.runAtL (φ m) (pre (pairEncode (β m) y)) (r.take (A.coinLen (φ m)))) := by
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairFstD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hαA : PolyTimeComputable fun z => pairSndD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairSndD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hβm : PolyTimeComputable fun z => pairSndD (NUPPT.inAdvice z) :=
    ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice
  have hF := ptc_comp hpost (ptc_comp A.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout hw
      (ptc_comp hpre (hβm.pairEncode NUPPT.polyTimeComputable_inArg)) hαA
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins)
        (hw.pairEncode NUPPT.polyTimeComputable_inCoins))))
  have hadv : ∀ m, (pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m)))
      (β m)).length ≤
      (PolyExpr.add (.add (.add (.mul (.const 4) p) (.const 6)) (.mul (.const 2) (A.adv.subst p)))
        b).eval m := by
    intro m
    simp only [length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ m
    have h₂ := A.advice_length (φ m)
    have h₃ := A.adv.eval_mono (hφ m)
    have h₄ := hβ m
    omega
  refine ⟨NUPPT.ofPolyTime hF (A.coins.subst p) _
    (fun m => pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m))) (β m)) hadv,
    rfl, fun m y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins]

/-- **Parameter change with advice-dependent pre- and post-processing**: as
`exists_reparam_pre_post`, but the post-processing also reads the advice: `B(1^m, y; r) =
post ⟨β m, A(1^{φ m}, pre ⟨β m, y⟩; r.take (A.coins (φ m)))⟩` (the reduction of
[PS10, Lemma 64.3] cuts `A`'s answer to a length stored in the advice).

**Proof sketch.** As `exists_reparam_pre_post`, with the raw function
`post ⟨β m, A.output (layout w (pre ⟨β m, y⟩) α coins')⟩`. -/
theorem _root_.Complexity.NUPPT.exists_reparam_pre_post_adv (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ ∀ m y r, B.runAtL m y r =
      post (pairEncode (β m)
        (A.runAtL (φ m) (pre (pairEncode (β m) y)) (r.take (A.coinLen (φ m))))) := by
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairFstD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hαA : PolyTimeComputable fun z => pairSndD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairSndD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hβm : PolyTimeComputable fun z => pairSndD (NUPPT.inAdvice z) :=
    ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice
  have hF := ptc_comp hpost (hβm.pairEncode (ptc_comp A.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout hw
      (ptc_comp hpre (hβm.pairEncode NUPPT.polyTimeComputable_inArg)) hαA
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins)
        (hw.pairEncode NUPPT.polyTimeComputable_inCoins)))))
  have hadv : ∀ m, (pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m)))
      (β m)).length ≤
      (PolyExpr.add (.add (.add (.mul (.const 4) p) (.const 6)) (.mul (.const 2) (A.adv.subst p)))
        b).eval m := by
    intro m
    simp only [length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ m
    have h₂ := A.advice_length (φ m)
    have h₃ := A.adv.eval_mono (hφ m)
    have h₄ := hβ m
    omega
  refine ⟨NUPPT.ofPolyTime hF (A.coins.subst p) _
    (fun m => pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m))) (β m)) hadv,
    rfl, fun m y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins]

/-! ## The split marker and the budget of Algorithm 64.2 -/

/-- The tail of the binary representation of `m` has `⌊log₂ m⌋` bits: `Nat.bits 0 = []`
and `Nat.size m = ⌊log₂ m⌋ + 1` for `m ≥ 1` (`Nat.lt_size`, `Nat.size_le`). -/
theorem length_tail_bits (m : ℕ) : (Nat.bits m).tail.length = Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [List.length_tail, Nat.size_eq_bits_len]
    have h1 : Nat.log 2 m < Nat.size m := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hm.ne')
    have h2 : Nat.size m ≤ Nat.log 2 m + 1 :=
      Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) m)
    omega

/-- The marker `(bits |y|).tail`, a string of `⌊log₂ |y|⌋` bits, is polynomial-time in `y`
(`Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.StateLoop.tail_poly`). -/
theorem polyTimeComputable_logMarker :
    PolyTimeComputable fun y : List Bool => (Nat.bits y.length).tail :=
  StateLoop.tail_poly.comp (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits)

/-- The binary budget `bits ((|y| + 1)³)` of [PS10, Algorithm 64.2] is polynomial-time
(`Turing.FinTM.computesFunInTime_polyBits 1 3`). -/
theorem polyTimeComputable_univBudget :
    PolyTimeComputable fun y : List Bool => Nat.bits ((y.length + 1) ^ 3) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyBits 1 3
  refine ⟨M, a, 4, fun y => ?_⟩
  simpa using hM y

/-! ## Serialization lengths of coded machines -/

/-- The serialization of a decoded code is no longer than the canonizer's running time on the
code (output length is at most the number of steps). -/
theorem length_serialize_decode_le (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have h := c.canonizer_computes α
  obtain ⟨-, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  have ho' : (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) (c.canonizerTime α.length)).output =
      (c.decode α).serialize := ho
  rw [← ho']
  exact c.canonizer.tm.output_length_le α _

/-- The sign serialization has two bits. -/
theorem length_signBits (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl

/-- The serialization of a transition record has at least two bits (its sign field). -/
theorem two_le_length_actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    2 ≤ (actionBits a).length := by
  simp only [actionBits, List.length_append, length_signBits]
  omega

/-- A `flatMap` whose pieces are all nonempty is at least as long as the index list. -/
theorem length_le_length_flatMap {α : Type*} (l : List α) (f : α → List Bool)
    (hf : ∀ a, 1 ≤ (f a).length) : l.length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  refine le_trans (by simp) (List.length_le_sum_of_one_le _ fun x hx => ?_)
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact hf a

/-- The serialization of a coded machine lists one nonempty transition block per state, so it
has at least `numStates + 1` bits (`Turing.CodeTM.serialize`). -/
theorem numStates_add_one_le_length_serialize (M : CodeTM) :
    M.numStates + 1 ≤ M.serialize.length := by
  have h1 : ∀ q : Fin (M.numStates + 1), 1 ≤
      (([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (M.tm.tr q inp fun _ => w)).length := by
    intro q
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
    have := two_le_length_actionBits (M.tm.tr q none fun _ => none)
    omega
  have h2 := length_le_length_flatMap (List.finRange (M.numStates + 1)) _ h1
  rw [List.length_finRange] at h2
  rw [CodeTM.serialize, length_pairEncode, List.length_append]
  omega

/-! ## Arithmetic and list facts -/

/-- The budget of `f_universal` covers a quadratic machine on the argument field:
`c₀ (m + 1)² ≤ (n + 1)³` for `m ≤ n` and `c₀ ≤ n + 1`. -/
theorem quadratic_le_cubic {c₀ m n : ℕ} (hm : m ≤ n) (hc : c₀ ≤ n + 1) :
    c₀ * (m + 1) ^ 2 ≤ (n + 1) ^ 3 := by
  calc c₀ * (m + 1) ^ 2 ≤ (n + 1) * (n + 1) ^ 2 :=
        Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) 2)
    _ = (n + 1) ^ 3 := by ring

/-- `2k ≤ 2^k` for every `k`. -/
theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]
      omega

/-- `2 ⌊log₂ n⌋ ≤ n`: with `k = ⌊log₂ n⌋`, `2k ≤ 2^k ≤ n` for `n ≥ 1`
(`Nat.pow_log_le_self`), and `⌊log₂ 0⌋ = 0`. Hence `n ≤ 2 (n − ⌊log₂ n⌋)`, the polynomial
majorant of the parameter change `n − ⌊log₂ n⌋ ↦ n` of [PS10, Theorem 63.1]. -/
theorem two_mul_log_two_le (n : ℕ) : 2 * Nat.log 2 n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_mul_le_two_pow _).trans (Nat.pow_log_le_self 2 hn.ne')

/-- A string of length `m` is the encoding of some `m`-bit string. -/
theorem exists_ofFn_eq_of_length {m : ℕ} {w : List Bool} (h : w.length = m) :
    ∃ x : Fin m → Bool, List.ofFn x = w :=
  ⟨fun i => w.get (Fin.cast h.symm i), List.ext_get (by simp [h]) fun i h₁ h₂ => by simp⟩

/-- Taking `p` bits of `w ++ 0^p` for `|w| ≤ p` appends `p − |w|` zeros to `w`. -/
theorem take_append_replicate_of_le {p : ℕ} {w : List Bool} (hw : w.length ≤ p) :
    (w ++ List.replicate p false).take p = w ++ List.replicate (p - w.length) false := by
  rw [List.take_append, List.take_of_length_le hw, List.take_replicate]
  congr 2
  omega

/-- **Zero-padded pairs with first components of equal length agree on the first component**
and on the padded second components: `⟨a, b⟩ ++ z = ⟨a', b'⟩ ++ z'` with `|a| = |a'|` forces
`a = a'` and `b ++ z = b' ++ z'` (the first `2|a| + 2` bits are the doubled first component
and the separator, `Turing.pairEncode_eq_dbl`; `pairEncode_injective` on `⟨a, []⟩`). -/
theorem pairEncode_append_eq {a a' b b' z z' : List Bool} (ha : a.length = a'.length)
    (h : pairEncode a b ++ z = pairEncode a' b' ++ z') : a = a' ∧ b ++ z = b' ++ z' := by
  rw [pairEncode_eq_dbl, pairEncode_eq_dbl, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc] at h
  have hlen : (dbl a).length = (dbl a').length := by simp [ha]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  refine ⟨?_, List.append_cancel_left h2⟩
  have h3 : pairEncode a [] = pairEncode a' [] := by
    rw [pairEncode_eq_dbl, pairEncode_eq_dbl, h1]
  exact congrArg Prod.fst (@pairEncode_injective (a, []) (a', []) h3)

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import Mathlib.Data.Nat.Find

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The padded strong one-way function of Lemma 64.3

Proof infrastructure for [PS10, Lemma 64.3] (`TCSlib.Cryptography.lemma_64_3`): from a strong
one-way family `𝓕` with evaluator `F`, the padded family `PadQuad.family F ℓ d` with
`inLen = var`, `outLen = 2·var` and

`g'_m(y) = (y.drop ℓ(ν m) ++ F ⟨1^{ν m}, y.take ℓ(ν m)⟩) ++ 0^*` (`2m` bits),

where `ν m = max {n ≤ m : n^d ≤ m}` (`PadQuad.nu`) recovers the parameter from the input
length. For `d` dominating `ℓ`, `𝓕.outLen` and the running time of `F` (`exists_pow_dominates`),
the data block and the `F`-call fit in the input (`ℓ(ν m) + L(ν m) ≤ (ν m)^d ≤ m`), so the
padding is lossless and `g'` inherits one-wayness (`PadQuad.strongOneWay`, the reduction
`B(1^n, f(b)) = A'(1^m, ⟨a, f(b)⟩ padded).take ℓ(n)` with the padding sampled from the coins,
[Gar26, Lemma 2.3]); a linear-time multitape evaluator (`PadQuad.exists_linearTime_gStr`, the
only new machine, **admitted**) gives a quadratic-time one-work-tape binary machine through
`Turing.FinTM.one_work_tape_binary` and `Turing.exists_codeTM` (`PadQuad.quadraticCode_of_linear`).

**Deviation:** the text defines `g'` on lengths `m = n^c` only; here every length `m` is
handled through `ν` (data first, padding after, zero-filled to `2m` bits), see the docstring of
`TCSlib.Cryptography.lemma_64_3`.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` — the parameter recovered from the input length;
  `TCSlib.Cryptography.PadQuad.raw`, `PadQuad.gStr`, `PadQuad.family` — the padded function.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_pow_dominates` — `p(n) ≤ n^d` eventually.
* `TCSlib.Cryptography.PadQuad.easy_of_linear`, `PadQuad.quadraticCode_of_linear` — the two
  computability clauses from the linear-time evaluator.
* `TCSlib.Cryptography.PadQuad.exists_linearTime_gStr` — the linear-time evaluator (admitted).
* `TCSlib.Cryptography.PadQuad.strongOneWay`, `TCSlib.Cryptography.PadQuad.exists_family` —
  one-wayness of the padded family and the statement of [PS10, Lemma 64.3] with
  `QuadraticCode` unfolded.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding).
-/

namespace TCSlib.Cryptography.PadQuad

open Complexity Turing TCSlib.Cryptography

/-! ## Polynomial domination and the parameter recovery -/

/-- Every syntactic polynomial is eventually dominated by a power: `p(n) ≤ n^d` for
`n ≥ n₁`, with `d ≥ 1` (`d := c + 1` and `n₁ := C 2^c + 1` for the majorant `C (n + 1)^c`). -/
theorem exists_pow_dominates (p : PolyExpr) : ∃ d n₁ : ℕ, 1 ≤ d ∧ ∀ n ≥ n₁, p.eval n ≤ n ^ d := by
  obtain ⟨C, c, h⟩ := p.eval_le
  refine ⟨c + 1, C * 2 ^ c + 1, by omega, fun n hn => ?_⟩
  calc p.eval n ≤ C * (n + 1) ^ c := h n
    _ ≤ C * (2 * n) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
    _ = (C * 2 ^ c) * n ^ c := by rw [mul_pow]; ring
    _ ≤ n * n ^ c := Nat.mul_le_mul_right _ (by omega)
    _ = n ^ (c + 1) := by ring

/-- The parameter recovered from the input length `m`: the largest `n ≤ m` with `n^d ≤ m`
(`ν m = ⌊m^{1/d}⌋`). -/
def nu (d m : ℕ) : ℕ := Nat.findGreatest (fun n => n ^ d ≤ m) m

/-- `ν(m)^d ≤ m`. -/
theorem nu_pow_le {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : nu d m ^ d ≤ m :=
  Nat.findGreatest_spec (P := fun n => n ^ d ≤ m) (Nat.zero_le m)
    (by show 0 ^ d ≤ m; rw [Nat.zero_pow hd]; exact Nat.zero_le m)

/-- `ν(m) ≤ m`. -/
theorem nu_le (d m : ℕ) : nu d m ≤ m := Nat.findGreatest_le m

/-- `m < (ν(m) + 1)^d`: the recovered parameter is maximal. -/
theorem lt_succ_nu_pow {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : m < (nu d m + 1) ^ d := by
  by_cases h : nu d m < m
  · have := Nat.findGreatest_is_greatest (P := fun n => n ^ d ≤ m) (n := m) (k := nu d m + 1)
      (Nat.lt_succ_self _) (by omega)
    exact not_le.mp this
  · have hm : nu d m = m := le_antisymm (nu_le d m) (not_lt.mp h)
    rw [hm]
    exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_self_pow (by omega) _)

/-- `n ≤ ν(m)` whenever `n^d ≤ m`. -/
theorem le_nu {d : ℕ} (hd : 1 ≤ d) {n m : ℕ} (h : n ^ d ≤ m) : n ≤ nu d m :=
  Nat.le_findGreatest ((Nat.le_self_pow (by omega) n).trans h) h

/-! ## The padded function -/

/-- The raw output of `g'` on `z` (`|z| = m`, `n = ν m`): the padding block `z.drop ℓ(n)`
followed by `F ⟨1^n, z.take ℓ(n)⟩` (data first, so that the split is a `pairSplitAt`). -/
def raw (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  z.drop (ℓ.eval (nu d z.length)) ++
    F (NUPPT.advInput (nu d z.length) (z.take (ℓ.eval (nu d z.length))))

/-- The string function of the padded family: the raw output zero-filled (or truncated) to
`2|z|` bits. -/
def gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  (raw F ℓ d z ++ List.replicate (2 * z.length) false).take (2 * z.length)

/-- `gStr` has exactly `2|z|` bits. -/
theorem length_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) :
    (gStr F ℓ d z).length = 2 * z.length := by
  simp only [gStr, List.length_take, List.length_append, List.length_replicate]
  omega

/-- `gStr` is length-regular with output length `2·var`. -/
theorem lengthRegular_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    FunFamily.LengthRegular (gStr F ℓ d) (.mul (.const 2) .var) := fun z => by
  simp [length_gStr]

/-- **The padded family** `g'` of [PS10, Lemma 64.3]: `FunFamily.ofString` of `gStr` with
output length `2·var` (so `inLen = var`). -/
def family (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) : FunFamily :=
  FunFamily.ofString (gStr F ℓ d) (.mul (.const 2) .var)

/-- The input length of the padded family is the parameter. -/
theorem family_inLen (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    (family F ℓ d).inLen = .var := rfl

/-- The encoding of the padded family's value is `gStr`. -/
theorem ofFn_family_f (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (m : ℕ)
    (x : Fin m → Bool) : List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x) :=
  FunFamily.ofFn_ofString_f (lengthRegular_gStr F ℓ d) m x

/-! ## The computability clauses -/

/-- **The linear-time evaluator of the padded family** [PS10, Lemma 64.3, "`g'` is computable
in time `O(n²)`"; the only new machine of the lemma] — **admitted**. Given a machine `M` for
`F` within `C (k + 1)^c` and `d` dominating the data length and the running time of `F` on
`⟨1^n, b⟩` (`hdom`), some multitape machine computes `gStr F ℓ d` in linear time.

**Proof sketch (construction).** On input `z` of length `m`: (1) the parameter `1^{ν m}` by
incremental unary counting — maintain `1^n` and the powers `1^{(n+1)^j}`, `j ≤ d`, on `d + 1`
tapes, advancing `n` while `1^{(n+1)^d}` fits in the input (the powers are updated by the
binomial identity, total cost `∑_{n ≤ ν m} O((n+1)^{d-1}) = O(m)`), or equivalently `d`-th root
extraction by consuming the input in chunks of sizes `(n+1)^d − n^d`; (2) `1^{ℓ(ν m)}` by
`Turing.FinTM.computesFunInTime_polyUnary` on the short string `1^{ν m}`, of cost
`O((ν m + 1)^{deg ℓ + 1}) ≤ O(m)` by `hdom` (through `Turing.FinTM.exists_comp_on_image`, which
charges the second stage at the original input length); (3) the split
`Turing.FinTM.computesFunInTime_pairSplitAt` on `⟨1^{ℓ(ν m)}, z⟩`; (4) the call of `M` on
`⟨1^{ν m}, z.take ℓ(ν m)⟩`, of cost `C (2 ν m + 3 + ℓ(ν m))^c ≤ (ν m)^d ≤ m` for `ν m ≥ n₁`
(finitely many smaller `m` are absorbed in the linear constant), again on the image; (5) the
concatenation `Turing.FinTM.computesFunInTime_pairConcat`, the zero filling (a one-state scan
of the input emitting two `false` per cell) and the cut to `2m` bits
(`pairSplitAt` on `⟨z ++ z, ·⟩`, `computesFunInTime_pairDup`/`pairConcat`). All stages are
linear or charged on short images, so the total is `c' (m + 1)`. -/
theorem exists_linearTime_gStr {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F fun k => C * (k + 1) ^ c) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1) := by
  sorry

/-- **`g'` is easy to compute** from a linear-time evaluator: the evaluator on `⟨1^m, y⟩`
applies `gStr` to the second component (`ofFn_family_f`). -/
theorem easy_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    (family F ℓ d).Easy := by
  have hg : PolyTimeComputable (gStr F ℓ d) := polyTimeComputable_of_linear h
  refine ⟨fun z => gStr F ℓ d (pairSndD z), hg.comp polyTimeComputable_pairSndD, fun m x => ?_⟩
  rw [ofFn_family_f]
  show gStr F ℓ d (pairSndD (pairEncode (List.replicate m true) (List.ofFn x))) = _
  rw [pairSndD_pairEncode]

/-- **`g'` is computable by a coded machine in quadratic time** from a linear-time multitape
evaluator: `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine within
`c₁ (c' (m + 1) + 1)² ≤ c₁ (c' + 1)² (m + 1)²`, and `Turing.exists_codeTM` a `CodeTM` with the
same runs. -/
theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin m → Bool),
      Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x))
        (c₀ * (m + 1) ^ 2) := by
  obtain ⟨M', c', hM'⟩ := h
  obtain ⟨M₁, c₁, hk, hM₁⟩ := FinTM.one_work_tape_binary M' _ _ hM'
  obtain ⟨Mc, hMc⟩ := exists_codeTM M₁ hk
  refine ⟨Mc, c₁ * (c' + 1) ^ 2, fun m x => ?_⟩
  rw [ofFn_family_f, hMc]
  refine (hM₁ (List.ofFn x)).mono ?_
  simp only [List.length_ofFn]
  calc c₁ * (c' * (m + 1) + 1) ^ 2 ≤ c₁ * ((c' + 1) * (m + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [Nat.add_mul, Nat.one_mul]; omega) 2)
    _ = c₁ * (c' + 1) ^ 2 * (m + 1) ^ 2 := by ring

/-! ## One-wayness of the padded family -/

/-- `List.ofFn` through a `finCongr` relabelling of the index type. -/
private theorem ofFn_arrowCongr {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) f) = List.ofFn f :=
  (List.ofFn_congr h f).symm

/-- The encoding of a pair of strings assembled by `Fin.appendEquiv` (and a length cast) is
the concatenation of the encodings. -/
private theorem ofFn_appendEquiv {a b n : ℕ} (h : a + b = n) (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) (Fin.append q.1 q.2)) = _
  rw [ofFn_arrowCongr, List.ofFn_fin_append]

/-- The encoding of a coin string reassembled by `splitCoins` (and a length cast) is the
concatenation of the encodings of the halves. -/
private theorem ofFn_splitCoins_symm_cast {a b n : ℕ} (h : a + b = n)
    (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((splitCoins a b).symm.trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) ((splitCoins a b).symm q)) = _
  rw [ofFn_arrowCongr]
  obtain ⟨q₁, q₂⟩ := q
  exact ofFn_splitCoins_symm a b q₁ q₂

section Hardness

variable {𝓕 : FunFamily} {F : List Bool → List Bool}
  (hFx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x))
  {d : ℕ} (hd : 1 ≤ d)

include hFx in
/-- The raw output on `b ++ a` (`|b| = ℓ(n)`, `|a| = m − ℓ(n)`, `ν m = n`) is `a ++ f_n(b)`. -/
theorem raw_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    raw F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = List.ofFn a ++ List.ofFn (𝓕.f n b) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  simp only [raw, hlen, hnu, List.take_left' (List.length_ofFn (f := b)),
    List.drop_left' (List.length_ofFn (f := b)), hFx]

include hFx in
/-- The padded output on `b ++ a` is `a ++ f_n(b)` followed by zeros (lossless padding, as
`(m − ℓ(n)) + L(n) ≤ 2m`). -/
theorem gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b : Fin (𝓕.inLen.eval n) → Bool)
    (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = (List.ofFn a ++ List.ofFn (𝓕.f n b)) ++
      List.replicate (2 * m - (List.ofFn a ++ List.ofFn (𝓕.f n b)).length) false := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold gStr
  rw [raw_eq hFx hnu hℓ b a, hlen, take_append_replicate_of_le]
  simp only [List.length_append, List.length_ofFn]
  omega

include hFx in
/-- The challenge the reduction hands to the inverter of `g'`: the padding evaluator on
`⟨1^m, a ++ f_n(b)⟩` is the encoding of `g'_m(b ++ a)`. -/
theorem padStr_eq_gStr {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    padStr (.mul (.const 2) .var) (List.replicate m true)
      (List.ofFn a ++ List.ofFn (𝓕.f n b)) = gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold padStr gStr
  rw [raw_eq hFx hnu hℓ b a, hlen]
  simp

include hFx in
/-- **Padding is injective on the data block**: equal padded outputs on `b' ++ a'` and
`b ++ a` force `f_n(b') = f_n(b)` (`List.append_inj` on the equal-length blocks). -/
theorem f_eq_of_gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b b' : Fin (𝓕.inLen.eval n) → Bool)
    (a a' : Fin (m - 𝓕.inLen.eval n) → Bool)
    (h : gStr F 𝓕.inLen d (List.ofFn b' ++ List.ofFn a') =
      gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a)) : 𝓕.f n b' = 𝓕.f n b := by
  rw [gStr_eq hFx hnu hℓ hL b' a', gStr_eq hFx hnu hℓ hL b a, List.append_assoc,
    List.append_assoc] at h
  obtain ⟨-, h2⟩ := List.append_inj h (by simp)
  exact List.ofFn_injective (List.append_inj_left h2 (by simp))

include hFx in
/-- **The padding reduction wins** [Gar26, Lemma 2.3, machine form]: if `A` at parameter `n`
samples the padding `a` from its first `p(n)` coins, hands `A'` (at the length `m` with
`ν m = n`) the padded `⟨a, f_n(b)⟩` and returns the first `ℓ(n)` bits of the answer, then `A`
inverts `f` at `n` at least as often as `A'` inverts `g'` at `m`.

**Proof sketch.** `invProbAt_eq_uprob` on both sides. Split the uniform input of `g'` as
`(b, a)` (`Fin.appendEquiv`); split `A`'s coins as `((a, a''), (ρ, ρ''))` (`splitCoins`, with
`A'.coins m ≤ A'.coins (p n)` by `PolyExpr.eval_mono`); the extra coins `a'', ρ''` are unread
(`uprob_fst`). On `((b, a), ρ)`, `A`'s challenge to `A'` is `g'_m(b ++ a)` (`padStr_eq_gStr`),
so an answer `x' = b' ++ a'` of `A'` with `g'_m(x') = g'_m(b ++ a)` gives `A`'s answer `b'` with
`f_n(b') = f_n(b)` (`f_eq_of_gStr_eq`); conclude by `uprob_mono`. -/
theorem invProbAt_family_le (A' A : NUPPT) {n m : ℕ} (hnu : nu d m = n)
    (hℓ : 𝓕.inLen.eval n ≤ m) (hL : 𝓕.outLen.eval n ≤ m) {p : PolyExpr} (hm : m ≤ p.eval n)
    (hAc : A.coins = .add p (A'.coins.subst p))
    (hA : ∀ y (r : List Bool), A.runAtL n y r =
      (A'.runAtL m (padStr (.mul (.const 2) .var) (List.replicate m true)
        ((r.take (p.eval n)).take (m - 𝓕.inLen.eval n) ++ y))
        ((r.drop (p.eval n)).take (A'.coinLen m))).take (𝓕.inLen.eval n)) :
    (family F 𝓕.inLen d).invProbAt A' m ≤ 𝓕.invProbAt A n := by
  have hcast₁ : 𝓕.inLen.eval n + (m - 𝓕.inLen.eval n) = m := by omega
  let e : (Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool) ≃ (Fin m → Bool) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hcast₁) (Equiv.refl Bool))
  have hofn : ∀ q, List.ofFn (e q) = List.ofFn q.1 ++ List.ofFn q.2 := fun q =>
    ofFn_appendEquiv hcast₁ q
  have hc₁ : A'.coinLen m ≤ A'.coinLen (p.eval n) := A'.coins.eval_mono hm
  have hcast₂ : (m - 𝓕.inLen.eval n) + (p.eval n - (m - 𝓕.inLen.eval n)) = p.eval n := by omega
  have hcast₃ : A'.coinLen m + (A'.coinLen (p.eval n) - A'.coinLen m) = A'.coinLen (p.eval n) := by
    omega
  have hcast₄ : p.eval n + A'.coinLen (p.eval n) = A.coinLen n := by
    simp [NUPPT.coinLen, hAc, PolyExpr.eval_subst]
  let eA : (Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ≃
      (Fin (p.eval n) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₂) (Equiv.refl Bool))
  let eR : A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool) ≃
      (Fin (A'.coinLen (p.eval n)) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₃) (Equiv.refl Bool))
  let eC : ((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
      (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃ A.Coins n :=
    (Equiv.prodCongr eA eR).trans
      ((splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool)))
  have hofnC : ∀ q, List.ofFn (eC q) =
      (List.ofFn q.1.1 ++ List.ofFn q.1.2) ++ (List.ofFn q.2.1 ++ List.ofFn q.2.2) := by
    intro q
    show List.ofFn (((splitCoins _ _).symm.trans
      (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool))) (eA q.1, eR q.2)) = _
    rw [ofFn_splitCoins_symm_cast]
    show List.ofFn (eA q.1) ++ List.ofFn (eR q.2) = _
    rw [ofFn_splitCoins_symm_cast, ofFn_splitCoins_symm_cast]
  let eArr : (((Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool)) × A'.Coins m) ×
      ((Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
        (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃
      (Fin (𝓕.inLen.eval n) → Bool) ×
        (((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
          (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      ((Equiv.prodCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob,
    ← uprob_comp_equiv (Equiv.prodCongr e (Equiv.refl (A'.Coins m))),
    ← uprob_comp_equiv (eArr.trans (Equiv.prodCongr (Equiv.refl _) eC))]
  rw [← uprob_fst (β := (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
    (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))]
  refine uprob_mono fun q hq => ?_
  obtain ⟨x', hx', hgx'⟩ := hq
  -- the components of `q`
  obtain ⟨⟨⟨b, a⟩, ρ⟩, ⟨a'', ρ''⟩⟩ := q
  -- the answer of `A'`, split as `b' ++ a'`
  obtain ⟨⟨b', a'⟩, hx'e⟩ : ∃ q', e q' = x' := ⟨e.symm x', e.apply_symm_apply x'⟩
  refine ⟨b', ?_, ?_⟩
  · show A.runAt n (List.ofFn (𝓕.f n b)) (eC ((a, a''), (ρ, ρ''))) = List.ofFn b'
    rw [NUPPT.runAt_eq, hofnC, hA]
    simp only [List.take_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.drop_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.take_left' (List.length_ofFn (f := a)), List.take_left' (List.length_ofFn (f := ρ))]
    rw [padStr_eq_gStr hFx hnu hℓ b a, ← hofn (b, a), ← ofFn_family_f, ← NUPPT.runAt_eq]
    have hx'' : A'.runAt m (List.ofFn ((family F 𝓕.inLen d).f m (e (b, a)))) ρ = List.ofFn x' := hx'
    rw [hx'', ← hx'e, hofn, List.take_left' (List.length_ofFn (f := b'))]
  · show 𝓕.f n b' = 𝓕.f n b
    have hg : (family F 𝓕.inLen d).f m (e (b', a')) = (family F 𝓕.inLen d).f m (e (b, a)) := by
      rw [hx'e]; exact hgx'
    have hg' := congrArg List.ofFn hg
    rw [ofFn_family_f, ofFn_family_f, hofn, hofn] at hg'
    exact f_eq_of_gStr_eq hFx hnu hℓ hL b b' a a' hg'

include hFx hd in
/-- **The padded family is strongly one-way** [PS10, Lemma 64.3, "`g'` is strongly one-way"],
given a linear-time evaluator (`hlin`) and `d` dominating `ℓ + L` from `n₁` on (`hdom`).

**Proof sketch.** *Easy* is `easy_of_linear`. *Hard:* let `A'` invert `g'` with probability
`≥ 1/m^e` at infinitely many `m` (`not_negligible_iff`). Call `m` good when `m ≥ n₁^d`,
`m ≥ 1` and `A'` is that successful at `m`; `φ n` is a good `m` with `ν m = n` when one exists
(else `0`), majorised by `p := (n + 1)^d` (`lt_succ_nu_pow`). The reduction `A` is
`NUPPT.exists_reparam_pre_post_adv A' φ p` with advice `⟨⟨1^{φ n}, 1^{φ n − ℓ(n)}⟩, 1^{ℓ(n)}⟩`,
pre-processing `⟨y, a⟩ ↦ padStr (2·var) 1^{φ n} (a.take (φ n − ℓ(n)) ++ y)` and post-processing
"the first `ℓ(n)` bits", behind `NUPPT.exists_split _ p` which samples the padding `a` from
the first `p(n)` coins. For every good `m` with `n := ν m ≥ max(n₀, 2^{de}, n₁)`,
`invProbAt_family_le` at `m' := φ n` gives `1/n^{de+1} ≤ 1/(n+1)^{de} ≤ 1/m'^e ≤ invProbAt A' m'
≤ 𝓕.invProbAt A n`, contradicting `h.hard A` at the degree `de + 1`. -/
theorem strongOneWay (h : 𝓕.StrongOneWay) {n₁ : ℕ}
    (hdom : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d)
    (hlin : ∃ (M' : FinTM Bool) (c' : ℕ),
      M'.ComputesFunInTime (gStr F 𝓕.inLen d) fun m => c' * (m + 1)) :
    (family F 𝓕.inLen d).StrongOneWay where
  easy := easy_of_linear hlin
  hard A' := by
    classical
    by_contra hneg
    obtain ⟨e, he⟩ := not_negligible_iff.mp hneg
    let good : ℕ → Prop := fun m => n₁ ^ d ≤ m ∧ 1 ≤ m ∧
      1 / (m : ℝ) ^ e ≤ (family F 𝓕.inLen d).invProbAt A' m
    let φ : ℕ → ℕ := fun n => if h : ∃ m, good m ∧ nu d m = n then h.choose else 0
    let p : PolyExpr := .pow (.add .var (.const 1)) d
    have hφ : ∀ n, φ n ≤ p.eval n := by
      intro n
      simp only [φ, p, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      split_ifs with hex
      · have h1 := hex.choose_spec.2
        have h2 := lt_succ_nu_pow hd hex.choose
        rw [h1] at h2
        exact h2.le
      · exact Nat.zero_le _
    have hφ_spec : ∀ n, (∃ m, good m ∧ nu d m = n) → good (φ n) ∧ nu d (φ n) = n := by
      intro n hex
      simp only [φ, dif_pos hex]
      exact hex.choose_spec
    let β : ℕ → List Bool := fun n => pairEncode
      (pairEncode (List.replicate (φ n) true) (List.replicate (φ n - 𝓕.inLen.eval n) true))
      (List.replicate (𝓕.inLen.eval n) true)
    have hβ : ∀ n, (β n).length ≤
        (PolyExpr.add (.add (.mul (.const 6) p) (.const 6)) 𝓕.inLen).eval n := by
      intro n
      have h1 := hφ n
      simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
        PolyExpr.eval_const]
      omega
    have hpre : PolyTimeComputable fun w => padStr (.mul (.const 2) .var)
        (pairFstD (pairFstD (pairFstD w)))
        ((pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length ++
          pairFstD (pairSndD w)) := by
      have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have hv : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have ha : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
        polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
      have hy : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
        polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
      have hcut : PolyTimeComputable fun w =>
          (pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length := by
        have h := (polyTimeComputable_pairTakePoly .var).comp (hv.pairEncode ha)
        convert h using 1
        funext w
        simp
      have h := (polyTimeComputable_padStr (.mul (.const 2) .var)).comp
        (hu.pairEncode (hcut.append hy))
      convert h using 1
      funext w
      simp
    have hpost : PolyTimeComputable fun w => (pairSndD w).take (pairSndD (pairFstD w)).length := by
      have h := (polyTimeComputable_pairTakePoly .var).comp
        ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
          polyTimeComputable_pairSndD)
      convert h using 1
      funext w
      simp
    obtain ⟨B, hBc, hB⟩ := A'.exists_reparam_pre_post_adv φ p hφ β _ hβ hpre hpost
    obtain ⟨A, hAc, -, hA⟩ := B.exists_split p
    have hA' : ∀ n y (r : List Bool), A.runAtL n y r =
        (A'.runAtL (φ n) (padStr (.mul (.const 2) .var) (List.replicate (φ n) true)
          ((r.take (p.eval n)).take (φ n - 𝓕.inLen.eval n) ++ y))
          ((r.drop (p.eval n)).take (A'.coinLen (φ n)))).take (𝓕.inLen.eval n) := by
      intro n y r
      rw [hA, hB]
      simp [β]
    -- the contradiction with the one-wayness of `𝓕` at degree `d e + 1`
    obtain ⟨n₀, hn₀⟩ := h.hard A (d * e + 1)
    obtain ⟨m, hm, hgm⟩ := he (max (max n₀ (2 ^ (d * e))) 1 ^ d + n₁ ^ d + 1)
    have hNd : max (max n₀ (2 ^ (d * e))) 1 ^ d ≤ m := by omega
    have hN : max (max n₀ (2 ^ (d * e))) 1 ≤ nu d m := le_nu hd hNd
    have hn₁ : n₁ ≤ nu d m := le_nu hd (by omega)
    have hgood : good m := ⟨by omega, by omega, by
      rwa [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hgm⟩
    obtain ⟨hgood', hnu'⟩ := hφ_spec (nu d m) ⟨m, hgood, rfl⟩
    -- notation: `n := nu d m`, `m' := φ n`
    have hn_n₀ : n₀ ≤ nu d m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
    have hn_pow : 2 ^ (d * e) ≤ nu d m :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    have hn_one : 1 ≤ nu d m := le_trans (le_max_right _ _) hN
    have hℓL : 𝓕.inLen.eval (nu d m) + 𝓕.outLen.eval (nu d m) ≤ φ (nu d m) := by
      refine (hdom _ hn₁).trans ?_
      have h2 := nu_pow_le hd (φ (nu d m))
      rw [hnu'] at h2
      exact h2
    have hm'p : φ (nu d m) ≤ p.eval (nu d m) := hφ _
    have hAc' : A.coins = .add p (A'.coins.subst p) := by rw [hAc, hBc]
    have hcore := invProbAt_family_le hFx A' A hnu' (by omega) (by omega) hm'p hAc'
      (hA' (nu d m))
    have hbound := hn₀ (nu d m) hn_n₀
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hbound
    have hsucc := hgood'.2.2
    -- real arithmetic: `1/n^(de+1) ≤ 1/(n+1)^(de) ≤ 1/m'^e`
    have hm'e : (φ (nu d m) : ℝ) ^ e ≤ ((nu d m : ℝ) + 1) ^ (d * e) := by
      have h1 : φ (nu d m) ^ e ≤ ((nu d m + 1) ^ d) ^ e := Nat.pow_le_pow_left hm'p e
      rw [← pow_mul] at h1
      exact_mod_cast h1
    have hnde : ((nu d m : ℝ) + 1) ^ (d * e) ≤ (nu d m : ℝ) ^ (d * e + 1) := by
      have h1 : (nu d m + 1) ^ (d * e) ≤ nu d m ^ (d * e + 1) := by
        calc (nu d m + 1) ^ (d * e) ≤ (2 * nu d m) ^ (d * e) :=
              Nat.pow_le_pow_left (by omega) _
          _ = 2 ^ (d * e) * nu d m ^ (d * e) := by rw [mul_pow]
          _ ≤ nu d m * nu d m ^ (d * e) := Nat.mul_le_mul_right _ hn_pow
          _ = nu d m ^ (d * e + 1) := by ring
      exact_mod_cast h1
    have hm'pos : (0 : ℝ) < (φ (nu d m) : ℝ) ^ e := by
      have : (1 : ℝ) ≤ (φ (nu d m) : ℝ) := by exact_mod_cast hgood'.2.1
      positivity
    have h1 : 1 / (nu d m : ℝ) ^ (d * e + 1) ≤ 1 / (φ (nu d m) : ℝ) ^ e :=
      one_div_le_one_div_of_le hm'pos (hm'e.trans hnde)
    linarith

end Hardness

/-- **[PS10, Lemma 64.3] with `QuadraticCode` unfolded**: from a strong one-way family, a
strong one-way family with `inLen = var` computable by a coded machine in time `c₀ (m + 1)²`
on the bare input — the padded family at the degree `d` of `exists_pow_dominates` applied to
`ℓ + L + (running time of the evaluator)`, given its linear-time evaluator
(`exists_linearTime_gStr`, admitted).

**Proof sketch.** `h.easy` gives `F` with machine `M` within `C (k + 1)^c`; dominate
`ℓ + L + C (2n + 3 + ℓ(n))^c` by `n^d` from `n₁` on (`exists_pow_dominates` on the syntactic
polynomial `add (add ℓ L) ((normal C c).subst (add (mul (const 2) var) (add (const 2) ℓ)))`);
`exists_linearTime_gStr` gives the linear evaluator; conclude with `strongOneWay` and
`quadraticCode_of_linear`. -/
theorem exists_family (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧
      ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓖.inLen.eval n) → Bool),
        M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓖.f n x))
          (c₀ * (𝓖.inLen.eval n + 1) ^ 2) := by
  obtain ⟨𝓕, h⟩ := h
  obtain ⟨F, ⟨M, C, c, hM⟩, hFx⟩ := h.easy
  obtain ⟨d, n₁, hd, hdom⟩ := exists_pow_dominates
    (.add (.add 𝓕.inLen 𝓕.outLen)
      ((PolyExpr.normal C c).subst (.add (.mul (.const 2) .var) (.add (.const 2) 𝓕.inLen))))
  have hdom₁ : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d := fun n hn => by
    have := hdom n hn
    simp only [PolyExpr.eval_add] at this
    omega
  have hdom₂ : ∀ n ≥ n₁, 𝓕.inLen.eval n + C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c ≤ n ^ d :=
    fun n hn => by
      have := hdom n hn
      simp only [PolyExpr.eval_add, PolyExpr.eval_subst, PolyExpr.eval_normal, PolyExpr.eval_mul,
        PolyExpr.eval_const, PolyExpr.eval_var] at this
      have h2 : C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c = C * (2 * n + (2 + 𝓕.inLen.eval n) + 1) ^ c := by
        congr 2
        omega
      omega
  have hlin := exists_linearTime_gStr hM 𝓕.inLen hd hdom₂
  exact ⟨family F 𝓕.inLen d, family_inLen F 𝓕.inLen d, strongOneWay hFx hd h hdom₁ hlin,
    quadraticCode_of_linear hlin⟩


end TCSlib.Cryptography.PadQuad
