## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03f2-pack.md =====

# Gate 03f2 ([PS10] ch. 2–4, factoring, RSA, Rabin; number theory): external statement audit pack

**Status: ready to dispatch once [Shilun-Allan-Li/tcslib#201](https://github.com/Shilun-Allan-Li/tcslib/pull/201) merges** (re-staged 2026-11-05 at that PR's head, the gate 03a + 03c repairs; first staged at `a3c5fa8b`; the evidence is under `evidence/f2/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`0c348ff94cacf24d96d99078c9dd9e328530c8d2` (the head of #201; its Lean files are what the branch holds once #201 merges). This pack covers the factoring assumption and the factoring-based candidates (the weak one-way function `f_mult`, the factoring collection, RSA and Rabin with their trapdoors), and the number theory they rest on (Euclid, modular exponentiation, groups, primality testing, quadratic residues, the density of primes).
- **This pack gates fills.** Its files hold **36 `sorry`s**, to be filled after this pack
  closes (user's ruling of 2026-11-05). A statement that cannot be proved as stated, or that is
  weaker than the source, must be found **now**.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03f2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §2.3 (book pp. 29–33), the factoring statements of §2.4 (Thms 33.5 and 36.3), and §2.6–§2.12 (pp. 41–63).

## Changes since the first staging (repairs of the interface packs; check them, do not re-find them)

The pin moved from `a3c5fa8b` to the head of the gate 03a + 03c repair PR. Changes in or near this pack's files:
- **G3-1** (gate 03b major, merged in #198): `Collection` gained the field `encD_decD`, which makes decoding canonical. The proofs:
  - the distinct-primes collection: `encodeDistinctPrimes_of_decode` (`Concrete.lean`, context);
  - `rsaTrapdoor`: `rsaEnc_of_rsaDec`, which covers the invalid-index branch (the canonical string of `1 mod N`);
  - Rabin's and Blum's collections: inline proofs.

  They rest on the numeral lemmas `natToList_length_listToNat` and `natToList_val_natCast` (`Arithmetic.lean`).
- **Gate 03l, major 1:** the axiom attestation below prints every public theorem and lemma of this pack's files, not only `Checks.lean`'s headlines.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also, for **every sorried
declaration**, say whether it is (a) true as stated and provable from the hypotheses it carries,
(b) true but weaker than the source, or (c) false or unprovable as stated. For (c), give a
counterexample or the missing hypothesis. Attempt at least **three adversarial instantiations**,
for example:
- a "Blum integer" generator whose primes are equal with non-negligible probability;
- a weak one-way function whose failure probability is not noticeable at some lengths;
- a Rabin inverter that uses its advice to know a square root of `-1`.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Candidates/{Factoring, RSA, Rabin}.lean`, `TCSlib/Cryptography/NumberTheory/{Chebyshev, Euclid, ModExp, Primality, QuadraticResidues, Units}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | `Candidates/Arithmetic.lean` (pack 03b); the files of packs 03a–03d |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11 (the arithmetic hypothesis bundle) and the open questions on Rabin/RSA scope; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Alg-37.4, Thm-51.1, Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Thm-63.10; the `NumberTheory/` rows Def-29.3 to Claim-63.1 (33 rows) |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the discrete-log candidates (pack 03f1) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (evidence under `evidence/f2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 73 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   54 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 230 prints of every public theorem and lemma in this pack's files:
   177 use only the standard axioms, and 53 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 36 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 10 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes at its head (`evidence-repairs/03ac/replay.log`); each line of
`replay.log` is the newest check of its module. The closure is smaller than at the first staging
because 03a's repair narrowed facade imports (`Randomized` → its three files).

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints of every public theorem and lemma of this pack's files;
- admissions: the 36 `sorry`s, listed by declaration;
- lint.

## Specific questions

1. **The factoring assumption (Asm 30.1) and `f_mult` (Thms 33.5, 36.3).**
   - Is the assumption on the right distribution: two independent uniform `n`-bit primes?
   - Is `f_mult` weakly one-way at the source's strength, with the density of primes
     (Chebyshev, Thm 31.3) as the only non-trivial input?
2. **The collections (Thm 51.1; RSA Thms 53.2, 55.2, 57.2; Rabin Thms 61.7, 61.8, 63.10).**
   - Are the samplers' specifications and closeness statements what `Collection` requires?
   - Is "RSA hardness implies factoring hardness" the right direction? Is "Rabin is as hard as
     factoring" stated for Blum integers, as decided (open question 3: `p ≠ q`, Blum integers,
     the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Thm 63.10's `Gen`)?
3. **The trapdoors** (`rsaInv_spec`, `blumInv_spec`). Is inversion with the trapdoor correct on
   every sampled index?
4. **Number theory.**
   - Are Euclid, modular exponentiation and the Miller–Rabin test stated with correct
     complexity and error bounds (Thm 49.14; Lem 50.15a/b)?
   - Run 3a deferred two minors here: P6-1, the oddness in Lemma 50.15, and Lemma 50.15b. Are
     they still minor?
5. **Sorried statements.** All 36 are in the three candidate files. Give each a sorry verdict
     (a / b / c).

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
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
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
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
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

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

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
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
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
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f2/replay.log =====

# closure of pack 03f2's files at 0c348ff94cacf24d96d99078c9dd9e328530c8d2: 73 modules, extracted from replay-combined.log
TCSlib/Complexity/ClassNP/CoNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/CounterProgPolyTime rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/NP rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PClosure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimeBlockTests rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePrefix rc=0 3s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 2s errors=0 sorry=2
TCSlib/Complexity/PolyHierarchy/Padding rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/PPT rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterBody rc=0 13s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 50s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 54s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 4s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 3s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProg rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgInput rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/CounterProgRun rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 3s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 11s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 6s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UnaryTape rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 60s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 3s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 3s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 6s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 6s errors=0 sorry=19
TCSlib/Cryptography/Foundations/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Euclid rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/ModExp rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/QuadraticResidues rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Units rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Amplification rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 2s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f2/axioms.log =====

# axiom prints of every public theorem and lemma for declarations in pack 03f2's files, at 0c348ff94cacf24d96d99078c9dd9e328530c8d2
TCSlib.Cryptography.Candidates.fmultNat_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmult_inLen: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmult_outLen: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmult_f: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmult_inv_factor: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.fmult_easy: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.modulusBits_eq_fmult: propext
TCSlib.Cryptography.Candidates.factorProb_nonneg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.factorProb_le_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.factorProb_eq_zero_of_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.coins_oneCallFactorer: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.eval_fmultWeakPoly: propext
TCSlib.Cryptography.Candidates.fmult_weakOneWay: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.eval_fmultBlocks: propext
TCSlib.Cryptography.Candidates.fmult_prod_inLen: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.exists_plantFactorer: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.samplePairOut_eq_encode: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factoringGen_runAt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.factoringSampler_runAt: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factoringSampler_spec: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factoringCollection_index: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factoringCollection_sampleClose: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.coins_collectionFactorer: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.collectionFactorer_runAt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factoringCollection_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsaProb_nonneg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaProb_le_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaProb_eq_zero_of_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaPerm_apply: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaPerm_symm_apply: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.mul_inv_val_modEq: propext, Quot.sound
TCSlib.Cryptography.Candidates.rsaMod_of_valid: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaMod_of_not_valid: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaMod_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.val_lt_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaEval_spec: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rsaEval: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaF_perm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaDec_rsaEnc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaEnc_of_rsaDec: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.sampleUnitL_spec: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.RSAParams.N_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.RSAParams.e_lt_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.RSAParams.d_lt_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaN_indexOf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaE_indexOf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaValid_indexOf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaMod_indexOf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsaGen_runAt: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rsaSampleRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rsaInvRaw: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaInv_runAt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaInv_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaSampler_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaCollection_index: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.negligible_rsaGenErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaCollection_sampleClose: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.coins_rsaBreaker: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaBreaker_runAt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsaCollection_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rsaFromFactorStep_correct: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.coins_rsaFromFactorer: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.factorProb_le_rsaProb: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rsa_imp_factoring: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.BlumDistinctPrimes.ne_two: propext, Quot.sound
TCSlib.Cryptography.Candidates.oddFactorProb_le: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumFactorProb_le: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumFactoring_of_factoring: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.crtNegOne_sq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.crtNegOne_ne_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.crtNegOne_ne_neg_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabin_symmetry: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.oddGen_runAt: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumGen_runAt: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_rabinIndexOf: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinMod_le: propext, Quot.sound
TCSlib.Cryptography.Candidates.rabinDec_rabinEnc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinEval_spec: propext, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rabinEval: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinSampler_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinCollection_index: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.negligible_rabinErr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinCollection_sampleClose: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinFactorer_runAt: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinCollection_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.blumMod_of_valid: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumMod_of_not_valid: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumMod_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.BlumValid.exists_mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.sqTo_bijective_of_exists: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blum_val_lt_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumDec_blumEnc: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumEval_spec: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumF_perm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_blumSampleRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.blumInv_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.blumSampler_spec: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_index: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay: propext,  sorryAx,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.card_primes: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.chebyshev_two_mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.chebyshev: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_prime_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_prime_bits: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_prime_pair: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclid_zero_right: propext, Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclid_of_mod_eq_zero: Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclid_of_mod_ne_zero: Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclidCalls_zero_right: propext
TCSlib.Cryptography.NumberTheory.extEuclidCalls_of_mod_eq_zero: none
TCSlib.Cryptography.NumberTheory.extEuclidCalls_of_mod_ne_zero: none
TCSlib.Cryptography.NumberTheory.extEuclid_spec: propext, Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclid_inv: propext, Quot.sound
TCSlib.Cryptography.NumberTheory.extEuclidCalls_le: propext, Quot.sound
TCSlib.Cryptography.NumberTheory.modExpLoop_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExpLoop_of_ne_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExpLoop_fst: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExp_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExp_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExp_eq_of_ne_one: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExp_cast: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExpLoop_snd_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.modExpMults_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.two_pow_mrExp_mul_mrOdd: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mrOdd_odd: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mrOdd_mul_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mem_mrLiars: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.MRLiar.ne_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.millerRabin_of_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.samplePrime_eq_none_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.samplePrime_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.statClose_samplePrime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat: none
TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins: propext
TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mem_QR_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.sq_mem_QR: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.coe_sqTo: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_units_eq_mul_card_QR: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_sqrt_eq_two: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_QR_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.div_four_succ_eq: propext, Quot.sound
TCSlib.Cryptography.NumberTheory.sq_pow_div_four_succ: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.pow_div_four_succ_mem_QR: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.sqrtMod3_sq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.crtUnits_fst: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.crtUnits_snd: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.mem_QR_mul_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.sq_crtUnits_symm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_sqrt_mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.coprime_of_ne: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_sqrt_mul_eq_four: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_QR_mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.pushesUniform_sqTo: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.blumSqrt_sq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.blumSqrt_mem_QR: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.eq_blumSqrt_of_sq_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.sqTo_bijective_of_blum: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.units_val_mem: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.totient_prime_mul_prime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.card_units_zmod_prime_mul_prime: propext,  Classical.choice,  Quot.sound
TCSlib.Cryptography.NumberTheory.units_pow_mod_totient: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.pow_mod_totient_modEq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.rsa_pow_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.rsa_pow_bijective: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.exists_rsa_inverse: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.NumberTheory.le_totient_mul_log_succ: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.length_natToList: propext
TCSlib.Cryptography.Candidates.natToList_zero: propext
TCSlib.Cryptography.Candidates.natToBits_succ_castSucc: propext, Quot.sound
TCSlib.Cryptography.Candidates.natToBits_succ_last: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_natToList_eq_mod: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_natToList: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.bitsToNat_natToBits: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.natToBits_bitsToNat: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.natToBits_injOn: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.natToList_injOn: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_lt_two_pow: propext, Quot.sound
TCSlib.Cryptography.Candidates.natToList_length_listToNat: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.natToList_val_natCast: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.mulStr_pairEncode: propext, Quot.sound
TCSlib.Cryptography.Candidates.mulStr_natToList: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.addStr_pairEncode: propext, Quot.sound
TCSlib.Cryptography.Candidates.subStr_pairEncode: propext, Quot.sound
TCSlib.Cryptography.Candidates.length_sizeStr: propext, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_add_lt_two_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_addStr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.listToNat_subStr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.leStr_pairEncode: propext, Quot.sound
TCSlib.Cryptography.Candidates.modExpStr_pairEncode: propext, Quot.sound
TCSlib.Cryptography.Candidates.primeStr_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Candidates.val_units_pow: propext, Quot.sound
TCSlib.Cryptography.Candidates.mul_lt_two_pow_add: propext, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f2/admissions.txt =====

# declarations with `sorry` in pack 03f2's files, at 0c348ff94cacf24d96d99078c9dd9e328530c8d2
TCSlib/Cryptography/Candidates/Factoring.lean:197 TCSlib.Cryptography.Candidates.fmult_easy
TCSlib/Cryptography/Candidates/Factoring.lean:322 TCSlib.Cryptography.Candidates.fmult_weakOneWay
TCSlib/Cryptography/Candidates/Factoring.lean:403 TCSlib.Cryptography.Candidates.exists_plantFactorer
TCSlib/Cryptography/Candidates/Factoring.lean:440 TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay
TCSlib/Cryptography/Candidates/Factoring.lean:507 TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw
TCSlib/Cryptography/Candidates/Factoring.lean:625 TCSlib.Cryptography.Candidates.factoringCollection_sampleClose
TCSlib/Cryptography/Candidates/Factoring.lean:671 TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le
TCSlib/Cryptography/Candidates/Factoring.lean:687 TCSlib.Cryptography.Candidates.factoringCollection_oneWay
TCSlib/Cryptography/Candidates/RSA.lean:490 TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw
TCSlib/Cryptography/Candidates/RSA.lean:528 TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr
TCSlib/Cryptography/Candidates/RSA.lean:625 TCSlib.Cryptography.Candidates.rsaSampler_spec
TCSlib/Cryptography/Candidates/RSA.lean:711 TCSlib.Cryptography.Candidates.rsaCollection_sampleClose
TCSlib/Cryptography/Candidates/RSA.lean:766 TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le
TCSlib/Cryptography/Candidates/RSA.lean:781 TCSlib.Cryptography.Candidates.rsaCollection_oneWay
TCSlib/Cryptography/Candidates/RSA.lean:865 TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw
TCSlib/Cryptography/Candidates/RSA.lean:898 TCSlib.Cryptography.Candidates.factorProb_le_rsaProb
TCSlib/Cryptography/Candidates/RSA.lean:911 TCSlib.Cryptography.Candidates.rsa_imp_factoring
TCSlib/Cryptography/Candidates/Rabin.lean:127 TCSlib.Cryptography.Candidates.oddFactorProb_le
TCSlib/Cryptography/Candidates/Rabin.lean:136 TCSlib.Cryptography.Candidates.blumFactorProb_le
TCSlib/Cryptography/Candidates/Rabin.lean:143 TCSlib.Cryptography.Candidates.blumFactoring_of_factoring
TCSlib/Cryptography/Candidates/Rabin.lean:335 TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw
TCSlib/Cryptography/Candidates/Rabin.lean:341 TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw
TCSlib/Cryptography/Candidates/Rabin.lean:457 TCSlib.Cryptography.Candidates.rabinSampler_spec
TCSlib/Cryptography/Candidates/Rabin.lean:525 TCSlib.Cryptography.Candidates.rabinCollection_sampleClose
TCSlib/Cryptography/Candidates/Rabin.lean:562 TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw
TCSlib/Cryptography/Candidates/Rabin.lean:609 TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le
TCSlib/Cryptography/Candidates/Rabin.lean:625 TCSlib.Cryptography.Candidates.rabinCollection_oneWay
TCSlib/Cryptography/Candidates/Rabin.lean:799 TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw
TCSlib/Cryptography/Candidates/Rabin.lean:818 TCSlib.Cryptography.Candidates.blumInv_spec
TCSlib/Cryptography/Candidates/Rabin.lean:835 TCSlib.Cryptography.Candidates.blumSampler_spec
TCSlib/Cryptography/Candidates/Rabin.lean:885 TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose
TCSlib/Cryptography/Candidates/Rabin.lean:905 TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le
TCSlib/Cryptography/Candidates/Rabin.lean:920 TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay
TCSlib/Cryptography/Candidates/Rabin.lean:944 TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw
TCSlib/Cryptography/Candidates/Rabin.lean:975 TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt
TCSlib/Cryptography/Candidates/Rabin.lean:990 TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/f2/lint.log =====

# scripts/style_lint.py on pack 03f2's files, at 0c348ff94cacf24d96d99078c9dd9e328530c8d2











0 findings in 10 files

## ===== TCSlib/Cryptography/Candidates/Factoring.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Factoring: `f_mult`, the factoring assumption, and the factoring-based candidates

The first candidate one-way function of [PS10, §2.3]: `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`
and `x · y` otherwise [PS10, Definition 29.1], on pairs of `n`-bit numbers; the *factoring
assumption* [PS10, Assumption 30.1]; and the three theorems resting on it: `f_mult` is a weak
one-way function [PS10, Theorem 33.5] through the one-call reduction `A''` of
[PS10, Algorithm 33.6] and the unique-factorization step [PS10, Claim 34.1]; its direct
product with `4n³` blocks is strongly one-way [PS10, Theorem 36.3] through the
random-planting one-call reduction of [PS10, Algorithm 37.4] and [PS10, Claim 36.2]; and
the factoring collection `{(p, q) ↦ pq}` is a collection of one-way functions
[PS10, Theorem 51.1].

Every statement about machines is conditional on the arithmetic hypothesis bundle
`Candidates.ArithmeticFP` (plan decision "conditional candidates", D11): `f_mult` is easy to
compute, the collection's evaluator is multiplication and its sampler runs `SamplePrime`
with a primality test, all of which need binary arithmetic on tapes.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the factoring assumption draws a uniform pair of
*distinct* primes of `Π_n` (the restriction `p ≠ q` needed by RSA and Rabin, decision log
"Rabin/RSA scope"), hands `A` the input `⟨1^n, N⟩` with `N = pq` as a `2n`-bit numeral, and
reads its answer as an `n`-bit numeral (wrong length = failure, D5); the text's
"`Pr[…] < ε(n)` for a negligible `ε`" is "`Pr[…]` is negligible" (the convention of
`FunFamily.StrongOneWay`). The reductions of Theorems 33.5 and 36.3 are the one-call
variants without primality test (the text's own remarks, pp. 34 and 37); the planting
position of Algorithm 37.4 is uniform, sampled by rejection (D10). The collection of
Theorem 51.1 uses `Π_n` (the text's `D_i` has exactly-`i/2`-bit primes, source error 24),
pairs of distinct primes, and at the degenerate parameters `n < 2`, where `Π_n` has no two
distinct primes, the domain of `n = 2`.

## Main definitions

* `TCSlib.Cryptography.Candidates.fmultNat`, `TCSlib.Cryptography.Candidates.fmult` —
  `f_mult` [PS10, Definition 29.1] as a `FunFamily` (input and output length `2n`).
* `TCSlib.Cryptography.Candidates.modulusBits`, `factorProb`,
  `TCSlib.Cryptography.Candidates.FactoringAssumption` — [PS10, Assumption 30.1] (the
  distribution `DistinctPrimes` is in `Candidates.Concrete`).
* `TCSlib.Cryptography.Candidates.oneCallFactorer` — the one-call reduction `A''`
  [PS10, Algorithm 33.6]; `TCSlib.Cryptography.Candidates.plantFactor`,
  `prodInverter` — the random-planting reduction [PS10, Algorithm 37.4] at the concrete
  level; `fmultBlocks` — `m_n = 4n³`; `fmultWeakPoly` — `q(n) = 8(n+1)²`.
* `TCSlib.Cryptography.Candidates.factoringCollection`, `factoringGen`, `factoringSampler`,
  `samplePairOut`, `collectionFactorer` — the factoring collection [PS10, Theorem 51.1].

## Main results

* `TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime` [PS10, Claim 34.1],
  `fmult_inv_factor` — an inverse of `f_mult` at a product of primes is a factor.
* `TCSlib.Cryptography.Candidates.fmult_weakOneWay` [PS10, Theorem 33.5].
* `TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay` [PS10, Theorem 36.3];
  `exists_plantFactorer` — the machine of [PS10, Algorithm 37.4].
* `TCSlib.Cryptography.Candidates.factoringCollection_oneWay` [PS10, Theorem 51.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3: Definition 29.1, Assumption 30.1, Theorem 33.5, Algorithm 33.6, Claim 34.1;
  §2.4.2: Claim 36.2, Theorem 36.3, Algorithm 37.4; §2.7: Theorem 51.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (`prodFun`, `yaoTry`: the concrete planting reduction).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The function `f_mult` [PS10, Definition 29.1] -/

/-- `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`, and `x · y` otherwise [PS10, Definition 29.1]
(the special case makes `(1, xy)` never a preimage of `xy`, footnote 2 on p. 29). -/
def fmultNat (x y : ℕ) : ℕ := if x = 1 ∨ y = 1 then 1 else x * y

/-- `f_mult` of two `n`-bit numbers fits in `2n` bits. -/
theorem fmultNat_lt {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : fmultNat x y < 2 ^ (2 * n) := by
  unfold fmultNat
  split_ifs with h1
  · have hn : n ≠ 0 := by
      rintro rfl
      simp only [pow_zero, Nat.lt_one_iff] at hx hy
      omega
    exact Nat.one_lt_two_pow (by omega)
  · rw [two_mul]
    exact mul_lt_two_pow_add hx hy

/-- **Claim 34.1** [PS10, Claim 34.1]: if `p, q` are primes and `f_mult(x', y') = pq` then
`x' ∈ {p, q}` (and `y'` is the other factor).

**Proof sketch.** `pq ≠ 1`, so `x' ≠ 1`, `y' ≠ 1` and `x' y' = pq`. A prime factor `r` of
`x'` (`Nat.exists_prime_and_dvd`) divides `pq`, so `r ∈ {p, q}` (`Nat.Prime.dvd_mul`,
`Nat.prime_dvd_prime_iff_eq`); if `r = p` then `x' = p s` with `s y' = q`, so `s ∈ {1, q}`
(`Nat.Prime.eq_one_or_self_of_dvd`), and `s = q` would force `y' = 1`; hence `x' = p`.
Symmetrically for `r = q`. -/
theorem fmultNat_eq_mul_prime {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : fmultNat x y = p * q) : x = p ∨ x = q := by
  have hpq1 : p * q ≠ 1 := by
    intro h1
    exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h1)
  unfold fmultNat at h
  split_ifs at h with h1
  · exact absurd h.symm hpq1
  push_neg at h1
  -- the key step: a prime `r` dividing `x`, with `r ∈ {p, q}`, and the cofactor analysis
  have key : ∀ {p q : ℕ}, p.Prime → q.Prime → x * y = p * q → p ∣ x → x = p := by
    intro p q hp hq h hpx
    obtain ⟨s, rfl⟩ := hpx
    have hsy : s * y = q := by
      have : p * (s * y) = p * q := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rcases hq.eq_one_or_self_of_dvd s ⟨y, hsy.symm⟩ with hs | hs
    · rw [hs, mul_one]
    · exfalso
      apply h1.2
      rw [hs] at hsy
      have : q * y = q * 1 := by rw [hsy, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hq.pos this
  obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd h1.1
  have hrpq : r ∣ p * q := hrx.trans (Dvd.intro y h)
  rcases (Nat.Prime.dvd_mul hr).mp hrpq with hrp | hrq
  · rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp hrp] at hrx
    exact Or.inl (key hp hq h hrx)
  · rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp hrq] at hrx
    exact Or.inr (key hq hp (by rw [h, mul_comm]) hrx)

/-- **`f_mult` as a function family** [PS10, Definition 29.1, §2.3]: at parameter `n` the
input is a `2n`-bit string `(x, y)` (two `n`-bit blocks, read as numbers) and the output is
`f_mult(x, y)` as a `2n`-bit numeral.

**Deviation:** the text's `f_mult : ℕ² → ℕ` "on inputs picked uniformly from `ℕ²`" is the
family of its restrictions to pairs of `n`-bit numbers, with input length `2n` (the proof
of Theorem 33.5 fixes the input length `2n`, `|x| = |y| = n`). -/
def fmult : FunFamily where
  inLen := .mul (.const 2) .var
  outLen := .mul (.const 2) .var
  f n x := natToBits (2 * n)
    (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1)))

/-- The input length of `f_mult` at parameter `n` is `2n`. -/
@[simp] theorem fmult_inLen (n : ℕ) : fmult.inLen.eval n = 2 * n := rfl

/-- The output length of `f_mult` at parameter `n` is `2n`. -/
@[simp] theorem fmult_outLen (n : ℕ) : fmult.outLen.eval n = 2 * n := rfl

/-- Unfolding `f_mult` on a `2n`-bit string. -/
theorem fmult_f (n : ℕ) (x : Fin (2 * n) → Bool) :
    fmult.f n x = natToBits (2 * n)
      (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1))) := rfl

/-- **An inverse of `f_mult` at a product of primes is a factor** [PS10, Claim 34.1, in the
form the reductions use]: if `f_mult(x') = pq` as `2n`-bit numerals, with `p, q < 2^n`
primes, then the first `n`-bit block of `x'` reads as `p` or as `q`.

Repair (run-3 audit P7-4): the former conclusion carried a dead middle disjunct
`bitsToNat (blocks 2 n x' 1) = q`, never produced by the proof and too weak for the reductions
(`A ∨ B ∨ C` does not give `A ∨ C`); it is now the two-way disjunction about block `0`.

**Proof sketch.** Both numerals encode numbers below `2^{2n}` (`fmultNat_lt`,
`mul_lt_two_pow_add`), so `f_mult(a, b) = pq` by `natToBits_injOn`; conclude by
`fmultNat_eq_mul_prime`. -/
theorem fmult_inv_factor {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : p < 2 ^ n)
    (hqn : q < 2 ^ n) (x' : Fin (2 * n) → Bool) (h : fmult.f n x' = natToBits (2 * n) (p * q)) :
    bitsToNat (FunFamily.blocks 2 n x' 0) = p ∨ bitsToNat (FunFamily.blocks 2 n x' 0) = q := by
  rw [fmult_f] at h
  have hlt : p * q < 2 ^ (2 * n) := by rw [two_mul]; exact mul_lt_two_pow_add hpn hqn
  exact fmultNat_eq_mul_prime hp hq
    (natToBits_injOn (fmultNat_lt (bitsToNat_lt _) (bitsToNat_lt _)) hlt h)

/-- **`f_mult` is easy to compute** [PS10, Theorem 33.5, "clearly computable in polynomial
time"], given binary multiplication and comparison (`ArithmeticFP`).

**Proof sketch.** The evaluator on `⟨1^n, w⟩` (`w` the `2n`-bit input) is an FP function:
`x := w.take n` and `y := w.drop n` (`Complexity.polyTimeComputable_pairTakePoly var`,
`polyTimeComputable_pairDropPoly var` on `⟨1^n, w⟩`), the tests `x = 1`, `y = 1` by two
comparisons with the numeral `[true]` (`H.le` on `⟨x, [true]⟩` and `⟨[true], x⟩`,
`polyTimeComputable_and`), the branch (`polyTimeComputable_ite`) between the constant
numeral `natToList (2n) 1 = 0^{2n-1} 1` (`polyTimeComputable_unaryPoly` mapped to zeros by
`polyTimeComputable_blockMap (const 1)`, then the last bit set) and `H.mul` on `⟨x, y⟩`
(`mulStr_natToList`: the `(n + n)`-bit product). Correctness: `List.ofFn x` on blocks is
`(List.ofFn w).take n`/`.drop n` (`FunFamily.ofFn_blocks_symm`, `List.ofFn_mul`) and
`bitsToNat = listToNat ∘ List.ofFn` (`bitsToNat_eq_listToNat`). -/
theorem fmult_easy (H : ArithmeticFP) : fmult.Easy := by
  sorry

/-! ## The factoring assumption [PS10, Assumption 30.1] -/

/-- The modulus `N = pq` of a pair of distinct primes of `Π_n`, as a `2n`-bit numeral: the
input handed to the factoring adversary (and the value `f_mult(p, q)`). -/
def modulusBits (n : ℕ) (z : DistinctPrimes n) : Fin (2 * n) → Bool := natToBits (2 * n) (z.p * z.q)

/-- `modulusBits` is `f_mult` at `(p, q)`: `fmultNat p q = pq` since neither prime is `1`. -/
theorem modulusBits_eq_fmult (n : ℕ) (z : DistinctPrimes n) :
    modulusBits n z = natToBits (2 * n) (fmultNat z.p z.q) := by
  unfold modulusBits fmultNat
  rw [if_neg]
  push_neg
  exact ⟨z.p_prime.ne_one, z.q_prime.ne_one⟩

/-- **The factoring experiment** [PS10, Assumption 30.1]:
`Pr[(p, q) ← Π_n × Π_n, p ≠ q; N ← pq; r : A(1^n, N; r) ∈ {p, q}]`, the answer of `A` read as
an `n`-bit numeral (`NUPPT.inverter n n (2n)`, wrong length = failure).

**Deviation:** uniform pair of *distinct* primes; `A` receives `1^n`; `N` as a `2n`-bit
numeral; `n`-bit answer (module docstring). -/
noncomputable def factorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : DistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1) w.2 = some x ∧
      (bitsToNat x = w.1.p ∨ bitsToNat x = w.1.q)

/-- **The factoring assumption** [PS10, Assumption 30.1]: every non-uniform PPT `A`
factors `N = pq`, for a uniform pair of distinct primes `p, q ∈ Π_n`, with negligible
probability.

**Deviation:** "there exists a negligible `ε` with `Pr[…] < ε(n)`" is stated as
"`Pr[…]` is negligible" (equivalent: take `ε = Pr + 2^{-n}`); see the module docstring for
the distribution and the input/output conventions. -/
def FactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => factorProb A n

/-- The factoring probability is nonnegative. -/
theorem factorProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ factorProb A n := uprob_nonneg _

/-- The factoring probability is at most one. -/
theorem factorProb_le_one (A : NUPPT) (n : ℕ) : factorProb A n ≤ 1 := uprob_le_one _

/-- At the degenerate parameters `n < 2` the factoring experiment is empty, so no machine
factors there (sanity: the assumption only constrains `n ≥ 2`). -/
theorem factorProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : factorProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold factorProb uprob
  simp

/-! ## The one-call reduction `A''` [PS10, Algorithm 33.6] -/

/-- **The one-call reduction `A''`** [PS10, Algorithm 33.6 and the remark on p. 34]:
`A''(1^n, N) := fst(A(1^n, N))`, the first `n` bits of the answer of the inverter `A` of
`f_mult`, with no primality test; the coins and advice of `A`.

**Deviation:** under D5 the inverter of the family `fmult` is activated at the parameter `n`
(input length `2n`, `FunFamily.invProbAt`), so `A''` calls `A(1^n, z')` — which is what
Algorithm 33.6 line 7 writes (source error 14 reads it as `A(1^{2n}, z')` in the text's
input-length parametrisation); the primality tests and the resampling of `A'` are dropped
(the text's `A''`).

Repair (run-3 audit P7-2): the former definition activated `A` at parameter `2n` (coins
`A.coins.subst (2·var)`, advice `A.advice (2n)`), which `fmult.invProbAt A n` (parameter `n`)
cannot be compared with; it is now `A` at parameter `n` with `A`'s own coins, and
`oneCallFactorer_coinLen` (`= A.coinLen (2n)`) is replaced by `coins_oneCallFactorer`. -/
noncomputable def oneCallFactorer (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => (fun u => (pairSndD u).take (PolyExpr.var.eval (pairFstD u).length))
      (pairEncode (NUPPT.inParam z) (A.output (NUPPT.layout (NUPPT.inParam z)
        (NUPPT.inArg z) (NUPPT.inAdvice z) (NUPPT.inCoins z)))))
    ((polyTimeComputable_pairTakePoly .var).comp (NUPPT.polyTimeComputable_inParam.pairEncode
      (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
        NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))))
    A.coins A.adv A.advice A.advice_length

/-- `A''` has the coins of `A` (so `(oneCallFactorer A).Coins n = A.Coins n`). -/
@[simp] theorem coins_oneCallFactorer (A : NUPPT) : (oneCallFactorer A).coins = A.coins := rfl

/-- **The activation of `A''`**: `A''(1^n, y; r) = (A(1^n, y; r)).take n`. -/
theorem oneCallFactorer_runAtL (A : NUPPT) (n : ℕ) (y r : List Bool) :
    (oneCallFactorer A).runAtL n y r = (A.runAtL n y r).take n := by
  unfold oneCallFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- The polynomial `q(n) = 8(n + 1)²` of the weak one-wayness of `f_mult`
[PS10, Theorem 33.5: `q(n) = 8n²`].

**Deviation:** `(n + 1)²` instead of `n²` (`q(0) > 0` is required by `WeakOneWay`); the
bound `1 - 1/(8(n+1)²)` is weaker than the text's. -/
def fmultWeakPoly : PolyExpr := PolyExpr.normal 8 2

/-- `q(n) = 8(n+1)²`. -/
theorem eval_fmultWeakPoly (n : ℕ) : fmultWeakPoly.eval n = 8 * (n + 1) ^ 2 := rfl

/-- **Theorem 33.5** [PS10, Theorem 33.5]: under the factoring assumption (and the arithmetic
hypotheses), `f_mult` is a weak one-way function: for every non-uniform PPT `A` and all
large `n`, `Pr[x, y ← {0,1}^n : f_mult(A(1^n, xy)) = xy] ≤ 1 - 1/(8(n+1)²)`.

**Deviation:** the adversary of the family receives `1^n` where the text writes `1^{2n}`
(the parameter is `n`, the input length `2n`; interderivable by `polyTimeComputable_unaryPoly`,
D5); `q(n) = 8(n+1)²` (`fmultWeakPoly`); the reduction is the one-call `A''` without
primality test; the factoring distribution is on distinct primes (module docstring).

**Proof sketch.** *Easy:* `fmult_easy H`. *Hard:* take `q := fmultWeakPoly` (positive) and
fix `A`. Suppose the bound fails infinitely often: `1 - 1/q(n) < fmult.invProbAt A n` for
`n` in an infinite set, and let `A'' := oneCallFactorer A` (same coins,
`coins_oneCallFactorer`; no reparametrisation: `invProbAt` and `factorProb` both activate
at parameter `n`, run-3 audit P7-2). On the event `S(x, r)` "`A(1^n, f_mult(x); r)` decodes
to a preimage `x'`" (`FunFamily.invProbAt_eq_uprob`, `NUPPT.inverter_eq_some_iff`) with `x`
a `2n`-bit string whose blocks read as primes `p, q`, `fmult_inv_factor` shows that block `0`
of `x'` reads as `p` or `q`, and block `0` is what `A''` returns: `oneCallFactorer_runAtL`,
`NUPPT.runAt_eq`, `(List.ofFn x').take n = List.ofFn (blocks 2 n x' 0)`
(`FunFamily.ofFn_blocks_symm`, `List.ofFn_succ`, `List.take_left`), so `A''` factors
`N = f_mult(x) = modulusBits` (`modulusBits_eq_fmult`) on `S`. Condition on `E` = "both blocks
prime" (`one_sub_div_le_uprob_subtype` with `δ = 1/(4n²)` from
`one_div_le_uprob_prime_pair_bits` transported along `FunFamily.blocks 2 n` and
`piFinTwoEquiv`, `uprob_subtype_prod_eq`): `Pr[S | E] ≥ 1 - 4n²/(8(n+1)²) ≥ 1/2`.
Transport the subtype to `Π_n × Π_n` by `primesPairEquiv` (`uprob_comp_equiv`), drop the
diagonal by `uprob_le_uprob_subtype_add` with `E' = (p ≠ q)`, `uprob_diag` and
`one_div_card_primes_le`: `factorProb A'' n ≥ 1/2 - 2n/2^n ≥ 1/4` for the infinitely many
`n ≥ 6`, contradicting `hF A''` by `not_negligible_iff` (`c = 1`). -/
theorem fmult_weakOneWay (H : ArithmeticFP) (hF : FactoringAssumption) : fmult.WeakOneWay := by
  sorry

/-! ## Hardness amplification for `f_mult` [PS10, Theorem 36.3] -/

/-- The number of blocks `m_n = 4n³` of [PS10, Theorem 36.3]. -/
def fmultBlocks : PolyExpr := .mul (.const 4) (.pow .var 3)

/-- `m_n = 4n³`. -/
@[simp] theorem eval_fmultBlocks (n : ℕ) : fmultBlocks.eval n = 4 * n ^ 3 := rfl

/-- The input length of `f_mult^{m_n}` at parameter `n` is `4n³ · 2n = 8n⁴` (the text's `n'`). -/
theorem fmult_prod_inLen (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := rfl

/-- **The total inverter of the direct product** induced by the machine `A` at parameter
`n`: encode the tuple of `m_n` values as a `8n⁴`-bit string (`FunFamily.blocks`), run
`A(1^n, ·)`, decode the answer as a tuple of `m_n` inputs, the all-zero tuple on a
wrong-length answer (the default of `invProbOpt_le_invProb`). -/
noncomputable def prodInverter (A : NUPPT) (n : ℕ) :
    (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) → A.Coins n →
      (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) :=
  fun ys r => FunFamily.blocks (fmultBlocks.eval n) (2 * n)
    ((A.inverter n ((fmult.prod fmultBlocks).inLen.eval n) ((fmult.prod fmultBlocks).outLen.eval n)
      ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false))

/-- **The random-planting one-call reduction** [PS10, Algorithm 37.4, one-call variant
without primality test] at the concrete level: on the challenge `N` with coins
`(i, (x⃗, y⃗), r)`, plant `N` at position `i` of `f'(x⃗, y⃗)` (`OneWay.yaoTry`), call the
inverter `B` of the direct product and return the first `n`-bit block (`x'_i`) of its
`i`-th answer.

**Deviation:** the position `i` is uniform instead of "the first prime pair" and no
primality test is made (the text's exercise, p. 37); the output is the first block of the
`i`-th answer ("Output `x'_i`"), which `fmult_inv_factor` shows to be a factor whenever
the answer is a preimage. -/
def plantFactor {n : ℕ} {ρ : Type*}
    (B : (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) → ρ →
      (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)))
    (N : Fin (2 * n) → Bool)
    (c : Fin (fmultBlocks.eval n) × ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × ρ)) :
    Fin n → Bool :=
  FunFamily.blocks 2 n (OneWay.yaoTry (fmult.f n) B N c) 0

/-- **The machine of Algorithm 37.4** [PS10, Algorithm 37.4]: for every inverter `A` of the
direct product there is a non-uniform PPT `A''` whose factoring probability is, up to the
statistical term `2^{-n}` of the rejection-sampled position, at least the probability that
the concrete planting reduction `plantFactor (prodInverter A n)` with ideal uniform coins
outputs a factor of `N = pq` for a uniform pair of distinct primes.

Repair (run-3 audit P7-5): the former sketch read `k n := m n` bits per position trial, for
which every trial fails with probability `1 − m/2^m ≥ 1/2` (`m ≥ 4`) and
`uprob_rejectionSample_none_le_half_pow` (`2^k ≤ 2m`) does not apply; the position is now
sampled from `k n := Nat.size (m n)` bits.

**Proof sketch.** `A''` is `NUPPT.ofPolyTime` of an FP function of the raw input
`⟨⟨⟨1^n, N⟩, α⟩, r⟩` with coins `add (mul var Bp) (add (mul m (mul (const 2) var)) A.coins)`,
where `m = fmultBlocks` and `Bp := add (mul (const 3) var) (const 3)` is the width of a
position block (`4n³ < 2^{3n+3}`, so `k n := Nat.size (m n) ≤ Bp n`, `Nat.size_le`), and advice
`α n := ⟨A.advice n, ⟨natToList (Bp n) (m n), 1^{k n}⟩⟩` (length bounded by a `PolyExpr`; the
unary `1^{k n}` is also `sizeStr` of the numeral, `H.size`): cut the coins
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly`), read the position
`i := (rejectionSample (m n) (k n) n (trials)).getD 0` from the first `k n` bits of each of the
`n` position blocks (`polyTimeComputable_pairTakePoly var` on `⟨1^{k n}, block⟩`, each trial
compared with the advice numeral by `H.le`, `polyTimeComputable_blockMap`,
`polyTimeComputable_ite`),
evaluate `f_mult` on the `m n` fresh `2n`-bit blocks (`polyTimeComputable_blockMap
(mul (const 2) var)` with the evaluator of `fmult_easy H`), plant `N` at block `i`
(`take`/`drop` at the unary offset `1^{i · 2n}`, `Turing.FinTM.computesFunInTime_unaryMul`),
call `A.output` on the layout `⟨⟨⟨1^n, z⃗⟩, A.advice n⟩, r'⟩` (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`), take block `i` of the answer when its length is `8n⁴`
(`polyTimeComputable_lenEq`, `_ite`; otherwise `0^{2n}`) and output its first `n` bits.
Functional identity: `A''.inverter n n (2n) N r = some (plantFactor (prodInverter A n) N (S n r))`
with `S n` the typed coin sampler (position by `(rejectionSample …).getD 0`, blocks by
`FunFamily.blocks`, coins verbatim), by `NUPPT.runAtL_ofPolyTime`, `NUPPT.inverter_eq_some_iff`,
`FunFamily.ofFn_blocks_symm` and `decodeFin_ofFn`. Probability: `statClose_rejectionSample
(m n) (k n) n 0` with `uprob_rejectionSample_none_le_half_pow` — its hypotheses
`m n ≤ 2^{k n}` and `2^{k n} ≤ 2 m n` are `Nat.lt_size_self` and `Nat.lt_size` at `k n − 1`
(`m n ≥ 4`) — puts the sampled position within `(1/2)^n` of uniform; `StatClose.prod` with
`StatClose.refl` on the other components,
`StatClose.comp_equiv_left` for the coin-string bijection and
`StatClose.abs_uprob_sub_le_prod` (auxiliary coins: the pair of primes) give the claim. -/
theorem exists_plantFactorer (H : ArithmeticFP) (A : NUPPT) :
    ∃ A'' : NUPPT, ∀ n, 1 ≤ n →
      uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q)
        - (1 / 2 : ℝ) ^ n ≤ factorProb A'' n := by
  sorry

/-- **Theorem 36.3** [PS10, Theorem 36.3]: under the factoring assumption (and the
arithmetic hypotheses), the direct product `f'((x₁, y₁), …, (x_{m_n}, y_{m_n})) =
(f_mult(x₁, y₁), …, f_mult(x_{m_n}, y_{m_n}))` with `m_n = 4n³` blocks is a strong one-way
function.

**Deviation:** the adversary receives `1^n` where the text writes `1^{n'}`, `n' = 8n⁴` (D5,
the deviation of `FunFamily.prod`); the reduction is the random-planting one-call variant
(`plantFactor`, `exists_plantFactorer`); factoring on distinct primes (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod (fmult_easy H)`. *Hard:* fix `A` and
suppose `fun n => (fmult.prod fmultBlocks).invProbAt A n` is not negligible;
`not_negligible_iff` gives `c` with `1/n^c ≤ invProbAt` for infinitely many `n`
(`FunFamily.invProbAt_nonneg`). `FunFamily.invProbAt_prod_eq` and `invProbOpt_le_invProb`
give `1/n^c ≤ invProb (prodFun (fmult.f n) (m n)) (prodInverter A n)` (the default
`fun _ => false` is `blocks` of the all-zero string). `invProb_prodFun_le_plant` with the
good set `G x` = "both blocks of `x` read as primes" yields
`1/n^c ≤ (1 - Pr[G])^{m n} + m n · Pr[G x ∧ f_mult(yaoTry … (f_mult x) c) = f_mult x]`;
`one_div_le_uprob_prime_pair_bits` (transported along `FunFamily.blocks 2 n` and
`piFinTwoEquiv`) gives `Pr[G] ≥ 1/(4n²)`, and `claim_36_2_half_pow` gives
`(1 - Pr[G])^{4n³} ≤ (1/2)^n`. Hence the planted experiment succeeds on a uniform good
input with probability at least `(1/n^c - (1/2)^n)/(4n³)` (`uprob_and_eq_mul_subtype`,
`uprob_le_one`). Transport the good subtype to `Π_n × Π_n` (`uprob_subtype_prod_eq`,
`primesPairEquiv`, `uprob_comp_equiv`); on it `fmult_inv_factor` turns a preimage into a
factor (`uprob_mono`, `modulusBits_eq_fmult`); drop the diagonal by
`uprob_le_uprob_subtype_add`, `uprob_diag` and `one_div_card_primes_le` to reach
`DistinctPrimes n`; `exists_plantFactorer H A` gives `A''` with
`factorProb A'' n ≥ (1/n^c - (1/2)^n)/(4n³) - 2n/2^n - (1/2)^n ≥ 1/(8 n^{c+3})` for the
infinitely many large `n`, contradicting `hF A''` through `not_negligible_iff`. -/
theorem fmult_prod_strongOneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (fmult.prod fmultBlocks).StrongOneWay := by
  sorry

/-! ## The factoring collection [PS10, Theorem 51.1] -/

/-- One truncated run of `SamplePrime(n)` [PS10, Algorithm 50.16] on a coin string: the
first `2n²` blocks of `n` bits are read (`padFin`, `NumberTheory.chunk`), the first prime
block is output, and the `n`-bit numeral of the prime `2` on failure.

Repair (run-3 audit P7-7): the fallback was `[]`; with a *prime* fallback (`natToBits n 2`
reads as `2` for `n ≥ 2`, `bitsToNat_natToBits`) the closeness lemma
`NumberTheory.statClose_samplePrime` applies to each run verbatim, and the pair fallback of
`samplePairOut`/`rsaGenParams` is taken only on the diagonal `p = q`. (For `n < 2` the
fallback reads as `0`, rejected by their validity tests.) -/
def samplePrimeL (n : ℕ) (r : List Bool) : List Bool :=
  List.ofFn ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n (padFin (2 * n ^ 2 * n) r))).getD
    (natToBits n 2))

/-- The output of the collection's sampler from two sampled blocks `a`, `b`: the pair of
`m`-bit numerals of the two numbers they read as, when these are distinct primes below `2^m`,
and the canonical default pair `encodeDistinctPrimes m default = ⟨2, 3⟩` otherwise (the D10
`getD`-default convention). -/
def samplePairOut (m : ℕ) (hm : 2 ≤ m) (a b : List Bool) : List Bool :=
  if (listToNat a).Prime ∧ (listToNat b).Prime ∧ listToNat a ≠ listToNat b ∧
      listToNat a < 2 ^ m ∧ listToNat b < 2 ^ m then
    pairEncode (natToList m (listToNat a)) (natToList m (listToNat b))
  else encodeDistinctPrimes m (DistinctPrimes.default hm)

/-- **The sampler's output is always a canonical encoding**: `samplePairOut m hm a b` is
`encodeDistinctPrimes m z` for some pair `z` of distinct primes (the sampled pair in the
accepting branch, the default pair otherwise). -/
theorem samplePairOut_eq_encode (m : ℕ) (hm : 2 ≤ m) (a b : List Bool) :
    ∃ z : DistinctPrimes m, samplePairOut m hm a b = encodeDistinctPrimes m z := by
  unfold samplePairOut
  split_ifs with h
  · exact ⟨⟨(⟨⟨listToNat a, h.2.2.2.1⟩, h.1⟩, ⟨⟨listToNat b, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩, rfl⟩
  · exact ⟨_, rfl⟩

/-- The string function of the collection's sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`:
two independent runs of `SamplePrime(n)` on the two halves of the coins, output as the pair
`⟨p, q⟩` of `(max n 2)`-bit numerals when both read as distinct primes, and the canonical
default pair `⟨2, 3⟩` otherwise (`samplePairOut`).

Repair (run-3 audit P3-1): the former output `⟨a, b⟩` with the fallback `[]` of a failed run
(rejected by `decodeDistinctPrimes`, as is `p = q`) is replaced by `samplePairOut`, so that
every output decodes (`Collection.sample_spec`). -/
def samplePairRaw (z : List Bool) : List Bool :=
  samplePairOut (max (NUPPT.inParam z).length 2) (le_max_right _ _)
    (samplePrimeL (NUPPT.inParam z).length ((NUPPT.inCoins z).take (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)))
    (samplePrimeL (NUPPT.inParam z).length ((NUPPT.inCoins z).drop (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)))

/-- **The sampler is polynomial-time** [PS10, Lemma 51.17] given a primality test: two
runs of the `SamplePrime` loop.

**Proof sketch.** Cut the coins at the unary length `1^{2n³}` (`polyTimeComputable_pairTakePoly`
/`_pairDropPoly samplePrimeCoins` on `⟨1^n, r⟩`); each half is handled by the
`iterateFind` loop of `NumberTheory.exists_samplePrime_nuppt` (`Complexity.polyTimeComputable_iterateFind`
with the step dropping `n` bits, the test `hP` on the first `n` bits, the payload those
bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
(`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
`none` branch of `iterateFind` (a constant string of unary-polynomial length,
`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
    PolyTimeComputable samplePairRaw := by
  sorry

/-- **The domain sampler of the factoring collection**: the uniform `NUPPT` running two
truncated `SamplePrime(n)` loops with `2 · 2n² · n` coins. -/
noncomputable def factoringSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_samplePairRaw H.prime)
    (.mul (.const 2) samplePrimeCoins)

/-- **The index generator of the factoring collection**: `Gen(1^n) = ⟨1^n, []⟩`, no coins
(the index is the unary parameter, as in `FunFamily.toCollection`). -/
noncomputable def factoringGen : NUPPT :=
  NUPPT.ofPolyTimeUniform
    (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)

/-- The activation of the index generator: `⟨1^n, []⟩`. -/
theorem factoringGen_runAt (n : ℕ) (r : factoringGen.Coins n) :
    factoringGen.runAt n [] r = pairEncode (List.replicate n true) [] := by
  rw [NUPPT.runAt_eq]
  unfold factoringGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The activation of the sampler on any index: `samplePairOut` of the two `SamplePrime(n)`
runs on the two halves of the coins. -/
theorem factoringSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool)
    (s : (factoringSampler H).Coins n) :
    (factoringSampler H).runAt n i s =
      samplePairOut (max n 2) (le_max_right _ _)
        (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n)))
        (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n))) := by
  rw [NUPPT.runAt_eq]
  unfold factoringSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [samplePairRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- **The factoring sampler's outputs decode and evaluate honestly** (the clause
`sample_spec` of `Collection`, [PS10, Definition 41.1 (2)]): at every parameter the output of
`factoringSampler` is the canonical encoding `encodeDistinctPrimes (max n 2) z` of some pair
`z` (`samplePairOut_eq_encode`), so it decodes to `z` (`decodeDistinctPrimes_encode`) and the
evaluator computes `f(z) = pq` on it (`mulStr_natToList`). Repair (run-3 audit P3-1). -/
theorem factoringSampler_spec (H : ArithmeticFP) (n : ℕ) (r : factoringGen.Coins n)
    (s : (factoringSampler H).Coins n) :
    ∃ z : DistinctPrimes (max (pairFstD (factoringGen.runAt n [] r)).length 2),
      decodeDistinctPrimes _ ((factoringSampler H).runAt n (pairFstD (factoringGen.runAt n [] r)) s) =
          some z ∧
        mulStr (pairSndD (pairEncode (pairFstD (factoringGen.runAt n [] r))
          ((factoringSampler H).runAt n (pairFstD (factoringGen.runAt n [] r)) s))) =
          natToList (2 * max (pairFstD (factoringGen.runAt n [] r)).length 2) (z.p * z.q) := by
  revert s
  rw [factoringGen_runAt, pairFstD_pairEncode, List.length_replicate]
  intro s
  rw [factoringSampler_runAt, pairSndD_pairEncode]
  obtain ⟨z, hz⟩ := samplePairOut_eq_encode (max n 2) (le_max_right _ _)
    (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n)))
    (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n)))
  rw [hz]
  refine ⟨z, decodeDistinctPrimes_encode _ z, ?_⟩
  simp only [encodeDistinctPrimes]
  rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]

/-- **The factoring collection** [PS10, Theorem 51.1]: indices `1^n` (`Gen(1^n) = ⟨1^n, []⟩`,
no coins, `factoringGen`), domains `D_{1^n} = {(p, q) ∈ Π_n × Π_n : p ≠ q}` encoded as `⟨p, q⟩`
with `n`-bit numerals, `f(p, q) = pq` as a `2n`-bit numeral, the sampler `factoringSampler`
(whose outputs always decode, `factoringSampler_spec`) and the evaluator `mulStr` of the
arithmetic bundle; decoding is canonical (`encodeDistinctPrimes_of_decode`).

**Deviation:** `Π_n` and distinct primes instead of the text's "`|p| = |q| = i/2`" (source
error 24); at parameters `n < 2` the domain is that of `n = 2` (`max n 2`), since `Π_n`
has no two distinct primes there (`DistinctPrimes.isEmpty_of_lt`); the index is the unary
parameter (`I = ℕ`), as in `FunFamily.toCollection`. -/
noncomputable def factoringCollection (H : ArithmeticFP) : Collection where
  D i := DistinctPrimes (max i.length 2)
  inhabitedD i := ⟨DistinctPrimes.default (le_max_right _ _)⟩
  encD i z := encodeDistinctPrimes (max i.length 2) z
  decD i w := decodeDistinctPrimes (max i.length 2) w
  decD_encD i z := decodeDistinctPrimes_encode _ z
  encD_decD _ _ _ h := encodeDistinctPrimes_of_decode h
  f i z := natToList (2 * max i.length 2) (z.p * z.q)
  gen := factoringGen
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := factoringSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval z := mulStr (pairSndD z)
  eval_poly := H.mul.comp polyTimeComputable_pairSndD
  eval_spec i z := by
    simp only [pairSndD_pairEncode, encodeDistinctPrimes]
    rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]
  sample_spec := factoringSampler_spec H

/-- The index generated by the factoring collection is `1^n`. -/
theorem factoringCollection_index (H : ArithmeticFP) (n : ℕ)
    (r : (factoringCollection H).gen.Coins n) :
    (factoringCollection H).index n r = List.replicate n true := by
  simp [Collection.index, factoringCollection, factoringGen, NUPPT.runAt_eq,
    NUPPT.runAtL_ofPolyTimeUniform, NUPPT.inParam, NUPPT.advInput]

/-- **The sampler is close to uniform** [PS10, Lemma 51.17 and Theorem 51.1, "sample two
random prime numbers"]: the decoded output of the factoring collection's sampler is within
a negligible statistical distance of the uniform pair of distinct primes.

**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := 2 (1/2)^n + 2n/2^n` for `n ≥ 2`
(negligible: `negligible_two_pow_neg`, `Negligible.mul_pow`, `Negligible.add`). For
`n ≥ 2` the index is `1^n` (`factoringCollection_index`) and the domain `DistinctPrimes n`;
the sampler's output on coins `r` is `⟨samplePrimeL n r₁, samplePrimeL n r₂⟩`
(`NUPPT.runAtL_ofPolyTimeUniform`, `samplePairRaw`), each half a `samplePrime n (2n²)` run
on `chunk` of its coins with the prime fallback `d = natToBits n 2` (`bitsToNat_natToBits`,
`Nat.prime_two`; run-3 audit P7-7), so `statClose_samplePrime n (2n²)` applies verbatim to
each run — within `(1 − 1/(2n))^{2n²} ≤ (1/2)^n` of the uniform prime
(`uprob_samplePrime_none_le_two_pow`'s bound) — and `StatClose.prod` gives the pair within
`2(1/2)^n` of uniform on `Π_n × Π_n`. The output `samplePairOut` re-encodes the two blocks
with `n`-bit numerals when they read as distinct primes (`bitsToNat_eq_listToNat`,
`natToBits_bitsToNat`: the numeral of an `n`-bit block is the block) and is the default pair
on the diagonal `p = q` (a failed run outputs the prime `2`, so no other case is left), so
against the uniform `some x` on `DistinctPrimes n` the extra error is the diagonal
`uprob_diag`, bounded by `one_div_card_primes_le`; combine with `StatClose.trans` and
`StatClose.map`. -/
theorem factoringCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (factoringCollection H).SampleClose δ := by
  sorry

/-- **The reduction from the collection to factoring** [PS10, proof of Theorem 51.1, "the
factoring assumption states that inverting `f_i` is hard"]: `A_fact(1^n, N) :=
fst(A(1^n, ⟨1^n, N⟩))`, the first component of the pair answered by an inverter `A` of the
collection at the index `1^n`; same coins and advice as `A`. -/
noncomputable def collectionFactorer (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => pairFstD (A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inParam z) (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z))))
    (polyTimeComputable_pairFstD.comp (A.polyTimeComputable_output.comp
      (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
        (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg)
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)))
    A.coins A.adv A.advice A.advice_length

/-- `collectionFactorer` has the coins of `A`. -/
@[simp] theorem coins_collectionFactorer (A : NUPPT) : (collectionFactorer A).coins = A.coins := rfl

/-- **The activation of the reduction**: `A_fact(1^n, y; r) = fst(A(1^n, ⟨1^n, y⟩; r))`. -/
theorem collectionFactorer_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : (collectionFactorer A).Coins n) :
    (collectionFactorer A).runAt n y r = pairFstD (A.runAt n (pairEncode (List.replicate n true) y) r) := by
  rw [NUPPT.runAt_eq]
  unfold collectionFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- **Inverting the collection factors** [PS10, proof of Theorem 51.1]: for `n ≥ 2`, the
inversion probability of `A` against the factoring collection is at most the factoring
probability of `collectionFactorer A`.

**Proof sketch.** The generator has no coins, so `Collection.invProbAt` is the inner
probability at the index `1^n` (`OneWay.uexp_const`, `factoringCollection_index`), whose
domain is `DistinctPrimes n` (`max n 2 = n`) and whose encoded value `f_i(p, q)` is
`natToList (2n) (pq) = List.ofFn (modulusBits n z)`. If `A`'s answer decodes
(`decodeDistinctPrimes`) to `(p', q')` with `natToList (2n) (p'q') = natToList (2n) (pq)`,
then `p'q' = pq` (`natToList_injOn`, `DistinctPrimes.mul_lt`) and `p' ∈ {p, q}`
(`fmultNat_eq_mul_prime` with `fmultNat p' q' = p'q'`, `modulusBits_eq_fmult`); the first
component of the answer is the `n`-bit numeral of `p'` (`decodeFin`,
`length_eq_of_decodeFin_eq_some`), which `collectionFactorer_runAt` returns and
`NUPPT.inverter` decodes to `natToBits n p'` (`natToBits_bitsToNat`); conclude by
`uprob_mono` with the coin types identified (`coins_collectionFactorer`). -/
theorem factoringCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (factoringCollection H).invProbAt A n ≤ factorProb (collectionFactorer A) n := by
  sorry

/-- **Theorem 51.1** [PS10, Theorem 51.1]: under the factoring assumption (and the
arithmetic hypotheses), the factoring collection `{f_i(p, q) = pq}` is a collection of
one-way functions.

**Deviation:** see `factoringCollection` (`Π_n`, distinct primes, degenerate parameters)
and the module docstring.

**Proof sketch.** The sampling clause is `factoringCollection_sampleClose H`. For the
hardness clause fix `A`: `factoringCollection_invProbAt_le H A` bounds the inversion
probability by `factorProb (collectionFactorer A) n` for `n ≥ 2`, which is negligible by
`hF (collectionFactorer A)`; conclude with `Negligible.mono` (`Collection.invProbAt_nonneg`,
`factorProb_nonneg`, threshold `n₀ = 2`). -/
theorem factoringCollection_oneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (factoringCollection H).OneWay := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/RSA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# RSA: the RSA assumption, the RSA collection, RSA ⟹ factoring, RSA trapdoor permutations

The RSA material of [PS10, §2.9–§2.11]: the *RSA assumption* [PS10, Assumption 53.1]; the
collection `RSA = {f_{N,e}(x) = x^e mod N}` with indices `(N, e)`, `N = pq`, `e ∈ Z*_{Φ(N)}`,
domain `Z_N^*`, which is a collection of one-way functions under the RSA assumption
[PS10, Theorem 53.2] because `x ↦ x^e` permutes `Z_N^*` [PS10, Theorem 54.3]; the
implication RSA assumption ⟹ factoring assumption through the adversary `A'` of
[PS10, Algorithm 55.3] [PS10, Theorem 55.2]; and the trapdoor collection with
`Gen(1^n) = ((N, e), d)`, `ed ≡ 1 (mod Φ(N))`, `f⁻¹_{N,d}(y) = y^d mod N`
[PS10, Theorem 57.2].

Conventions (plan decisions D3–D5, D10, D11 and the decision log "Rabin/RSA scope"). The
modulus is `N = pq` for a uniform pair of *distinct* primes `p, q ∈ Π_n`
(`Candidates.DistinctPrimes`), so that `Φ(N) = (p−1)(q−1)`; the exponent `e` is uniform in
`Z*_{Φ(N)}` and `y` uniform in `Z_N^*`; the adversary receives `⟨1^n, ⟨N, ⟨e, y⟩⟩⟩` with
`2n`-bit numerals and its answer is read as a `2n`-bit numeral `x` with `x^e ≡ y (mod N)`.
Indices of the collection are the strings `⟨N, e⟩`; the domain at an index is `Z_N^*`
when the index is *valid* (`N ≠ 0`, `gcd(e, Φ(N)) = 1`) and the one-element group `Z_1^*`
otherwise, so that `f_{N,e}` is a permutation of the domain at *every* string index (the
frozen `PermCollection` quantifies over all strings) while the evaluator is one modular
exponentiation. The generator runs two truncated `SamplePrime` loops, falls back to the
pair `(2, 3)` when they fail or coincide, and samples `e` by rejection over bit strings of
the length of `Φ(N)` (`sampleUnitL`); the domain sampler samples `Z_N^*` the same way.
Every machine statement is conditional on the arithmetic bundle `ArithmeticFP`.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. In particular the RSA assumption is stated on distinct primes (the
text's `Φ(N) = (p−1)(q−1)` needs `p ≠ q`, source error 5), the honest samplers are
truncated rejection samplers whose laws are within `rsaGenErr n` of the ideal ones (D10), the
generator outputs the trapdoor `⟨N, d⟩` (the inverter of Definition 56.1 receives the
trapdoor only), and at the degenerate parameters `n < 2` the generator works at `n = 2`.

## Main definitions

* `TCSlib.Cryptography.Candidates.rsaProb`, `TCSlib.Cryptography.Candidates.RSAAssumption`
  — [PS10, Assumption 53.1].
* `TCSlib.Cryptography.Candidates.rsaPerm` — the permutation `x ↦ x^e` of `Z_N^*`
  [PS10, Theorem 54.3].
* `TCSlib.Cryptography.Candidates.RSAParams`, `rsaGenParams`, `rsaGenRaw`, `rsaGen`,
  `sampleUnitL`, `unitSampleStr`, `rsaSampler`, `rsaInv` — the generator, domain sampler and
  trapdoor inverter.
* `TCSlib.Cryptography.Candidates.rsaTrapdoor` — the RSA collection of trapdoor permutations
  [PS10, Theorem 57.2]; `TCSlib.Cryptography.Candidates.rsaCollection` — its underlying
  collection [PS10, Theorem 53.2].
* `TCSlib.Cryptography.Candidates.rsaFromFactorStep`, `rsaFromFactorer` — the adversary
  `A'` of [PS10, Algorithm 55.3]; `rsaBreaker` — the RSA adversary of an inverter of the
  collection.

## Main results

* `TCSlib.Cryptography.Candidates.rsaPerm_symm_apply`, `pushesUniform_rsaPerm`
  [PS10, Theorem 54.3] (proved).
* `TCSlib.Cryptography.Candidates.rsaCollection_oneWay` [PS10, Theorem 53.2].
* `TCSlib.Cryptography.Candidates.rsa_imp_factoring` [PS10, Theorem 55.2];
  `rsaFromFactorStep_correct` — Algorithm 55.3 inverts whenever the factor is right (proved).
* `TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay` [PS10, Theorem 57.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.9: Assumption 53.1, Theorem 53.2, Theorem 54.3; §2.10: Theorem 55.2, Algorithm 55.3;
  §2.11: Definition 56.1, Theorem 57.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The RSA assumption [PS10, Assumption 53.1] -/

/-- The input `⟨N, ⟨e, y⟩⟩` handed to the RSA adversary at parameter `n`: the modulus
`N = pq`, the exponent `e ∈ Z*_{Φ(N)}` and the challenge `y ∈ Z_N^*`, all as `2n`-bit
numerals [PS10, Assumption 53.1]. -/
def rsaInput (n : ℕ) (z : DistinctPrimes n) (e : (ZMod (Nat.totient (z.p * z.q)))ˣ)
    (y : (ZMod (z.p * z.q))ˣ) : List Bool :=
  pairEncode (natToList (2 * n) (z.p * z.q))
    (pairEncode (natToList (2 * n) (e : ZMod (Nat.totient (z.p * z.q))).val)
      (natToList (2 * n) (y : ZMod (z.p * z.q)).val))

/-- **The RSA experiment** [PS10, Assumption 53.1]:
`Pr[p, q ← Π_n, p ≠ q; N ← pq; e ← Z*_{Φ(N)}; y ← Z_N^*; x ← A(1^n, N, e, y) : x^e ≡ y (mod N)]`,
the average over the uniform pair of distinct primes of the probability, over `e`, `y` and
the coins of `A`, that the answer of `A` decodes to a `2n`-bit numeral `x` with
`x^e = y` in `Z_N`.

**Deviation:** distinct primes; `A` receives `1^n`; `2n`-bit numerals; wrong-length answers
fail (module docstring). -/
noncomputable def rsaProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun z : DistinctPrimes n =>
    uprob fun w : (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
      ∃ x : Fin (2 * n) → Bool,
        decodeFin (2 * n) (A.runAt n (rsaInput n z w.1 w.2.1) w.2.2) = some x ∧
          ((bitsToNat x : ℕ) : ZMod (z.p * z.q)) ^ (w.1 : ZMod (Nat.totient (z.p * z.q))).val =
            (w.2.1 : ZMod (z.p * z.q))

/-- **The RSA assumption** [PS10, Assumption 53.1]: every non-uniform PPT computes `e`-th
roots modulo a random `N = pq` with negligible probability.

**Deviation:** "`Pr[…] < ε(n)` for a negligible `ε`" is "`Pr[…]` is negligible"; see the
module docstring for the distribution and the input/output conventions. -/
def RSAAssumption : Prop := ∀ A : NUPPT, Negligible fun n => rsaProb A n

/-- The RSA probability is nonnegative. -/
theorem rsaProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ rsaProb A n := by
  unfold rsaProb uexp
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The RSA probability is at most one. -/
theorem rsaProb_le_one (A : NUPPT) (n : ℕ) : rsaProb A n ≤ 1 := by
  rcases isEmpty_or_nonempty (DistinctPrimes n) with h | h
  · unfold rsaProb uexp
    simp
  · unfold rsaProb
    exact (OneWay.uexp_mono fun z => uprob_le_one _).trans (OneWay.uexp_const 1).le

/-- At the degenerate parameters `n < 2` the RSA experiment is empty. -/
theorem rsaProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : rsaProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold rsaProb uexp
  simp

/-! ## The RSA permutation [PS10, Theorem 54.3] -/

/-- **`x ↦ x^e` is a permutation of `Z_N^*`** [PS10, Theorem 54.3] for `e` coprime to
`Φ(N)`, packaged as an `Equiv` (`NumberTheory.rsa_pow_bijective`). -/
noncomputable def rsaPerm (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N)) :
    (ZMod N)ˣ ≃ (ZMod N)ˣ :=
  Equiv.ofBijective (fun x => x ^ e) (rsa_pow_bijective he)

/-- `rsaPerm` is `x ↦ x^e`. -/
@[simp] theorem rsaPerm_apply (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N))
    (x : (ZMod N)ˣ) : rsaPerm N e he x = x ^ e := rfl

/-- **The inverse map is `y ↦ y^d`** [PS10, Theorem 54.3]: if `ed ≡ 1 (mod Φ(N))` then
`(rsaPerm N e)⁻¹ y = y^d`. -/
theorem rsaPerm_symm_apply (N e d : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N))
    (hed : e * d ≡ 1 [MOD Nat.totient N]) (y : (ZMod N)ˣ) :
    (rsaPerm N e he).symm y = y ^ d := by
  apply (rsaPerm N e he).injective
  rw [Equiv.apply_symm_apply, rsaPerm_apply, ← pow_mul, mul_comm, pow_mul]
  exact (rsa_pow_pow hed y).symm

/-- **`x ↦ x^e` pushes the uniform distribution on `Z_N^*` to itself** [PS10, proof of
Theorem 53.2: "the distributions `{(e, x^e)}` and `{(e, y)}` are identical"]. -/
theorem pushesUniform_rsaPerm (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N)) :
    HardcoreBit.PushesUniform (fun x : (ZMod N)ˣ => x ^ e) :=
  HardcoreBit.pushesUniform_equiv (rsaPerm N e he)

/-- **The decryption exponent from the modular inverse**: for `gcd(e, Φ) = 1`,
`d := (e⁻¹ : Z_Φ).val` satisfies `ed ≡ 1 (mod Φ)` [PS10, Theorem 54.3, "let `d` be its
inverse"; computed by `ExtendedEuclid`, Algorithm 43.2]. -/
theorem mul_inv_val_modEq (e Φ : ℕ) (h : Nat.Coprime e Φ) :
    e * ((e : ZMod Φ)⁻¹).val ≡ 1 [MOD Φ] := by
  have h1 := ZMod.coe_mul_inv_eq_one e h
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_one_eq_one_mod] at h2
  show e * ((e : ZMod Φ)⁻¹).val % Φ = 1 % Φ
  rw [Nat.mul_mod]
  rw [Nat.mul_mod, Nat.mod_mod] at h2
  exact h2

/-! ## Indices, domains and encodings of the RSA collection -/

/-- The modulus `N` read from the index `⟨N, e⟩`. -/
def rsaN (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The exponent `e` read from the index `⟨N, e⟩`. -/
def rsaE (i : List Bool) : ℕ := listToNat (pairSndD i)

/-- An index `⟨N, e⟩` is *valid* when `N ≠ 0` and `gcd(e, Φ(N)) = 1`, the condition under
which `x ↦ x^e` permutes `Z_N^*` [PS10, Theorem 54.3]. (Not efficiently decidable from the
index — the generator only ever outputs valid indices.) -/
def RSAValid (i : List Bool) : Prop := rsaN i ≠ 0 ∧ Nat.Coprime (rsaE i) (Nat.totient (rsaN i))

instance : DecidablePred RSAValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The modulus of the domain at an index: `N` for a valid index, `1` otherwise (so that the
domain is always a finite group). -/
def rsaMod (i : List Bool) : ℕ := if RSAValid i then rsaN i else 1

instance (i : List Bool) : NeZero (rsaMod i) := by
  unfold rsaMod
  split_ifs with h
  · exact ⟨h.1⟩
  · exact ⟨one_ne_zero⟩

/-- `rsaMod` of a valid index is `N`. -/
theorem rsaMod_of_valid {i : List Bool} (h : RSAValid i) : rsaMod i = rsaN i := if_pos h

/-- `rsaMod` of an invalid index is `1`. -/
theorem rsaMod_of_not_valid {i : List Bool} (h : ¬ RSAValid i) : rsaMod i = 1 := if_neg h

/-- `rsaMod i ≤ 2^{|N|}` where `|N|` is the width of the modulus numeral. -/
theorem rsaMod_le (i : List Bool) : rsaMod i ≤ 2 ^ (pairFstD i).length := by
  unfold rsaMod
  split_ifs with h
  · exact (listToNat_lt_two_pow _).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits in the width of the modulus numeral. -/
theorem val_lt_two_pow (i : List Bool) (x : (ZMod (rsaMod i))ˣ) :
    (x : ZMod (rsaMod i)).val < 2 ^ (pairFstD i).length :=
  lt_of_lt_of_le (ZMod.val_lt _) (rsaMod_le i)

/-- The number encoding an element of the domain: its residue for a valid index, and the
canonical representative `1 mod N` of the one-element domain of an invalid index. -/
def rsaEncVal (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : ℕ :=
  if RSAValid i then (x : ZMod (rsaMod i)).val else 1 % rsaN i

/-- The string encoding of an element of `D_{⟨N, e⟩}`: `rsaEncVal` as a numeral of the width
of the modulus numeral. -/
def rsaEnc (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : List Bool :=
  natToList (pairFstD i).length (rsaEncVal i x)

/-- The decoder of `D_{⟨N, e⟩}`: for a valid index, a numeral of the right width reading as a
number below `N` coprime to `N` (`ZMod.unitOfCoprime`); for an invalid index, the canonical
string of the one-element domain. -/
def rsaDec (i : List Bool) (w : List Bool) : Option (ZMod (rsaMod i))ˣ :=
  if RSAValid i then
    if h : w.length = (pairFstD i).length ∧ listToNat w < rsaMod i ∧
        Nat.Coprime (listToNat w) (rsaMod i) then
      some (ZMod.unitOfCoprime (listToNat w) h.2.2)
    else none
  else if w = natToList (pairFstD i).length (1 % rsaN i) then some 1 else none

/-- `f_{N,e}(x) = x^e mod N` as a string function on the encoded element, mirroring the
evaluator `modExpStr` [PS10, Theorem 53.2]. -/
def rsaF (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : List Bool :=
  natToList (pairFstD i).length (listToNat (rsaEnc i x) ^ rsaE i % rsaN i)

/-- The evaluator of the RSA collection on `⟨⟨N, e⟩, x⟩`: one modular exponentiation
`modExpStr ⟨x, ⟨e, N⟩⟩` [PS10, Theorem 53.2, "requires only one modular exponentiation"]. -/
def rsaEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD z) (pairEncode (pairSndD (pairFstD z)) (pairFstD (pairFstD z))))

/-- The evaluator computes `rsaF` on encoded elements. -/
theorem rsaEval_spec (i : List Bool) (x : (ZMod (rsaMod i))ˣ) :
    rsaEval (pairEncode i (rsaEnc i x)) = rsaF i x := by
  simp [rsaEval, rsaF, rsaE, rsaN]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rsaEval (H : ArithmeticFP) : PolyTimeComputable rsaEval :=
  H.modExp.comp (polyTimeComputable_pairSndD.pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- The permutation of `D_{⟨N, e⟩}`: `x ↦ x^e` [PS10, Theorem 54.3] for a valid index, the
identity of the one-element domain otherwise. -/
noncomputable def rsaPermAt (i : List Bool) : (ZMod (rsaMod i))ˣ ≃ (ZMod (rsaMod i))ˣ :=
  if hv : RSAValid i then
    rsaPerm (rsaMod i) (rsaE i) (by rw [rsaMod_of_valid hv]; exact hv.2)
  else Equiv.refl _

/-- **`f_{N,e}` is the encoded permutation** at every index (the clause `f_perm` of
`PermCollection`): `rsaF i x = rsaEnc i (rsaPermAt i x)`.

**Proof sketch.** Valid index: both sides are the numeral of `x.val^e mod N`
(`val_units_pow`, `listToNat_natToList`). Invalid index: the domain is `Z_1^*`, the
encoding is the canonical `1 mod N`, and `(1 mod N)^e mod N = 1 mod N` (both `0` when
`N = 1`, both `1` otherwise); the width-`0` case is trivial. -/
theorem rsaF_perm (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : rsaF i x = rsaEnc i (rsaPermAt i x) := by
  rcases Nat.eq_zero_or_pos (pairFstD i).length with hl | hl
  · simp [rsaF, rsaEnc, hl, natToList_zero]
  by_cases hv : RSAValid i
  · have hM : rsaMod i = rsaN i := rsaMod_of_valid hv
    have hlt := val_lt_two_pow i x
    simp only [rsaF, rsaEnc, rsaEncVal, if_pos hv, rsaPermAt, dif_pos hv, rsaPerm_apply,
      listToNat_natToList hlt, val_units_pow]
    congr 1
    exact congrArg (fun M => (x : ZMod (rsaMod i)).val ^ rsaE i % M) hM.symm
  · have h1 : 1 % rsaN i < 2 ^ (pairFstD i).length :=
      lt_of_le_of_lt (Nat.mod_le _ _) (Nat.one_lt_two_pow hl.ne')
    simp only [rsaF, rsaEnc, rsaEncVal, if_neg hv, rsaPermAt, dif_neg hv, Equiv.refl_apply,
      listToNat_natToList h1]
    congr 1
    rcases Nat.lt_or_ge (rsaN i) 2 with h2 | h2
    · interval_cases (rsaN i)
      · simp
      · simp [Nat.mod_one]
    · rw [Nat.mod_eq_of_lt (by omega : 1 < rsaN i), one_pow, Nat.mod_eq_of_lt (by omega : 1 < rsaN i)]

/-- **Decoding inverts encoding** (the clause `decD_encD` of `Collection`).

**Proof sketch.** Valid index: the encoding has the right width, reads as `x.val < N`
coprime to `N`, and `ZMod.unitOfCoprime x.val = x` (`ZMod.natCast_zmod_val`). Invalid index:
the domain `Z_1^*` is a singleton (`ZMod.subsingleton_iff`). -/
theorem rsaDec_rsaEnc (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : rsaDec i (rsaEnc i x) = some x := by
  by_cases hv : RSAValid i
  · have hlt := val_lt_two_pow i x
    have hl : listToNat (rsaEnc i x) = (x : ZMod (rsaMod i)).val := by
      simp only [rsaEnc, rsaEncVal, if_pos hv]
      exact listToNat_natToList hlt
    rw [rsaDec, if_pos hv, dif_pos ⟨by simp [rsaEnc], by rw [hl]; exact ZMod.val_lt _,
      by rw [hl]; exact ZMod.val_coe_unit_coprime x⟩]
    congr 1
    ext
    simp [ZMod.coe_unitOfCoprime, hl]
  · haveI : Subsingleton (ZMod (rsaMod i)) := ZMod.subsingleton_iff.2 (rsaMod_of_not_valid hv)
    rw [rsaDec, if_neg hv, if_pos (by simp [rsaEnc, rsaEncVal, if_neg hv])]
    congr 1
    exact Units.ext (Subsingleton.elim _ _)

/-- **Decoding is canonical** (the clause `Collection.encD_decD` of `rsaTrapdoor`; gate 03b,
finding 1): a string that `rsaDec i` decodes to `x` is `rsaEnc i x`. At a valid index it is a
numeral of the modulus width reading as `x.val < N` (`natToList_val_natCast`); at an invalid
index it is the canonical string of `1 mod N`. -/
theorem rsaEnc_of_rsaDec {i w : List Bool} {x : (ZMod (rsaMod i))ˣ} (h : rsaDec i w = some x) :
    rsaEnc i x = w := by
  rw [rsaDec] at h
  split_ifs at h with hv hw hw'
  · rw [← Option.some.inj h, rsaEnc, rsaEncVal, if_pos hv, ZMod.coe_unitOfCoprime]
    exact natToList_val_natCast hw.1 hw.2.1
  · rw [← Option.some.inj h, rsaEnc, rsaEncVal, if_neg hv, hw']

/-! ## The generator, the domain sampler and the inverter -/

/-- The width `B(n) = 2(n + 2)` of a coin block of the rejection samplers (at least the bit
length of any modulus `N < 2^{2 max(n,2)}`). -/
def rsaBlock : PolyExpr := .mul (.const 2) (.add .var (.const 2))

/-- The number of trials `T(n) = (4n + 8) n` of the rejection samplers: with acceptance rate
at least `1/(2 ⌈log₂ N⌉) ≥ 1/(4n + 8)` per trial (`NumberTheory.le_totient_mul_log_succ`,
C9), the failure probability is at most `e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). -/
def rsaTrials : PolyExpr := .mul (.add (.mul (.const 4) .var) (.const 8)) .var

/-- The coins of the domain sampler: `T(n)` blocks of `B(n)` bits. -/
def rsaSampleCoins : PolyExpr := .mul rsaTrials rsaBlock

/-- The coins of the generator: two `SamplePrime` runs and one unit sampler. -/
def rsaGenCoins : PolyExpr := .add (.mul (.const 2) samplePrimeCoins) rsaSampleCoins

/-- **Rejection sampling of a unit modulo `N`** from a coin list: `Candidates.rejectBlocksL`
with the acceptance test `v < N ∧ gcd(v, N) = 1` — `T` trials, trial `t` reading the first `k`
bits of the `t`-th block of `B` bits as a number `v`; `none` if every trial is rejected. With
`k` the bit length of `N`, the acceptance rate is `Φ(N)/2^k ≥ 1/(2k)` [PS10, Theorem 53.2,
"sample a random element from `Z*_{Φ(N)}`" and "the set `D_i` is also easy to sample"].
Repair (run-3 audit P7-6): an instance of the shared sampler (closeness:
`statClose_rejectBlocksL`); the function is unchanged. -/
def sampleUnitL (N k B T : ℕ) (r : List Bool) : Option ℕ :=
  rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r

/-- A sampled value is below `N` and coprime to `N`. -/
theorem sampleUnitL_spec {N k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleUnitL N k B T r = some v) :
    v < N ∧ Nat.Coprime v N :=
  (rejectBlocksL_spec h).1

/-- The string function of the domain sampler on the modulus numeral `w` at parameter `n`
with coins `r`: a unit modulo `N = listToNat w` by rejection (`sampleUnitL` with the bit
length `Nat.size N` of `N`), written as a numeral of the width of `w`; the fallback `1 mod N`
on failure. -/
def unitSampleStr (w : List Bool) (n : ℕ) (r : List Bool) : List Bool :=
  natToList w.length
    ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n) r).getD
      (1 % listToNat w))

/-- The parameters output by the RSA generator at parameter `m`: distinct primes `p, q ∈ Π_m`,
an exponent `e < Φ(N)` coprime to `Φ(N)` and its inverse `d < Φ(N)`, `ed ≡ 1 (mod Φ(N))`
[PS10, Theorem 57.2, `[(N, e), d] ← Gen(1^n)`]. -/
structure RSAParams (m : ℕ) where
  /-- The pair of distinct primes. -/
  z : DistinctPrimes m
  /-- The public exponent. -/
  e : ℕ
  /-- The trapdoor exponent. -/
  d : ℕ
  /-- `e < Φ(N)`. -/
  e_lt : e < Nat.totient (z.p * z.q)
  /-- `gcd(e, Φ(N)) = 1`. -/
  e_cop : Nat.Coprime e (Nat.totient (z.p * z.q))
  /-- `d < Φ(N)`. -/
  d_lt : d < Nat.totient (z.p * z.q)
  /-- `ed ≡ 1 (mod Φ(N))`. -/
  ed : e * d ≡ 1 [MOD Nat.totient (z.p * z.q)]

namespace RSAParams

variable {m : ℕ}

/-- The modulus `N = pq`. -/
def N (P : RSAParams m) : ℕ := P.z.p * P.z.q

/-- `N < 2^{2m}`. -/
theorem N_lt (P : RSAParams m) : P.N < 2 ^ (2 * m) := P.z.mul_lt

/-- `e < 2^{2m}`. -/
theorem e_lt_two_pow (P : RSAParams m) : P.e < 2 ^ (2 * m) :=
  lt_of_lt_of_le P.e_lt ((Nat.totient_le _).trans P.N_lt.le)

/-- `d < 2^{2m}`. -/
theorem d_lt_two_pow (P : RSAParams m) : P.d < 2 ^ (2 * m) :=
  lt_of_lt_of_le P.d_lt ((Nat.totient_le _).trans P.N_lt.le)

end RSAParams

/-- **The generator's computation** [PS10, Theorem 53.2, "generate two primes `p, q`,
multiply them to generate `N`, and … sample a random element from `Z*_{Φ(N)}`";
Theorem 57.2]: two truncated `SamplePrime(m)` runs on the first two coin segments
(`samplePrimeL`), the fallback `(2, 3)` unless both are primes below `2^m` and distinct,
then `e` by `sampleUnitL` modulo `Φ(N)` on the remaining coins (fallback `e = 1`) and
`d = e⁻¹ mod Φ(N)`. The primes are drawn from `Π_{max m 2}` (the fallback needs `m ≥ 2`). -/
def rsaGenParams (m : ℕ) (r : List Bool) : RSAParams (max m 2) :=
  let L := samplePrimeCoins.eval (max m 2)
  let p := listToNat (samplePrimeL (max m 2) (r.take L))
  let q := listToNat (samplePrimeL (max m 2) ((r.drop L).take L))
  let z : DistinctPrimes (max m 2) :=
    if h : p.Prime ∧ q.Prime ∧ p ≠ q ∧ p < 2 ^ max m 2 ∧ q < 2 ^ max m 2 then
      ⟨(⟨⟨p, h.2.2.2.1⟩, h.1⟩, ⟨⟨q, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩
    else DistinctPrimes.default (le_max_right _ _)
  let Φ := Nat.totient (z.p * z.q)
  let eo := sampleUnitL Φ (Nat.size Φ) (rsaBlock.eval (max m 2)) (rsaTrials.eval (max m 2))
    (r.drop (2 * L))
  have he : eo.getD 1 < Φ ∧ Nat.Coprime (eo.getD 1) Φ := by
    match heo : eo with
    | some v => exact sampleUnitL_spec heo
    | none => exact ⟨z.one_lt_totient, Nat.coprime_one_left _⟩
  { z := z
    e := eo.getD 1
    d := ((eo.getD 1 : ZMod Φ)⁻¹).val
    e_lt := he.1
    e_cop := he.2
    d_lt := ZMod.val_lt _
    ed := mul_inv_val_modEq _ _ he.2 }

/-- The index `⟨N, e⟩` of the parameters, with `2m`-bit numerals. -/
def rsaIndexOf (m : ℕ) (P : RSAParams m) : List Bool :=
  pairEncode (natToList (2 * m) P.N) (natToList (2 * m) P.e)

/-- The trapdoor `⟨N, d⟩` of the parameters, with `2m`-bit numerals. -/
def rsaTrapOf (m : ℕ) (P : RSAParams m) : List Bool :=
  pairEncode (natToList (2 * m) P.N) (natToList (2 * m) P.d)

/-- The modulus read from `rsaIndexOf` is `N`. -/
@[simp] theorem rsaN_indexOf (m : ℕ) (P : RSAParams m) : rsaN (rsaIndexOf m P) = P.N := by
  simp [rsaN, rsaIndexOf, listToNat_natToList P.N_lt]

/-- The exponent read from `rsaIndexOf` is `e`. -/
@[simp] theorem rsaE_indexOf (m : ℕ) (P : RSAParams m) : rsaE (rsaIndexOf m P) = P.e := by
  simp [rsaE, rsaIndexOf, listToNat_natToList P.e_lt_two_pow]

/-- Generated indices are valid. -/
theorem rsaValid_indexOf (m : ℕ) (P : RSAParams m) : RSAValid (rsaIndexOf m P) :=
  ⟨by rw [rsaN_indexOf]; exact NeZero.ne (P.z.p * P.z.q),
    by rw [rsaN_indexOf, rsaE_indexOf]; exact P.e_cop⟩

/-- The domain modulus at a generated index is `N`. -/
theorem rsaMod_indexOf (m : ℕ) (P : RSAParams m) : rsaMod (rsaIndexOf m P) = P.N := by
  rw [rsaMod_of_valid (rsaValid_indexOf m P), rsaN_indexOf]

/-- The output `⟨⟨N, e⟩, ⟨N, d⟩⟩` of the generator at parameter `m` on the coins `r`. -/
def rsaGenOut (m : ℕ) (r : List Bool) : List Bool :=
  pairEncode (rsaIndexOf _ (rsaGenParams m r)) (rsaTrapOf _ (rsaGenParams m r))

/-- The string function of the generator on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`:
`rsaGenOut` at the parameter `n` read from `1^n` on the coins. -/
def rsaGenRaw (z : List Bool) : List Bool := rsaGenOut (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The generator is polynomial-time** [PS10, Theorem 53.2, "the set `I` is easy to
sample"] given the arithmetic bundle.

**Proof sketch.** Cut the coins at the unary lengths `1^{2m³}` (`polyTimeComputable_pairTakePoly`
/`_pairDropPoly samplePrimeCoins` on `⟨1^m, r⟩`, with `1^m = 1^{max n 2}` by
`polyTimeComputable_unaryPoly`); each prime is the `iterateFind` loop of
`NumberTheory.exists_samplePrime_nuppt` with the test `H.prime`; the validity test is two
`H.prime` calls, a `pairEq` test and two `H.le` comparisons with `1^m`, the fallback a
constant (`polyTimeComputable_ite`; the fallback prime `2` of a failed `samplePrimeL` run is a
constant numeral, P7-7); `N` is `H.mul`; `Φ(N) = (p−1)(q−1)` by two decrements `H.sub` on
`⟨p, [true]⟩`, `⟨q, [true]⟩` (`listToNat_subStr`) and `H.mul`; the unary bit length
`1^{Nat.size Φ}` is `H.size` (run-3 audit P7-1); the rejection loop (`sampleUnitL =
rejectBlocksL`) is `polyTimeComputable_iterateFind` over the blocks of `1^{B(m)}` bits, each
trial reading `Nat.size Φ` bits (`polyTimeComputable_pairTakePoly var` on
`⟨1^{Nat.size Φ}, block⟩`) with the tests `H.le` and `H.xgcd` (`gcd = 1`), and `d` is the
second component of `xgcdStr ⟨e, Φ⟩`; pair the numerals. -/
theorem polyTimeComputable_rsaGenRaw (H : ArithmeticFP) : PolyTimeComputable rsaGenRaw := by
  sorry

/-- **The RSA generator** `Gen(1^n) = ⟨⟨N, e⟩, ⟨N, d⟩⟩` as a uniform `NUPPT`
[PS10, Theorem 57.2, "`[(N, e), d] ← Gen(1^n)`"].

**Deviation (run-3 audit P3-5):** the trapdoor is `⟨N, d⟩` where the text's is `d`, because
`TrapdoorCollection.inv_spec` hands the inverter `⟨t, y⟩` without the index (the literal
`Inv((i, t), y)` form of Definition 56.1 (6) was not adopted); `N` is therefore carried in the
trapdoor. -/
noncomputable def rsaGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaGenRaw H) rsaGenCoins

/-- The activation of the generator: `rsaGenOut n` on the coins. -/
theorem rsaGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n) :
    (rsaGen H).runAt n [] r = rsaGenOut n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold rsaGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rsaGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, ⟨N, e⟩⟩, α⟩, r⟩`:
`unitSampleStr` on the modulus numeral. -/
def rsaSampleRaw (z : List Bool) : List Bool :=
  unitSampleStr (pairFstD (NUPPT.inArg z)) (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The unit sampler is polynomial-time** [PS10, Theorem 53.2, "the set `D_i` is also
easy to sample"]: for any polynomial-time projection `f` of the raw input to the modulus
numeral, `z ↦ unitSampleStr (f z) n (coins z)` is polynomial-time (shared by the RSA and
Rabin samplers).

**Proof sketch.** The unary bit length `1^{Nat.size N}` of `N = f z` is `H.size` (run-3
audit P7-1); the trial loop (`sampleUnitL = rejectBlocksL`) is
`polyTimeComputable_iterateFind` over the blocks of `1^{B(n)}` bits
(`polyTimeComputable_pairDropPoly`), each trial reading the first `k` bits
(`polyTimeComputable_pairTakePoly var` on `⟨1^k, block⟩`), comparing them with `N` (`H.le`)
and testing `gcd = 1` (`H.xgcd`, `pairEq` with `[true]`); the output is padded to the width
of the numeral (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_unitSampleStr (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
  sorry

/-- The domain sampler of the RSA collection is polynomial-time. -/
theorem polyTimeComputable_rsaSampleRaw (H : ArithmeticFP) : PolyTimeComputable rsaSampleRaw :=
  polyTimeComputable_unitSampleStr H (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- **The domain sampler of the RSA collection**: a uniform `NUPPT` with `T(n) B(n)` coins. -/
noncomputable def rsaSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaSampleRaw H) rsaSampleCoins

/-- The string function of the trapdoor inverter on the raw layout `⟨⟨⟨1^n, ⟨⟨N, d⟩, y⟩⟩, α⟩, r⟩`:
`y^d mod N` by one modular exponentiation [PS10, Theorem 57.2, `f⁻¹_{N,d}(y) = y^d mod N`]. -/
def rsaInvRaw (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (NUPPT.inArg z))
    (pairEncode (pairSndD (pairFstD (NUPPT.inArg z))) (pairFstD (pairFstD (NUPPT.inArg z)))))

/-- The inverter's string function is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rsaInvRaw (H : ArithmeticFP) : PolyTimeComputable rsaInvRaw :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      NUPPT.polyTimeComputable_inArg)).pairEncode
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
        NUPPT.polyTimeComputable_inArg))))

/-- **The trapdoor inverter** `Inv(1^n, ⟨⟨N, d⟩, y⟩) = y^d mod N` as a uniform `NUPPT` without
coins. -/
noncomputable def rsaInv (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaInvRaw H) (.const 0)

/-- The activation of the inverter on `⟨⟨N, d⟩, y⟩`. -/
theorem rsaInv_runAt (H : ArithmeticFP) (n : ℕ) (t y : List Bool) (s : (rsaInv H).Coins n) :
    (rsaInv H).runAt n (pairEncode t y) s =
      natToList (pairFstD t).length (listToNat y ^ listToNat (pairSndD t) % listToNat (pairFstD t)) := by
  rw [NUPPT.runAt_eq]
  unfold rsaInv
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rsaInvRaw, NUPPT.inArg, NUPPT.advInput]

/-- **The trapdoor inverter decodes to `f⁻¹_{N,e}(y) = y^d`** at every generated index
(the clause `inv_spec` of `TrapdoorCollection`, [PS10, Theorem 57.2, "`e·d = 1 mod Φ(N)`"]).

**Proof sketch.** By `rsaGen_runAt` the index is `⟨N, e⟩` and the trapdoor `⟨N, d⟩` of
`P := rsaGenParams`; the index is valid (`rsaValid_indexOf`, `rsaMod_indexOf`), so
`rsaEnc i y` is the numeral of `y.val`; `rsaInv_runAt` returns the numeral of
`y.val^d mod N = (y^d).val` (`val_units_pow`), which `rsaDec` decodes to `y^d`
(`rsaDec_rsaEnc`); and `(rsaPermAt i).symm y = y^d` by `rsaPerm_symm_apply` with `P.ed`. -/
theorem rsaInv_spec (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n)
    (y : (ZMod (rsaMod (pairFstD ((rsaGen H).runAt n [] r))))ˣ) (s : (rsaInv H).Coins n) :
    rsaDec _ ((rsaInv H).runAt n (pairEncode (pairSndD ((rsaGen H).runAt n [] r)) (rsaEnc _ y)) s) =
      some ((rsaPermAt _).symm y) := by
  revert y
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode, pairSndD_pairEncode]
  generalize rsaGenParams n (List.ofFn r) = P
  intro y
  have hv := rsaValid_indexOf _ P
  have hM := rsaMod_indexOf _ P
  have hlen : (pairFstD (rsaIndexOf _ P)).length = 2 * max n 2 := by
    simp [rsaIndexOf]
  have hed : rsaE (rsaIndexOf _ P) * P.d ≡ 1 [MOD Nat.totient (rsaMod (rsaIndexOf _ P))] := by
    rw [hM, rsaE_indexOf]; exact P.ed
  have hsymm : (rsaPermAt (rsaIndexOf _ P)).symm y = y ^ P.d := by
    unfold rsaPermAt
    rw [dif_pos hv]
    exact rsaPerm_symm_apply _ _ _ _ hed y
  have henc : listToNat (rsaEnc (rsaIndexOf _ P) y) = (y : ZMod (rsaMod (rsaIndexOf _ P))).val := by
    unfold rsaEnc rsaEncVal
    rw [if_pos hv]
    exact listToNat_natToList (val_lt_two_pow _ y)
  rw [rsaInv_runAt, hsymm]
  simp only [rsaTrapOf, pairFstD_pairEncode, pairSndD_pairEncode, length_natToList,
    listToNat_natToList P.N_lt, listToNat_natToList P.d_lt_two_pow, henc]
  have hval : (y : ZMod (rsaMod (rsaIndexOf _ P))).val ^ P.d % P.N =
      ((y ^ P.d : (ZMod (rsaMod (rsaIndexOf _ P)))ˣ) : ZMod (rsaMod (rsaIndexOf _ P))).val := by
    rw [val_units_pow]
    exact congrArg (fun M => (y : ZMod (rsaMod (rsaIndexOf _ P))).val ^ P.d % M) hM.symm
  rw [hval, ← rsaDec_rsaEnc (rsaIndexOf _ P) (y ^ P.d)]
  congr 1
  unfold rsaEnc rsaEncVal
  rw [if_pos hv, hlen]

/-- **The RSA sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index `⟨N, e⟩` is valid with modulus `N` (`rsaGen_runAt`, `rsaValid_indexOf`,
`rsaMod_indexOf`), and the sampler outputs the `2m`-bit numeral of a unit `v < N`
(`sampleUnitL_spec`, or the fallback `1 % N = 1`), which `rsaDec` decodes to
`x = ZMod.unitOfCoprime v` with `rsaEnc i x` the same numeral; `rsaEval_spec` gives the
evaluator clause.

**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`, `rsaSampleRaw`,
`unitSampleStr`, `rsaGen_runAt`), case on `sampleUnitL`; `rsaDec`'s test is discharged by
`length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp.
`Nat.coprime_one_left`; the decoded unit has value `v` (`ZMod.coe_unitOfCoprime`,
`ZMod.val_natCast`, `Nat.mod_eq_of_lt`), so `rsaEnc i x = natToList (2m) v` and
`rsaEval_spec` applies. -/
theorem rsaSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n)
    (s : (rsaSampler H).Coins n) :
    ∃ x, rsaDec (pairFstD ((rsaGen H).runAt n [] r))
        ((rsaSampler H).runAt n (pairFstD ((rsaGen H).runAt n [] r)) s) = some x ∧
      rsaEval (pairEncode (pairFstD ((rsaGen H).runAt n [] r))
        ((rsaSampler H).runAt n (pairFstD ((rsaGen H).runAt n [] r)) s)) = rsaF _ x := by
  sorry

/-! ## The RSA trapdoor collection [PS10, Theorems 53.2 and 57.2] -/

/-- **The RSA collection of trapdoor permutations** [PS10, Theorem 57.2; Theorem 53.2 for
the underlying collection]: indices `⟨N, e⟩`, domains `D_{⟨N,e⟩} = Z_N^*` (valid indices),
`f_{N,e}(x) = x^e mod N`, the generator `rsaGen`, the sampler `rsaSampler`, the evaluator
`rsaEval` (one modular exponentiation), the permutation `x ↦ x^e` [PS10, Theorem 54.3] and
the inverter `rsaInv` computing `y^d mod N` from the trapdoor `⟨N, d⟩`.

**Deviation:** module docstring (valid/invalid indices, trapdoor `⟨N, d⟩`, truncated
samplers, `max n 2`). -/
noncomputable def rsaTrapdoor (H : ArithmeticFP) : TrapdoorCollection where
  D i := (ZMod (rsaMod i))ˣ
  encD := rsaEnc
  decD := rsaDec
  decD_encD := rsaDec_rsaEnc
  encD_decD _ _ _ := rsaEnc_of_rsaDec
  f := rsaF
  gen := rsaGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := rsaSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rsaEval
  eval_poly := polyTimeComputable_rsaEval H
  eval_spec := rsaEval_spec
  sample_spec := rsaSampler_spec H
  perm := rsaPermAt
  f_perm := rsaF_perm
  inv := rsaInv H
  inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  inv_spec := rsaInv_spec H

/-- **The RSA collection** [PS10, Theorem 53.2]: the collection underlying `rsaTrapdoor`. -/
noncomputable def rsaCollection (H : ArithmeticFP) : Collection := (rsaTrapdoor H).toCollection

/-- The index generated by the RSA collection is `⟨N, e⟩` of `rsaGenParams`. -/
theorem rsaCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rsaCollection H).gen.Coins n) :
    (rsaCollection H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
  show pairFstD ((rsaGen H).runAt n [] r) = _
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]

/-- The statistical error of the honest samplers at parameter `n`:
`2 · 2^{-n}` (two `SamplePrime` failures), `2n/2^n` (the diagonal `p = q`) and `e^{-n}`
(the unit sampler), negligible. -/
noncomputable def rsaGenErr (n : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n + Real.exp (-(n : ℝ))

/-- `rsaGenErr` is negligible.

**Proof sketch.** `negligible_two_pow_neg` with `Negligible.const_mul`, `Negligible.mul_pow`
(`2n/2^n = 2 · n · (1/2)^n`) and `Negligible.mono` with `exp_neg_le_half_pow`;
`Negligible.add`. -/
theorem negligible_rsaGenErr : Negligible rsaGenErr := by
  have h1 : Negligible fun n : ℕ => (1 / 2 : ℝ) ^ n := by
    simpa [one_div] using negligible_two_pow_neg
  have h4 : Negligible fun n : ℕ => Real.exp (-(n : ℝ)) :=
    h1.mono ⟨0, fun n _ => by
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
      exact exp_neg_le_half_pow n⟩
  refine (((h1.const_mul 2).add ((h1.mul_pow 1).const_mul 2)).add h4).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold rsaGenErr
  rw [pow_one, one_div, inv_pow]
  field_simp

/-- **The domain sampler is close to uniform** [PS10, Theorem 53.2, "the set `D_i` is also
easy to sample"]: the decoded output of `rsaSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_N^*`.

**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := e^{-n}` for `n ≥ 2`. At a generated
index `⟨N, e⟩` (`rsaCollection_index`, valid by `rsaValid_indexOf`, `N = pq < 2^{2n}`) the
sampler's output is `unitSampleStr` on the numeral of `N` (`NUPPT.runAtL_ofPolyTimeUniform`,
`rsaSampleRaw`): `T(n)` trials each reading `k = Nat.size N ≤ 2n` uniform bits
(`k ≤ B(n)`), accepted iff the value is a unit; `sampleUnitL` is `rejectBlocksL` of the unit
predicate, so `statClose_rejectBlocksL` (default `1`) gives closeness `(1 - Pr[unit])^{T(n)}`
to the uniform element of `{v < 2^k | v < N ∧ gcd(v, N) = 1} ≃ Z_N^*`, decoded by `rsaDec` to
the uniform element of `Z_N^*` (`StatClose.map`, `decodeFin`-style injectivity). The acceptance rate is `Φ(N)/2^k ≥ Φ(N)/(2N) ≥ 1/(2k)`
(`Nat.lt_size_self`, `Nat.size_le`, `NumberTheory.le_totient_mul_log_succ`) `≥ 1/(4n+8)`,
and `(1 - 1/(4n+8))^{(4n+8)n} ≤ e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). Negligibility:
`exp_neg_le_half_pow`, `negligible_two_pow_neg`, `Negligible.mono`. -/
theorem rsaCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rsaCollection H).SampleClose δ := by
  sorry

/-- **The RSA adversary of an inverter of the collection** [PS10, proof of Theorem 53.2]:
`A'(1^n, ⟨N, ⟨e, y⟩⟩) := A(1^n, ⟨⟨N, e⟩, y⟩)`, a re-pairing of the input; coins and advice
of `A`. -/
noncomputable def rsaBreaker (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z))))
        (pairSndD (pairSndD (NUPPT.inArg z))))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam
      (((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
          NUPPT.polyTimeComputable_inArg))).pairEncode
        (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
          NUPPT.polyTimeComputable_inArg)))
      NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    A.coins A.adv A.advice A.advice_length

/-- `rsaBreaker` has the coins of `A`. -/
@[simp] theorem coins_rsaBreaker (A : NUPPT) : (rsaBreaker A).coins = A.coins := rfl

/-- The activation of `rsaBreaker`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = A(1^n, ⟨⟨N, e⟩, y⟩; r)`. -/
theorem rsaBreaker_runAt (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaBreaker A).Coins n) :
    (rsaBreaker A).runAt n (pairEncode N (pairEncode e y)) r =
      A.runAt n (pairEncode (pairEncode N e) y) r := by
  rw [NUPPT.runAt_eq]
  unfold rsaBreaker
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- **Inverting the RSA collection breaks the RSA assumption** [PS10, proof of Theorem 53.2]:
for `n ≥ 2`, the inversion probability of `A` against the RSA collection is at most the RSA
probability of `rsaBreaker A` plus the statistical error of the generator.

**Proof sketch.** At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid), the domain
is `Z_N^*` (`rsaMod_indexOf`), `f_{N,e}(x)` is the numeral of `(x^e).val` (`rsaF_perm`,
`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`PermCollection.f_injective`),
so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", which implies the RSA
event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
`bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
(`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
  sorry

/-- **Theorem 53.2** [PS10, Theorem 53.2]: under the RSA assumption (and the arithmetic
hypotheses), the RSA collection `{f_{N,e}(x) = x^e mod N}` is a collection of one-way
functions.

**Deviation:** module docstring (distinct primes, truncated samplers, valid indices).

**Proof sketch.** The sampling clause is `rsaCollection_sampleClose H`. For the hardness
clause fix `A`: `rsaCollection_invProbAt_le H A` bounds the inversion probability by
`rsaProb (rsaBreaker A) n + rsaGenErr n` for `n ≥ 2`, negligible by `hR (rsaBreaker A)`,
`negligible_rsaGenErr` and `Negligible.add`; conclude by `Negligible.mono`
(`Collection.invProbAt_nonneg`, threshold `2`). -/
theorem rsaCollection_oneWay (H : ArithmeticFP) (hR : RSAAssumption) : (rsaCollection H).OneWay := by
  sorry

/-- **Theorem 57.2** [PS10, Theorem 57.2]: under the RSA assumption (and the arithmetic
hypotheses), RSA with `Gen(1^n) = ((N, e), d)` and `f⁻¹_{N,d}(y) = y^d mod N` is a collection
of trapdoor permutations: clauses (1)–(4) and (6) are the data of `rsaTrapdoor`
(`rsaPermAt` [Theorem 54.3], `rsaGen`, `rsaSampler`, `rsaEval`, `rsaInv_spec`), and the
hardness clause (5) is `rsaCollection_oneWay`. -/
theorem rsaTrapdoor_oneWay (H : ArithmeticFP) (hR : RSAAssumption) : (rsaTrapdoor H).OneWay :=
  rsaCollection_oneWay H hR

/-! ## RSA implies factoring [PS10, Theorem 55.2, Algorithm 55.3] -/

/-- **The computation of `A'`** [PS10, Algorithm 55.3] after the call `p' ← A(N)`: `q' := N / p'`;
abort (output `[]`) unless `p' q' = N`; `Φ := (p'−1)(q'−1)`; `d := e⁻¹ mod Φ`
(`ExtendedEuclid`, `ZMod.inv`); output `y^d mod N` as a `2n`-bit numeral.

**Deviation:** the factoring adversary of Assumption 30.1 returns one factor; the other is
recovered by division (text issue). -/
def rsaFromFactorStep (n : ℕ) (s : List Bool) (N e y : ℕ) : List Bool :=
  if listToNat s * (N / listToNat s) = N then
    natToList (2 * n)
      (y ^ ((e : ZMod ((listToNat s - 1) * (N / listToNat s - 1)))⁻¹).val % N)
  else []

/-- **Algorithm 55.3 succeeds whenever the factor is right** [PS10, proof of Theorem 55.2,
"provided that the factors are correct, … this always succeeds with probability 1"]: if `s`
reads as `p` or `q`, then on `(N, e, y)` with `N = pq`, `gcd(e, Φ(N)) = 1` and `y ∈ Z_N^*`
the output decodes to a `2n`-bit numeral `x` with `x^e = y` in `Z_N`.

**Proof sketch.** `q' = N / p` is the other prime (`Nat.mul_div_cancel_left`), so the test
passes and `(p'−1)(q'−1) = Φ(N)` (`DistinctPrimes.totient_mul`); `d` satisfies
`ed ≡ 1 (mod Φ(N))` (`mul_inv_val_modEq`); the output is the numeral of
`y.val^d mod N = (y^d).val < N < 2^{2n}` (`val_units_pow`, `decodeFin_ofFn`,
`bitsToNat_natToBits`), and `(y^d)^e = y` by `rsa_pow_pow`. -/
theorem rsaFromFactorStep_correct {n : ℕ} (z : DistinctPrimes n) {s : List Bool}
    (hs : listToNat s = z.p ∨ listToNat s = z.q) {e : ℕ}
    (he : Nat.Coprime e (Nat.totient (z.p * z.q))) (y : (ZMod (z.p * z.q))ˣ) :
    ∃ x : Fin (2 * n) → Bool,
      decodeFin (2 * n) (rsaFromFactorStep n s (z.p * z.q) e (y : ZMod (z.p * z.q)).val) = some x ∧
        ((bitsToNat x : ℕ) : ZMod (z.p * z.q)) ^ e = (y : ZMod (z.p * z.q)) := by
  have hpq : listToNat s * (z.p * z.q / listToNat s) = z.p * z.q ∧
      (listToNat s - 1) * (z.p * z.q / listToNat s - 1) = Nat.totient (z.p * z.q) := by
    rcases hs with hs | hs <;> rw [hs]
    · rw [Nat.mul_div_cancel_left _ z.p_prime.pos, z.totient_mul]
      exact ⟨rfl, rfl⟩
    · rw [Nat.mul_div_cancel _ z.q_prime.pos, z.totient_mul]
      exact ⟨mul_comm _ _, mul_comm _ _⟩
  have he' : Nat.Coprime e ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)) := by
    rw [hpq.2]; exact he
  have hed : e * ((e : ZMod ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)))⁻¹).val ≡ 1
      [MOD Nat.totient (z.p * z.q)] := by
    unfold Nat.ModEq
    rw [← hpq.2]
    exact mul_inv_val_modEq e _ he'
  set d := ((e : ZMod ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)))⁻¹).val
  have hv : (y : ZMod (z.p * z.q)).val ^ d % (z.p * z.q) < 2 ^ (2 * n) :=
    (Nat.mod_lt _ (NeZero.pos _)).trans z.mul_lt
  refine ⟨natToBits (2 * n) ((y : ZMod (z.p * z.q)).val ^ d % (z.p * z.q)), ?_, ?_⟩
  · rw [rsaFromFactorStep, if_pos hpq.1, natToList]
    exact decodeFin_ofFn _
  · rw [bitsToNat_natToBits hv, ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm d e, pow_mul]
    exact congrArg Units.val (rsa_pow_pow hed y)

/-- The string function of `A'` [PS10, Algorithm 55.3] on the raw layout
`⟨⟨⟨1^n, ⟨N, ⟨e, y⟩⟩⟩, α⟩, r⟩`: run `A` on `⟨⟨⟨1^n, N⟩, α⟩, r⟩` (same coins and advice) and
apply `rsaFromFactorStep`. -/
def rsaFromFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rsaFromFactorStep (NUPPT.inParam z).length
    (A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
      (NUPPT.inCoins z)))
    (listToNat (pairFstD (NUPPT.inArg z))) (listToNat (pairFstD (pairSndD (NUPPT.inArg z))))
    (listToNat (pairSndD (pairSndD (NUPPT.inArg z))))

/-- **`A'` is polynomial-time** [PS10, Theorem 55.2, "the running time of `A'` is essentially
the running time of `A` plus `O(log³ n)`"] given the arithmetic bundle.

**Proof sketch.** `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` by `H.divMod`; the test `p' q' = N` by `H.mul` and
`polyTimeComputable_pairEq` (`polyTimeComputable_ite`); the decrements `p' − 1`, `q' − 1`
by `H.sub` with `[true]` (run-3 audit P7-1); `Φ` by `H.mul`; `d` as the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` by `H.modExp`; padding to `2n` bits by
`polyTimeComputable_unaryPoly`/`_blockMap`. -/
theorem polyTimeComputable_rsaFromFactorRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rsaFromFactorRaw A) := by
  sorry

/-- **The adversary `A'`** [PS10, Algorithm 55.3] as a non-uniform PPT with the coins and
advice of the factoring adversary `A`. -/
noncomputable def rsaFromFactorer (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rsaFromFactorRaw H A) A.coins A.adv A.advice A.advice_length

/-- `rsaFromFactorer` has the coins of `A`. -/
@[simp] theorem coins_rsaFromFactorer (H : ArithmeticFP) (A : NUPPT) :
    (rsaFromFactorer H A).coins = A.coins := rfl

/-- The activation of `A'`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = rsaFromFactorStep n (A(1^n, N; r)) N e y`. -/
theorem rsaFromFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N e y : List Bool)
    (r : (rsaFromFactorer H A).Coins n) :
    (rsaFromFactorer H A).runAt n (pairEncode N (pairEncode e y)) r =
      rsaFromFactorStep n (A.runAt n N r) (listToNat N) (listToNat e) (listToNat y) := by
  rw [NUPPT.runAt_eq]
  unfold rsaFromFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rsaFromFactorRaw, NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **A factorer gives an RSA breaker with the same probability** [PS10, proof of
Theorem 55.2]: `Pr[A factors N] ≤ Pr[A' breaks RSA]`.

**Proof sketch.** `rsaProb` averages over `z` the probability over `(e, y, r)`; for fixed
`z` and `r`, if `A(1^n, N; r)` reads as `p` or `q` then `A'` succeeds for *every* `(e, y)`
(`rsaFromFactorer_runAt`, `rsaFromFactorStep_correct`, `rsaInput`,
`listToNat_natToList`), so `Pr_{e,y,r}[A' wins | z] ≥ Pr_r[A factors | z]` (`uprob_mono`,
`uprob_fst`-style marginalization with the coordinates reordered by `uprob_comp_equiv`);
and `factorProb A n = uexp_z Pr_r[A factors | z]` (`uprob_prod`). -/
theorem factorProb_le_rsaProb (H : ArithmeticFP) (A : NUPPT) (n : ℕ) :
    factorProb A n ≤ rsaProb (rsaFromFactorer H A) n := by
  sorry

/-- **Theorem 55.2** [PS10, Theorem 55.2]: the RSA assumption implies the factoring
assumption (under the arithmetic hypotheses).

**Deviation:** both assumptions on uniform pairs of distinct primes of `Π_n`
(module docstring); the text's `n`/`k` mix-up is resolved as `n`.

**Proof sketch.** For every `A`, `factorProb A n ≤ rsaProb (rsaFromFactorer H A) n`
(`factorProb_le_rsaProb`), which is negligible by `hR`; conclude by `Negligible.mono`
(`factorProb_nonneg`). -/
theorem rsa_imp_factoring (H : ArithmeticFP) (hR : RSAAssumption) : FactoringAssumption := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/Candidates/Rabin.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.NumberTheory.QuadraticResidues

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rabin: the Rabin collection, Rabin ⟺ factoring, Rabin trapdoor permutations

The Rabin material of [PS10, §2.12]: the collection `R = {f_N(x) = x² mod N}` with indices
`N = pq`, domain `Z_N^*` and range `QR_N`, one-way under the factoring assumption
[PS10, Theorem 61.7]; the equivalence of its one-wayness with the factoring assumption
[PS10, Theorem 61.8] through the factoring adversary `A'(N)` of [PS10, Algorithm 62.9]
("sample `x ← Z_N^*`, `y := x²`, `z ← A(N, y)`, output `gcd(x − z, N)`") and the
symmetry lemma "the root returned differs from `±x` half the time" (Claim-62.2 of the inventory,
replacing the text's heuristic "one of the four roots with equal probability"); and the
Rabin collection of *trapdoor permutations* on Blum integers `N = pq`,
`p ≡ q ≡ 3 (mod 4)`, with domain `QR_N`, where squaring is a permutation with the unique
residue root as inverse [PS10, Theorem 63.10].

Conventions (decision log "Rabin/RSA scope", plan errors 5–6; D3–D5, D10, D11). The moduli
are products of distinct *odd* primes of `Π_n` for Theorems 61.7/61.8 (the symmetry lemma
needs `−1 ≠ 1` modulo both factors) and of distinct *Blum* primes for Theorem 63.10; the
factoring assumption is used on these restricted index distributions through the
conditioning lemmas `oddFactorProb_le`, `blumFactorProb_le`, the latter under the explicit
density hypothesis `BlumDensity` (`2^n ≤ 4n · #{p ∈ Π_n : p ≡ 3 (mod 4)}`, not available in
Mathlib). The generators run truncated restricted `SamplePrime` loops with the fallbacks
`(3, 5)` and `(3, 7)` and output `⟨N, ⟨p, q⟩⟩`; domains at string indices follow the RSA
module (valid indices carry `Z_N^*` resp. `QR_N`, invalid ones the one-element group); the
evaluator is one modular squaring; the trapdoor inverter combines the roots
`y^{(p+1)/4} mod p`, `y^{(q+1)/4} mod q` [PS10, Theorem 58.2] by the CRT formula of
[PS10, Theorem 58.3]. Every machine statement is conditional on `ArithmeticFP`.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Theorem 61.8 (⇐) is stated for Blum moduli only (square roots modulo
`p ≡ 1 (mod 4)` are not formalized, text gap); Theorem 63.10's hardness takes the density
hypothesis `BlumDensity`; the generators work at `max n 3`.

## Main definitions

* `TCSlib.Cryptography.Candidates.OddDistinctPrimes`, `BlumDistinctPrimes`, `oddFactorProb`,
  `blumFactorProb`, `BlumFactoringAssumption`, `BlumDensity` — the restricted index
  distributions and hypotheses.
* `TCSlib.Cryptography.Candidates.rabinGenParams`, `rabinGenOut`, `oddGen`, `blumGen`,
  `rabinSampler`, `blumSampler`, `blumInvNat`, `blumInv` — generators, samplers, inverter.
* `TCSlib.Cryptography.Candidates.rabinCollection` [PS10, Theorem 61.7];
  `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor` [PS10, Theorem 63.10].
* `TCSlib.Cryptography.Candidates.rabinFactorStep`, `rabinFactorer` — the adversary `A'`
  of [PS10, Algorithm 62.9]; `rabinBlumInverter` — the root finder from a factorer
  [PS10, Theorem 61.8 ⇐].

## Main results

* `TCSlib.Cryptography.Candidates.rabin_symmetry` — Claim-62.2 (the symmetry lemma).
* `TCSlib.Cryptography.Candidates.rabinCollection_oneWay` [PS10, Theorems 61.7, 61.8 ⇒].
* `TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay` [PS10, Theorem 61.8 ⇐].
* `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay` [PS10, Theorem 63.10].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.12: Theorems 58.2, 58.3, 60.5, 61.7, 61.8, Algorithm 62.9, Theorem 63.10.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Restricted index distributions -/

/-- Pairs of distinct *odd* primes of `Π_n`: the index distribution of the Rabin collection
[PS10, Theorem 61.7] (`p ≠ q` odd is needed by Theorem 60.5 and the symmetry lemma). -/
abbrev OddDistinctPrimes (n : ℕ) : Type := {z : DistinctPrimes n // z.p ≠ 2 ∧ z.q ≠ 2}

/-- Pairs of distinct *Blum* primes (`≡ 3 (mod 4)`) of `Π_n`: the index distribution of
[PS10, Theorem 63.10]. -/
abbrev BlumDistinctPrimes (n : ℕ) : Type := {z : DistinctPrimes n // z.p % 4 = 3 ∧ z.q % 4 = 3}

/-- The Blum primes of `Π_n`. -/
abbrev BlumPrimes (n : ℕ) : Type := {p : Primes n // (p.1 : ℕ) % 4 = 3}

/-- Blum primes are odd. -/
theorem BlumDistinctPrimes.ne_two {n : ℕ} (z : BlumDistinctPrimes n) : z.1.p ≠ 2 ∧ z.1.q ≠ 2 :=
  ⟨fun h => by have := z.2.1; rw [h] at this; omega, fun h => by have := z.2.2; rw [h] at this; omega⟩

/-- The factoring experiment of [PS10, Assumption 30.1] on uniform pairs of distinct odd
primes (`factorProb` conditioned on oddness). -/
noncomputable def oddFactorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : OddDistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1.1) w.2 = some x ∧
      (bitsToNat x = w.1.1.p ∨ bitsToNat x = w.1.1.q)

/-- The factoring experiment on uniform pairs of distinct Blum primes. -/
noncomputable def blumFactorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : BlumDistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1.1) w.2 = some x ∧
      (bitsToNat x = w.1.1.p ∨ bitsToNat x = w.1.1.q)

/-- **The factoring assumption on Blum integers** [PS10, Theorem 63.10, "if the Factoring
Assumption holds", restricted to `p ≡ q ≡ 3 (mod 4)`]: every non-uniform PPT factors a
uniform Blum modulus with negligible probability. -/
def BlumFactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => blumFactorProb A n

/-- **Density of Blum primes** (explicit hypothesis, decision log "Rabin/RSA scope"):
`2^n ≤ 4n · #{p < 2^n prime, p ≡ 3 (mod 4)}` for `n ≥ 2`, the analogue of
[PS10, Claim 33.1] for primes `≡ 3 (mod 4)` (true by Dirichlet's theorem with error terms,
not available in Mathlib). -/
def BlumDensity : Prop := ∀ n, 2 ≤ n → 2 ^ n ≤ 4 * n * Fintype.card (BlumPrimes n)

/-- **Conditioning on oddness** [PS10, Theorem 61.7, implicit]: for `n ≥ 6` the factoring
probability on odd pairs is at most twice the factoring probability.

**Proof sketch.** `uprob_and_eq_mul_subtype` with `E` = "both odd" (transported along
`uprob_subtype_prod_eq`): `Pr[E] · oddFactorProb = Pr[E ∧ S] ≤ factorProb`, and
`Pr[¬E] ≤ Pr[p = 2] + Pr[q = 2] = 2/|Π_n| ≤ 4n/2^n ≤ 1/2` for `n ≥ 6`
(`one_div_card_primes_le`, `uprob_eq_one_div_card` on the first coordinate), so
`Pr[E] ≥ 1/2`. -/
theorem oddFactorProb_le (A : NUPPT) {n : ℕ} (hn : 6 ≤ n) : oddFactorProb A n ≤ 2 * factorProb A n := by
  sorry

/-- **Conditioning on Blum primes** under the density hypothesis: for `n ≥ 6`,
`blumFactorProb A n ≤ 64 n² · factorProb A n`.

**Proof sketch.** As `oddFactorProb_le` with `E` = "both `≡ 3 (mod 4)`":
`Pr[E] = B(B−1)/(|Π_n|(|Π_n|−1)) ≥ ((B−1)/2^n)² ≥ 1/(64n²)` with `B = #BlumPrimes n ≥ 2^n/(4n)`
(`hD`), `B − 1 ≥ 2^n/(8n)` for `n ≥ 6` and `|Π_n| ≤ 2^n`. -/
theorem blumFactorProb_le (hD : BlumDensity) (A : NUPPT) {n : ℕ} (hn : 6 ≤ n) :
    blumFactorProb A n ≤ 64 * (n : ℝ) ^ 2 * factorProb A n := by
  sorry

/-- **Factoring is hard on Blum integers** under the factoring assumption and the density
hypothesis: `blumFactorProb_le`, `hF A`, `Negligible.mul_pow`, `Negligible.const_mul`,
`Negligible.mono` (threshold `6`). -/
theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption) :
    BlumFactoringAssumption := by
  sorry

/-! ## The symmetry lemma (Claim-62.2) -/

/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
  (crtUnits h).symm (1, -1)

/-- `u² = 1`. -/
theorem crtNegOne_sq {p q : ℕ} (h : p.Coprime q) : crtNegOne h ^ 2 = 1 := by
  rw [crtNegOne, ← map_pow, show ((1 : (ZMod p)ˣ), (-1 : (ZMod q)ˣ)) ^ 2 = (1, 1) by
    rw [Prod.pow_mk, one_pow, neg_one_sq], Prod.mk_one_one, map_one]

/-- `u ≠ 1` for `q` odd: the second CRT component of `u` is `−1 ≠ 1` in `Z_q`
(`ZMod.neg_one_ne_one`). -/
theorem crtNegOne_ne_one {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (h : p.Coprime q)
    (hq2 : q ≠ 2) : crtNegOne h ≠ 1 := by
  intro heq
  haveI : Fact (2 < q) := ⟨lt_of_le_of_ne hq.out.two_le (Ne.symm hq2)⟩
  have h1 : ((crtUnits h (crtNegOne h)).2 : ZMod q) = -1 := by
    rw [crtNegOne, MulEquiv.apply_symm_apply]; simp
  have h2 := crtUnits_snd h (crtNegOne h)
  rw [h1, heq, Units.val_one, ZMod.cast_one (dvd_mul_left q p)] at h2
  exact ZMod.neg_one_ne_one h2

/-- `u ≠ −1` for `p` odd: the first CRT component of `u` is `1 ≠ −1` in `Z_p`. -/
theorem crtNegOne_ne_neg_one {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (h : p.Coprime q)
    (hp2 : p ≠ 2) : crtNegOne h ≠ -1 := by
  intro heq
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  have h1 : ((crtUnits h (crtNegOne h)).1 : ZMod p) = 1 := by
    rw [crtNegOne, MulEquiv.apply_symm_apply]; simp
  have h2 := crtUnits_fst h (crtNegOne h)
  rw [h1, heq, Units.val_neg, Units.val_one, ZMod.cast_neg (dvd_mul_right p q),
    ZMod.cast_one (dvd_mul_right p q)] at h2
  exact ZMod.neg_one_ne_one h2.symm

/-- **The symmetry lemma** (Claim-62.2 of the inventory; the concrete content of
[PS10, Theorem 61.8 ⇒] replacing "`A` outputs one of the four square roots with equal
probability"): for `N = pq`, `p ≠ q` odd primes, and any (possibly failing) root finder
`Z : Z_N^* → ρ → Option Z_N^*` that sees only `y = x²` and independent coins, the probability
that `Z(x²)` is a root of `x²` *different from `±x`* is at least half the probability that
it is a root of `x²`.

**Proof sketch.** Let `u := crtNegOne` and `σ(x) := u x`, a bijection of `Z_N^*`
(`Equiv.mulLeft`) with `σ(x)² = x²` (`crtNegOne_sq`) and `σ(x) ∉ {±x}` (else `u = ±1`,
i.e. `(1, −1) = (1, 1)` or `(−1, −1)` in `Z_p^* × Z_q^*`, contradicting `−1 ≠ 1` for odd
`p, q`, `crtNegOne_ne_one`, `crtNegOne_ne_neg_one`). Let `S(x, r)` be "the answer is a
root", `B(x, r)` "`S` and the answer is `±x`" and `G(x, r)` "`S` and the answer is not
`±x`". Then `B(σ x, r)` implies `G(x, r)` (the answer is `±ux`, which is not `±x`), so
`Pr[B] = Pr[B ∘ (σ × id)] ≤ Pr[G]` (`uprob_comp_equiv (Equiv.prodCongr σ (Equiv.refl ρ))`,
`uprob_mono`), and `Pr[S] ≤ Pr[B ∨ G] ≤ Pr[B] + Pr[G] ≤ 2 Pr[G]` (`uprob_or_le`). -/
theorem rabin_symmetry {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {ρ : Type*} [Fintype ρ]
    (Z : (ZMod (p * q))ˣ → ρ → Option (ZMod (p * q))ˣ) :
    uprob (fun w : (ZMod (p * q))ˣ × ρ => ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2) ≤
      2 * uprob (fun w : (ZMod (p * q))ˣ × ρ =>
        ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcop := coprime_of_ne hpq
  have hu2 : crtNegOne hcop ^ 2 = 1 := crtNegOne_sq hcop
  have hu1 : crtNegOne hcop ≠ 1 := crtNegOne_ne_one hcop hq2
  have hu1' : crtNegOne hcop ≠ -1 := crtNegOne_ne_neg_one hcop hp2
  let e : (ZMod (p * q))ˣ × ρ ≃ (ZMod (p * q))ˣ × ρ :=
    Equiv.prodCongr (Equiv.mulLeft (crtNegOne hcop)) (Equiv.refl ρ)
  have hB : uprob (fun w : (ZMod (p * q))ˣ × ρ =>
      ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ (z = w.1 ∨ z = -w.1)) ≤
      uprob (fun w : (ZMod (p * q))ˣ × ρ =>
        ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1) := by
    rw [← uprob_comp_equiv e]
    apply uprob_mono
    rintro ⟨x, r⟩ ⟨z, hz, hz2, hzx⟩
    have hsq : (crtNegOne hcop * x) ^ 2 = x ^ 2 := by rw [mul_pow, hu2, one_mul]
    simp only [e, Equiv.prodCongr_apply, Equiv.coe_mulLeft, Equiv.refl_apply, Prod.map_apply,
      hsq] at hz hz2 hzx
    refine ⟨z, hz, hz2, ?_, ?_⟩
    · intro hzx'
      rw [hzx'] at hzx
      rcases hzx with h | h
      · exact hu1 (mul_right_cancel ((one_mul x).trans h)).symm
      · have h' : crtNegOne hcop * x = -1 * x := by
          rw [neg_one_mul]; exact neg_eq_iff_eq_neg.mp h.symm
        exact hu1' (mul_right_cancel h')
    · intro hzx'
      rw [hzx'] at hzx
      rcases hzx with h | h
      · have h' : crtNegOne hcop * x = -1 * x := by rw [neg_one_mul]; exact h.symm
        exact hu1' (mul_right_cancel h')
      · exact hu1 (mul_right_cancel ((one_mul x).trans (neg_inj.mp h))).symm
  calc uprob (fun w : (ZMod (p * q))ˣ × ρ => ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2)
      ≤ uprob (fun w : (ZMod (p * q))ˣ × ρ =>
          (∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ (z = w.1 ∨ z = -w.1)) ∨
          (∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1)) := by
        apply uprob_mono
        rintro w ⟨z, hz, hz2⟩
        by_cases h : z = w.1 ∨ z = -w.1
        · exact Or.inl ⟨z, hz, hz2, h⟩
        · push_neg at h
          exact Or.inr ⟨z, hz, hz2, h.1, h.2⟩
    _ ≤ _ + _ := uprob_or_le _ _
    _ ≤ 2 * _ := by linarith

/-! ## Generators for restricted prime classes -/

/-- The number of trials `4m²` of the restricted prime sampler (density at least `1/(4m)`
of odd primes, resp. of Blum primes under `BlumDensity`, gives failure `≤ e^{-m}`). -/
def rabinTrials : PolyExpr := .mul (.const 4) (.pow .var 2)

/-- The coins of one restricted prime sampler: `4m² · m`. -/
def rabinPrimeCoins : PolyExpr := .mul rabinTrials .var

/-- The coins of the Rabin generators: two restricted prime samplers. -/
def rabinGenCoins : PolyExpr := .mul (.const 2) rabinPrimeCoins

/-- One truncated run of `SamplePrime` restricted to a class `P` of primes
[PS10, Theorem 63.10, "`Gen(1^n)` samples a pair `(N, (p, q))` s.t. `N ∈ I`"; Algorithm 50.16
with the extra test]: `Candidates.rejectBlocksL` with the test "prime and in `P`" on `4m²`
blocks of `m` bits, output as the `m`-bit numeral of the first hit, or of the fallback prime
`d` (in `P`) when every block is rejected. Repair (run-3 audit P7-6/P7-7): an instance of the
shared `rejectBlocksL` (formerly the typed `firstHit` on `chunk`ed blocks with the fallback
`[]`), so that `statClose_rejectBlocksL` applies with the default `d`. -/
def samplePrimePL (P : ℕ → Prop) [DecidablePred P] (m d : ℕ) (r : List Bool) : List Bool :=
  natToList m ((rejectBlocksL (fun v => v.Prime ∧ P v) m m (4 * m ^ 2) r).getD d)

/-- The parameters of a Rabin generator: a pair of distinct primes of `Π_m` in the class `P`. -/
structure RabinParams (P : ℕ → Prop) (m : ℕ) where
  /-- The pair of distinct primes. -/
  z : DistinctPrimes m
  /-- `p ∈ P`. -/
  hp : P z.p
  /-- `q ∈ P`. -/
  hq : P z.q

/-- A pair of primes below `8` as an element of `DistinctPrimes (max m 3)`. -/
def smallDistinctPrimes (m : ℕ) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ha8 : a < 8) (hb8 : b < 8) : DistinctPrimes (max m 3) :=
  have h8 : 8 ≤ 2 ^ max m 3 :=
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ max m 3 := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  ⟨(⟨⟨a, lt_of_lt_of_le ha8 h8⟩, ha⟩, ⟨⟨b, lt_of_lt_of_le hb8 h8⟩, hb⟩), hab⟩

/-- The fallback `(3, 5)` of the odd generator. -/
def oddDefault (m : ℕ) : RabinParams (· ≠ 2) (max m 3) :=
  ⟨smallDistinctPrimes m Nat.prime_three Nat.prime_five (by norm_num) (by norm_num) (by norm_num),
    (by decide : (3 : ℕ) ≠ 2), (by decide : (5 : ℕ) ≠ 2)⟩

/-- The fallback `(3, 7)` of the Blum generator. -/
def blumDefault (m : ℕ) : RabinParams (· % 4 = 3) (max m 3) :=
  ⟨smallDistinctPrimes m Nat.prime_three (by decide : Nat.Prime 7) (by norm_num) (by norm_num)
    (by norm_num), (by decide : 3 % 4 = 3), (by decide : 7 % 4 = 3)⟩

/-- **The computation of a Rabin generator** at parameter `m` (primes from `Π_{max m 3}`):
two restricted `SamplePrime` runs on the two halves of the coins (fallback primes: the
components of `dflt m`), the fallback `dflt` unless both are distinct primes of the class
below `2^{max m 3}`. -/
def rabinGenParams (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3)) (m : ℕ)
    (r : List Bool) : RabinParams P (max m 3) :=
  let L := rabinPrimeCoins.eval (max m 3)
  let p := listToNat (samplePrimePL P (max m 3) (dflt m).z.p (r.take L))
  let q := listToNat (samplePrimePL P (max m 3) (dflt m).z.q ((r.drop L).take L))
  if h : p.Prime ∧ q.Prime ∧ p ≠ q ∧ p < 2 ^ max m 3 ∧ q < 2 ^ max m 3 ∧ P p ∧ P q then
    ⟨⟨(⟨⟨p, h.2.2.2.1⟩, h.1⟩, ⟨⟨q, h.2.2.2.2.1⟩, h.2.1⟩), h.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  else dflt m

/-- The index `N = pq` as a `2m`-bit numeral. -/
def rabinIndexOf {P : ℕ → Prop} (m : ℕ) (R : RabinParams P m) : List Bool :=
  natToList (2 * m) (R.z.p * R.z.q)

/-- The output `⟨N, ⟨p, q⟩⟩` of a Rabin generator at parameter `m` on the coins `r`
(the trapdoor `⟨p, q⟩` with `m`-bit numerals, `encodeDistinctPrimes`). -/
def rabinGenOut (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3)) (m : ℕ)
    (r : List Bool) : List Bool :=
  pairEncode (rabinIndexOf _ (rabinGenParams P dflt m r))
    (encodeDistinctPrimes _ (rabinGenParams P dflt m r).z)

/-- The string function of a Rabin generator on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`. -/
def rabinGenRaw (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3))
    (z : List Bool) : List Bool :=
  rabinGenOut P dflt (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The odd generator is polynomial-time** [PS10, Theorem 61.7, "`I` is easy to sample"].

**Proof sketch.** As `polyTimeComputable_rsaGenRaw` without the exponent: the coins are cut
at `1^{4m³}` (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rabinPrimeCoins`); each
prime is an `iterateFind` loop (`Complexity.polyTimeComputable_iterateFind`) whose test is
`H.prime` conjoined with the oddness test (the last bit, `polyTimeComputable_lenEq`-style
projection) and whose `none` branch is the constant fallback numeral; the validity test uses
`H.prime`, `polyTimeComputable_pairEq`, `H.le`; `N` by `H.mul`; the fallback pair is a
constant (`polyTimeComputable_ite`). -/
theorem polyTimeComputable_oddGenRaw (H : ArithmeticFP) :
    PolyTimeComputable (rabinGenRaw (· ≠ 2) oddDefault) := by
  sorry

/-- **The Blum generator is polynomial-time** [PS10, Theorem 63.10 (2)]: as
`polyTimeComputable_oddGenRaw` with the test "`p ≡ 3 (mod 4)`" on the last two bits. -/
theorem polyTimeComputable_blumGenRaw (H : ArithmeticFP) :
    PolyTimeComputable (rabinGenRaw (· % 4 = 3) blumDefault) := by
  sorry

/-- **The generator of the Rabin collection** (odd distinct primes) as a uniform `NUPPT`. -/
noncomputable def oddGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_oddGenRaw H) rabinGenCoins

/-- **The generator of the Blum Rabin collection** as a uniform `NUPPT`,
`Gen(1^n) = ⟨N, ⟨p, q⟩⟩` [PS10, Theorem 63.10 (2)].

**Deviation (run-3 audit P3-5):** the trapdoor inverter receives `⟨⟨p, q⟩, y⟩` without the
index `N` (`TrapdoorCollection.inv_spec`; the literal `Inv((i, t), y)` form of Definition
56.1 (6) was not adopted) and recomputes `N = pq`. -/
noncomputable def blumGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumGenRaw H) rabinGenCoins

/-- The activation of the odd generator. -/
theorem oddGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (oddGen H).Coins n) :
    (oddGen H).runAt n [] r = rabinGenOut (· ≠ 2) oddDefault n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold oddGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rabinGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The activation of the Blum generator. -/
theorem blumGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n) :
    (blumGen H).runAt n [] r = rabinGenOut (· % 4 = 3) blumDefault n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold blumGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rabinGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The modulus read from a Rabin index is `N`. -/
@[simp] theorem listToNat_rabinIndexOf {P : ℕ → Prop} (m : ℕ) (R : RabinParams P m) :
    listToNat (rabinIndexOf m R) = R.z.p * R.z.q :=
  listToNat_natToList R.z.mul_lt

/-! ## The Rabin collection [PS10, Theorem 61.7] -/

/-- The modulus of the domain at the index `N`: `N` itself, or `1` when the string reads as
`0` (so that the domain is a finite group). -/
def rabinMod (i : List Bool) : ℕ := max (listToNat i) 1

instance (i : List Bool) : NeZero (rabinMod i) := ⟨by unfold rabinMod; omega⟩

/-- `rabinMod i ≤ 2^{|i|}`. -/
theorem rabinMod_le (i : List Bool) : rabinMod i ≤ 2 ^ i.length := by
  unfold rabinMod
  have := listToNat_lt_two_pow i
  have := Nat.one_le_two_pow (n := i.length)
  omega

/-- The encoding of `x ∈ Z_N^*`: its residue as a numeral of the width of the index. -/
def rabinEnc (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : List Bool :=
  natToList i.length (x : ZMod (rabinMod i)).val

/-- The decoder of `Z_N^*`: a numeral of the width of the index reading as a number below `N`
coprime to `N`. -/
def rabinDec (i : List Bool) (w : List Bool) : Option (ZMod (rabinMod i))ˣ :=
  if h : w.length = i.length ∧ listToNat w < rabinMod i ∧ Nat.Coprime (listToNat w) (rabinMod i) then
    some (ZMod.unitOfCoprime (listToNat w) h.2.2)
  else none

/-- Decoding inverts encoding on `Z_N^*`. -/
theorem rabinDec_rabinEnc (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : rabinDec i (rabinEnc i x) = some x := by
  have hl : listToNat (rabinEnc i x) = (x : ZMod (rabinMod i)).val :=
    listToNat_natToList (lt_of_lt_of_le (ZMod.val_lt _) (rabinMod_le i))
  rw [rabinDec, dif_pos ⟨by simp [rabinEnc], by rw [hl]; exact ZMod.val_lt _,
    by rw [hl]; exact ZMod.val_coe_unit_coprime x⟩]
  congr 1
  ext
  simp [ZMod.coe_unitOfCoprime, hl]

/-- `f_N(x) = x² mod N` on the encoded element, mirroring the evaluator [PS10, Theorem 61.7]. -/
def rabinF (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : List Bool :=
  natToList i.length (listToNat (rabinEnc i x) ^ 2 % listToNat i)

/-- The evaluator of the Rabin collections on `⟨N, x⟩`: `modExpStr ⟨x, ⟨2, N⟩⟩`
[PS10, Theorem 61.7, one modular squaring]. -/
def rabinEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD z) (pairEncode [true, false] (pairFstD z)))

/-- The evaluator computes `rabinF` on encoded elements. -/
theorem rabinEval_spec (i : List Bool) (x : (ZMod (rabinMod i))ˣ) :
    rabinEval (pairEncode i (rabinEnc i x)) = rabinF i x := by
  simp [rabinEval, rabinF, listToNat]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rabinEval (H : ArithmeticFP) : PolyTimeComputable rabinEval :=
  H.modExp.comp (polyTimeComputable_pairSndD.pairEncode
    ((polyTimeComputable_const [true, false]).pairEncode polyTimeComputable_pairFstD))

/-- The string function of the domain sampler of the Rabin collection on the raw layout
`⟨⟨⟨1^n, N⟩, α⟩, r⟩`: a unit modulo `N` by rejection (`unitSampleStr`). -/
def rabinSampleRaw (z : List Bool) : List Bool :=
  unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The domain sampler of the Rabin collection**: a uniform `NUPPT` with `T(n) B(n)` coins
(`polyTimeComputable_unitSampleStr`). -/
noncomputable def rabinSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg)
    rsaSampleCoins

/-- **The Rabin sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is the numeral of `N = pq` (`oddGen_runAt`, `rabinIndexOf`) with
`rabinMod i = N` (`listToNat_rabinIndexOf`), and the sampler outputs the `|i|`-bit numeral of a
unit `v < N` (`unitSampleStr`, `sampleUnitL_spec`, or the fallback `1 % N = 1`), which
`rabinDec` decodes to `ZMod.unitOfCoprime v` with `rabinEnc` the same numeral; `rabinEval_spec`
gives the evaluator clause.

**Proof sketch.** As `rsaSampler_spec`: unfold the activation
(`NUPPT.runAtL_ofPolyTimeUniform`, `rabinSampleRaw`), case on `sampleUnitL`, discharge
`rabinDec`'s test by `length_natToList`, `listToNat_natToList`, `sampleUnitL_spec` /
`Nat.coprime_one_left`, and read the value back (`ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/
theorem rabinSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (oddGen H).Coins n)
    (s : (rabinSampler H).Coins n) :
    ∃ x, rabinDec (pairFstD ((oddGen H).runAt n [] r))
        ((rabinSampler H).runAt n (pairFstD ((oddGen H).runAt n [] r)) s) = some x ∧
      rabinEval (pairEncode (pairFstD ((oddGen H).runAt n [] r))
        ((rabinSampler H).runAt n (pairFstD ((oddGen H).runAt n [] r)) s)) = rabinF _ x := by
  sorry

/-- **The Rabin collection** [PS10, Theorem 61.7]: indices `N = pq` (distinct odd primes),
domains `Z_N^*`, `f_N(x) = x² mod N`, generator `oddGen`, sampler `rabinSampler`, evaluator
`rabinEval`.

**Deviation:** module docstring (odd distinct primes, truncated samplers, `max n 3`);
"`Z_n^*`" of the text read as `Z_N^*`. -/
noncomputable def rabinCollection (H : ArithmeticFP) : Collection where
  D i := (ZMod (rabinMod i))ˣ
  encD := rabinEnc
  decD := rabinDec
  decD_encD := rabinDec_rabinEnc
  encD_decD i w x h := by -- canonical decoding (gate 03b, finding 1)
    rw [rabinDec] at h; split_ifs at h with hw
    rw [← Option.some.inj h, rabinEnc, ZMod.coe_unitOfCoprime, natToList_val_natCast hw.1 hw.2.1]
  f := rabinF
  gen := oddGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := rabinSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rabinEval
  eval_poly := polyTimeComputable_rabinEval H
  eval_spec := rabinEval_spec
  sample_spec := rabinSampler_spec H

/-- The index generated by the Rabin collection is the numeral of `N`. -/
theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection H).gen.Coins n) :
    (rabinCollection H).index n r = rabinIndexOf _ (rabinGenParams (· ≠ 2) oddDefault n (List.ofFn r)) := by
  show pairFstD ((oddGen H).runAt n [] r) = _
  rw [oddGen_runAt, rabinGenOut, pairFstD_pairEncode]

/-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).

Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
`2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
`4n/2^n`. -/
noncomputable def rabinErr (n : ℕ) : ℝ := 4 * Real.exp (-(n : ℝ)) + 4 * n / 2 ^ n

/-- `rabinErr` is negligible (`exp_neg_le_half_pow`, `negligible_two_pow_neg`,
`Negligible.const_mul`, `Negligible.mul_pow`, `Negligible.add`). -/
theorem negligible_rabinErr : Negligible rabinErr := by
  have h1 : Negligible fun n : ℕ => (1 / 2 : ℝ) ^ n := by
    simpa [one_div] using negligible_two_pow_neg
  have h4 : Negligible fun n : ℕ => Real.exp (-(n : ℝ)) :=
    h1.mono ⟨0, fun n _ => by
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
      exact exp_neg_le_half_pow n⟩
  refine ((h4.const_mul 4).add ((h1.mul_pow 1).const_mul 4)).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold rabinErr
  rw [pow_one, one_div, inv_pow]
  field_simp

/-- **The domain sampler of the Rabin collection is close to uniform** [PS10, Theorem 61.7]:
as `rsaCollection_sampleClose` (`δ n := 1` for `n < 3`, `e^{-n}` otherwise) at the index
`N = pq` with `N < 2^{2n}` (`rabinCollection_index`, `listToNat_rabinIndexOf`), decoding by
`rabinDec`. -/
theorem rabinCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rabinCollection H).SampleClose δ := by
  sorry

/-! ## The factoring adversary `A'` [PS10, Algorithm 62.9] -/

/-- **The computation of `A'(N)`** [PS10, Algorithm 62.9] after `x ← Z_N^*` and
`z ← A(N, x² mod N)`: abort (output `[]`) unless `z² ≡ x² (mod N)`; else output
`gcd((x − z) mod N, N)` as an `n`-bit numeral (the answer format of Assumption 30.1). -/
def rabinFactorStep (n N x : ℕ) (zs : List Bool) : List Bool :=
  if listToNat zs ^ 2 % N = x ^ 2 % N then
    natToList n (Nat.gcd ((x : ZMod N) - (listToNat zs : ZMod N)).val N)
  else []

/-- The string function of `A'` on the raw layout `⟨⟨⟨1^n, N⟩, α⟩, r⟩`: `x` from the first
`T(n) B(n)` coins by `unitSampleStr`, `y := x² mod N`, the call `A(1^n, ⟨N, y⟩)` on the
remaining coins with the advice of `A`, then `rabinFactorStep`. -/
def rabinFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rabinFactorStep (NUPPT.inParam z).length (listToNat (NUPPT.inArg z))
    (listToNat (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length
      ((NUPPT.inCoins z).take (rsaSampleCoins.eval (NUPPT.inParam z).length))))
    (A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inArg z) (natToList (NUPPT.inArg z).length
        (listToNat (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length
          ((NUPPT.inCoins z).take (rsaSampleCoins.eval (NUPPT.inParam z).length))) ^ 2 %
          listToNat (NUPPT.inArg z))))
      (NUPPT.inAdvice z) ((NUPPT.inCoins z).drop (rsaSampleCoins.eval (NUPPT.inParam z).length))))

/-- **`A'` is polynomial-time** [PS10, Theorem 61.8 ⇒].

**Proof sketch.** Cut the coins at `1^{T(n) B(n)}` (`polyTimeComputable_pairTakePoly`/
`_pairDropPoly rsaSampleCoins`); `x` by `polyTimeComputable_unitSampleStr`; `y` by
`H.modExp` with the exponent `[true, false]`; the call by `A.polyTimeComputable_output` on
`NUPPT.polyTimeComputable_layout`; the test `z² ≡ y` by `H.modExp` and
`polyTimeComputable_pairEq`; `(x − z) mod N = (x + (N ∸ (z mod N))) mod N` by `H.divMod`,
`H.sub`, `H.add` and `H.divMod` (run-3 audit P7-1); the gcd is the first component of
`xgcdStr` (`H.xgcd`); the width `n` by `polyTimeComputable_pairTakePoly var`. -/
theorem polyTimeComputable_rabinFactorRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rabinFactorRaw A) := by
  sorry

/-- **The factoring adversary `A'`** [PS10, Algorithm 62.9] as a non-uniform PPT: coins
`T(n) B(n)` (for `x`) plus the coins of `A`, advice of `A`. -/
noncomputable def rabinFactorer (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rabinFactorRaw H A) (.add rsaSampleCoins A.coins)
    A.adv A.advice A.advice_length

/-- The activation of `A'` on the numeral `N` with coins `r`. -/
theorem rabinFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N : List Bool)
    (r : (rabinFactorer H A).Coins n) :
    (rabinFactorer H A).runAt n N r =
      rabinFactorStep n (listToNat N)
        (listToNat (unitSampleStr N n ((List.ofFn r).take (rsaSampleCoins.eval n))))
        (A.runAtL n (pairEncode N (natToList N.length
          (listToNat (unitSampleStr N n ((List.ofFn r).take (rsaSampleCoins.eval n))) ^ 2 % listToNat N)))
          ((List.ofFn r).drop (rsaSampleCoins.eval n))) := by
  rw [NUPPT.runAt_eq]
  unfold rabinFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rabinFactorRaw, NUPPT.runAtL, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **Inverting the Rabin collection factors** [PS10, Theorem 61.8 ⇒, Algorithm 62.9]: for
`n ≥ 3`, the inversion probability of `A` against the Rabin collection is at most twice the
factoring probability of `A'` on odd moduli plus the statistical error.

**Proof sketch.** At a generated index `N = pq` (`rabinCollection_index`), the domain is
`Z_N^*` and `f_N(x)` is the numeral of `(x²).val` (`val_units_pow`), so the event is "`A`
decodes to a root of `x²`". With `Z(y, r) := rabinDec N (A(1^n, ⟨N, y⟩; r))`, the
symmetry lemma `rabin_symmetry` (odd `p ≠ q`) shows that with probability at least half of it the
root `z` differs from `±x`, and then `gcd((x − z).val, N) ∈ {p, q}`
(`NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq`), which `rabinFactorStep` outputs as an
`n`-bit numeral (`rabinFactorer_runAt`, `NUPPT.inverter_eq_some_iff`, `natToBits_bitsToNat`).
The unit `x` of `A'` is sampled by `unitSampleStr` within `e^{-n}` of uniform
(`statClose_rejectBlocksL`, as in `rsaCollection_sampleClose`; `StatClose.abs_uprob_sub_le_prod`),
paid twice through the factor `2` of the symmetry step, and the law of `N` under `oddGen` is
within `2e^{-n} + 4n/2^n` of the uniform *distinct* odd pair: each restricted sampler is
`statClose_rejectBlocksL` with the fallback prime of `oddDefault` and the odd-prime density
`(|Π_n| − 1)/2^n ≥ 1/(4n)` for `n ≥ 3` (`two_pow_le_two_mul_card_primes`), `4n²` trials
(`one_sub_one_div_pow_le_exp_neg`), then `StatClose.prod` and `StatClose.map` through the
validity test, whose pushforward of the uniform odd pair differs from the uniform distinct odd
pair by the diagonal `uprob_diag` on the restricted class, `1/(P − 1) ≤ 2/P` (`P ≥ 2`) with
`one_div_card_primes_le` (run-3 audit P7-3); `uexp_prod`/`uprob_prod` reorganize the coins
(total `rabinErr n`). -/
theorem rabinCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 3 ≤ n) :
    (rabinCollection H).invProbAt A n ≤ 2 * oddFactorProb (rabinFactorer H A) n + rabinErr n := by
  sorry

/-- **Theorem 61.7 / Theorem 61.8 (⇒)** [PS10, Theorems 61.7 and 61.8]: under the factoring
assumption (and the arithmetic hypotheses), the Rabin collection `{f_N(x) = x² mod N}` is a
collection of one-way functions.

**Deviation:** indices with distinct odd primes; the factoring assumption on `DistinctPrimes`
is transferred by `oddFactorProb_le`.

**Proof sketch.** Sampling: `rabinCollection_sampleClose H`. Hardness: for `n ≥ 6`,
`rabinCollection_invProbAt_le` and `oddFactorProb_le` give
`invProbAt ≤ 4 · factorProb (rabinFactorer H A) n + rabinErr n`, negligible by
`hF (rabinFactorer H A)`, `Negligible.const_mul`, `negligible_rabinErr`, `Negligible.add`;
conclude by `Negligible.mono` (`Collection.invProbAt_nonneg`). -/
theorem rabinCollection_oneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (rabinCollection H).OneWay := by
  sorry

/-! ## The Rabin trapdoor collection on Blum integers [PS10, Theorem 63.10] -/

/-- A string index is a *valid Blum index* when it reads as `N = pq` with `p ≠ q` primes
`≡ 3 (mod 4)` (decidable by bounded search; the generator only outputs such indices). -/
def BlumValid (i : List Bool) : Prop :=
  ∃ p ∈ Finset.range (listToNat i), ∃ q ∈ Finset.range (listToNat i),
    p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ listToNat i = p * q

instance : DecidablePred BlumValid := fun i => by unfold BlumValid; infer_instance

/-- The modulus of the domain at a Blum index: `N` for a valid index, `1` otherwise. -/
def blumMod (i : List Bool) : ℕ := if BlumValid i then listToNat i else 1

instance (i : List Bool) : NeZero (blumMod i) := by
  unfold blumMod
  split_ifs with h
  · obtain ⟨p, hp, q, hq, hpp, hqp, -, -, -, hN⟩ := h
    exact ⟨by rw [hN]; exact mul_ne_zero hpp.ne_zero hqp.ne_zero⟩
  · exact ⟨one_ne_zero⟩

/-- `blumMod` of a valid index is `N`. -/
theorem blumMod_of_valid {i : List Bool} (h : BlumValid i) : blumMod i = listToNat i := if_pos h

/-- `blumMod` of an invalid index is `1`. -/
theorem blumMod_of_not_valid {i : List Bool} (h : ¬ BlumValid i) : blumMod i = 1 := if_neg h

/-- `blumMod i ≤ 2^{|i|}`. -/
theorem blumMod_le (i : List Bool) : blumMod i ≤ 2 ^ i.length := by
  unfold blumMod
  split_ifs
  · exact (listToNat_lt_two_pow _).le
  · exact Nat.one_le_two_pow

/-- A valid Blum index has a Blum factorization. -/
theorem BlumValid.exists_mul {i : List Bool} (h : BlumValid i) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ blumMod i = p * q := by
  have hM := blumMod_of_valid h
  obtain ⟨p, -, q, -, hp, hq, hpq, hp3, hq3, hN⟩ := h
  exact ⟨p, q, hp, hq, hpq, hp3, hq3, by rw [hM, hN]⟩

/-- **Squaring is a permutation of `QR_M`** for every Blum modulus `M = pq`
(`NumberTheory.sqTo_bijective_of_blum` transported along `M = pq`). -/
theorem sqTo_bijective_of_exists (M : ℕ) [NeZero M]
    (h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ M = p * q) :
    Function.Bijective (fun x : QR M => sqTo M (x : (ZMod M)ˣ)) := by
  obtain ⟨p, q, hp, hq, hpq, hp3, hq3, rfl⟩ := h
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  exact sqTo_bijective_of_blum (coprime_of_ne hpq) hp3 hq3

/-- The number encoding an element of `QR_N`: its residue for a valid index, the canonical
`1 mod N` for the one-element domain of an invalid index. -/
def blumEncVal (i : List Bool) (x : QR (blumMod i)) : ℕ :=
  if BlumValid i then ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val else 1 % listToNat i

/-- The string encoding of an element of `D_N = QR_N`. -/
def blumEnc (i : List Bool) (x : QR (blumMod i)) : List Bool := natToList i.length (blumEncVal i x)

/-- The decoder of `QR_N`: for a valid index, a numeral of the right width reading as a unit
below `N` that is a quadratic residue (`QR` membership is decidable); for an invalid index,
the canonical string of the one-element domain. -/
def blumDec (i : List Bool) (w : List Bool) : Option (QR (blumMod i)) :=
  if BlumValid i then
    if h : w.length = i.length ∧ listToNat w < blumMod i ∧ Nat.Coprime (listToNat w) (blumMod i) then
      if hq : ZMod.unitOfCoprime (listToNat w) h.2.2 ∈ QR (blumMod i) then some ⟨_, hq⟩ else none
    else none
  else if w = natToList i.length (1 % listToNat i) then some 1 else none

/-- The residue of an element of `QR_N` fits in the width of the index. -/
theorem blum_val_lt_two_pow (i : List Bool) (x : QR (blumMod i)) :
    ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val < 2 ^ i.length :=
  lt_of_lt_of_le (ZMod.val_lt _) (blumMod_le i)

/-- **Decoding inverts encoding on `QR_N`** (as `rsaDec_rsaEnc`, with the residue test
discharged by `x.2`). -/
theorem blumDec_blumEnc (i : List Bool) (x : QR (blumMod i)) : blumDec i (blumEnc i x) = some x := by
  by_cases hv : BlumValid i
  · have hl : listToNat (blumEnc i x) = ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val := by
      simp only [blumEnc, blumEncVal, if_pos hv]
      exact listToNat_natToList (blum_val_lt_two_pow i x)
    have hu : ZMod.unitOfCoprime (listToNat (blumEnc i x))
        (by rw [hl]; exact ZMod.val_coe_unit_coprime _) = (x : (ZMod (blumMod i))ˣ) := by
      ext
      simp [ZMod.coe_unitOfCoprime, hl]
    have hmem : ZMod.unitOfCoprime (listToNat (blumEnc i x))
        (by rw [hl]; exact ZMod.val_coe_unit_coprime _) ∈ QR (blumMod i) := by
      rw [hu]; exact x.2
    rw [blumDec, if_pos hv, dif_pos ⟨by simp [blumEnc], by rw [hl]; exact ZMod.val_lt _,
      by rw [hl]; exact ZMod.val_coe_unit_coprime _⟩, dif_pos hmem]
    congr 1
    exact Subtype.ext hu
  · haveI : Subsingleton (ZMod (blumMod i)) := ZMod.subsingleton_iff.2 (blumMod_of_not_valid hv)
    rw [blumDec, if_neg hv, if_pos (by simp [blumEnc, blumEncVal, if_neg hv])]
    congr 1
    exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

/-- `f_N(x) = x² mod N` on the encoded residue, mirroring the evaluator [PS10, Theorem 63.10]. -/
def blumF (i : List Bool) (x : QR (blumMod i)) : List Bool :=
  natToList i.length (listToNat (blumEnc i x) ^ 2 % listToNat i)

/-- The evaluator `rabinEval` computes `blumF` on encoded residues. -/
theorem blumEval_spec (i : List Bool) (x : QR (blumMod i)) :
    rabinEval (pairEncode i (blumEnc i x)) = blumF i x := by
  simp [rabinEval, blumF, listToNat]

/-- The permutation of `D_N = QR_N`: squaring [PS10, Theorem 63.10 (1), Claim-63.1] for a
valid Blum index, the identity of the one-element domain otherwise. -/
noncomputable def blumPermAt (i : List Bool) : QR (blumMod i) ≃ QR (blumMod i) :=
  if hv : BlumValid i then
    Equiv.ofBijective (fun x : QR (blumMod i) => sqTo (blumMod i) (x : (ZMod (blumMod i))ˣ))
      (sqTo_bijective_of_exists _ hv.exists_mul)
  else Equiv.refl _

/-- **`f_N` is the encoded permutation** at every index (the clause `f_perm`): as `rsaF_perm`
with `e = 2`. -/
theorem blumF_perm (i : List Bool) (x : QR (blumMod i)) : blumF i x = blumEnc i (blumPermAt i x) := by
  rcases Nat.eq_zero_or_pos i.length with hl | hl
  · simp [blumF, blumEnc, hl, natToList_zero]
  by_cases hv : BlumValid i
  · have hM := blumMod_of_valid hv
    simp only [blumF, blumEnc, blumEncVal, if_pos hv, blumPermAt, dif_pos hv, Equiv.ofBijective_apply,
      coe_sqTo, listToNat_natToList (blum_val_lt_two_pow i x), val_units_pow]
    congr 1
    exact congrArg (fun M => ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val ^ 2 % M) hM.symm
  · have h1 : 1 % listToNat i < 2 ^ i.length :=
      lt_of_le_of_lt (Nat.mod_le _ _) (Nat.one_lt_two_pow hl.ne')
    simp only [blumF, blumEnc, blumEncVal, if_neg hv, blumPermAt, dif_neg hv, Equiv.refl_apply,
      listToNat_natToList h1]
    congr 1
    rcases Nat.lt_or_ge (listToNat i) 2 with h2 | h2
    · interval_cases (listToNat i)
      · simp
      · simp
    · rw [Nat.mod_eq_of_lt (by omega : 1 < listToNat i), one_pow,
        Nat.mod_eq_of_lt (by omega : 1 < listToNat i)]

/-- The string function of the `QR_N` sampler on the raw layout `⟨⟨⟨1^n, N⟩, α⟩, r⟩`: the
square of a rejection-sampled unit [PS10, Theorem 63.10 (3)]; `4`-to-`1` maps push uniform
to uniform (`NumberTheory.pushesUniform_sqTo`, C5). -/
def blumSampleRaw (z : List Bool) : List Bool :=
  modExpStr (pairEncode (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length (NUPPT.inCoins z))
    (pairEncode [true, false] (NUPPT.inArg z)))

/-- The `QR_N` sampler is polynomial-time (`polyTimeComputable_unitSampleStr`, `H.modExp`). -/
theorem polyTimeComputable_blumSampleRaw (H : ArithmeticFP) : PolyTimeComputable blumSampleRaw :=
  H.modExp.comp ((polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_const [true, false]).pairEncode NUPPT.polyTimeComputable_inArg))

/-- **The domain sampler of the Blum Rabin collection** as a uniform `NUPPT`. -/
noncomputable def blumSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumSampleRaw H) rsaSampleCoins

/-- **The CRT root formula** [PS10, Theorems 58.2 and 58.3, Algorithm 60.4 "`C⁻¹`"]: the
residue root of `y` modulo a Blum integer `pq`, `(a · q · (q⁻¹ mod p) + b · p · (p⁻¹ mod q)) mod pq`
with `a = y^{(p+1)/4} mod p` and `b = y^{(q+1)/4} mod q`; equals `NumberTheory.blumSqrt`. -/
def blumInvNat (p q y : ℕ) : ℕ :=
  (y ^ (p / 4 + 1) % p * (q * ((q : ZMod p)⁻¹).val) + y ^ (q / 4 + 1) % q * (p * ((p : ZMod q)⁻¹).val)) %
    (p * q)

/-- The string function of the trapdoor inverter on the raw layout
`⟨⟨⟨1^n, ⟨⟨p, q⟩, y⟩⟩, α⟩, r⟩`: `blumInvNat p q y` as a numeral of the width of `y`. -/
def blumInvRaw (z : List Bool) : List Bool :=
  natToList (pairSndD (NUPPT.inArg z)).length
    (blumInvNat (listToNat (pairFstD (pairFstD (NUPPT.inArg z))))
      (listToNat (pairSndD (pairFstD (NUPPT.inArg z)))) (listToNat (pairSndD (NUPPT.inArg z))))

/-- **The inverter is polynomial-time** [PS10, Theorem 63.10 (6)]: two `H.modExp` calls with
the exponents `p/4 + 1`, `q/4 + 1` (`H.divMod`, then `H.add` with `[true]`), the CRT
coefficients by `H.xgcd` and `H.mul`, the sum by `H.add` (run-3 audit P7-1) and a final
`H.divMod`. -/
theorem polyTimeComputable_blumInvRaw (H : ArithmeticFP) : PolyTimeComputable blumInvRaw := by
  sorry

/-- **The trapdoor inverter** `Inv(1^n, ⟨⟨p, q⟩, y⟩)` as a uniform `NUPPT` without coins. -/
noncomputable def blumInv (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumInvRaw H) (.const 0)

/-- **The inverter decodes to the residue root** at every generated Blum index (the clause
`inv_spec` of `TrapdoorCollection`, [PS10, Theorem 63.10 (6)]).

**Proof sketch.** By `blumGen_runAt` the index is the numeral of `N = pq` and the trapdoor
`⟨p, q⟩` (`encodeDistinctPrimes`), with `p ≠ q` Blum primes (`rabinGenParams`), so the index
is `BlumValid`; `blumEnc i y` is the numeral of `y.val`. The inverter returns the numeral of
`blumInvNat p q y.val`, which equals `(blumSqrt y).val`: the CRT formula `s` satisfies
`s ≡ y^{(p+1)/4} (mod p)` and `s ≡ y^{(q+1)/4} (mod q)` (`ZMod.coe_mul_inv_eq_one`,
`crtUnits_fst`/`crtUnits_snd`), hence `s = crtUnits⁻¹(a, b)` by injectivity of `crtUnits`
(`ZMod.chineseRemainder`); `blumSqrt_mem_QR` puts it in `QR_N`, so `blumDec` decodes it
(`blumDec_blumEnc`), and `(blumPermAt i).symm y = blumSqrt y` by `eq_blumSqrt_of_sq_eq`
(`Equiv.ofBijective_symm_apply_apply`). -/
theorem blumInv_spec (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n)
    (y : QR (blumMod (pairFstD ((blumGen H).runAt n [] r)))) (s : (blumInv H).Coins n) :
    blumDec _ ((blumInv H).runAt n (pairEncode (pairSndD ((blumGen H).runAt n [] r)) (blumEnc _ y)) s) =
      some ((blumPermAt _).symm y) := by
  sorry

/-- **The `QR_N` sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2), Theorem 63.10 (3)]; repair of the run-3 audit,
P3-1): at every parameter the generated index is a valid Blum index (`blumGen_runAt`,
`rabinGenParams`, `BlumValid`), and the sampler outputs the `|i|`-bit numeral of `u² mod N` for
a unit `u < N` (`blumSampleRaw`, `modExpStr_pairEncode`, `unitSampleStr`, `sampleUnitL_spec`),
a unit residue (`Nat.Coprime.pow_left`, `sq_mem_QR`), which `blumDec` decodes to that residue
with `blumEnc` the same numeral; `blumEval_spec` gives the evaluator clause.

**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`), then the
computation above with `blumDec`'s tests (`length_natToList`, `listToNat_natToList`,
`Nat.mod_lt`, `ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/
theorem blumSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n)
    (s : (blumSampler H).Coins n) :
    ∃ x, blumDec (pairFstD ((blumGen H).runAt n [] r))
        ((blumSampler H).runAt n (pairFstD ((blumGen H).runAt n [] r)) s) = some x ∧
      rabinEval (pairEncode (pairFstD ((blumGen H).runAt n [] r))
        ((blumSampler H).runAt n (pairFstD ((blumGen H).runAt n [] r)) s)) = blumF _ x := by
  sorry

/-- **The Rabin collection of trapdoor permutations on Blum integers** [PS10, Theorem 63.10]:
indices `N = pq` with `p ≡ q ≡ 3 (mod 4)`, domains `D_N = R_N = QR_N`,
`Gen(1^n) = ⟨N, ⟨p, q⟩⟩`, `f_N(x) = x² mod N`, `f⁻¹_{p,q}(y)` the unique residue root
(`blumPermAt`, `blumInv`).

**Deviation:** module docstring (Blum primes, valid/invalid indices, `max n 3`). -/
noncomputable def rabinBlumTrapdoor (H : ArithmeticFP) : TrapdoorCollection where
  D i := QR (blumMod i)
  inhabitedD _ := ⟨1⟩
  encD := blumEnc
  decD := blumDec
  decD_encD := blumDec_blumEnc
  encD_decD i w x h := by -- canonical decoding (gate 03b, finding 1)
    rw [blumDec] at h; split_ifs at h with hv hw hq hw' <;> rw [← Option.some.inj h, blumEnc, blumEncVal]
    · rw [if_pos hv, ZMod.coe_unitOfCoprime, natToList_val_natCast hw.1 hw.2.1]
    · rw [if_neg hv, hw']
  f := blumF
  gen := blumGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := blumSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rabinEval
  eval_poly := polyTimeComputable_rabinEval H
  eval_spec := blumEval_spec
  sample_spec := blumSampler_spec H
  perm := blumPermAt
  f_perm := blumF_perm
  inv := blumInv H
  inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  inv_spec := blumInv_spec H

/-- The index generated by the Blum Rabin collection is the numeral of `N`. -/
theorem rabinBlumTrapdoor_index (H : ArithmeticFP) (n : ℕ) (r : (rabinBlumTrapdoor H).gen.Coins n) :
    (rabinBlumTrapdoor H).index n r =
      rabinIndexOf _ (rabinGenParams (· % 4 = 3) blumDefault n (List.ofFn r)) := by
  show pairFstD ((blumGen H).runAt n [] r) = _
  rw [blumGen_runAt, rabinGenOut, pairFstD_pairEncode]

/-- **The `QR_N` sampler is close to uniform** [PS10, Theorem 63.10 (3)]: the square of a
unit within `e^{-n}` of uniform (`rsaCollection_sampleClose`'s argument) is within `e^{-n}`
of a uniform residue (`NumberTheory.pushesUniform_sqTo`, `statClose_of_pushesUniform`,
`StatClose.map`, `StatClose.trans`); decoding by `blumDec` (`sq_mem_QR`). -/
theorem rabinBlumTrapdoor_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rabinBlumTrapdoor H).toCollection.SampleClose δ := by
  sorry

/-- **Inverting the Blum Rabin collection factors** [PS10, Theorem 63.10 (5), via
Algorithm 62.9]: for `n ≥ 3` and under the density hypothesis, the inversion probability of
`A` against `rabinBlumTrapdoor` is at most twice the Blum factoring probability of `A'`
plus the statistical error.

**Proof sketch.** As `rabinCollection_invProbAt_le`: the ideal `x ← QR_N` gives `y = x²`
uniform on `QR_N` (squaring is a bijection of `QR_N`, `blumPermAt`), and the reduction's
`y = r²` for a uniform unit `r` has the same law (`pushesUniform_sqTo`); the answer `z` of
`A` decodes to a residue root of `y`, and `rabin_symmetry` (with `Z` the decoded answer,
coerced to `Z_N^*`) gives `z ∉ {±r}` half the time, hence a factor by
`gcd_sub_eq_prime_of_sq_eq_sq`. The law of `N` under `blumGen` is within `2e^{-n} + 4n/2^n`
of the uniform distinct Blum pair by `statClose_rejectBlocksL` with the fallback prime of
`blumDefault` and the density `hD` (acceptance `≥ 1/(4n)` per trial, `4n²` trials,
`one_sub_one_div_pow_le_exp_neg`), `StatClose.prod`, `StatClose.map` through the validity test
and the diagonal `1/B ≤ 4n/2^n` from `hD` (`uprob_diag`; run-3 audit P7-3); the unit sampler's
`e^{-n}` is paid twice (total `rabinErr n`). -/
theorem rabinBlumTrapdoor_invProbAt_le (H : ArithmeticFP) (hD : BlumDensity) (A : NUPPT) {n : ℕ}
    (hn : 3 ≤ n) :
    (rabinBlumTrapdoor H).toCollection.invProbAt A n ≤
      2 * blumFactorProb (rabinFactorer H A) n + rabinErr n := by
  sorry

/-- **Theorem 63.10** [PS10, Theorem 63.10]: under the factoring assumption, the density of
Blum primes and the arithmetic hypotheses, the Rabin collection on Blum integers with domain
`QR_N` is a collection of trapdoor permutations: clauses (1)–(4) and (6) are the data of
`rabinBlumTrapdoor` (`blumPermAt` [Claim-63.1], `blumGen`, `blumSampler`, `rabinEval`,
`blumInv_spec`), and the hardness clause (5) follows from
`rabinBlumTrapdoor_invProbAt_le`, `blumFactoring_of_factoring hD hF`, `negligible_rabinErr`
and `Negligible.mono` (sampling: `rabinBlumTrapdoor_sampleClose`).

**Deviation:** factoring assumption restricted to Blum moduli through the density hypothesis. -/
theorem rabinBlumTrapdoor_oneWay (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    (rabinBlumTrapdoor H).OneWay := by
  sorry

/-! ## Theorem 61.8 (⇐): Rabin one-way implies factoring (Blum moduli) -/

/-- **The root finder from a factorer** [PS10, proof of Theorem 61.8, "only if" direction]:
`A'(N, y)`: `p' ← A(N)`, `q' := N / p'`, abort unless `p' q' = N`, else output the CRT root
`blumInvNat p' q' y` as a numeral of the width of `y`. -/
def rabinRootStep (s : List Bool) (N : ℕ) (y : List Bool) : List Bool :=
  if listToNat s * (N / listToNat s) = N then
    natToList y.length (blumInvNat (listToNat s) (N / listToNat s) (listToNat y))
  else []

/-- The string function of the root finder on the raw layout `⟨⟨⟨1^n, ⟨N, y⟩⟩, α⟩, r⟩`: run
`A` on `⟨⟨⟨1^n, N⟩, α⟩, r⟩` and apply `rabinRootStep`. -/
def rabinRootRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rabinRootStep (A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (listToNat (pairFstD (NUPPT.inArg z))) (pairSndD (NUPPT.inArg z))

/-- **The root finder is polynomial-time**: `A.polyTimeComputable_output` on the re-paired
layout, `H.divMod`, `H.mul`, `polyTimeComputable_pairEq`, `polyTimeComputable_ite`, and the
CRT formula as in `polyTimeComputable_blumInvRaw`. -/
theorem polyTimeComputable_rabinRootRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rabinRootRaw A) := by
  sorry

/-- **The inverter of the Blum Rabin collection built from a factorer** `A` (coins and advice
of `A`) [PS10, Theorem 61.8 ⇐]. -/
noncomputable def rabinBlumInverter (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rabinRootRaw H A) A.coins A.adv A.advice A.advice_length

/-- The activation of the root finder: `A'(1^n, ⟨N, y⟩; r) = rabinRootStep (A(1^n, N; r)) N y`. -/
theorem rabinBlumInverter_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N y : List Bool)
    (r : (rabinBlumInverter H A).Coins n) :
    (rabinBlumInverter H A).runAt n (pairEncode N y) r = rabinRootStep (A.runAt n N r) (listToNat N) y := by
  rw [NUPPT.runAt_eq]
  unfold rabinBlumInverter
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rabinRootRaw, NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **A Blum factorer inverts the Blum Rabin collection** [PS10, proof of Theorem 61.8 ⇐,
"from the correct `p, q` we can compute the square root of `u` with probability 1"]: for
`n ≥ 3` and under the density hypothesis, `blumFactorProb A n` is at most the inversion
probability of `rabinBlumInverter A` plus the statistical error.

**Proof sketch.** When `A(1^n, N; r)` reads as `p` or `q`, `q' = N / p'` is the other prime
and `blumInvNat p' q' y.val = (blumSqrt y).val` (the CRT argument of `blumInv_spec`), the
residue root of `y`, which `blumDec` decodes and which is `(blumPermAt N).symm y`; hence
`A'` wins for every `y` (`rabinBlumInverter_runAt`, `uprob_mono`). The ideal uniform Blum
pair is within `2e^{-n} + 4n/2^n ≤ rabinErr n` of the generator's law
(`statClose_rejectBlocksL` with `hD`, the diagonal `1/B ≤ 4n/2^n` from `hD`,
`StatClose.abs_uprob_sub_le_prod`, `uexp_prod`; run-3 audit P7-3). -/
theorem blumFactorProb_le_invProbAt (H : ArithmeticFP) (hD : BlumDensity) (A : NUPPT) {n : ℕ}
    (hn : 3 ≤ n) :
    blumFactorProb A n ≤ (rabinBlumTrapdoor H).toCollection.invProbAt (rabinBlumInverter H A) n + rabinErr n := by
  sorry

/-- **Theorem 61.8 (⇐)** [PS10, Theorem 61.8, "only if"], Blum form: if the Blum Rabin
collection is one-way (and the density hypothesis holds) then factoring Blum integers is
hard.

**Deviation:** stated for Blum moduli (square roots modulo `p ≡ 1 (mod 4)` are not
formalized, text gap) and for the `QR_N`-domain collection of Theorem 63.10.

**Proof sketch.** For every `A`, `blumFactorProb_le_invProbAt` bounds `blumFactorProb A n`
by `invProbAt (rabinBlumInverter H A) n + rabinErr n`, negligible by `h.hard`,
`negligible_rabinErr`, `Negligible.add`; conclude by `Negligible.mono` (`uprob_nonneg`). -/
theorem blumFactoring_of_rabinBlum_oneWay (H : ArithmeticFP) (hD : BlumDensity)
    (h : (rabinBlumTrapdoor H).OneWay) : BlumFactoringAssumption := by
  sorry

end TCSlib.Cryptography.Candidates

## ===== TCSlib/Cryptography/NumberTheory/Chebyshev.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Chebyshev's lower bound on the prime counting function and the density of primes

The set `Π_n` of primes below `2^n` [PS10, §2.3.2] and the two facts about it that the
candidate one-way functions of [PS10, ch. 2] rest on: Chebyshev's bound
`π(x) ≥ x / (2 log₂ x)` [PS10, Theorem 31.3] and its corollary that at least a `1/(2n)`
fraction of the `n`-bit numbers are prime [PS10, §2.3.2, Claim-33.1 of the inventory].

The proof follows [PS10, Theorem 31.3] through the central binomial coefficient: `C(2x, x)`
is at least `2^x`, and every prime power dividing it is at most `2x` (the corrected
[PS10, Claim 32.4], `Nat.pow_factorization_choose_le`), so `2^x ≤ (2x)^{π(2x)}`. This
*integer core* (`two_pow_le_pow_primeCounting`) is proved; the density corollary
(`two_pow_le_two_mul_card_primes`) follows from it at `x = 2^{n-1}`; the real-logarithm form
of the theorem (`chebyshev`) follows for even arguments by taking logarithms and for odd
arguments by the text's monotonicity of `t / log t`.

**Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
`x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
`Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
(`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.Primes` — `Π_n`, the primes below `2^n`, as a finite
  type ([PS10, §2.3.2]).

## Main results

* `TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting` — the integer core of
  Chebyshev's bound, `2^x ≤ (2x)^{π(2x)}` [PS10, Theorem 31.3].
* `TCSlib.Cryptography.NumberTheory.chebyshev_two_mul`,
  `TCSlib.Cryptography.NumberTheory.chebyshev` — the real-logarithm form
  [PS10, Theorem 31.3].
* `TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes`,
  `TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime`,
  `TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair` — the density of primes
  among `n`-bit numbers, as a cardinality and as uniform probabilities (Claim-33.1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3.2: Theorem 31.3, Claim 32.4 and the prime-density corollary on p. 33.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset

/-! ### The set `Π_n` -/

/-- `Π_n`: the primes below `2^n`, i.e. the primes among the `n`-bit numbers, as a finite
type; the uniform distribution on it is `uprob` over this type [PS10, §2.3.2]. It contains
`2` and all small primes (the text's later "`n`-bit primes" is this set, used consistently
throughout the campaign). -/
abbrev Primes (n : ℕ) : Type := {p : Fin (2 ^ n) // (p : ℕ).Prime}

/-- `|Π_n|` is the number of primes strictly below `2^n` (`Nat.primeCounting'`). -/
theorem card_primes (n : ℕ) : Fintype.card (Primes n) = Nat.primeCounting' (2 ^ n) := by
  rw [← Nat.primesBelow_card_eq_primeCounting', ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun p => ⟨p.1, Nat.mem_primesBelow.2 ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, (Nat.mem_primesBelow.1 p.2).1⟩, (Nat.mem_primesBelow.1 p.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-! ### The integer core of Chebyshev's bound -/

/-- `2x ≤ 2^x` for `x ≥ 1`. -/
private theorem two_mul_le_two_pow : ∀ x : ℕ, 1 ≤ x → 2 * x ≤ 2 ^ x
  | 0, h => absurd h (by omega)
  | 1, _ => le_rfl
  | x + 2, _ => by
    have := two_mul_le_two_pow (x + 1) (by omega)
    rw [pow_succ]
    omega

/-- The central binomial coefficient dominates `2^x` [PS10, proof of Theorem 31.3,
"`X > 2^x`"; the inequality is an equality at `x = 1`]. -/
private theorem two_pow_le_centralBinom (x : ℕ) (hx : 0 < x) : 2 ^ x ≤ Nat.centralBinom x := by
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom x hx
  have h2 : 2 * x ≤ 2 ^ x := two_mul_le_two_pow x hx
  have : (2 * x) * 2 ^ x ≤ (2 * x) * Nat.centralBinom x := by
    calc (2 * x) * 2 ^ x ≤ 2 ^ x * 2 ^ x := Nat.mul_le_mul_right _ h2
      _ = 4 ^ x := by rw [← mul_pow]; norm_num
      _ ≤ (2 * x) * Nat.centralBinom x := h4
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **The integer core of Chebyshev's theorem** [PS10, Theorem 31.3]: for `x ≥ 1`,
`2^x ≤ (2x)^{π(2x)}`, where `π(2x)` is the number of primes `≤ 2x`; taking logarithms,
`π(2x) ≥ x / log₂(2x) = (2x) / (2 log₂(2x))`.

**Proof sketch.** `X = C(2x, x) ≥ 2^x` (`Nat.four_pow_le_two_mul_self_mul_centralBinom` and
`2x ≤ 2^x`), `X = ∏_{p ≤ 2x} p^{ν_p(X)}` (`Nat.prod_pow_factorization_centralBinom`), each
prime factor contributes `p^{ν_p(X)} ≤ 2x` (the corrected [PS10, Claim 32.4],
`Nat.pow_factorization_choose_le`) and each non-prime contributes `1`, so the product is at
most `(2x)^{#\{p ≤ 2x prime\}} = (2x)^{π(2x)}`. -/
theorem two_pow_le_pow_primeCounting (x : ℕ) (hx : 0 < x) :
    2 ^ x ≤ (2 * x) ^ Nat.primeCounting (2 * x) := by
  have hprod : Nat.centralBinom x ≤ ∏ p ∈ range (2 * x + 1), (if p.Prime then 2 * x else 1) := by
    rw [← Nat.prod_pow_factorization_centralBinom x]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p _ => ?_
    by_cases hp : p.Prime
    · rw [if_pos hp, Nat.centralBinom_eq_two_mul_choose]
      exact Nat.pow_factorization_choose_le (by omega)
    · rw [if_neg hp, Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
  have hcount : ∏ p ∈ range (2 * x + 1), (if p.Prime then 2 * x else 1) =
      (2 * x) ^ Nat.primeCounting (2 * x) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Nat.primeCounting,
      ← Nat.primesBelow_card_eq_primeCounting']
    rfl
  calc 2 ^ x ≤ Nat.centralBinom x := two_pow_le_centralBinom x hx
    _ ≤ _ := hprod
    _ = _ := hcount

/-- **Chebyshev's bound at even arguments** [PS10, Theorem 31.3]: for `x ≥ 1`,
`(2x) / (2 log₂(2x)) ≤ π(2x)`.

**Proof sketch.** Take `log₂` of `two_pow_le_pow_primeCounting` (monotone,
`Real.logb_pow`, `log₂ 2 = 1`): `x ≤ π(2x) · log₂(2x)`; divide by `2 log₂(2x) > 0`. -/
theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
    (2 * x : ℝ) / (2 * Real.logb 2 (2 * x)) ≤ Nat.primeCounting (2 * x) := by
  have hcore : ((2 : ℝ) ^ x) ≤ ((2 * x : ℕ) : ℝ) ^ Nat.primeCounting (2 * x) := by
    exact_mod_cast two_pow_le_pow_primeCounting x hx
  have hx1 : (1 : ℝ) < 2 * x := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast hx
    linarith
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hcore
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  push_cast at hlog
  have hpos : 0 < Real.logb 2 (2 * x) := Real.logb_pos (by norm_num) hx1
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Chebyshev's theorem** [PS10, Theorem 31.3]: for every natural `m ≥ 2`,
`m / (2 log₂ m) ≤ π(m)`.

**Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).

**Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
(equivalently `(m+1)^m ≤ m^{m+1}` for `m ≥ 3`, i.e. `(1 + 1/m)^m ≤ e < 3 ≤ m`, from
`Real.add_one_le_exp`), so `2x / (2 log₂(2x)) ≥ m / (2 log₂ m)`. Sub-obligations:
`Nat.primeCounting` is constant across a non-prime (`Nat.count_succ`), the monotonicity
inequality in `Real.logb`, and the case `m = 3` (`π(3) = 2 ≥ 3 / (2 log₂ 3)`). -/
theorem chebyshev (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) / (2 * Real.logb 2 m) ≤ Nat.primeCounting m := by
  rcases Nat.even_or_odd m with ⟨x, hx⟩ | ⟨x, hx⟩
  · -- even `m = 2x`
    have hx0 : 0 < x := by omega
    rw [hx, show x + x = 2 * x by ring]
    push_cast
    exact chebyshev_two_mul x hx0
  · -- odd `m = 2x + 1 ≥ 3`: `π(m) = π(m + 1)` and `t / log₂ t` is increasing
    have hx1 : 1 ≤ x := by omega
    have hπ : Nat.primeCounting m = Nat.primeCounting (2 * (x + 1)) := by
      rw [show 2 * (x + 1) = m + 1 by omega]
      show Nat.primeCounting' (m + 1) = Nat.primeCounting' (m + 1 + 1)
      have hnp : ¬ Nat.Prime (m + 1) := by
        rw [show m + 1 = 2 * (x + 1) by omega]
        exact Nat.not_prime_mul (a := 2) (b := x + 1) (by norm_num) (by omega)
      rw [Nat.primeCounting', Nat.count_succ Nat.Prime (m + 1), if_neg hnp, add_zero]
    rw [hπ]
    have h1 := chebyshev_two_mul (x + 1) (by omega)
    have hm1 : ((2 * (x + 1) : ℕ) : ℝ) = (m : ℝ) + 1 := by
      rw [hx]
      push_cast
      ring
    push_cast at h1
    push_cast at hm1
    rw [hm1] at h1
    refine le_trans ?_ h1
    -- monotonicity of `t ↦ t / log₂ t` from `m` to `m + 1`, for `m ≥ 3`
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast (by omega : 3 ≤ m)
    have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
    have hlogm1 : 0 < Real.log (m + 1) := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : ((m : ℝ) + 1) ^ m ≤ (m : ℝ) ^ (m + 1) := by
      have hmpos : (0 : ℝ) < m := by linarith
      have he : (1 + 1 / (m : ℝ)) ^ m ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 / (m : ℝ))
        calc (1 + 1 / (m : ℝ)) ^ m ≤ (Real.exp (1 / m)) ^ m :=
              pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = Real.exp 1 := by
              rw [← Real.exp_nat_mul]
              congr 1
              field_simp
      have h3 : Real.exp 1 ≤ 3 := by
        have := Real.exp_one_lt_d9
        norm_num at this
        linarith
      calc ((m : ℝ) + 1) ^ m = (m : ℝ) ^ m * (1 + 1 / m) ^ m := by
            rw [← mul_pow]
            congr 1
            field_simp
        _ ≤ (m : ℝ) ^ m * 3 := by gcongr; exact he.trans h3
        _ ≤ (m : ℝ) ^ m * m := by gcongr
        _ = (m : ℝ) ^ (m + 1) := by rw [pow_succ]
    have hlogkey : (m : ℝ) * Real.log (m + 1) ≤ (m + 1) * Real.log m := by
      have := Real.log_le_log (by positivity) hkey
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have hdiv := div_le_div_of_nonneg_right hlogkey hlog2.le
    rw [Real.logb, Real.logb, div_le_div_iff₀ (mul_pos two_pos (div_pos hlogm hlog2))
      (mul_pos two_pos (div_pos hlogm1 hlog2))]
    calc (m : ℝ) * (2 * (Real.log (m + 1) / Real.log 2))
        = 2 * ((m * Real.log (m + 1)) / Real.log 2) := by ring
      _ ≤ 2 * (((m + 1) * Real.log m) / Real.log 2) := by linarith
      _ = ((m : ℝ) + 1) * (2 * (Real.log m / Real.log 2)) := by ring

/-! ### The density of primes among `n`-bit numbers -/

/-- `π(2^n) = π'(2^n)` for `n ≥ 2`: `2^n` is not prime. -/
private theorem primeCounting_two_pow (n : ℕ) (hn : 2 ≤ n) :
    Nat.primeCounting (2 ^ n) = Nat.primeCounting' (2 ^ n) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, if_neg, add_zero]
  exact fun h => not_prime_pow (by omega) (Nat.prime_iff.1 h)

/-- **Prime density** [PS10, §2.3.2, p. 33, Claim-33.1]: for `n ≥ 2`, `|Π_n| ≥ 2^n / (2n)`,
i.e. at least a `1/(2n)` fraction of the `n`-bit numbers are prime.

**Deviation:** `n ≥ 2` (`Π_1 = ∅`); §2.6.6 (p. 50) misquotes the bound as `1/n`.

**Proof sketch.** The integer core at `x = 2^{n−1}` gives `2^{2^{n−1}} ≤ (2^n)^{π(2^n)}`,
hence `2^{n−1} ≤ n · π(2^n)`; `π(2^n) = |Π_n|` since `2^n` is not prime. -/
theorem two_pow_le_two_mul_card_primes (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n ≤ 2 * n * Fintype.card (Primes n) := by
  have hcore := two_pow_le_pow_primeCounting (2 ^ (n - 1)) (by positivity)
  have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2, ← pow_mul] at hcore
  have hexp : 2 ^ (n - 1) ≤ n * Nat.primeCounting (2 ^ n) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hcore
  rw [card_primes, ← primeCounting_two_pow n hn]
  calc 2 ^ n = 2 * 2 ^ (n - 1) := h2.symm
    _ ≤ 2 * (n * Nat.primeCounting (2 ^ n)) := Nat.mul_le_mul le_rfl hexp
    _ = 2 * n * Nat.primeCounting (2 ^ n) := by ring

/-- The probability that a uniform number below `2^n` is prime is `|Π_n| / 2^n`. -/
theorem uprob_prime_eq (n : ℕ) :
    uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) = Fintype.card (Primes n) / 2 ^ n := by
  rw [uprob_eq_card_filter, Fintype.card_subtype, Fintype.card_fin]
  push_cast
  rfl

/-- A uniform `n`-bit string read as a number (`bitsToNat`) is prime with the same probability
as a uniform number below `2^n`: the bridge between the sampler of [PS10, Algorithm 50.16]
(`x ← {0,1}^n`) and `Π_n`. -/
theorem uprob_prime_bits (n : ℕ) :
    uprob (fun b : Fin n → Bool => (bitsToNat b).Prime) =
      uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) :=
  uprob_comp_equiv (bitsEquiv n) (fun x : Fin (2 ^ n) => (x : ℕ).Prime)

/-- **Prime density as a probability** [PS10, §2.3.2, Claim-33.1]: for `n ≥ 2`, a uniform
number below `2^n` is prime with probability at least `1/(2n)`. -/
theorem one_div_le_uprob_prime (n : ℕ) (hn : 2 ≤ n) :
    1 / (2 * n : ℝ) ≤ uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) := by
  rw [uprob_prime_eq, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h := two_pow_le_two_mul_card_primes n hn
  have h' : (2 : ℝ) ^ n ≤ 2 * n * Fintype.card (Primes n) := by exact_mod_cast h
  linarith

/-- A uniform pair of numbers below `2^n` consists of two primes with probability
`Pr[prime]^2` (independent coordinates). -/
theorem uprob_prime_pair (n : ℕ) :
    uprob (fun z : Fin (2 ^ n) × Fin (2 ^ n) => (z.1 : ℕ).Prime ∧ (z.2 : ℕ).Prime) =
      uprob (fun x : Fin (2 ^ n) => (x : ℕ).Prime) ^ 2 := by
  exact (HardcoreBit.uprob_prod_and (fun x : Fin (2 ^ n) => (x : ℕ).Prime)
    (fun x : Fin (2 ^ n) => (x : ℕ).Prime)).trans (sq _).symm

/-- **Prime pairs** [PS10, proof of Theorem 33.5, "with probability `1/4n²` a random input
pair consists of two primes"]: for `n ≥ 2`, a uniform pair of numbers below `2^n` is a pair
of primes with probability at least `1/(4n²)`. -/
theorem one_div_le_uprob_prime_pair (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : Fin (2 ^ n) × Fin (2 ^ n) => (z.1 : ℕ).Prime ∧ (z.2 : ℕ).Prime) := by
  rw [uprob_prime_pair]
  have h := one_div_le_uprob_prime n hn
  have h0 : (0 : ℝ) ≤ 1 / (2 * n) := by positivity
  calc 1 / (4 * (n : ℝ) ^ 2) = (1 / (2 * n)) ^ 2 := by field_simp; ring
    _ ≤ _ := pow_le_pow_left₀ h0 h 2

end TCSlib.Cryptography.NumberTheory

## ===== TCSlib/Cryptography/NumberTheory/Euclid.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The extended Euclidean algorithm

The recursive `ExtendedEuclid(a, b)` of [PS10, Algorithm 43.2], returning Bézout
coefficients `(x, y)` with `ax + by = gcd(a, b)`, together with its recursive-call counter.
Both are defined by well-founded recursion on the second argument exactly as the text's
pseudo-code. The two facts proved about it are the ones the text proves:

* [PS10, Claim 43.3]: on `a > b` with `a < 2^n` the algorithm makes at most `2n` recursive
  calls (`extEuclidCalls_le`), by the text's induction on `n` with the two cases `b < 2^n`
  and `b ≥ 2^n` (in the second case `a mod b < 2^n` after one more call);
* [PS10, Claim 44.5]: correctness `ax + by = gcd(a, b)` (`extEuclid_spec`), by strong
  induction on `b` and the regrouping `d = b(x − ⌊a/b⌋y) + ay` of the text.

Mathlib's own extended Euclid (`Nat.xgcd`, `Nat.gcdA`, `Nat.gcdB`, `Nat.gcd_eq_gcd_ab`) is
the same algorithm in iterative form; the text's recursive variant and its call count are
formalized here because the call bound is what [PS10] proves. The modular inverse
`extEuclid_inv` is the use the text makes of the algorithm (inverses in `Z_N^*`,
[PS10, §2.6.4, Theorem 46.8], the RSA decryption exponent [PS10, Theorem 57.2]).

**Deviation:** the text's precondition is `a > b > 0` (Algorithm 43.2) or `a > b ≥ 0`
(Claim 43.3); on `b = 0` the recursion of the text falls through to `ExtendedEuclid(0, a)`,
which returns `(0, 1)` and then `(1, 0 − 1 · ⌊a/0⌋)`; here `b = 0` is an explicit base case
returning `(1, 0)` with no recursive call (same value, one call fewer). The "polynomial
time in `log a + log b`" remark (inventory Rem-43.6) is machine-level and not formalized;
Claim 43.3 is its mathematical content.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.extEuclid` — `ExtendedEuclid(a, b)` [PS10, Algorithm 43.2].
* `TCSlib.Cryptography.NumberTheory.extEuclidCalls` — its number of recursive calls.

## Main results

* `TCSlib.Cryptography.NumberTheory.extEuclid_spec` — `ax + by = gcd(a, b)`
  [PS10, Claim 44.5].
* `TCSlib.Cryptography.NumberTheory.extEuclidCalls_le` — at most `2n` recursive calls for
  `a < 2^n` [PS10, Claim 43.3].
* `TCSlib.Cryptography.NumberTheory.extEuclid_inv` — the first coefficient is the inverse of
  `a` modulo `N` when `gcd(a, N) = 1`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.2: Algorithm 43.2, Claims 43.3, 44.4 and 44.5.)
-/

namespace TCSlib.Cryptography.NumberTheory

/-! ### The algorithm -/

/-- `ExtendedEuclid(a, b)` [PS10, Algorithm 43.2]: if `a mod b = 0` return `(0, 1)`; otherwise
let `(x, y) ← ExtendedEuclid(b, a mod b)` and return `(y, x − y ⌊a/b⌋)`. The value is the pair
of Bézout coefficients `(x, y)` with `ax + by = gcd(a, b)` (`extEuclid_spec`). Defined by
well-founded recursion on `b` (`a mod b < b`); the base case `b = 0` returns `(1, 0)`
(Deviation, see the module docstring). -/
def extEuclid (a b : ℕ) : ℤ × ℤ :=
  if _hb : b = 0 then (1, 0)
  else if a % b = 0 then (0, 1)
  else
    let r := extEuclid b (a % b)
    (r.2, r.1 - r.2 * ((a / b : ℕ) : ℤ))
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

/-- The number of recursive calls made by `ExtendedEuclid(a, b)` [PS10, Claim 43.3]: `0` in
the base cases, one more than the count of the call on `(b, a mod b)` otherwise. -/
def extEuclidCalls (a b : ℕ) : ℕ :=
  if _hb : b = 0 then 0
  else if a % b = 0 then 0
  else extEuclidCalls b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

/-- Unfolding: the base case `b = 0`. -/
theorem extEuclid_zero_right (a : ℕ) : extEuclid a 0 = (1, 0) := by
  rw [extEuclid]
  simp

/-- Unfolding: the base case `a mod b = 0` (`b ≠ 0`). -/
theorem extEuclid_of_mod_eq_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b = 0) :
    extEuclid a b = (0, 1) := by
  rw [extEuclid, dif_neg hb, if_pos h]

/-- Unfolding: the recursive case. -/
theorem extEuclid_of_mod_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b ≠ 0) :
    extEuclid a b =
      ((extEuclid b (a % b)).2,
        (extEuclid b (a % b)).1 - (extEuclid b (a % b)).2 * ((a / b : ℕ) : ℤ)) := by
  rw [extEuclid, dif_neg hb, if_neg h]

/-- Unfolding: no recursive call when `b = 0`. -/
theorem extEuclidCalls_zero_right (a : ℕ) : extEuclidCalls a 0 = 0 := by
  rw [extEuclidCalls]
  simp

/-- Unfolding: no recursive call when `a mod b = 0` (`b ≠ 0`). -/
theorem extEuclidCalls_of_mod_eq_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b = 0) :
    extEuclidCalls a b = 0 := by
  rw [extEuclidCalls, dif_neg hb, if_pos h]

/-- Unfolding: one call plus the calls of `(b, a mod b)` in the recursive case. -/
theorem extEuclidCalls_of_mod_ne_zero {a b : ℕ} (hb : b ≠ 0) (h : a % b ≠ 0) :
    extEuclidCalls a b = extEuclidCalls b (a % b) + 1 := by
  rw [extEuclidCalls, dif_neg hb, if_neg h]

/-! ### Correctness -/

/-- **Correctness of the extended Euclidean algorithm** [PS10, Claim 44.5]: if
`ExtendedEuclid(a, b) = (x, y)` then `ax + by = gcd(a, b)`.

**Proof sketch.** Strong induction on `b`. If `b = 0` the value `(1, 0)` gives `a = gcd(a, 0)`.
If `b ∣ a` the value `(0, 1)` gives `b = gcd(a, b)`. Otherwise the recursive call returns
`(x, y)` with `bx + (a mod b)y = gcd(b, a mod b) = gcd(a, b)` ([PS10, Claim 44.4],
`Nat.gcd_rec`), and the regrouping `bx + (a mod b)y = b(x − ⌊a/b⌋y) + ay` (using
`a = b⌊a/b⌋ + a mod b`) shows the returned pair `(y, x − ⌊a/b⌋y)` is correct. -/
theorem extEuclid_spec (a b : ℕ) :
    (extEuclid a b).1 * a + (extEuclid a b).2 * b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    by_cases hb : b = 0
    · subst hb
      rw [extEuclid_zero_right]
      simp
    by_cases h : a % b = 0
    · rw [extEuclid_of_mod_eq_zero hb h, Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)]
      simp
    · rw [extEuclid_of_mod_ne_zero hb h]
      have hrec := ih (a % b) (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) b
      have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
        rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
      have hdiv : ((a : ℕ) : ℤ) = (b : ℤ) * ((a / b : ℕ) : ℤ) + ((a % b : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod a b).symm
      rw [hgcd, ← hrec]
      linear_combination (extEuclid b (a % b)).2 * hdiv

/-- The first Bézout coefficient of `ExtendedEuclid(a, N)` is the inverse of `a` modulo `N`
when `gcd(a, N) = 1`: the computation of inverses in `Z_N^*` [PS10, §2.6.4, proof of
Theorem 46.8; §2.9, the RSA exponent `d = e⁻¹ mod Φ(N)`]. -/
theorem extEuclid_inv (a N : ℕ) (h : Nat.gcd a N = 1) :
    ((extEuclid a N).1 : ZMod N) * (a : ZMod N) = 1 := by
  have hspec := extEuclid_spec a N
  rw [h] at hspec
  have hcast := congrArg (Int.cast : ℤ → ZMod N) hspec
  push_cast at hcast
  rwa [ZMod.natCast_self, mul_zero, add_zero] at hcast

/-! ### The recursive-call bound -/

/-- **The call bound** [PS10, Claim 43.3]: if `a > b` and `a < 2^n` then `ExtendedEuclid(a, b)`
makes at most `2n` recursive calls.

**Deviation:** the text's case 2 writes `b > 2^n` for `b ≥ 2^n`; the text's precondition
`b ≥ 0` is `b < a` here (with `b = 0` a base case).

**Proof sketch.** Induction on `n`, for all `a, b`. The base cases of the algorithm make no
call. In the recursive case let `r = a mod b < b`. Case `b < 2^n`: the call on `(b, r)` meets
the induction hypothesis, total `≤ 2n + 1`. Case `b ≥ 2^n`: then `a < 2^{n+1} ≤ 2b`, so
`⌊a/b⌋ = 1` and `r = a − b < 2^{n+1} − 2^n = 2^n`; the call on `(b, r)` either stops at once
or recurses on `(r, b mod r)` with `r < 2^n`, which meets the induction hypothesis: total
`≤ 2 + 2n`. -/
theorem extEuclidCalls_le (n : ℕ) : ∀ a b : ℕ, b < a → a < 2 ^ n → extEuclidCalls a b ≤ 2 * n := by
  induction n with
  | zero =>
    intro a b hba ha
    omega
  | succ n ih =>
    intro a b hba ha
    by_cases hb : b = 0
    · subst hb
      rw [extEuclidCalls_zero_right]
      omega
    by_cases h : a % b = 0
    · rw [extEuclidCalls_of_mod_eq_zero hb h]
      omega
    rw [extEuclidCalls_of_mod_ne_zero hb h]
    have hr : a % b < b := Nat.mod_lt _ (Nat.pos_of_ne_zero hb)
    by_cases hb' : b < 2 ^ n
    · have := ih b (a % b) hr hb'
      omega
    · push_neg at hb'
      -- `a mod b + b ≤ a`, hence `a mod b < 2^n`
      have hab : a % b + b ≤ a := by
        have hmod := Nat.mod_add_div a b
        have hq : 1 ≤ a / b := (Nat.one_le_div_iff (Nat.pos_of_ne_zero hb)).2 hba.le
        have hbq : b ≤ b * (a / b) := Nat.le_mul_of_pos_right _ hq
        omega
      have hr2 : a % b < 2 ^ n := by
        rw [pow_succ] at ha
        omega
      by_cases h2 : b % (a % b) = 0
      · rw [extEuclidCalls_of_mod_eq_zero h h2]
        omega
      · rw [extEuclidCalls_of_mod_ne_zero h h2]
        have := ih (a % b) (b % (a % b)) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) hr2
        omega

end TCSlib.Cryptography.NumberTheory

## ===== TCSlib/Cryptography/NumberTheory/ModExp.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Modular exponentiation by repeated squaring

The loop `ModularExponentiation(a, x, N)` of [PS10, Algorithm 45.5]: `r ← 1`; while `x > 0`:
if `x` is odd then `r ← r·a mod N`; `x ← ⌊x/2⌋`; `a ← a² mod N`; return `r`. The loop is
written as a tail recursion on the state `(r, a, x)` instrumented with a counter of the
modular multiplications performed (one squaring per iteration, plus one multiplication when
`x` is odd). Its correctness `modExp a x N = a^x mod N` is proved, and the operation count of
[PS10, Theorem 45.6] is proved in the form "at most `2(⌊log₂ x⌋ + 1)` modular
multiplications" (`modExpMults_le`): the loop runs `⌊log₂ x⌋ + 1` times for `x > 0`.

**Deviation:** [PS10, Theorem 45.6] states the running time `O(log x · log² N)` for a machine
charging `log² N` per modular multiplication; the campaign has no binary-arithmetic machines
(plan D11), so the bound is stated as an explicit count of modular multiplications, with no
cost monad. The text's restriction `a ∈ [1, N]` is immaterial and dropped; the remark on
p. 46 that Euler's theorem "removes the restriction that `x < N`" refers to a restriction the
algorithm does not have. For `x = 0` the loop returns the literal `1` (not `1 mod N`), so the
correctness equation needs `x > 0` or `N ≠ 1`.

## Main definitions

* `TCSlib.Cryptography.NumberTheory.modExpLoop` — the instrumented loop.
* `TCSlib.Cryptography.NumberTheory.modExp` — `a^x mod N` by repeated squaring
  [PS10, Algorithm 45.5].
* `TCSlib.Cryptography.NumberTheory.modExpMults` — the number of modular multiplications.

## Main results

* `TCSlib.Cryptography.NumberTheory.modExp_eq` — correctness, `modExp a x N = a^x % N`.
* `TCSlib.Cryptography.NumberTheory.modExpMults_le` — at most `2(⌊log₂ x⌋ + 1)` modular
  multiplications [PS10, Theorem 45.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.3: Algorithm 45.5, Theorem 45.6.)
-/

namespace TCSlib.Cryptography.NumberTheory

/-! ### The loop -/

/-- The loop of [PS10, Algorithm 45.5] on the state `(r, a, x)` with the counter `c` of modular
multiplications performed so far: while `x > 0`, multiply `r` by `a` modulo `N` when `x` is odd
(one multiplication), halve `x` and square `a` modulo `N` (one multiplication). Returns the
final `r` and the final count. -/
def modExpLoop (N r a x c : ℕ) : ℕ × ℕ :=
  if hx : x = 0 then (r, c)
  else
    modExpLoop N (if x % 2 = 1 then r * a % N else r) (a * a % N) (x / 2)
      (c + if x % 2 = 1 then 2 else 1)
termination_by x
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hx) one_lt_two

/-- `ModularExponentiation(a, x, N)` [PS10, Algorithm 45.5]: `a^x mod N` by repeated
squaring, i.e. the product `∏_{i : x_i = 1} a^{2^i} mod N` over the binary digits of `x`. -/
def modExp (a x N : ℕ) : ℕ := (modExpLoop N 1 a x 0).1

/-- The number of modular multiplications performed by `ModularExponentiation(a, x, N)`
(squarings and multiplications by `r`), the cost measure of [PS10, Theorem 45.6]. -/
def modExpMults (a x N : ℕ) : ℕ := (modExpLoop N 1 a x 0).2

/-- Unfolding: the loop stops at `x = 0`. -/
theorem modExpLoop_zero (N r a c : ℕ) : modExpLoop N r a 0 c = (r, c) := by
  rw [modExpLoop]
  simp

/-- Unfolding: one iteration of the loop for `x ≠ 0`. -/
theorem modExpLoop_of_ne_zero (N r a x c : ℕ) (hx : x ≠ 0) :
    modExpLoop N r a x c =
      modExpLoop N (if x % 2 = 1 then r * a % N else r) (a * a % N) (x / 2)
        (c + if x % 2 = 1 then 2 else 1) := by
  rw [modExpLoop, dif_neg hx]

/-! ### Correctness -/

/-- The loop invariant: for `x > 0` the value is `r · a^x mod N`.

**Proof sketch.** Strong induction on `x`. If `x = 1` the loop multiplies once and stops. Else
the recursive call computes `r' · (a² mod N)^{⌊x/2⌋} mod N` with `r' ≡ r · a^{x mod 2}`, and
`r · a^{x mod 2} · (a²)^{⌊x/2⌋} = r · a^x` since `x = 2⌊x/2⌋ + x mod 2`; the reductions modulo
`N` commute with the products (`Nat.ModEq`). -/
theorem modExpLoop_fst (N : ℕ) :
    ∀ x r a c : ℕ, 0 < x → (modExpLoop N r a x c).1 = r * a ^ x % N := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro r a c hx
    rw [modExpLoop_of_ne_zero N r a x c hx.ne']
    by_cases hx2 : x / 2 = 0
    · have hx1 : x = 1 := by omega
      subst hx1
      rw [modExpLoop_zero]
      simp
    · rw [ih (x / 2) (Nat.div_lt_self hx one_lt_two) _ _ _ (Nat.pos_of_ne_zero hx2)]
      have h1 : (a * a % N) ^ (x / 2) ≡ (a * a) ^ (x / 2) [MOD N] := (Nat.mod_modEq _ _).pow _
      have h2 : (if x % 2 = 1 then r * a % N else r) ≡ r * a ^ (x % 2) [MOD N] := by
        split_ifs with hodd
        · rw [hodd, pow_one]
          exact Nat.mod_modEq _ _
        · have h0 : x % 2 = 0 := by omega
          rw [h0, pow_zero, mul_one]
      have h3 := h2.mul h1
      have hx' : r * a ^ (x % 2) * (a * a) ^ (x / 2) = r * a ^ x := by
        rw [← pow_two, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
      rw [hx'] at h3
      exact h3

/-- **Correctness of repeated squaring** [PS10, Algorithm 45.5]: for `x > 0`,
`modExp a x N = a^x mod N`. -/
theorem modExp_eq (a x N : ℕ) (hx : 0 < x) : modExp a x N = a ^ x % N :=
  (modExpLoop_fst N x 1 a 0 hx).trans (by rw [one_mul])

/-- The loop returns the literal `1` on `x = 0` (the initial value of `r`). -/
theorem modExp_zero (a N : ℕ) : modExp a 0 N = 1 := by
  rw [modExp, modExpLoop_zero]

/-- Correctness for every exponent when `N ≠ 1` (then `1 = 1 mod N`). -/
theorem modExp_eq_of_ne_one (a x N : ℕ) (hN : N ≠ 1) : modExp a x N = a ^ x % N := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rw [modExp_zero, pow_zero, Nat.one_mod_eq_one.2 hN]
  · exact modExp_eq a x N hx

/-- Correctness in `ZMod N`: the computed residue is `a^x`. -/
theorem modExp_cast (a x N : ℕ) (hx : 0 < x) : ((modExp a x N : ℕ) : ZMod N) = (a : ZMod N) ^ x := by
  rw [modExp_eq a x N hx, ZMod.natCast_mod, Nat.cast_pow]

/-! ### The operation count -/

/-- The counter of the loop: at most `2(⌊log₂ x⌋ + 1)` multiplications are added for `x > 0`,
none for `x = 0`.

**Proof sketch.** Strong induction on `x`: one iteration adds at most `2` and halves `x`, and
`⌊log₂ ⌊x/2⌋⌋ = ⌊log₂ x⌋ − 1` for `x ≥ 2` (`Nat.log_div_base`); `x = 1` is the last
iteration. -/
theorem modExpLoop_snd_le (N : ℕ) :
    ∀ x r a c : ℕ, (modExpLoop N r a x c).2 ≤ c + (if x = 0 then 0 else 2 * (Nat.log 2 x + 1)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro r a c
    by_cases hx : x = 0
    · subst hx
      rw [modExpLoop_zero]
      simp
    rw [modExpLoop_of_ne_zero N r a x c hx, if_neg hx]
    have hrec := ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx) one_lt_two)
      (if x % 2 = 1 then r * a % N else r) (a * a % N) (c + if x % 2 = 1 then 2 else 1)
    by_cases hx2 : x / 2 = 0
    · rw [if_pos hx2] at hrec
      have hx1 : x = 1 := by omega
      subst hx1
      simp only [Nat.log_one_right, zero_add, mul_one]
      split_ifs at hrec ⊢ <;> omega
    · rw [if_neg hx2, Nat.log_div_base] at hrec
      have hlog : 1 ≤ Nat.log 2 x := Nat.log_pos one_lt_two (by omega)
      split_ifs at hrec ⊢ <;> omega

/-- **The operation count of repeated squaring** [PS10, Theorem 45.6]: `ModularExponentiation`
performs at most `2(⌊log₂ x⌋ + 1)` modular multiplications (each iteration of the loop
performs at most two, and there are `⌊log₂ x⌋ + 1` iterations).

**Deviation:** operation count instead of the text's `O(log x · log² N)` machine time (D11). -/
theorem modExpMults_le (a x N : ℕ) : modExpMults a x N ≤ 2 * (Nat.log 2 x + 1) := by
  have := modExpLoop_snd_le N x 1 a 0
  rw [zero_add] at this
  refine this.trans ?_
  split_ifs <;> omega

end TCSlib.Cryptography.NumberTheory

## ===== TCSlib/Cryptography/NumberTheory/Primality.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Complexity.Randomized.Closure
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Analysis.Complex.Exponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Primality testing and sampling a random prime

The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:

* the set `L_N` of Miller–Rabin *liars* [PS10, p. 49], in the corrected form: for `N` with
  `N − 1 = u · 2^j`, `u` odd, `α ∈ L_N` iff `α^{N−1} = 1` and none of the intermediate powers
  `α^{u 2^i}` (`i < j`) is a non-trivial square root of `1`;
* the `t`-round test `millerRabin N t` [PS10, Algorithm 49.13] on bases `α ∈ [1, N−1]`;
* [PS10, Lemma 50.15]: for prime `N`, `L_N` is all of `Z_N \ {0}` (`|L_N| = N − 1`, proved);
  for odd composite `N`, `|L_N| ≤ (N−1)/2` (proved, the subgroup argument of [CLRS09]);
* [PS10, Theorem 49.14]: the test accepts every prime (proved) and rejects a composite
  except with probability `≤ 2^{−t}` (proved);
* `SamplePrime(n)` [PS10, Algorithm 50.16] as a truncated rejection sampler: `T` uniform
  `n`-bit strings, the first prime one (`firstHit` of `Sampling.lean`), and
  [PS10, Lemma 51.17]: the output is uniform on `Π_n` conditioned on success (proved), the
  failure probability is `≤ (1 − 1/(2n))^T` (proved), `≤ e^{−n}` at `T = 2n²` (proved), and
  the sampler is a PPT given a polynomial-time primality test (proved; machine level).

**Deviation (source error):** the text defines `L_N` with "`N = u2^j`" and a condition on
`i = j` only, which is vacuous; the intended `N − 1 = u 2^j` and `∀ i < j` are used.
**Deviation:** the text draws `α ← Z_N`, which includes `α = 0 ∉ L_N` and would make the
test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
**Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
density as `1/n` (it is `1/(2n)`, Claim-33.1).

## Main definitions

* `TCSlib.Cryptography.NumberTheory.mrExp`, `TCSlib.Cryptography.NumberTheory.mrOdd` — the
  decomposition `N − 1 = u · 2^j`.
* `TCSlib.Cryptography.NumberTheory.MRLiar`, `TCSlib.Cryptography.NumberTheory.mrLiars` —
  the liar set `L_N` [PS10, Definition on p. 49, corrected].
* `TCSlib.Cryptography.NumberTheory.millerRabin` — the test [PS10, Algorithm 49.13].
* `TCSlib.Cryptography.NumberTheory.samplePrime` — `SamplePrime` [PS10, Algorithm 50.16].
* `TCSlib.Cryptography.NumberTheory.samplePrimeCoins`,
  `TCSlib.Cryptography.NumberTheory.chunk` — its coin polynomial and coin layout.

## Main results

* `TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime`,
  `TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime` — `|L_N| = N − 1` for prime `N`
  [PS10, Lemma 50.15, first half].
* `TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le` — `|L_N| ≤ (N−1)/2` for odd
  composite `N` [PS10, Lemma 50.15, second half].
* `TCSlib.Cryptography.NumberTheory.millerRabin_of_prime`,
  `TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le` — [PS10, Theorem 49.14].
* `TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some`,
  `TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le`,
  `TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp`,
  `TCSlib.Cryptography.NumberTheory.statClose_samplePrime`,
  `TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt` — [PS10, Lemma 51.17].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.5: the set `L_N`, Algorithm 49.13, Theorem 49.14, Lemma 50.15; §2.6.6:
  Algorithm 50.16, Lemma 51.17.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer `uprob`).
* [CLRS09] T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to
  Algorithms*, 3rd ed., MIT Press, 2009. (Theorem 31.38 and 31.39: the Miller–Rabin
  liar bound.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset Complexity Turing

/-! ### The Miller–Rabin liar set -/

/-- The exponent `j` of the decomposition `N − 1 = u · 2^j` with `u` odd [PS10, p. 49]
(the `2`-adic valuation of `N − 1`). -/
def mrExp (N : ℕ) : ℕ := (N - 1).factorization 2

/-- The odd part `u` of the decomposition `N − 1 = u · 2^j` [PS10, p. 49]. -/
def mrOdd (N : ℕ) : ℕ := (N - 1) / 2 ^ mrExp N

/-- `2^j · u = N − 1`. -/
theorem two_pow_mrExp_mul_mrOdd (N : ℕ) : 2 ^ mrExp N * mrOdd N = N - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (N - 1) 2

/-- `u` is odd for `N ≥ 2`. -/
theorem mrOdd_odd {N : ℕ} (hN : 2 ≤ N) : Odd (mrOdd N) := by
  have h := Nat.not_dvd_ordCompl Nat.prime_two (show N - 1 ≠ 0 by omega)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)

/-- `u · 2^j = N − 1`, so the last intermediate power is `α^{N−1}`. -/
theorem mrOdd_mul_two_pow (N : ℕ) : mrOdd N * 2 ^ mrExp N = N - 1 := by
  rw [mul_comm, two_pow_mrExp_mul_mrOdd]

/-- **The Miller–Rabin liar set `L_N`** [PS10, §2.6.5, p. 49, corrected]: with
`N − 1 = u · 2^j` (`u` odd), `α ∈ L_N` iff `α^{N−1} = 1` and for every `i < j`, if
`α^{u 2^{i+1}} = 1` then `α^{u 2^i} ∈ {1, −1}` — no intermediate power encountered by
repeated squaring is a non-trivial square root of `1`.

**Deviation (source error):** the text writes `N = u 2^j` and states the second condition
for `i = j` only (vacuous); this is the intended definition. -/
def MRLiar (N : ℕ) (α : ZMod N) : Prop :=
  α ^ (N - 1) = 1 ∧ ∀ i < mrExp N, α ^ (mrOdd N * 2 ^ (i + 1)) = 1 →
    α ^ (mrOdd N * 2 ^ i) = 1 ∨ α ^ (mrOdd N * 2 ^ i) = -1

instance (N : ℕ) : DecidablePred (MRLiar N) := fun _ => by
  unfold MRLiar
  infer_instance

/-- The liar set `L_N` as a finset of `Z_N` [PS10, p. 49]. -/
def mrLiars (N : ℕ) [NeZero N] : Finset (ZMod N) := univ.filter (MRLiar N)

/-- Unfolding of membership in `L_N`. -/
theorem mem_mrLiars {N : ℕ} [NeZero N] (α : ZMod N) : α ∈ mrLiars N ↔ MRLiar N α := by
  simp [mrLiars]

/-- A liar is nonzero (for `N ≥ 2`): `0^{N−1} = 0 ≠ 1`. -/
theorem MRLiar.ne_zero {N : ℕ} (hN : 2 ≤ N) {α : ZMod N} (h : MRLiar N α) : α ≠ 0 := by
  rintro rfl
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨h1, -⟩ := h
  rw [zero_pow (by omega)] at h1
  exact zero_ne_one h1

/-- **Primes have only liars** [PS10, Lemma 50.15, first half]: for prime `N`, `α ∈ L_N` iff
`α ≠ 0`.

**Proof sketch.** Fermat's little theorem gives `α^{N−1} = 1` for `α ≠ 0`
(`ZMod.pow_card_sub_one_eq_one`); in the field `Z_N`, `β² = 1` forces `β = ±1`
(`mul_self_eq_one_iff`), applied to `β = α^{u 2^i}` whose square is `α^{u 2^{i+1}}`.
Conversely `0 ∉ L_N`. -/
theorem mrLiar_iff_of_prime {N : ℕ} [hN : Fact N.Prime] (α : ZMod N) : MRLiar N α ↔ α ≠ 0 := by
  constructor
  · exact MRLiar.ne_zero hN.out.two_le
  · intro hα
    refine ⟨ZMod.pow_card_sub_one_eq_one hα, fun i _ h => ?_⟩
    have hsq : α ^ (mrOdd N * 2 ^ i) * α ^ (mrOdd N * 2 ^ i) = 1 := by
      rw [← pow_add, ← two_mul, mul_left_comm, ← pow_succ']
      exact h
    exact mul_self_eq_one_iff.1 hsq

/-- **`|L_N| = N − 1` for prime `N`** [PS10, Lemma 50.15, first half]. -/
theorem card_mrLiars_of_prime {N : ℕ} [Fact N.Prime] : (mrLiars N).card = N - 1 := by
  rw [mrLiars, Finset.filter_congr (fun α _ => mrLiar_iff_of_prime α), Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-! #### The subgroup of liars ([CLRS09, Theorem 31.38]) -/

/-- A liar is a unit: `α^{N−1} = 1` with `N − 1 ≥ 1` (`IsUnit.of_pow_eq_one`). -/
private theorem mrLiar_isUnit {N : ℕ} (hN : 2 ≤ N) {α : ZMod N} (h : MRLiar N α) : IsUnit α :=
  IsUnit.of_pow_eq_one h.1 (by omega)

/-- `w^m = 1` in `(Z_N)^*` iff `w^m = 1` in `Z_N`. -/
private theorem units_pow_eq_one_iff {N m : ℕ} (w : (ZMod N)ˣ) :
    w ^ m = 1 ↔ (w : ZMod N) ^ m = 1 := by
  rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]

/-- `w^m = −1` in `(Z_N)^*` iff `w^m = −1` in `Z_N`. -/
private theorem units_pow_eq_neg_one_iff {N m : ℕ} (w : (ZMod N)ˣ) :
    w ^ m = -1 ↔ (w : ZMod N) ^ m = -1 := by
  rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- **Lagrange:** a proper subgroup of a finite group has at most half the elements
(`Subgroup.card_subgroup_dvd_card`; the index is not `1` by `Subgroup.eq_top_of_card_eq`). -/
private theorem two_mul_card_le_of_ne_top {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : 2 * Nat.card H ≤ Nat.card G := by
  obtain ⟨k, hk⟩ := H.card_subgroup_dvd_card
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hne : Nat.card H ≠ Nat.card G := fun h => hH (Subgroup.eq_top_of_card_eq H h)
  rcases k with _ | _ | k
  · omega
  · rw [Nat.zero_add, mul_one] at hk
    exact absurd hk.symm hne
  · rw [hk]
    nlinarith

/-- If every liar is (the value of) an element of a subgroup `H` of `(Z_N)^*`, then
`|L_N| ≤ |H|` (the map `α ↦ α` as a unit is injective, `Nat.card_le_card_of_injective`). -/
private theorem card_mrLiars_le_card {N : ℕ} [NeZero N] (hN : 2 ≤ N) (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ α : ZMod N, MRLiar N α → ∀ hu : IsUnit α, hu.unit ∈ H) :
    (mrLiars N).card ≤ Nat.card H := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective
    (fun a : {x // x ∈ mrLiars N} =>
      (⟨(mrLiar_isUnit hN ((mem_mrLiars a.1).1 a.2)).unit,
        hH a.1 ((mem_mrLiars a.1).1 a.2) _⟩ : H)) ?_
  intro a b hab
  have := congrArg (fun x : H => ((x : (ZMod N)ˣ) : ZMod N)) hab
  simp only [IsUnit.unit_spec] at this
  exact Subtype.ext this

/-- The subgroup `{x ∈ (Z_N)^* | x^m = 1}` (the kernel of `x ↦ x^m`). -/
private def powOneSubgroup (N m : ℕ) : Subgroup (ZMod N)ˣ where
  carrier := {x | x ^ m = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, ha, inv_one]

/-- Membership in `powOneSubgroup`. -/
private theorem mem_powOneSubgroup {N m : ℕ} (x : (ZMod N)ˣ) :
    x ∈ powOneSubgroup N m ↔ x ^ m = 1 := Iff.rfl

/-- The subgroup `{x ∈ (Z_N)^* | x^m = ±1}` (the preimage of `{±1}` under `x ↦ x^m`). -/
private def powPmOneSubgroup (N m : ℕ) : Subgroup (ZMod N)ˣ where
  carrier := {x | x ^ m = 1 ∨ x ^ m = -1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> simp
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow]
    have hinv : (-1 : (ZMod N)ˣ)⁻¹ = -1 :=
      inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg])
    rcases ha with ha | ha <;> rw [ha] <;> simp [hinv]

/-- Membership in `powPmOneSubgroup`. -/
private theorem mem_powPmOneSubgroup {N m : ℕ} (x : (ZMod N)ˣ) :
    x ∈ powPmOneSubgroup N m ↔ x ^ m = 1 ∨ x ^ m = -1 := Iff.rfl

/-- `−1 ≠ 1` in `Z_d` for a divisor `d > 1` of an odd number (`d ≠ 2`, so `d ≥ 3`). -/
private theorem neg_one_ne_one_of_dvd_odd {N d : ℕ} (hodd : Odd N) (hd : d ∣ N) (h1 : 1 < d) :
    (-1 : ZMod d) ≠ 1 := by
  have hne := Odd.ne_two_of_dvd_nat hodd hd
  haveI : Fact (2 < d) := ⟨by omega⟩
  exact ZMod.neg_one_ne_one

/-- **A Carmichael number is not a prime power** [CLRS09, Theorem 31.39, Case 1]: if every
unit of `Z_N` satisfies `a^{N−1} = 1` and `N = p^a` is a proper prime power, contradiction.

**Proof sketch.** `|Z_N^*| = Φ(p^a) = p^{a−1}(p−1)` is divisible by `p` (`a ≥ 2`), so by
Cauchy's theorem (`exists_prime_orderOf_dvd_card`) some unit `g` has order `p`; then
`g^{N−1} = 1` gives `p ∣ N − 1`, while `p ∣ N`, so `p ∣ 1`. -/
private theorem not_prime_pow_of_forall_pow {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (h2 : 2 < N)
    (hA : ∀ a : (ZMod N)ˣ, a ^ (N - 1) = 1) {p a : ℕ} (hp : p.Prime) (hNp : N = p ^ a) :
    False := by
  have ha : 2 ≤ a := by
    rcases a with _ | _ | a
    · rw [pow_zero] at hNp; omega
    · exfalso
      rw [Nat.zero_add, pow_one] at hNp
      exact hN (hNp ▸ hp)
    · omega
  haveI := Fact.mk hp
  have hdvd : p ∣ Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient, hNp, Nat.totient_prime_pow hp (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hdvd
  have h1 : p ∣ N - 1 := hg ▸ orderOf_dvd_of_pow_eq_one (hA g)
  have h3 : p ∣ N := hNp ▸ dvd_pow_self p (by omega)
  have : p ∣ 1 := by
    have := Nat.dvd_sub h3 h1
    rwa [Nat.sub_sub_self (by omega : 1 ≤ N)] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- A composite `N > 2` all of whose units satisfy `a^{N−1} = 1` splits as `N = n₁ n₂` with
`n₁, n₂ > 1` coprime: `n₁ = ordProj[p] N`, `n₂ = ordCompl[p] N` for `p = N.minFac`
(`n₂ = 1` would make `N` a prime power, `not_prime_pow_of_forall_pow`). -/
private theorem exists_coprime_factorization {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (h2 : 2 < N)
    (hA : ∀ a : (ZMod N)ˣ, a ^ (N - 1) = 1) :
    ∃ n₁ n₂ : ℕ, n₁ * n₂ = N ∧ Nat.Coprime n₁ n₂ ∧ 1 < n₁ ∧ 1 < n₂ := by
  have hN0 : N ≠ 0 := by omega
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  refine ⟨ordProj[N.minFac] N, ordCompl[N.minFac] N, Nat.ordProj_mul_ordCompl_eq_self N _,
    (Nat.coprime_ordCompl hp hN0).pow_left _, ?_, ?_⟩
  · have hpos := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
    exact Nat.one_lt_pow (by omega) hp.one_lt
  · by_contra h
    have hpos := Nat.ordCompl_pos N.minFac hN0
    have h1 : ordCompl[N.minFac] N = 1 := by omega
    have := Nat.ordProj_mul_ordCompl_eq_self N N.minFac
    rw [h1, mul_one] at this
    exact not_prime_pow_of_forall_pow hN h2 hA hp this.symm

/-- **The CRT witness** [CLRS09, Theorem 31.39, Case 2]: for odd `N = n₁ n₂` with coprime
`n₁, n₂ > 1` and a unit `v` with `v^m = −1`, the unit `w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)`
(`Nat.chineseRemainder`) has `w^m ∉ {1, −1}`.

**Proof sketch.** Under the reductions `Z_N → Z_{n₁}`, `Z_N → Z_{n₂}` (`ZMod.castHom`),
`w^m ↦ v^m = −1` and `w^m ↦ 1` respectively; `w^m = 1` would give `−1 = 1` in `Z_{n₁}` and
`w^m = −1` would give `−1 = 1` in `Z_{n₂}`, impossible for odd moduli `> 1`
(`neg_one_ne_one_of_dvd_odd`). `w` is a unit since `w` is coprime to `n₁` (as `v` is) and to
`n₂` (as `1` is) (`ZMod.unitOfCoprime`). -/
private theorem exists_unit_pow_ne {N : ℕ} [NeZero N] (hodd : Odd N) {n₁ n₂ : ℕ}
    (hN : n₁ * n₂ = N) (hcop : Nat.Coprime n₁ n₂) (h1 : 1 < n₁) (h2 : 1 < n₂) {m : ℕ}
    (v : (ZMod N)ˣ) (hv : v ^ m = -1) : ∃ w : (ZMod N)ˣ, w ^ m ≠ 1 ∧ w ^ m ≠ -1 := by
  have hd₁ : n₁ ∣ N := ⟨n₂, hN.symm⟩
  have hd₂ : n₂ ∣ N := ⟨n₁, by rw [← hN, mul_comm]⟩
  obtain ⟨k, hk₁, hk₂⟩ := Nat.chineseRemainder hcop (v : ZMod N).val 1
  have hkcop : Nat.Coprime k N := by
    rw [← hN, Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.Coprime, hk₁.gcd_eq]
      exact Nat.Coprime.coprime_dvd_right hd₁ (ZMod.val_coe_unit_coprime v)
    · rw [Nat.Coprime, hk₂.gcd_eq]
      exact Nat.gcd_one_left _
  have hπ₁ : ZMod.castHom hd₁ (ZMod n₁) (k : ZMod N) =
      ZMod.castHom hd₁ (ZMod n₁) (v : ZMod N) := by
    rw [ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_natCast hd₁, ← ZMod.natCast_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hk₁
  have hw : ((ZMod.unitOfCoprime k hkcop : (ZMod N)ˣ) : ZMod N) = (k : ZMod N) :=
    ZMod.coe_unitOfCoprime k hkcop
  have hv' : (v : ZMod N) ^ m = -1 := (units_pow_eq_neg_one_iff v).1 hv
  have hA : ZMod.castHom hd₁ (ZMod n₁) ((k : ZMod N) ^ m) = -1 := by
    rw [map_pow, hπ₁, ← map_pow, hv', map_neg, map_one]
  have hB : ZMod.castHom hd₂ (ZMod n₂) ((k : ZMod N) ^ m) = 1 := by
    rw [map_pow, ZMod.castHom_apply, ZMod.cast_natCast hd₂,
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hk₂, Nat.cast_one, one_pow]
  refine ⟨ZMod.unitOfCoprime k hkcop, fun h => ?_, fun h => ?_⟩
  · have h' : (k : ZMod N) ^ m = 1 := by rw [← hw]; exact (units_pow_eq_one_iff _).1 h
    rw [h', map_one] at hA
    exact neg_one_ne_one_of_dvd_odd hodd hd₁ h1 hA.symm
  · have h' : (k : ZMod N) ^ m = -1 := by rw [← hw]; exact (units_pow_eq_neg_one_iff _).1 h
    rw [h', map_neg, map_one] at hB
    exact neg_one_ne_one_of_dvd_odd hodd hd₂ h2 hB

/-- **Every liar lands in `{±1}` at the critical exponent:** if `j'` is at least every
`i ≤ j − 1` for which some unit `v` has `v^{u 2^i} = −1`, then every liar `α` has
`α^{u 2^{j'}} ∈ {1, −1}` [CLRS09, Theorem 31.39, Case 2].

**Proof sketch.** Induction on `i ≤ j` for the claim "`α^{u 2^i} = 1` implies
`α^{u 2^{j'}} ∈ {±1}`", applied at `i = j` where `α^{u 2^j} = α^{N−1} = 1`. At `i = 0`,
`α^u = 1` forces `α^{u 2^{j'}} = 1`. At `i + 1`: by the liar condition `α^{u 2^i} ∈ {±1}`; if
`1`, use the induction hypothesis; if `−1`, then `α` (a unit) witnesses the index `i`, so
`i ≤ j'` by maximality and `α^{u 2^{j'}} = (−1)^{2^{j'−i}}`, which is `−1` for `j' = i` and `1`
for `j' > i` (`Even.neg_one_pow`). -/
private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
    (hmax : ∀ i ≤ mrExp N - 1, (∃ v : (ZMod N)ˣ, v ^ (mrOdd N * 2 ^ i) = -1) → i ≤ j')
    {α : ZMod N} (hα : MRLiar N α) :
    α ^ (mrOdd N * 2 ^ j') = 1 ∨ α ^ (mrOdd N * 2 ^ j') = -1 := by
  have hunit : IsUnit α := mrLiar_isUnit (by omega) hα
  have key : ∀ i ≤ mrExp N, α ^ (mrOdd N * 2 ^ i) = 1 →
      α ^ (mrOdd N * 2 ^ j') = 1 ∨ α ^ (mrOdd N * 2 ^ j') = -1 := by
    intro i
    induction i with
    | zero =>
      intro _ h0
      left
      rw [pow_zero, mul_one] at h0
      rw [pow_mul, h0, one_pow]
    | succ i ih =>
      intro hi hsucc
      rcases hα.2 i (by omega) hsucc with h1 | h1
      · exact ih (by omega) h1
      · have hle : i ≤ j' := hmax i (by omega)
          ⟨hunit.unit, by rw [units_pow_eq_neg_one_iff, IsUnit.unit_spec]; exact h1⟩
        have hsplit : mrOdd N * 2 ^ j' = mrOdd N * 2 ^ i * 2 ^ (j' - i) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
        rw [hsplit, pow_mul, h1]
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          right
          simp
        · left
          exact Even.neg_one_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact key (mrExp N) le_rfl (by rw [mrOdd_mul_two_pow]; exact hα.1)

/-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
`N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.

**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).

**Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
`mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
liar (`card_mrLiars_le_card`, `two_mul_card_le_of_ne_top`, `|Z_N^*| = Φ(N) < N`). If some
unit `a` has `a^{N−1} ≠ 1`, take `{x | x^{N−1} = 1}` (`powOneSubgroup`). Otherwise (`N` a
Carmichael number) `N` is not a prime power (`not_prime_pow_of_forall_pow`: by Cauchy's
result, for `N = p^k`, `k ≥ 2`, a unit of order `p` would give `p ∣ N − 1`), so `N = n₁ n₂`
with coprime `n₁, n₂ > 1` (`exists_coprime_factorization`); let `j'` be the largest
`i ≤ j − 1` such that some unit `v` has `v^{u 2^{i}} = −1` (`Nat.findGreatest`; `i = 0`
qualifies with `v = −1`, `u` odd); then `B = {x ∈ Z_N^* | x^{u 2^{j'}} = ±1}`
(`powPmOneSubgroup`) contains every liar (`liar_pow_mem`), and the unit `w` with
`w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)` (CRT, `exists_unit_pow_ne`) has `w^{u 2^{j'}} ∉ {±1}`,
so `B` is proper. -/
theorem two_mul_card_mrLiars_le {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (hodd : N % 2 = 1)
    (h2 : 2 < N) : 2 * (mrLiars N).card ≤ N - 1 := by
  classical
  -- it suffices to find a proper subgroup of the units containing every liar
  suffices h : ∃ H : Subgroup (ZMod N)ˣ, H ≠ ⊤ ∧
      ∀ α : ZMod N, MRLiar N α → ∀ hu : IsUnit α, hu.unit ∈ H by
    obtain ⟨H, hH, hL⟩ := h
    have h1 := card_mrLiars_le_card (by omega) H hL
    have h3 := two_mul_card_le_of_ne_top H hH
    have h4 : Nat.card (ZMod N)ˣ = N.totient := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    have h5 := Nat.totient_lt N (by omega)
    omega
  by_cases hA : ∃ a : (ZMod N)ˣ, a ^ (N - 1) ≠ 1
  · -- some unit violates Fermat: the liars lie in the kernel of `x ↦ x^{N−1}`
    obtain ⟨a, ha⟩ := hA
    refine ⟨powOneSubgroup N (N - 1), fun htop => ha ?_, fun α hα hu => ?_⟩
    · exact (mem_powOneSubgroup a).1 (htop ▸ Subgroup.mem_top a)
    · rw [mem_powOneSubgroup, units_pow_eq_one_iff, IsUnit.unit_spec]
      exact hα.1
  · -- `N` is a Carmichael number: the largest-index construction
    push_neg at hA
    have hj : 0 < mrExp N :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega)
        (Nat.dvd_of_mod_eq_zero (by omega))
    have hu : Odd (mrOdd N) := mrOdd_odd (by omega)
    set P : ℕ → Prop := fun i => ∃ v : (ZMod N)ˣ, v ^ (mrOdd N * 2 ^ i) = -1 with hP
    have hP0 : P 0 := ⟨-1, by rw [pow_zero, mul_one]; exact hu.neg_one_pow⟩
    have hj'P : P (Nat.findGreatest P (mrExp N - 1)) :=
      Nat.findGreatest_spec (Nat.zero_le _) hP0
    have hmax : ∀ i ≤ mrExp N - 1, P i → i ≤ Nat.findGreatest P (mrExp N - 1) :=
      fun i hi hPi => Nat.le_findGreatest hi hPi
    obtain ⟨v, hv⟩ := hj'P
    obtain ⟨n₁, n₂, hN12, hcop, hn₁, hn₂⟩ := exists_coprime_factorization hN h2 hA
    obtain ⟨w, hw1, hw2⟩ := exists_unit_pow_ne (Nat.odd_iff.2 hodd) hN12 hcop hn₁ hn₂ v hv
    refine ⟨powPmOneSubgroup N (mrOdd N * 2 ^ Nat.findGreatest P (mrExp N - 1)),
      fun htop => ?_, fun α hα hunit => ?_⟩
    · rcases (mem_powPmOneSubgroup w).1 (htop ▸ Subgroup.mem_top w) with h | h
      exacts [hw1 h, hw2 h]
    · rw [mem_powPmOneSubgroup, units_pow_eq_one_iff, units_pow_eq_neg_one_iff,
        IsUnit.unit_spec]
      exact liar_pow_mem h2 hmax hα

/-! ### The Miller–Rabin test -/

/-- **The Miller–Rabin test** [PS10, Algorithm 49.13] with `t` rounds on the bases
`α_1, …, α_t ∈ [1, N−1]` (the base `i : Fin (N−1)` is `i + 1`): accept `N = 2`; reject even
`N > 2`; otherwise output "prime" (`true`) iff every base is a liar.

**Deviation:** bases in `[1, N−1]` rather than the text's `Z_N` (which contains `0 ∉ L_N`);
even `N` rejected directly. -/
def millerRabin (N t : ℕ) (α : Fin t → Fin (N - 1)) : Bool :=
  if N = 2 then true
  else if N % 2 = 0 then false
  else decide (∀ i, MRLiar N (((α i : ℕ) + 1 : ℕ) : ZMod N))

/-- A base `i + 1` with `i < N − 1` is a nonzero residue. -/
private theorem base_ne_zero {N : ℕ} (hN : 2 ≤ N) (i : Fin (N - 1)) :
    (((i : ℕ) + 1 : ℕ) : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have := i.2
  omega

/-- **Miller–Rabin accepts every prime** [PS10, Theorem 49.14, second sentence]: for prime
`N` and every choice of bases the test outputs "prime".

**Proof sketch.** `N = 2` is the base case; a prime is odd otherwise; every base `α ≠ 0` is a
liar by `mrLiar_iff_of_prime`. -/
theorem millerRabin_of_prime {N : ℕ} [hN : Fact N.Prime] (t : ℕ) (α : Fin t → Fin (N - 1)) :
    millerRabin N t α = true := by
  unfold millerRabin
  split_ifs with h2 heven
  · rfl
  · exfalso
    have := hN.out.eq_two_or_odd.resolve_left h2
    omega
  · simp only [decide_eq_true_eq]
    intro i
    exact (mrLiar_iff_of_prime _).2 (base_ne_zero hN.out.two_le (α i))

/-- **Miller–Rabin rejects composites with probability `≥ 1 − 2^{−t}`**
[PS10, Theorem 49.14, first sentence]: for composite `N > 2` and `t` uniform independent
bases in `[1, N−1]`, the test outputs "prime" with probability at most `(1/2)^t`.

**Deviation:** "at least" `1 − 2^{−t}` (the text says "with probability").

**Proof sketch.** Even `N > 2` are rejected outright. For odd composite `N` the test accepts
iff all `t` bases are liars; the bases are independent (`uprob_pi_forall`), so the
probability is `Pr[α ∈ L_N]^t` with `Pr[α ∈ L_N] = |L_N ∖ {0}| / (N−1) = |L_N| / (N−1)`
(`0 ∉ L_N`, `MRLiar.ne_zero`; the map `i ↦ i + 1` is a bijection of `[0, N−2]` onto
`Z_N ∖ {0}`), and `|L_N| ≤ (N−1)/2` by `two_mul_card_mrLiars_le`. -/
theorem uprob_millerRabin_le {N : ℕ} (hN : ¬ N.Prime) (h2 : 2 < N) (t : ℕ) :
    uprob (fun α : Fin t → Fin (N - 1) => millerRabin N t α = true) ≤ (1 / 2 : ℝ) ^ t := by
  haveI : NeZero N := ⟨by omega⟩
  by_cases heven : N % 2 = 0
  · -- even composites are rejected outright
    have hfalse : ∀ α : Fin t → Fin (N - 1), millerRabin N t α = true ↔ False := by
      intro α
      unfold millerRabin
      rw [if_neg (by omega), if_pos heven]
      simp
    rw [OneWay.uprob_congr hfalse, uprob_false]
    positivity
  have hodd : N % 2 = 1 := by omega
  -- the test accepts iff every base is a liar
  have hiff : ∀ α : Fin t → Fin (N - 1), millerRabin N t α = true ↔
      ∀ i, MRLiar N (((α i : ℕ) + 1 : ℕ) : ZMod N) := by
    intro α
    unfold millerRabin
    rw [if_neg (by omega), if_neg heven]
    simp
  rw [OneWay.uprob_congr hiff,
    OneWay.uprob_pi_forall (fun i : Fin (N - 1) => MRLiar N (((i : ℕ) + 1 : ℕ) : ZMod N)),
    Fintype.card_fin]
  refine pow_le_pow_left₀ (uprob_nonneg _) ?_ t
  -- the bases `i + 1` that are liars are in bijection with `L_N` (`0 ∉ L_N`)
  rw [uprob_eq_card_filter, Fintype.card_fin]
  have hcard : (univ.filter fun i : Fin (N - 1) => MRLiar N (((i : ℕ) + 1 : ℕ) : ZMod N)).card =
      (mrLiars N).card := by
    refine Finset.card_bij (fun i _ => (((i : ℕ) + 1 : ℕ) : ZMod N)) ?_ ?_ ?_
    · intro i hi
      rw [mem_mrLiars]
      exact (mem_filter.1 hi).2
    · intro i _ j _ hij
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        at hij
      exact Fin.ext (by omega)
    · intro α hα
      rw [mem_mrLiars] at hα
      have hne : α.val ≠ 0 := fun h => hα.ne_zero (by omega) ((ZMod.val_eq_zero α).1 h)
      have hlt := α.val_lt
      refine ⟨⟨α.val - 1, by omega⟩, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        simp only
        rw [show α.val - 1 + 1 = α.val by omega, ZMod.natCast_zmod_val]
        exact hα
      · simp only
        rw [show α.val - 1 + 1 = α.val by omega, ZMod.natCast_zmod_val]
  rw [hcard]
  have hle := two_mul_card_mrLiars_le hN hodd h2
  rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < N - 1)) (by norm_num), one_mul]
  exact_mod_cast (by omega : (mrLiars N).card * 2 ≤ N - 1)

/-! ### Sampling a random prime -/

/-- **`SamplePrime(n)`** [PS10, Algorithm 50.16], truncated to `T` trials: given `T` uniform
`n`-bit strings `x_1, …, x_T`, output the first one that reads (`bitsToNat`) as a prime, or
`⊥` (`none`) if none does. The instance of `firstHit` (lemma C4) for the predicate
"prime" on `n`-bit numbers.

**Deviation:** strict PPT with `T` trials and failure output instead of the text's expected
polynomial-time loop (D10); exact primality (`Nat.Prime`) instead of Miller–Rabin. -/
def samplePrime (n T : ℕ) (xs : Fin T → (Fin n → Bool)) : Option (Fin n → Bool) :=
  firstHit (fun b : Fin n → Bool => (bitsToNat b).Prime) xs

/-- `SamplePrime` fails exactly when none of the `T` strings is prime. -/
theorem samplePrime_eq_none_iff (n T : ℕ) (xs : Fin T → (Fin n → Bool)) :
    samplePrime n T xs = none ↔ ∀ t, ¬ (bitsToNat (xs t)).Prime :=
  firstHit_eq_none_iff _ xs

/-- A successful output of `SamplePrime` is prime. -/
theorem samplePrime_prime {n T : ℕ} {xs : Fin T → (Fin n → Bool)} {b : Fin n → Bool}
    (h : samplePrime n T xs = some b) : (bitsToNat b).Prime :=
  firstHit_eq_some_imp (fun b : Fin n → Bool => (bitsToNat b).Prime) h

/-- **Uniformity of `SamplePrime`** [PS10, Lemma 51.17, "a randomly selected `n`-bit prime"]:
conditioned on success the output is uniform on the primes — any two `n`-bit primes are
output with the same probability (lemma C4, `firstHit_uniform_of_some`). -/
theorem samplePrime_uniform_of_some (n T : ℕ) {b b' : Fin n → Bool} (hb : (bitsToNat b).Prime)
    (hb' : (bitsToNat b').Prime) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = some b) =
      uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = some b') :=
  firstHit_uniform_of_some _ T hb hb'

/-- The failure probability of `SamplePrime` is exactly `(1 − Pr[prime])^T`. -/
theorem uprob_samplePrime_none (n T : ℕ) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = none) =
      (1 - uprob (fun b : Fin n → Bool => (bitsToNat b).Prime)) ^ T :=
  uprob_firstHit_none _ T

/-- **Failure probability of `SamplePrime`** [PS10, Lemma 51.17 and p. 50]: for `n ≥ 2`,
`SamplePrime` fails with probability at most `(1 − 1/(2n))^T` (prime density `≥ 1/(2n)`,
Claim-33.1).

**Deviation:** the text's density `1/n` (p. 50) is `1/(2n)`. -/
theorem uprob_samplePrime_none_le (n T : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = none) ≤
      (1 - 1 / (2 * n : ℝ)) ^ T := by
  rw [uprob_samplePrime_none]
  have hdens := one_div_le_uprob_prime n hn
  rw [← uprob_prime_bits] at hdens
  have h1 := uprob_le_one (fun b : Fin n → Bool => (bitsToNat b).Prime)
  exact pow_le_pow_left₀ (by linarith) (by linarith) T

/-- **`SamplePrime` with `2n²` trials fails with probability at most `e^{−n}`**
[PS10, Lemma 51.17]: the truncation of the text's expected-polynomial loop at `T = 2n²`.

**Proof sketch.** `(1 − 1/(2n))^{2n²} = (1 − n/(2n²))^{2n²} ≤ e^{−n}`
(`Real.one_sub_div_pow_le_exp_neg`). -/
theorem uprob_samplePrime_none_le_exp (n : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin (2 * n ^ 2) → (Fin n → Bool) => samplePrime n (2 * n ^ 2) xs = none) ≤
      Real.exp (-n) := by
  refine (uprob_samplePrime_none_le n (2 * n ^ 2) hn).trans ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnn : (n : ℝ) * 1 ≤ n * n := mul_le_mul_of_nonneg_left hn' (by linarith)
  have h := Real.one_sub_div_pow_le_exp_neg (n := 2 * n ^ 2) (t := n)
    (by push_cast; nlinarith)
  have heq : (1 - (n : ℝ) / ((2 * n ^ 2 : ℕ) : ℝ)) = 1 - 1 / (2 * n : ℝ) := by
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- **`SamplePrime` with `2n²` trials fails with probability at most `2^{−n}`**: the form of
[PS10, Lemma 51.17] used by the collections (`e^{−n} ≤ 2^{−n}`). -/
theorem uprob_samplePrime_none_le_two_pow (n : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin (2 * n ^ 2) → (Fin n → Bool) => samplePrime n (2 * n ^ 2) xs = none) ≤
      (1 / 2 : ℝ) ^ n := by
  refine (uprob_samplePrime_none_le_exp n hn).trans ?_
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hinv : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  calc Real.exp (-n) = Real.exp (-1) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hinv n

/-- **`SamplePrime` is statistically close to uniform on `Π_n`** [PS10, Lemma 51.17, the form
consumed by the collections]: falling back to a fixed prime `d` on failure, the sampler is
within `(1 − 1/(2n))^T` of the uniform distribution on the `n`-bit primes (C4,
`statClose_firstHit`). -/
theorem statClose_samplePrime (n T : ℕ) (hn : 2 ≤ n) {d : Fin n → Bool}
    (hd : (bitsToNat d).Prime) :
    StatClose (fun xs : Fin T → (Fin n → Bool) => (samplePrime n T xs).getD d)
      (fun p : {b : Fin n → Bool // (bitsToNat b).Prime} => (p : Fin n → Bool))
      ((1 - 1 / (2 * n : ℝ)) ^ T) := by
  refine (statClose_firstHit (fun b : Fin n → Bool => (bitsToNat b).Prime) T hd).mono ?_
  have hdens := one_div_le_uprob_prime n hn
  rw [← uprob_prime_bits] at hdens
  have h1 := uprob_le_one (fun b : Fin n → Bool => (bitsToNat b).Prime)
  exact pow_le_pow_left₀ (by linarith) (by linarith) T

/-! ### `SamplePrime` as a machine -/

/-- The number read from a bit string on a tape (most significant bit first): the list form of
`bitsToNat`. -/
def listToNat (w : List Bool) : ℕ := w.foldl (fun a c => 2 * a + if c then 1 else 0) 0

/-- `bitsToNat` is `listToNat` of the list of bits. -/
theorem bitsToNat_eq_listToNat {n : ℕ} (b : Fin n → Bool) : bitsToNat b = listToNat (List.ofFn b) :=
  rfl

/-- The coin polynomial of `SamplePrime` at `T = 2n²` trials of `n` bits: `2n² · n`. -/
def samplePrimeCoins : PolyExpr :=
  PolyExpr.mul (PolyExpr.mul (PolyExpr.const 2) (PolyExpr.pow PolyExpr.var 2)) PolyExpr.var

/-- `samplePrimeCoins` evaluates to `2n² · n`. -/
theorem eval_samplePrimeCoins (n : ℕ) : samplePrimeCoins.eval n = 2 * n ^ 2 * n := rfl

/-- The `T` blocks of `n` bits of a coin string of length `T · n`: block `t` is the bits
`t·n, …, t·n + n − 1`. -/
def chunk (T n : ℕ) (r : Fin (T * n) → Bool) : Fin T → Fin n → Bool := fun t i =>
  r ⟨t * n + i, by
    have ht : (t : ℕ) + 1 ≤ T := t.2
    calc (t : ℕ) * n + i < (t : ℕ) * n + n := by omega
      _ = ((t : ℕ) + 1) * n := by ring
      _ ≤ T * n := Nat.mul_le_mul_right n ht⟩

/-! #### The `SamplePrime` state loop -/

/-- The step of the `SamplePrime` loop on the state word `⟨1^n, s⟩`: discard the first `n`
bits of the remaining coins `s`, keeping the parameter. -/
private def spStep (x : List Bool) : List Bool :=
  pairEncode (pairFstD x) ((pairSndD x).drop (PolyExpr.var.eval (pairFstD x).length))

/-- The current candidate of the `SamplePrime` loop on the state word `⟨1^n, s⟩`: the first
`n` bits of the remaining coins `s`. -/
private def spOut (x : List Bool) : List Bool :=
  (pairSndD x).take (PolyExpr.var.eval (pairFstD x).length)

/-- The acceptance test of the `SamplePrime` loop: the current candidate reads as a prime. -/
private def spAcc (x : List Bool) : Bool := decide (listToNat (spOut x)).Prime

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at `var`). -/
private theorem spStep_poly : PolyTimeComputable spStep :=
  polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairDropPoly .var)

/-- The candidate is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` at `var`). -/
private theorem spOut_poly : PolyTimeComputable spOut := polyTimeComputable_pairTakePoly .var

/-- The acceptance test is polynomial-time given the primality test `hP`. -/
private theorem spAcc_poly
    (hP : PolyTimeComputable fun w : List Bool => [decide (listToNat w).Prime]) :
    PolyTimeComputable fun x => [spAcc x] := hP.comp spOut_poly

/-- The orbit of the step from `⟨u, s⟩`: after `i` rounds the state is `⟨u, s.drop (i·|u|)⟩`. -/
private theorem spStep_iterate (u s : List Bool) (i : ℕ) :
    spStep^[i] (pairEncode u s) = pairEncode u (s.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [spStep, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
      List.drop_drop]
    congr 2
    ring

/-- One step at most doubles the length: `|spStep x| ≤ 2|x| + 2`
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
private theorem length_spStep_le (x : List Bool) : (spStep x).length ≤ 2 * x.length + 2 := by
  have := StateLoop.length_pairFstD_add_pairSndD_le x
  simp only [spStep, length_pairEncode, PolyExpr.eval_var, List.length_drop]
  omega

/-- From the first round on the state is a pair whose second component only shrinks. -/
private theorem length_spStep_spStep_le (x : List Bool) :
    (spStep (spStep x)).length ≤ (spStep x).length := by
  simp only [spStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
    PolyExpr.eval_var, List.length_drop]
  omega

/-- The orbit bound `|spStep^[i] x| ≤ 2|x| + 2` demanded by the repetition lemma (for every
word `x`, not only for well-formed state words). -/
private theorem length_spStep_iterate_le (x : List Bool) (i : ℕ) :
    (spStep^[i] x).length ≤ 2 * x.length + 2 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    induction i with
    | zero => exact length_spStep_le x
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact (length_spStep_spStep_le _).trans ih

/-- Block `t` of the coin layout `chunk` is the `t`-th `n`-bit segment of the coin list. -/
private theorem ofFn_chunk {T n : ℕ} (r : Fin (T * n) → Bool) (t : Fin T) :
    List.ofFn (chunk T n r t) = ((List.ofFn r).drop (t * n)).take n := by
  have ht : ((t : ℕ) + 1) * n ≤ T * n := Nat.mul_le_mul_right n t.2
  rw [Nat.add_mul, one_mul] at ht
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp [chunk]

/-- `firstHit` returns the first draw satisfying `E` (induction on the number of draws,
`List.finRange_succ`). -/
private theorem firstHit_eq_some_of_first {α : Type*} (E : α → Prop) [DecidablePred E] :
    ∀ {T : ℕ} (xs : Fin T → α) (t : Fin T), E (xs t) → (∀ t' < t, ¬ E (xs t')) →
      firstHit E xs = some (xs t)
  | 0, _, t, _, _ => t.elim0
  | T + 1, xs, t, ht, hfirst => by
    unfold firstHit
    rw [List.finRange_succ, List.findSome?_cons]
    rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
    · simp [ht]
    · have h0 : ¬ E (xs 0) := hfirst 0 (Fin.succ_pos t')
      simp only [h0, if_false]
      rw [List.findSome?_map]
      have ih := firstHit_eq_some_of_first E (fun s => xs s.succ) t' ht
        (fun s hs => hfirst s.succ (Fin.succ_lt_succ_iff.2 hs))
      unfold firstHit at ih
      exact ih

/-- Along the orbit from `⟨1^n, rs⟩`, the acceptance test at round `i` tests block `i`. -/
private theorem spAcc_iterate (n : ℕ) (rs : List Bool) (i : ℕ) :
    spAcc (spStep^[i] (pairEncode (List.replicate n true) rs)) =
      decide (listToNat ((rs.drop (i * n)).take n)).Prime := by
  rw [spStep_iterate]
  simp [spAcc, spOut]

/-- Along the orbit from `⟨1^n, rs⟩`, the candidate at round `i` is block `i`. -/
private theorem spOut_iterate (n : ℕ) (rs : List Bool) (i : ℕ) :
    spOut (spStep^[i] (pairEncode (List.replicate n true) rs)) = (rs.drop (i * n)).take n := by
  rw [spStep_iterate]
  simp [spOut]

/-- **The loop computes `SamplePrime`:** the `find?` form of the iterated search from the
state word `⟨1^n, r⟩` over `List.range (|⟨1^n, r⟩| + 1)` rounds is `samplePrime n (2n²)` on
the blocks of `r` (as bits, `[]` on failure).

**Proof sketch.** Round `i` tests block `i` (`spAcc_iterate`); blocks `i ≥ 2n²` are empty
and read `0`, not a prime; the range `|⟨1^n, r⟩| + 1 ≥ 2n²` covers every block. If the search
succeeds at round `k` (`List.find?_eq_some_iff_getElem`), then `k < 2n²`, block `k` is prime
and no earlier block is, so `firstHit` returns block `k` (`firstHit_eq_some_of_first`,
`ofFn_chunk`); if it fails, no block is prime and `samplePrime` returns `none`
(`samplePrime_eq_none_iff`). -/
private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
    (match (List.range (PolyExpr.var.eval
        (pairEncode (List.replicate n true) (List.ofFn r)).length + 1)).find?
        (fun i => spAcc (spStep^[i] (pairEncode (List.replicate n true) (List.ofFn r)))) with
      | some i => spOut (spStep^[i] (pairEncode (List.replicate n true) (List.ofFn r)))
      | none => []) =
      ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r)).map List.ofFn).getD [] := by
  have hlen : (List.ofFn r).length = 2 * n ^ 2 * n := List.length_ofFn
  have hblock : ∀ t : Fin (2 * n ^ 2),
      decide (listToNat (((List.ofFn r).drop (t * n)).take n)).Prime =
        decide (bitsToNat (chunk (2 * n ^ 2) n r t)).Prime := by
    intro t
    rw [bitsToNat_eq_listToNat, ofFn_chunk]
  have hbig : ∀ i, 2 * n ^ 2 ≤ i →
      decide (listToNat (((List.ofFn r).drop (i * n)).take n)).Prime = false := by
    intro i hi
    have hnil : (List.ofFn r).drop (i * n) = [] :=
      List.drop_eq_nil_of_le (by rw [hlen]; exact Nat.mul_le_mul_right n hi)
    simp [hnil, listToNat, Nat.not_prime_zero]
  have hrange : 2 * n ^ 2 ≤
      PolyExpr.var.eval (pairEncode (List.replicate n true) (List.ofFn r)).length + 1 := by
    simp only [PolyExpr.eval_var, length_pairEncode, List.length_replicate, hlen]
    have : n ^ 2 ≤ n ^ 2 * n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact Nat.le_mul_of_pos_right _ h
    have h2 : 2 * n ^ 2 * n = 2 * (n ^ 2 * n) := by ring
    omega
  simp only [spAcc_iterate]
  split
  · rename_i k hf
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hpk, j, hj, hjk, hfirst⟩ := hf
    rw [List.getElem_range] at hjk
    subst hjk
    have hkT : j < 2 * n ^ 2 := by
      by_contra h
      rw [hbig j (not_lt.1 h)] at hpk
      exact Bool.false_ne_true hpk
    have hsome : samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r) =
        some (chunk (2 * n ^ 2) n r ⟨j, hkT⟩) := by
      refine firstHit_eq_some_of_first _ _ ⟨j, hkT⟩ ?_ ?_
      · have := hblock ⟨j, hkT⟩
        rw [this] at hpk
        exact of_decide_eq_true hpk
      · intro t' ht'
        have h1 := hfirst t'.val (by simpa using ht')
        rw [List.getElem_range, hblock t'] at h1
        simpa using h1
    rw [hsome, spOut_iterate]
    simp only [Option.map_some, Option.getD_some, ofFn_chunk]
  · rename_i hf
    rw [List.find?_eq_none] at hf
    have hnone : samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r) = none := by
      rw [samplePrime_eq_none_iff]
      intro t ht
      have := hf t (by rw [List.mem_range]; have := t.2; omega)
      rw [hblock t] at this
      exact this (by simpa using ht)
    rw [hnone]
    rfl

/-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
(`polyTimeComputable_pairDropPoly var`), the acceptance test `spAcc` is the primality test
`hP` on the first `n` bits (`polyTimeComputable_pairTakePoly var`), the payload `spOut` is
those `n` bits; `R = var` rounds (the input length `|⟨1^n, r⟩| ≥ 2n²` covers every block,
later rounds see the empty block), orbit length bounded by `P = 2·var + 2`
(`length_spStep_iterate_le`); the `List.range.find?` form of the iterated search is
`firstHit` over the blocks of `r` (`chunk`), `spFind_eq`. Package by
`NUPPT.ofPolyTimeUniform` with `coins = samplePrimeCoins` after the projection
`z ↦ ⟨inParam z, inCoins z⟩`, and read the activation through
`NUPPT.runAtL_ofPolyTimeUniform` and the layout projections. -/
theorem exists_samplePrime_nuppt
    (hP : PolyTimeComputable fun w : List Bool => [decide (listToNat w).Prime]) :
    ∃ A : NUPPT, A.Uniform ∧ A.coins = samplePrimeCoins ∧
      ∀ (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool),
        A.runAtL n [] (List.ofFn r) =
          ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r)).map List.ofFn).getD [] := by
  have hF := polyTimeComputable_iterateFind spStep_poly (spAcc_poly hP) spOut_poly
    PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 2))
    (fun x i _ => by simpa using length_spStep_iterate_le x i)
  have hpre : PolyTimeComputable fun z => pairEncode (NUPPT.inParam z) (NUPPT.inCoins z) :=
    NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  refine ⟨NUPPT.ofPolyTimeUniform (hF.comp hpre) samplePrimeCoins,
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun n r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  have h1 : NUPPT.inParam (pairEncode (pairEncode (NUPPT.advInput n []) []) (List.ofFn r)) =
      List.replicate n true := by
    simp [NUPPT.inParam, NUPPT.advInput]
  have h2 : NUPPT.inCoins (pairEncode (pairEncode (NUPPT.advInput n []) []) (List.ofFn r)) =
      List.ofFn r := by
    simp [NUPPT.inCoins]
  simp only [Function.comp_apply, h1, h2]
  exact spFind_eq n r

end TCSlib.Cryptography.NumberTheory

## ===== TCSlib/Cryptography/NumberTheory/QuadraticResidues.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Units.Equiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quadratic residues, square roots and the Chinese remainder theorem

The square-root theory of [PS10, §2.12] behind the Rabin collection:

* `QR N = {x² | x ∈ Z_N^*}`, the quadratic residues modulo `N`, as a subgroup of `Z_N^*`
  (the image of the squaring homomorphism) [PS10, pp. 57 and 59];
* for an odd prime `p`, `QR_p` has `(p−1)/2` elements and every residue has exactly two
  square roots `±x` [PS10, Lemma 57.1];
* for `p ≡ 3 (mod 4)`, `y ↦ y^{(p+1)/4}` extracts square roots in `QR_p`
  [PS10, Theorem 58.2];
* the Chinese remainder theorem for two coprime moduli at the level of unit groups,
  `crtUnits : Z_{pq}^* ≃* Z_p^* × Z_q^*` [PS10, Theorem 58.3, Mathlib's
  `ZMod.chineseRemainder`];
* `x ∈ QR_N` iff both CRT components are residues [PS10, Theorem 59.4];
* squaring on `Z_N^*` is `4`-to-`1` for `N = pq`, `p ≠ q` odd primes [PS10, Theorem 60.5], so
  `|QR_N| = |Z_N^*|/4` [PS10, Corollary 60.6] and squaring pushes the uniform distribution on
  `Z_N^*` to the uniform distribution on `QR_N` (lemma C5, the sampler of
  [PS10, Theorem 63.10]);
* square roots modulo `N` from square roots modulo `p` and `q` [PS10, Claim-60.7 of the
  inventory, p. 60];
* two square roots `x, z` of the same residue with `z ≠ ±x` factor `N` through
  `gcd(x − z, N)` [PS10, proof of Theorem 61.8, Claim-62.1 of the inventory];
* for a Blum integer (`p ≡ q ≡ 3 (mod 4)`) every residue has exactly one square root in
  `QR_N`, computed by `blumSqrt` [PS10, p. 63, Claim-63.1 of the inventory].

**Deviation:** [PS10, Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6] silently need
`p ≠ q` odd primes (they fail for `N = p²` and for `p = 2`); the hypotheses are explicit.
**Deviation:** [PS10, Theorem 59.4] has the typo "`zinQRq`" and its proof labels the two
directions backwards. The CRT is stated for two moduli only (every use in the chapter).

## Main definitions

* `TCSlib.Cryptography.NumberTheory.QR` — the quadratic residues `QR_N ≤ Z_N^*`.
* `TCSlib.Cryptography.NumberTheory.sqTo` — squaring `Z_N^* → QR_N`.
* `TCSlib.Cryptography.NumberTheory.sqrtMod3` — square roots modulo `p ≡ 3 (mod 4)`.
* `TCSlib.Cryptography.NumberTheory.crtUnits` — the CRT isomorphism of unit groups.
* `TCSlib.Cryptography.NumberTheory.blumSqrt` — the square root in `QR_N` for Blum `N`.

## Main results

* `TCSlib.Cryptography.NumberTheory.card_sqrt_eq_two`,
  `TCSlib.Cryptography.NumberTheory.card_QR_prime` — [PS10, Lemma 57.1].
* `TCSlib.Cryptography.NumberTheory.sq_pow_div_four_succ`,
  `TCSlib.Cryptography.NumberTheory.sqrtMod3_sq` — [PS10, Theorem 58.2].
* `TCSlib.Cryptography.NumberTheory.mem_QR_mul_iff` — [PS10, Theorem 59.4].
* `TCSlib.Cryptography.NumberTheory.card_sqrt_mul_eq_four` — [PS10, Theorem 60.5].
* `TCSlib.Cryptography.NumberTheory.card_QR_mul`,
  `TCSlib.Cryptography.NumberTheory.pushesUniform_sqTo` — [PS10, Corollary 60.6] and C5.
* `TCSlib.Cryptography.NumberTheory.sq_crtUnits_symm` — Claim-60.7.
* `TCSlib.Cryptography.NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq` — Claim-62.1.
* `TCSlib.Cryptography.NumberTheory.blumSqrt_sq`,
  `TCSlib.Cryptography.NumberTheory.blumSqrt_mem_QR`,
  `TCSlib.Cryptography.NumberTheory.eq_blumSqrt_of_sq_eq`,
  `TCSlib.Cryptography.NumberTheory.sqTo_bijective_of_blum` — Claim-63.1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.12: Lemma 57.1, Theorem 58.2, Theorem 58.3, Theorem 59.4, Theorem 60.5,
  Corollary 60.6, the remark on p. 60, the proof of Theorem 61.8, and the remark after
  Theorem 63.10.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset

/-! ### Quadratic residues -/

/-- **The quadratic residues** `QR_N = {x² mod N | x ∈ Z_N^*}` [PS10, p. 57 for `N = p`,
p. 59 for `N = pq`], as the subgroup of `Z_N^* = (ZMod N)ˣ` which is the range of the
squaring homomorphism. -/
def QR (N : ℕ) : Subgroup (ZMod N)ˣ := (powMonoidHom 2 : (ZMod N)ˣ →* (ZMod N)ˣ).range

/-- Unfolding: `x ∈ QR_N` iff `x = y²` for some unit `y`. -/
theorem mem_QR_iff {N : ℕ} (x : (ZMod N)ˣ) : x ∈ QR N ↔ ∃ y : (ZMod N)ˣ, y ^ 2 = x := by
  simp [QR, MonoidHom.mem_range, powMonoidHom_apply]

/-- Membership in `QR_N` is decidable (finite search for a root), so `QR_N` is a `Fintype`. -/
instance (N : ℕ) [NeZero N] : DecidablePred (· ∈ QR N) :=
  MonoidHom.decidableMemRange (powMonoidHom 2 : (ZMod N)ˣ →* (ZMod N)ˣ)

/-- Every square is a residue. -/
theorem sq_mem_QR {N : ℕ} (x : (ZMod N)ˣ) : x ^ 2 ∈ QR N := (mem_QR_iff _).2 ⟨x, rfl⟩

/-- Squaring as a map `Z_N^* → QR_N` (the Rabin function `f_N(x) = x² mod N`
[PS10, Theorems 61.7 and 63.10], with its codomain made explicit). -/
def sqTo (N : ℕ) (x : (ZMod N)ˣ) : QR N := ⟨x ^ 2, sq_mem_QR x⟩

/-- Unfolding: the value of `sqTo`. -/
@[simp] theorem coe_sqTo {N : ℕ} (x : (ZMod N)ˣ) : (sqTo N x : (ZMod N)ˣ) = x ^ 2 := rfl

/-- Fibre counting for the squaring map: if every residue has exactly `c` square roots then
`|Z_N^*| = c · |QR_N|` [PS10, Lemma 57.1 and Corollary 60.6, the counting step].

**Proof sketch.** `Finset.card_eq_sum_card_fiberwise` for `sqTo N : Z_N^* → QR_N`; each fibre
`{x | sqTo N x = y}` is `{x | x² = y}`, of size `c`. -/
theorem card_units_eq_mul_card_QR {N : ℕ} [NeZero N] {c : ℕ}
    (hfib : ∀ y ∈ QR N, (univ.filter fun x : (ZMod N)ˣ => x ^ 2 = y).card = c) :
    Fintype.card (ZMod N)ˣ = c * Nat.card (QR N) := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := (ZMod N)ˣ),
    Finset.card_eq_sum_card_fiberwise (f := sqTo N) (t := univ) (fun _ _ => mem_univ _)]
  have : ∀ y : QR N, (univ.filter fun x : (ZMod N)ˣ => sqTo N x = y).card = c := by
    intro y
    rw [← hfib y y.2]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    rw [Subtype.ext_iff, coe_sqTo]
  simp only [this, sum_const, card_univ, smul_eq_mul, mul_comm]

/-! ### Square roots modulo a prime -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- `-1 ≠ 1` in `Z_p` for an odd prime `p`, in the form `y ≠ -y` for a unit `y`. -/
private theorem ne_neg_self (hp2 : p ≠ 2) (y : (ZMod p)ˣ) : y ≠ -y := by
  intro h
  have h2 : (2 : ZMod p) * (y : ZMod p) = 0 := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    simp only [Units.val_neg] at this
    linear_combination this
  rcases mul_eq_zero.1 h2 with h2 | hy
  · have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2)
    rcases (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this with rfl
    exact hp2 rfl
  · exact y.ne_zero hy

/-- **Residues modulo an odd prime have exactly two square roots** [PS10, Lemma 57.1,
"for every `a ∈ QR_p` there are exactly two distinct values `x` with `x² = a`"]: for
`a ∈ QR_p`, `#{x ∈ Z_p^* | x² = a} = 2`.

**Proof sketch.** With `a = y²`, `x² = y²` iff `(x − y)(x + y) = 0` iff `x = ±y` in the
field `Z_p` (`Units.sq_eq_sq_iff_eq_or_eq_neg`), and `y ≠ −y` since `p` is odd. -/
theorem card_sqrt_eq_two (hp2 : p ≠ 2) {a : (ZMod p)ˣ} (ha : a ∈ QR p) :
    (univ.filter fun x : (ZMod p)ˣ => x ^ 2 = a).card = 2 := by
  obtain ⟨y, rfl⟩ := (mem_QR_iff a).1 ha
  have hfilter : (univ.filter fun x : (ZMod p)ˣ => x ^ 2 = y ^ 2) = {y, -y} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact Units.sq_eq_sq_iff_eq_or_eq_neg
  rw [hfilter, Finset.card_pair (ne_neg_self hp2 y)]

/-- **`|QR_p| = (p−1)/2`** for an odd prime `p` [PS10, Lemma 57.1].

**Proof sketch.** Fibre counting (`card_units_eq_mul_card_QR`) with `c = 2`
(`card_sqrt_eq_two`) and `|Z_p^*| = p − 1`. -/
theorem card_QR_prime (hp2 : p ≠ 2) : Nat.card (QR p) = (p - 1) / 2 := by
  have h := card_units_eq_mul_card_QR (N := p) (c := 2) fun y hy => card_sqrt_eq_two hp2 hy
  rw [ZMod.card_units] at h
  omega

/-- The exponent of [PS10, Theorem 58.2]: for `p = 4k + 3`, `p / 4 + 1 = k + 1`. -/
theorem div_four_succ_eq (hp3 : p % 4 = 3) : 4 * (p / 4 + 1) = (p - 1) + 2 := by
  have := Nat.div_add_mod p 4
  have := hp.out.two_le
  omega

/-- **Square roots modulo `p ≡ 3 (mod 4)`** [PS10, Theorem 58.2]: if `p = 4k + 3` and
`y ∈ QR_p` then `(y^{k+1})² = y` (and so `(−y^{k+1})² = y`), with `k + 1 = p / 4 + 1`.

**Proof sketch.** With `y = a²`: `(y^{k+1})² = a^{4k+4} = a^{p−1} · a² = a² = y` by Fermat's
little theorem (`ZMod.units_pow_card_sub_one_eq_one`). -/
theorem sq_pow_div_four_succ (hp3 : p % 4 = 3) {y : (ZMod p)ˣ} (hy : y ∈ QR p) :
    (y ^ (p / 4 + 1)) ^ 2 = y := by
  obtain ⟨a, rfl⟩ := (mem_QR_iff y).1 hy
  calc ((a ^ 2) ^ (p / 4 + 1)) ^ 2 = a ^ (4 * (p / 4 + 1)) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = a ^ (p - 1) * a ^ 2 := by rw [div_four_succ_eq hp3, pow_add]
    _ = a ^ 2 := by rw [ZMod.units_pow_card_sub_one_eq_one, one_mul]

/-- The root `y^{(p+1)/4}` of [PS10, Theorem 58.2] is itself a residue (an even power of a
root of `y`): the root selected by the Rabin trapdoor [PS10, Theorem 63.10]. -/
theorem pow_div_four_succ_mem_QR {y : (ZMod p)ˣ} (hy : y ∈ QR p) : y ^ (p / 4 + 1) ∈ QR p := by
  obtain ⟨a, rfl⟩ := (mem_QR_iff y).1 hy
  exact (mem_QR_iff _).2 ⟨a ^ (p / 4 + 1), by rw [← pow_mul, ← pow_mul, mul_comm]⟩

/-- **The square-root algorithm for `p ≡ 3 (mod 4)`** [PS10, Theorem 58.2] on residues:
`sqrtMod3 p y = y^{p/4 + 1}`. -/
def sqrtMod3 (p : ℕ) (y : ZMod p) : ZMod p := y ^ (p / 4 + 1)

/-- **Correctness of `sqrtMod3`** [PS10, Theorem 58.2]: for `p ≡ 3 (mod 4)` and a square
`y ∈ Z_p` (including `0`), `(sqrtMod3 p y)² = y`.

**Proof sketch.** `y = 0` is immediate; otherwise `y = a·a` with `a ≠ 0` and
`(y^{k+1})² = a^{p−1} a² = a²` by `ZMod.pow_card_sub_one_eq_one`. -/
theorem sqrtMod3_sq (hp3 : p % 4 = 3) {y : ZMod p} (hy : IsSquare y) : sqrtMod3 p y ^ 2 = y := by
  obtain ⟨a, rfl⟩ := hy
  unfold sqrtMod3
  by_cases ha : a = 0
  · subst ha
    rw [mul_zero, zero_pow (by omega), zero_pow (by norm_num)]
  calc ((a * a) ^ (p / 4 + 1)) ^ 2 = a ^ (4 * (p / 4 + 1)) := by
        rw [← pow_two, ← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = a ^ (p - 1) * a ^ 2 := by rw [div_four_succ_eq hp3, pow_add]
    _ = a * a := by rw [ZMod.pow_card_sub_one_eq_one ha, one_mul, pow_two]

end Prime

/-! ### The Chinese remainder theorem on unit groups -/

section CRT

variable {p q : ℕ}

/-- **The Chinese remainder theorem for units** [PS10, Theorem 58.3, two moduli]: for coprime
`p, q`, reduction modulo `p` and `q` is a group isomorphism `Z_{pq}^* ≃ Z_p^* × Z_q^*`
(Mathlib's ring isomorphism `ZMod.chineseRemainder` restricted to units). -/
def crtUnits (h : p.Coprime q) : (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- The first component of `crtUnits` is reduction modulo `p`. -/
theorem crtUnits_fst (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    ((crtUnits h x).1 : ZMod p) = ((x : ZMod (p * q)).cast : ZMod p) := by
  show (ZMod.chineseRemainder h (x : ZMod (p * q))).1 = _
  exact Prod.fst_zmod_cast _

/-- The second component of `crtUnits` is reduction modulo `q`. -/
theorem crtUnits_snd (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    ((crtUnits h x).2 : ZMod q) = ((x : ZMod (p * q)).cast : ZMod q) := by
  show (ZMod.chineseRemainder h (x : ZMod (p * q))).2 = _
  exact Prod.snd_zmod_cast _

/-- **Residues modulo `pq`** [PS10, Theorem 59.4]: for coprime `p, q` and `x ∈ Z_{pq}^*`,
`x ∈ QR_{pq}` iff `x mod p ∈ QR_p` and `x mod q ∈ QR_q`.

**Deviation:** the text's "`zinQRq`" typo; its proof labels `⇒`/`⇐` backwards.

**Proof sketch.** `crtUnits` is a group isomorphism, so it maps squares to squares and a pair
is a square iff both components are; the inverse direction lifts roots `a, b` of the
components to the root `crtUnits⁻¹(a, b)` of `x`. -/
theorem mem_QR_mul_iff (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    x ∈ QR (p * q) ↔ (crtUnits h x).1 ∈ QR p ∧ (crtUnits h x).2 ∈ QR q := by
  simp only [mem_QR_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨(crtUnits h y).1, by rw [map_pow]; rfl⟩, ⟨(crtUnits h y).2, by rw [map_pow]; rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(crtUnits h).symm (a, b), ?_⟩
    rw [← map_pow, show (a, b) ^ 2 = (a ^ 2, b ^ 2) from rfl, ha, hb, MulEquiv.symm_apply_apply]

/-- **Square roots modulo `N` from square roots modulo the factors** [PS10, p. 60, the remark
after Corollary 60.6; Claim-60.7 of the inventory]: if `a² = x mod p` and `b² = x mod q`
then `s = crtUnits⁻¹(a, b)` satisfies `s² = x`. -/
theorem sq_crtUnits_symm (h : p.Coprime q) {x : (ZMod (p * q))ˣ} {a : (ZMod p)ˣ} {b : (ZMod q)ˣ}
    (ha : a ^ 2 = (crtUnits h x).1) (hb : b ^ 2 = (crtUnits h x).2) :
    ((crtUnits h).symm (a, b)) ^ 2 = x := by
  rw [← map_pow, show (a, b) ^ 2 = (a ^ 2, b ^ 2) from rfl, ha, hb, MulEquiv.symm_apply_apply]

/-- The square roots of `x` modulo `pq` correspond to pairs of square roots modulo `p` and
modulo `q` [PS10, proof of Theorem 60.5]: `#{s | s² = x} = #{a | a² = x mod p} · #{b | b² = x mod q}`.

**Proof sketch.** `crtUnits` restricts to a bijection between the root sets
(`Equiv.subtypeEquiv`, `Equiv.subtypeProdEquivProd`). -/
theorem card_sqrt_mul (h : p.Coprime q) [NeZero p] [NeZero q] (x : (ZMod (p * q))ˣ) :
    (univ.filter fun s : (ZMod (p * q))ˣ => s ^ 2 = x).card =
      (univ.filter fun a : (ZMod p)ˣ => a ^ 2 = (crtUnits h x).1).card *
        (univ.filter fun b : (ZMod q)ˣ => b ^ 2 = (crtUnits h x).2).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_prod]
  refine Fintype.card_congr (((crtUnits h).toEquiv.subtypeEquiv ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : (ZMod p)ˣ => a ^ 2 = (crtUnits h x).1)
      (q := fun b : (ZMod q)ˣ => b ^ 2 = (crtUnits h x).2)))
  intro s
  show s ^ 2 = x ↔ (crtUnits h s).1 ^ 2 = (crtUnits h x).1 ∧ (crtUnits h s).2 ^ 2 = (crtUnits h x).2
  rw [← (crtUnits h).injective.eq_iff, map_pow, Prod.ext_iff]
  rfl

end CRT

/-! ### Squaring modulo `pq` is four-to-one -/

section TwoPrimes

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- Distinct primes are coprime. -/
theorem coprime_of_ne (hpq : p ≠ q) : p.Coprime q := (Nat.coprime_primes hp.out hq.out).2 hpq

/-- **Squaring on `Z_N^*` is `4`-to-`1`** [PS10, Theorem 60.5]: for `N = pq` with `p ≠ q` odd
primes, every residue `y ∈ QR_N` has exactly four square roots in `Z_N^*`.

**Deviation:** the text omits `p ≠ q` and oddness.

**Proof sketch.** `card_sqrt_mul` reduces to the root counts modulo `p` and `q`, each `2`
by `card_sqrt_eq_two` (the components are residues by `mem_QR_mul_iff`). -/
theorem card_sqrt_mul_eq_four (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {y : (ZMod (p * q))ˣ}
    (hy : y ∈ QR (p * q)) : (univ.filter fun x : (ZMod (p * q))ˣ => x ^ 2 = y).card = 4 := by
  have h := coprime_of_ne hpq
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  rw [card_sqrt_mul h, card_sqrt_eq_two hp2 h1, card_sqrt_eq_two hq2 h2]

/-- **`|QR_N| = |Z_N^*| / 4`** [PS10, Corollary 60.6]: for `N = pq`, `p ≠ q` odd primes,
`|Z_N^*| = 4 |QR_N|` (so `|QR_N| = (p−1)(q−1)/4`).

**Proof sketch.** Fibre counting (`card_units_eq_mul_card_QR`) with `c = 4`
(`card_sqrt_mul_eq_four`). -/
theorem card_QR_mul (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    Fintype.card (ZMod (p * q))ˣ = 4 * Nat.card (QR (p * q)) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  exact card_units_eq_mul_card_QR fun y hy => card_sqrt_mul_eq_four hpq hp2 hq2 hy

/-- **Squaring pushes uniform to uniform** (lemma C5 for `QR_N`; the sampler of
[PS10, Theorem 63.10 (3)] and the "same distribution" step of [PS10, Theorem 61.8]): for
`N = pq`, `p ≠ q` odd primes, the square of a uniform unit is a uniform residue.

**Proof sketch.** `pushesUniform_of_card_fiber` with every fibre of `sqTo N` of size `4`
(`card_sqrt_mul_eq_four`). -/
theorem pushesUniform_sqTo (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
    HardcoreBit.PushesUniform (sqTo (p * q)) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  refine pushesUniform_of_card_fiber (sqTo (p * q)) (c := 4) (by norm_num) fun y => ?_
  rw [← card_sqrt_mul_eq_four hpq hp2 hq2 y.2]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [Subtype.ext_iff, coe_sqTo]

/-- **Two square roots that differ by more than a sign factor `N`** [PS10, proof of
Theorem 61.8; Claim-62.1 of the inventory]: for `N = pq` with `p ≠ q` primes and units `x, z`
with `x² = z²`, `z ≠ x` and `z ≠ −x`, the number `gcd((x − z) mod N, N)` is `p` or `q`.

**Proof sketch.** `(x − z)(x + z) = 0` in `Z_N`, so `N ∣ (x−z).val · (x+z).val`; `x − z ≠ 0` and
`x + z ≠ 0` give `N ∤ (x−z).val` and `N ∤ (x+z).val` (both values are `< N`). By
`Nat.Prime.dvd_mul`, each of `p, q` divides `(x−z).val` or `(x+z).val`; not both divide
`(x−z).val` (else `N ∣ (x−z).val`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`) and not both divide
`(x+z).val`; so exactly one of them divides `(x−z).val`, and the gcd with `N = pq`, a
divisor of `N` different from `1` and `N`, is that prime (`Nat.dvd_mul`, `Nat.dvd_prime`). -/
theorem gcd_sub_eq_prime_of_sq_eq_sq (hpq : p ≠ q) {x z : (ZMod (p * q))ˣ} (hsq : x ^ 2 = z ^ 2)
    (hne : z ≠ x) (hne' : z ≠ -x) :
    Nat.gcd ((x : ZMod (p * q)) - z).val (p * q) = p ∨
      Nat.gcd ((x : ZMod (p * q)) - z).val (p * q) = q := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcop : p.Coprime q := coprime_of_ne hpq
  -- `(x − z)(x + z) = 0` in `Z_N`
  have hprod : ((x : ZMod (p * q)) - (z : ZMod (p * q))) * ((x : ZMod (p * q)) + (z : ZMod (p * q))) = 0 := by
    have h2 : (x : ZMod (p * q)) ^ 2 = (z : ZMod (p * q)) ^ 2 := by
      have := congrArg Units.val hsq
      simpa [Units.val_pow_eq_pow_val] using this
    linear_combination h2
  have hdvd : p * q ∣ ((x : ZMod (p * q)) - z).val * ((x : ZMod (p * q)) + z).val := by
    have := ZMod.val_mul ((x : ZMod (p * q)) - (z : ZMod (p * q)))
      ((x : ZMod (p * q)) + (z : ZMod (p * q)))
    rw [hprod, ZMod.val_zero] at this
    exact Nat.dvd_of_mod_eq_zero this.symm
  -- neither factor is divisible by `N`
  have hd0 : ¬ p * q ∣ ((x : ZMod (p * q)) - z).val := by
    intro hdv
    have h0 : ((x : ZMod (p * q)) - z) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdv (ZMod.val_lt _))
    exact hne (Units.ext (sub_eq_zero.1 h0).symm)
  have he0 : ¬ p * q ∣ ((x : ZMod (p * q)) + z).val := by
    intro hdv
    have h0 : ((x : ZMod (p * q)) + z) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdv (ZMod.val_lt _))
    apply hne'
    apply Units.ext
    rw [Units.val_neg]
    exact eq_neg_of_add_eq_zero_right h0
  have hp_dvd := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_mul_right p q) hdvd)
  have hq_dvd := (Nat.Prime.dvd_mul hq.out).1 (dvd_trans (dvd_mul_left q p) hdvd)
  rcases hp_dvd with hpd | hpe <;> rcases hq_dvd with hqd | hqe
  · exact absurd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd) hd0
  · left
    have hqd : ¬ q ∣ ((x : ZMod (p * q)) - z).val :=
      fun hqd => hd0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd)
    rw [Nat.Coprime.gcd_mul _ hcop, Nat.gcd_eq_right hpd,
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hqd).symm, mul_one]
  · right
    have hpd : ¬ p ∣ ((x : ZMod (p * q)) - z).val :=
      fun hpd => hd0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd)
    rw [Nat.Coprime.gcd_mul _ hcop, Nat.gcd_eq_right hqd,
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpd).symm, one_mul]
  · exact absurd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpe hqe) he0

end TwoPrimes

/-! ### Blum integers -/

section Blum

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **The square root in `QR_N` of a Blum integer** [PS10, Theorem 63.10, `f⁻¹_{p,q}`]: for
`N = pq` with `p ≡ q ≡ 3 (mod 4)`, combine the roots `y^{(p+1)/4} mod p` and `y^{(q+1)/4} mod q`
of [PS10, Theorem 58.2] by the CRT. -/
def blumSqrt (h : p.Coprime q) (y : (ZMod (p * q))ˣ) : (ZMod (p * q))ˣ :=
  (crtUnits h).symm ((crtUnits h y).1 ^ (p / 4 + 1), (crtUnits h y).2 ^ (q / 4 + 1))

/-- **`blumSqrt` is a square root** [PS10, Theorem 63.10 (6)]: for `p ≡ q ≡ 3 (mod 4)` and
`y ∈ QR_N`, `(blumSqrt y)² = y`.

**Proof sketch.** The components of `y` are residues (`mem_QR_mul_iff`), their
`(·)^{(p+1)/4}` powers are roots (`sq_pow_div_four_succ`), and `sq_crtUnits_symm` combines
them. -/
theorem blumSqrt_sq (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) {y : (ZMod (p * q))ˣ}
    (hy : y ∈ QR (p * q)) : (blumSqrt h y) ^ 2 = y := by
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  exact sq_crtUnits_symm h (sq_pow_div_four_succ hp3 h1) (sq_pow_div_four_succ hq3 h2)

/-- **`blumSqrt` lands in `QR_N`** [PS10, p. 63, "only one of the roots is also a square"]:
for `y ∈ QR_N`, `blumSqrt y ∈ QR_N`.

**Proof sketch.** Both components are residues (`pow_div_four_succ_mem_QR`), and
`mem_QR_mul_iff` for `crtUnits⁻¹(a, b)`. -/
theorem blumSqrt_mem_QR (h : p.Coprime q) {y : (ZMod (p * q))ˣ} (hy : y ∈ QR (p * q)) :
    blumSqrt h y ∈ QR (p * q) := by
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  rw [mem_QR_mul_iff h, blumSqrt, MulEquiv.apply_symm_apply]
  exact ⟨pow_div_four_succ_mem_QR h1, pow_div_four_succ_mem_QR h2⟩

/-- **Uniqueness of the residue root** [PS10, p. 63, Claim-63.1 of the inventory]: for a Blum
integer `N = pq` (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`), a residue `x ∈ QR_N` with `x² = y` equals
`blumSqrt y`.

**Proof sketch.** Let `a = x mod p`, `r = (y mod p)^{(p+1)/4}`; both are residues with
`a² = r² = y mod p`, so `a = ±r` (`Units.sq_eq_sq_iff_eq_or_eq_neg`). If `a = −r` then
`−1 = a r⁻¹` is a residue (quotient of residues, `QR p` a subgroup), contradicting
`ZMod.exists_sq_eq_neg_one_iff` for `p ≡ 3 (mod 4)`; hence `a = r`. Likewise modulo `q`; so
`crtUnits x = crtUnits (blumSqrt y)` and `x = blumSqrt y` by injectivity. -/
theorem eq_blumSqrt_of_sq_eq (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    {x y : (ZMod (p * q))ˣ} (hx : x ∈ QR (p * q)) (hxy : x ^ 2 = y) : x = blumSqrt h y := by
  obtain ⟨hxp, hxq⟩ := (mem_QR_mul_iff h x).1 hx
  have hy : y ∈ QR (p * q) := hxy ▸ sq_mem_QR x
  obtain ⟨hyp, hyq⟩ := (mem_QR_mul_iff h y).1 hy
  -- the component lemma: a residue root of a residue is the `(·)^{(r+1)/4}` root
  have key : ∀ {r : ℕ} [Fact r.Prime] (_ : r % 4 = 3) {a b : (ZMod r)ˣ},
      a ∈ QR r → b ∈ QR r → a ^ 2 = b → a = b ^ (r / 4 + 1) := by
    intro r _ hr3 a b ha hb hab
    have hroot : (b ^ (r / 4 + 1)) ^ 2 = b := sq_pow_div_four_succ hr3 hb
    have hmem : b ^ (r / 4 + 1) ∈ QR r := pow_div_four_succ_mem_QR hb
    rcases Units.sq_eq_sq_iff_eq_or_eq_neg.1 (hab.trans hroot.symm) with h1 | h1
    · exact h1
    · exfalso
      have hneg : (-1 : (ZMod r)ˣ) ∈ QR r := by
        have : (-1 : (ZMod r)ˣ) = a * (b ^ (r / 4 + 1))⁻¹ := by
          rw [h1, neg_mul, mul_inv_cancel]
        rw [this]
        exact (QR r).mul_mem ha ((QR r).inv_mem hmem)
      obtain ⟨u, hu⟩ := (mem_QR_iff _).1 hneg
      have hsq : IsSquare (-1 : ZMod r) := by
        refine ⟨(u : ZMod r), ?_⟩
        have := congrArg Units.val hu
        rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
        rw [← this, sq]
      exact ZMod.exists_sq_eq_neg_one_iff.1 hsq hr3
  have hp' : (crtUnits h x).1 = (crtUnits h y).1 ^ (p / 4 + 1) :=
    key hp3 hxp hyp (by rw [← hxy, map_pow]; rfl)
  have hq' : (crtUnits h x).2 = (crtUnits h y).2 ^ (q / 4 + 1) :=
    key hq3 hxq hyq (by rw [← hxy, map_pow]; rfl)
  apply (crtUnits h).injective
  rw [blumSqrt, MulEquiv.apply_symm_apply, Prod.ext_iff]
  exact ⟨hp', hq'⟩

/-- **Squaring is a permutation of `QR_N` for a Blum integer** [PS10, Theorem 63.10 (1),
"this makes Rabin a (trapdoor) permutation"]: `sqTo N` restricted to `QR_N` is a bijection of
`QR_N`, with inverse `blumSqrt`.

**Proof sketch.** Injective by `eq_blumSqrt_of_sq_eq` (two residue roots of the same `y` are
both `blumSqrt y`); surjective by `blumSqrt_sq` and `blumSqrt_mem_QR`. -/
theorem sqTo_bijective_of_blum (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) :
    Function.Bijective (fun x : QR (p * q) => sqTo (p * q) (x : (ZMod (p * q))ˣ)) := by
  constructor
  · intro x x' hxx'
    have hsq : (x : (ZMod (p * q))ˣ) ^ 2 = (x' : (ZMod (p * q))ˣ) ^ 2 := by
      have := congrArg (fun u : QR (p * q) => (u : (ZMod (p * q))ˣ)) hxx'
      simpa using this
    exact Subtype.ext ((eq_blumSqrt_of_sq_eq h hp3 hq3 x.2 rfl).trans
      (eq_blumSqrt_of_sq_eq h hp3 hq3 x'.2 hsq.symm).symm)
  · intro y
    exact ⟨⟨blumSqrt h y, blumSqrt_mem_QR h y.2⟩, Subtype.ext (blumSqrt_sq h hp3 hq3 y.2)⟩

end Blum

end TCSlib.Cryptography.NumberTheory

## ===== TCSlib/Cryptography/NumberTheory/Units.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Max

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The group `Z_N^*`, Euler's theorem and the RSA permutation

The multiplicative group `Z_N^* = (ZMod N)ˣ` of [PS10, §2.6.4] and the consequences of
Euler's theorem that the RSA and factoring candidates of [PS10, §2.7–§2.9] use:

* `Z_N^*` is the group of units of `ZMod N`; its elements are the residues `x ∈ [1, N−1]` with
  `gcd(x, N) = 1` [PS10, Theorem 46.8] (Mathlib: `ZMod.unitsEquivCoprime`,
  `ZMod.isUnit_iff_coprime`; `units_val_mem` records the range `[1, N−1]`);
* `|Z_N^*| = Φ(N)` with `Φ(p) = p − 1` and `Φ(pq) = (p−1)(q−1)` for distinct primes
  [PS10, Claim 47.2 and p. 47];
* Euler's theorem `a^{Φ(N)} = 1` [PS10, Theorem 47.10] is `ZMod.pow_totient`; Fermat's
  little theorem [PS10, Corollary 48.11] is `ZMod.pow_card_sub_one_eq_one`;
* exponents may be reduced modulo `Φ(N)` [PS10, Corollary 48.12];
* `x ↦ x^e` is a permutation of `Z_N^*` when `e ∈ Z^*_{Φ(N)}`, with inverse `y ↦ y^d` for
  `ed ≡ 1 (mod Φ(N))` [PS10, Theorem 54.3];
* the density `Φ(m)/m ≥ 1/(log₂ m + 1)` (inventory lemma C9), used to sample `Z^*_{Φ(N)}` by
  rejection in [PS10, Theorem 53.2].

**Deviation:** the text's `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`
(`Φ(p²) = p(p−1)`); the hypothesis is explicit here.

## Main definitions

None: `Z_N^*` is `(ZMod N)ˣ` and `Φ` is `Nat.totient` (Mathlib).

## Main results

* `TCSlib.Cryptography.NumberTheory.totient_prime_mul_prime`,
  `TCSlib.Cryptography.NumberTheory.card_units_zmod_prime_mul_prime` — `Φ(pq) = (p−1)(q−1)`
  and `|Z_{pq}^*|` [PS10, Claim 47.2].
* `TCSlib.Cryptography.NumberTheory.units_pow_mod_totient`,
  `TCSlib.Cryptography.NumberTheory.pow_mod_totient_modEq` — `a^x = a^{x mod Φ(N)}`
  [PS10, Corollary 48.12].
* `TCSlib.Cryptography.NumberTheory.rsa_pow_pow`,
  `TCSlib.Cryptography.NumberTheory.rsa_pow_bijective` — the RSA permutation and its inverse
  [PS10, Theorem 54.3].
* `TCSlib.Cryptography.NumberTheory.le_totient_mul_log_succ` — `m ≤ Φ(m)(⌊log₂ m⌋ + 1)` (C9).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.4: Theorem 46.8, Claim 47.2, Theorem 47.10, Corollaries 48.11–48.12; §2.9:
  Theorem 54.3.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Nat

/-! ### The group `Z_N^*` -/

/-- The elements of `Z_N^*` are residues in `[1, N−1]` [PS10, Theorem 46.8, the description
`Z_N^* = {x ∈ [1, N−1] | gcd(x, N) = 1}`; the coprimality is `ZMod.unitsEquivCoprime`]. -/
theorem units_val_mem {N : ℕ} [Fact (1 < N)] (u : (ZMod N)ˣ) :
    1 ≤ (u : ZMod N).val ∧ (u : ZMod N).val ≤ N - 1 := by
  have hne : (u : ZMod N) ≠ 0 := u.ne_zero
  have hlt := (u : ZMod N).val_lt
  have hpos : (u : ZMod N).val ≠ 0 := fun h => hne (ZMod.val_eq_zero _ |>.1 h)
  omega

/-- **The totient of a product of two distinct primes** [PS10, Claim 47.2 and p. 47]:
`Φ(pq) = (p−1)(q−1)`; also `Φ(p) = p − 1` (`Nat.totient_prime`).

**Deviation:** `p ≠ q` is required (the text omits it). -/
theorem totient_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    φ (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]

/-- `|Z_{pq}^*| = Φ(pq) = (p−1)(q−1)` for distinct primes [PS10, Claim 47.2,
"`|Z_N^*| = Φ(N)`"]. -/
theorem card_units_zmod_prime_mul_prime {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) : Fintype.card (ZMod (p * q))ˣ = (p - 1) * (q - 1) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  rw [ZMod.card_units_eq_totient, totient_prime_mul_prime hp.out hq.out hpq]

/-! ### Euler's theorem and exponent reduction -/

/-- **Exponent reduction modulo `Φ(N)`** [PS10, Corollary 48.12]: for `a ∈ Z_N^*` and every
`x`, `a^x = a^{x mod Φ(N)}`.

**Proof sketch.** Write `x = Φ(N)⌊x/Φ(N)⌋ + (x mod Φ(N))` and apply Euler's theorem
`a^{Φ(N)} = 1` (`ZMod.pow_totient`). -/
theorem units_pow_mod_totient {N : ℕ} (a : (ZMod N)ˣ) (x : ℕ) : a ^ x = a ^ (x % φ N) := by
  conv_lhs => rw [← Nat.div_add_mod x (φ N)]
  rw [pow_add, pow_mul, ZMod.pow_totient, one_pow, one_mul]

/-- **Exponent reduction modulo `Φ(N)`, integer form** [PS10, Corollary 48.12]: for
`gcd(a, N) = 1`, `a^x ≡ a^{x mod Φ(N)} (mod N)`. -/
theorem pow_mod_totient_modEq {a N : ℕ} (h : Nat.Coprime a N) (x : ℕ) :
    a ^ x ≡ a ^ (x % φ N) [MOD N] := by
  conv_lhs => rw [← Nat.div_add_mod x (φ N)]
  rw [pow_add, pow_mul]
  calc (a ^ φ N) ^ (x / φ N) * a ^ (x % φ N) ≡ 1 ^ (x / φ N) * a ^ (x % φ N) [MOD N] :=
        ((Nat.ModEq.pow_totient h).pow _).mul_right _
    _ = a ^ (x % φ N) := by rw [one_pow, one_mul]

/-! ### The RSA permutation -/

/-- **RSA decryption inverts encryption** [PS10, Theorem 54.3]: if `ed ≡ 1 (mod Φ(N))` then
`(x^e)^d = x` for every `x ∈ Z_N^*`; so `y ↦ y^d` is the inverse of `x ↦ x^e`.

**Proof sketch.** `(x^e)^d = x^{ed} = x^{ed mod Φ(N)} = x^{1 mod Φ(N)} = x` by
`units_pow_mod_totient`. -/
theorem rsa_pow_pow {N e d : ℕ} (hed : e * d ≡ 1 [MOD φ N]) (x : (ZMod N)ˣ) :
    (x ^ e) ^ d = x := by
  rw [← pow_mul, units_pow_mod_totient x (e * d), show e * d % φ N = 1 % φ N from hed,
    ← units_pow_mod_totient, pow_one]

/-- **RSA is a permutation** [PS10, Theorem 54.3]: for `e` coprime to `Φ(N)` (i.e.
`e ∈ Z^*_{Φ(N)}`), `x ↦ x^e` is a bijection of `Z_N^*`.

**Proof sketch.** `|Z_N^*| = Φ(N)` (`ZMod.card_units_eq_totient`), and raising to a power
coprime to the group order is a bijection of any finite group (`powCoprime`; the inverse is
`y ↦ y^d` with `ed ≡ 1 (mod Φ(N))`, `rsa_pow_pow`). -/
theorem rsa_pow_bijective {N e : ℕ} [NeZero N] (he : Nat.Coprime e (φ N)) :
    Function.Bijective (fun x : (ZMod N)ˣ => x ^ e) := by
  have h : (Nat.card (ZMod N)ˣ).Coprime e := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact he.symm
  exact (powCoprime h).bijective

/-- **Existence of the decryption exponent** [PS10, Theorem 54.3, "let `d` be its inverse"]:
for `e ∈ Z^*_{Φ(N)}` and `N > 2` there is `d < Φ(N)` with `ed ≡ 1 (mod Φ(N))`. -/
theorem exists_rsa_inverse {N e : ℕ} (hN : 2 < N) (he : Nat.Coprime e (φ N)) :
    ∃ d, d < φ N ∧ e * d ≡ 1 [MOD φ N] := by
  have h1 : 1 < φ N := by
    have hpos : 0 < φ N := Nat.totient_pos.2 (by omega)
    have heven := Nat.totient_even hN
    rcases heven with ⟨k, hk⟩
    omega
  obtain ⟨d, hd⟩ := Nat.exists_mul_emod_eq_one_of_coprime he h1
  refine ⟨d % φ N, Nat.mod_lt _ (by omega), ?_⟩
  show e * (d % φ N) % φ N = 1 % φ N
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hd, Nat.one_mod_eq_one.2 (by omega)]

/-! ### Density of units -/

/-- The combinatorial core of C9: for a finite set `S` of naturals `≥ 2`,
`∏_{p ∈ S} p ≤ (∏_{p ∈ S} (p − 1)) · (|S| + 1)` (the `k` distinct elements `p_1 < ⋯ < p_k`
satisfy `p_i ≥ i + 1`, so `∏ p_i/(p_i − 1) ≤ ∏ (i+1)/i = k + 1`).

**Proof sketch.** Induction on `S` removing its maximum `a` (`Finset.induction_on_max`): the
remaining `k` elements lie in `[2, a)`, so `k + 2 ≤ a`, and then
`a · k' ≤ (a − 1)(k' + 1)` for `k' = k + 1`. -/
private theorem prod_le_prod_pred_mul_card (S : Finset ℕ) :
    (∀ p ∈ S, 2 ≤ p) → ∏ p ∈ S, p ≤ (∏ p ∈ S, (p - 1)) * (S.card + 1) := by
  induction S using Finset.induction_on_max with
  | h0 => intro; simp
  | step a s hlt ih =>
    intro hS
    have ha : 2 ≤ a := hS a (Finset.mem_insert_self _ _)
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hcard : s.card ≤ a - 2 := by
      have hsub : s ⊆ Finset.Ico 2 a := fun x hx => Finset.mem_Ico.2 ⟨hs x hx, hlt x hx⟩
      have := Finset.card_le_card hsub
      rwa [Nat.card_Ico] at this
    rw [Finset.prod_insert hnot, Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have hstep : a * (s.card + 1) ≤ (a - 1) * (s.card + 1 + 1) := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have : s.card + 1 ≤ a' := by omega
      nlinarith
    calc a * ∏ p ∈ s, p ≤ a * ((∏ p ∈ s, (p - 1)) * (s.card + 1)) := Nat.mul_le_mul_left _ (ih hs)
      _ = (∏ p ∈ s, (p - 1)) * (a * (s.card + 1)) := by ring
      _ ≤ (∏ p ∈ s, (p - 1)) * ((a - 1) * (s.card + 1 + 1)) := Nat.mul_le_mul_left _ hstep
      _ = (a - 1) * (∏ p ∈ s, (p - 1)) * (s.card + 1 + 1) := by ring

/-- **Density of units** (inventory lemma C9, used to sample `Z^*_{Φ(N)}` by rejection in
[PS10, Theorem 53.2]): for `m ≥ 1`, `Φ(m)/m ≥ 1/(⌊log₂ m⌋ + 1)`, i.e.
`m ≤ Φ(m) · (⌊log₂ m⌋ + 1)`.

**Proof sketch.** `Φ(m)/m = ∏_{p ∣ m} (1 − 1/p)` (`Nat.totient_eq_div_primeFactors_mul` /
`Nat.totient_mul_prod_primeFactors`). If `m` has `k` distinct prime factors
`p_1 < ⋯ < p_k` then `p_i ≥ i + 1`, so `∏ (1 − 1/p_i) ≥ ∏_{i=1}^k i/(i+1) = 1/(k+1)`; and
`2^k ≤ ∏ p_i ≤ m` gives `k ≤ ⌊log₂ m⌋`. Sub-obligations: the sorted enumeration of
`m.primeFactors` with `p_i ≥ i + 1` (`Finset.orderEmbOfFin`, strictly increasing from `≥ 2`),
the telescoping product, and `Finset.prod_le` monotonicity. -/
theorem le_totient_mul_log_succ (m : ℕ) (hm : 0 < m) : m ≤ φ m * (Nat.log 2 m + 1) := by
  have hS : ∀ p ∈ m.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hcore := prod_le_prod_pred_mul_card m.primeFactors hS
  have hcard : m.primeFactors.card ≤ Nat.log 2 m := by
    apply Nat.le_log_of_pow_le one_lt_two
    calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hS
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := hS p hp; omega
  have hkey := Nat.totient_mul_prod_primeFactors m
  refine Nat.le_of_mul_le_mul_right (c := ∏ p ∈ m.primeFactors, (p - 1)) ?_ hpos
  calc m * ∏ p ∈ m.primeFactors, (p - 1) = φ m * ∏ p ∈ m.primeFactors, p := hkey.symm
    _ ≤ φ m * ((∏ p ∈ m.primeFactors, (p - 1)) * (m.primeFactors.card + 1)) :=
        Nat.mul_le_mul_left _ hcore
    _ ≤ φ m * ((∏ p ∈ m.primeFactors, (p - 1)) * (Nat.log 2 m + 1)) := by gcongr
    _ = φ m * (Nat.log 2 m + 1) * ∏ p ∈ m.primeFactors, (p - 1) := by ring

end TCSlib.Cryptography.NumberTheory

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
* `TCSlib.Cryptography.Candidates.natToList_length_listToNat`,
  `TCSlib.Cryptography.Candidates.natToList_val_natCast` — a numeral is the numeral of its
  value at its own width (canonicity of the candidates' decoders).
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

/-- **A numeral rewritten at its own width is unchanged**: `natToList |w| (listToNat w) = w`
(the numeral decoders of the candidates are canonical; gate 03b, finding 1). -/
theorem natToList_length_listToNat (w : List Bool) : natToList w.length (listToNat w) = w := by
  have h := natToBits_bitsToNat w.get
  rw [bitsToNat_eq_listToNat, List.ofFn_get] at h
  rw [natToList, h, List.ofFn_get]

/-- **A numeral of width `k` reading below `M` is the `k`-bit numeral of its residue in
`Z_M`**: `natToList k ((listToNat w : Z_M).val) = w` for `|w| = k` and `listToNat w < M`. -/
theorem natToList_val_natCast {k M : ℕ} {w : List Bool} (hk : w.length = k)
    (hM : listToNat w < M) : natToList k ((listToNat w : ZMod M).val) = w := by
  rw [ZMod.val_cast_of_lt hM, ← hk, natToList_length_listToNat]

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

## ===== TCSlib/Cryptography/Asymptotic/Collections.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
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
Algorithm 104.3 and Theorem 104.4); and the equivalence with single strong one-way functions
[PS10, Theorem 42.2].

A `Collection` (foundation decisions D3–D5, D10) has string indices `i : List Bool`, at each
index a finite inhabited domain `D i` with an encoding `encD i` and a total, canonical decoder
`decD i` (a string decodes only if it is an encoding, `encD_decD`),
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

Repair (gate 03b, finding 1; ruling G3-1): decoding is canonical (`Collection.encD_decD`), so
the outputs of the sampler and of the trapdoor inverter are encodings, on which every function
correct on encodings is right (`Collection.apply_of_decD`). The helpers of Theorem 42.2 are in
`TCSlib.Cryptography.Asymptotic.CollectionsHelpers` (names unchanged).

## Main definitions

* `TCSlib.Cryptography.Collection` (`encD_decD`, `sample_spec`, `index`, `trap`, `SampleClose`,
  `invProbAt`), `TCSlib.Cryptography.Collection.OneWay` — collections of one-way functions
  [PS10, Definition 41.1]; `TCSlib.Cryptography.Collection.HardCore` — hard-core predicate
  for a collection [PS10, Definition 78.3, collection form].
* `TCSlib.Cryptography.PermCollection`, `PermCollection.OneWay` [PS10, Definition 55.1];
  `TCSlib.Cryptography.TrapdoorCollection`, `TrapdoorCollection.OneWay`
  [PS10, Definition 56.1].
* `TCSlib.Cryptography.FunFamily.toCollection` [PS10, Theorem 42.2 ⇐] (with
  `Complexity.NUPPT.withIndexParam` of `CollectionsHelpers`);
  `TCSlib.Cryptography.Collection.owfRaw`, `Collection.owfFamily`, `Collection.OutLenBound`,
  `Collection.EvalSampled` [PS10, Theorem 42.2 ⇒] (with `splitCoins` of `CollectionsHelpers`).

## Main results

* `TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay`,
  `FunFamily.StrongOneWay.exists_collection_oneWay` — [PS10, Theorem 42.2 ⇐] (proved).
* `TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay` (proved from the explicit
  form), `Collection.OneWay.owfFamily_strongOneWay` — [PS10, Theorem 42.2 ⇒] (proved).
* `TCSlib.Cryptography.Collection.evalSampled` — honest evaluation on sampled strings, from
  `sample_spec`.
* `TCSlib.Cryptography.Collection.decD_eq_some_iff`, `Collection.apply_of_decD`,
  `Collection.eval_of_decD`, `Collection.sample_eq_encD`, `Collection.HardCore.evaluator` —
  canonical decoding and its consequences.
* `TCSlib.Cryptography.Collection.exists_outLenBound` — `g` has a polynomial output length.
* `TCSlib.Cryptography.TrapdoorCollection.inv_preimage`, `TrapdoorCollection.inv_eq_encD`,
  `TrapdoorCollection.eval_inv`, `TCSlib.Cryptography.PermCollection.f_injective` — sanity for
  Definitions 55.1 and 56.1 (decode level and string level).
* `TCSlib.Cryptography.FunFamily.not_toCollection_oneWay_id` — non-vacuity: the collection of
  the identity is not one-way.

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
string indices, finite inhabited domains with an encoding and a total decoder that is
canonical (a string decodes to `x` only if it is the encoding of `x`, `encD_decD`), the string
function `f i`, a uniform `NUPPT` index generator `Gen(1^n) = ⟨i, t⟩` (`t` ignored by plain
collections), a uniform `NUPPT` domain sampler `Sample(1^n, i)` whose outputs at generated
indices are elements of `D_i` on which the evaluator computes `f_i` (`sample_spec`, the
membership half of clause (2)), and a polynomial-time evaluator `eval ⟨i, x⟩ = f i x` on
encoded elements. The uniformity and hardness clauses are the predicates `SampleClose` and
`OneWay`.

Repair (run-3 audit P3-1): the field `sample_spec` was added (see its docstring).
Repair (gate 03b, finding 1; ruling G3-1): the field `encD_decD` was added (see its
docstring). -/
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
  /-- Decoding is canonical: a string decodes only if it is the encoding of its value, so the
  sampler's outputs (`sample_spec`) and the trapdoor inverter's (`inv_spec`) are encodings
  [PS10, Definitions 41.1 (2), 56.1 (6): "an element of `D_i`", "computes `f_i^{-1}(y)`"].
  Repair (gate 03b, finding 1; ruling G3-1): with a lenient decoder the sampler and the inverter
  could output strings on which `eval` and a hard-core evaluator (pinned on encodings) misbehave;
  the inversion game is now the text's, whose adversary answers with an element. -/
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w
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
[PS10, Definition 78.3], unnumbered, used by Lemma 84.1, Algorithm 104.3 and Theorem 104.4):
`h_i(x)` is polynomial-time computable from `⟨i, x⟩` (on the encoding of `x`, hence on every
string decoding to `x`, `HardCore.evaluator`), and for every non-uniform PPT `A` there
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

/-! ### Canonical decoding (gate 03b, finding 1) -/

/-- **A string decodes to `x` iff it is the encoding of `x`** (`decD_encD` and the canonicity
field `encD_decD`). -/
theorem decD_eq_some_iff (F : Collection) {i w : List Bool} {x : F.D i} :
    F.decD i w = some x ↔ w = F.encD i x :=
  ⟨fun h => (F.encD_decD i w x h).symm, fun h => h ▸ F.decD_encD i x⟩

/-- **A function correct on encodings is correct on every decodable string**: if
`g ⟨i, encD_i x⟩ = v_i(x)` for every `i` and `x`, then `g ⟨i, w⟩ = v_i(x)` whenever `w`
decodes to `x` (canonical decoding, `encD_decD`). -/
theorem apply_of_decD (F : Collection) {β : Type*} {g : List Bool → β} {v : ∀ i, F.D i → β}
    (hg : ∀ i x, g (pairEncode i (F.encD i x)) = v i x) {i w : List Bool} {x : F.D i}
    (h : F.decD i w = some x) : g (pairEncode i w) = v i x := by
  rw [← F.encD_decD i w x h]
  exact hg i x

/-- **The evaluator computes `f_i` on every decodable string**: `eval ⟨i, w⟩ = f_i(x)` whenever
`w` decodes to `x` ([PS10, Definition 41.1 (3)] on every representation of `x`). -/
theorem eval_of_decD (F : Collection) {i w : List Bool} {x : F.D i} (h : F.decD i w = some x) :
    F.eval (pairEncode i w) = F.f i x :=
  F.apply_of_decD F.eval_spec h

/-- **The sampler outputs encodings** ([PS10, Definition 41.1 (2)], "returns an element of
`D_i`"): at every generated index, every output of `Sample(1^n, i)` is `encD_i x` for some
`x ∈ D_i` (`sample_spec` and canonical decoding). -/
theorem sample_eq_encD (F : Collection) (n : ℕ) (r : F.gen.Coins n) (s : F.sample.Coins n) :
    ∃ x, F.sample.runAt n (F.index n r) s = F.encD (F.index n r) x :=
  let ⟨x, hx, _⟩ := F.sample_spec n r s
  ⟨x, (F.encD_decD _ _ x hx).symm⟩

/-- **A hard-core predicate is evaluable on every decodable string**: the evaluator `H` of
`HardCore` (correct on encodings) satisfies `H ⟨i, w⟩ = [h_i(x)]` whenever `w` decodes to `x`,
in particular on the outputs of the sampler and of a trapdoor inverter
(`Collection.apply_of_decD`). -/
theorem HardCore.evaluator {F : Collection} {h : ∀ i, F.D i → Bool} (hh : F.HardCore h) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x] :=
  let ⟨H, hH, hHx⟩ := hh.1
  ⟨H, hH, fun _ _ _ hw => F.apply_of_decD (v := fun i x => [h i x]) hHx hw⟩

end Collection

/-! ## Permutations and trapdoor permutations -/

/-- A *collection of permutations* [PS10, Definition 55.1]: every `f_i` is a permutation of
`D_i` (`f_i = encD_i ∘ perm_i`, `perm_i : D_i ≃ D_i`, so `R_i = D_i` up to encoding);
one-wayness is `PermCollection.OneWay`. `perm` and `f_perm` hold at every index string, which
is stronger than the text's `i ∈ I` and harmless: at indices outside `Gen`'s range `D i` may be
a one-element domain (as in the RSA and Blum candidates). -/
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
`⟨i, t⟩ ← Gen(1^n)` and `y ∈ D_i`, decodes to `f_i^{-1}(y)` for every coin string (so, by
canonical decoding, outputs its encoding: `TrapdoorCollection.inv_eq_encD`); the
hardness clause (5) is `TrapdoorCollection.OneWay`.

**Deviation:** the inverter receives `1^n` and the trapdoor `t` only, where the text gives it
"`(i, t)` from `Gen`" — run-3 audit P3-5, the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form was not
adopted. The two classes coincide: a text TDP becomes one of this shape with the trapdoor
`t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`, efficient, and harmless because the trapdoor never
reaches the adversary, who receives `⟨i, f_i(x)⟩` only in `Collection.invProbAt`), and this
shape is a text TDP whose `Inv` ignores `i`. (The candidates pack the index into `t`: RSA's
`Gen` outputs `⟨⟨N, e⟩, ⟨N, d⟩⟩` for the text's `[(N, e), d]`, Rabin's trapdoor `⟨p, q⟩`
determines `N`.) "`f_i^{-1}(y)`, `y ∈ R_i`" is `(perm i).symm y`, `y ∈ D_i` (the range is
`D_i` up to encoding). -/
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
[PS10, Definition 56.1 (6)], decode level; the string level is `TrapdoorCollection.eval_inv`):
its decoded answer `x'` satisfies `f_i(x') = encD i y`. -/
theorem TrapdoorCollection.inv_preimage (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n)
    (y : T.D (T.index n r)) (s : T.inv.Coins n) :
    ∃ x', T.decD _ (T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s) = some x' ∧
      T.f (T.index n r) x' = T.encD (T.index n r) y :=
  ⟨(T.perm _).symm y, T.inv_spec n r y s, by rw [T.f_perm, Equiv.apply_symm_apply]⟩

/-- **The trapdoor inverter outputs the encoding of `f_i^{-1}(y)`** ([PS10, Definition 56.1 (6)],
"computes `f_i^{-1}(y)`"): `Inv(1^n, ⟨t, encD_i y⟩) = encD_i (perm_i⁻¹ y)` for every generated
`⟨i, t⟩`, every `y ∈ D_i` and every coin string (`inv_spec` and canonical decoding). -/
theorem TrapdoorCollection.inv_eq_encD (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n)
    (y : T.D (T.index n r)) (s : T.inv.Coins n) :
    T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s = T.encD _ ((T.perm _).symm y) :=
  (T.encD_decD _ _ _ (T.inv_spec n r y s)).symm

/-- **The evaluator maps the inverter's output back to `y`** (string-level sanity for
[PS10, Definition 56.1 (6)]): `eval ⟨i, Inv(1^n, ⟨t, encD_i y⟩)⟩ = encD_i y`.

**Proof sketch.** The inverter's output is `encD_i (perm_i⁻¹ y)` (`inv_eq_encD`), on which
`eval` computes `f_i (perm_i⁻¹ y) = encD_i (perm_i (perm_i⁻¹ y)) = encD_i y` (`eval_spec`,
`f_perm`). -/
theorem TrapdoorCollection.eval_inv (T : TrapdoorCollection) (n : ℕ) (r : T.gen.Coins n)
    (y : T.D (T.index n r)) (s : T.inv.Coins n) :
    T.eval (pairEncode (T.index n r) (T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s)) =
      T.encD _ y := by
  rw [T.inv_eq_encD n r y s, T.eval_spec, T.f_perm, Equiv.apply_symm_apply]

/-! ## Theorem 42.2 (⇐): a strong one-way function is a collection -/

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
`s` and `F` computes `f n s` on it (`sample_spec`, by `decodeFin_ofFn` and `hspec`); decoding is
canonical (`encD_decD`, by `ofFn_of_decodeFin_eq_some`).

**Deviation:** the text's "`I = {0}`, `D_0 = ℕ`" becomes the unary parameter as the index
with the domain `{0,1}^{inLen n}` at `i = 1^n` (the domain must depend on `n`, D5). -/
noncomputable def toCollection : Collection where
  D i := Fin (𝓕.inLen.eval i.length) → Bool
  encD _ x := List.ofFn x
  decD i w := decodeFin (𝓕.inLen.eval i.length) w
  decD_encD _ x := decodeFin_ofFn x
  encD_decD _ _ _ h := ofFn_of_decodeFin_eq_some h
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

/-- **The collection of the identity is not one-way** (non-vacuity of `Collection.OneWay`,
[PS10, Definition 41.1]; gate 03b, finding 13): for every evaluator `F` of
`FunFamily.ofString id var`, the collection `toCollection F` is inverted with probability one by
the machine that returns the second component of its argument.

**Proof sketch.** Let `B(1^n, ⟨i, y⟩; r) := y` (`ofPolyTimeUniform` of `pairSndD ∘ inArg`).
Then `B.withIndexParam` returns its argument (`withIndexParam_runAt`, `pairSndD_pairEncode`),
so the collection's inversion probability against `B` is `1` at every `n`
(`toCollection_invProbAt`, `FunFamily.invProbAt_ofString_id_eq_one`), and the constant `1` is
not negligible (`c = 0`). -/
theorem FunFamily.not_toCollection_oneWay_id (F : List Bool → List Bool)
    (hF : PolyTimeComputable F)
    (hspec : ∀ n (x : Fin ((ofString id .var).inLen.eval n) → Bool),
      F (NUPPT.advInput n (List.ofFn x)) = List.ofFn ((ofString id .var).f n x)) :
    ¬ ((ofString id .var).toCollection F hF hspec).OneWay := by
  intro h
  let B : NUPPT := NUPPT.ofPolyTimeUniform (f := fun z => pairSndD (NUPPT.inArg z))
    (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg) (.const 0)
  have hB : ∀ n y (r : B.withIndexParam.Coins n), B.withIndexParam.runAt n y r = y := by
    intro n y r
    rw [NUPPT.withIndexParam_runAt, NUPPT.runAt_eq]
    show (NUPPT.ofPolyTimeUniform (f := fun z => pairSndD (NUPPT.inArg z)) _ (.const 0)).runAtL n
      (pairEncode (List.replicate n true) y) (List.ofFn r) = y
    rw [NUPPT.runAtL_ofPolyTimeUniform]
    show pairSndD (NUPPT.inArg (NUPPT.layout (List.replicate n true)
      (pairEncode (List.replicate n true) y) [] (List.ofFn r))) = y
    rw [NUPPT.inArg_layout, pairSndD_pairEncode]
  obtain ⟨n₀, hn₀⟩ := h.hard B 0
  have := hn₀ n₀ le_rfl
  simp [toCollection_invProbAt, invProbAt_ofString_id_eq_one hB] at this

/-! ## Theorem 42.2 (⇒): a collection gives a strong one-way function -/

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

**Proof sketch.** *Easy* (`owfFamily_easy`). The evaluator on `⟨1^n, r⟩` pads
`owfRawStr 1^n r ++ [true]` to `L(n)` bits (`polyTimeComputable_padStr L`), where
`owfRawStr 1^n r` computes `i := pairFstD (Gen.output ⟨⟨⟨1^n, []⟩, []⟩, r.take (gen.coins n)⟩)`
and `⟨i, eval ⟨i, Sample.output ⟨⟨⟨1^n, i⟩, []⟩, r.drop (gen.coins n)⟩⟩⟩`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly G.gen.coins`, `NUPPT.polyTimeComputable_layout`,
the output functions of `Gen` and `Sample`, `G.eval_poly`, pairing). On `⟨1^n, List.ofFn r⟩` it
returns `List.ofFn (g n r)`: `Gen` and `Sample` are uniform, so their activations are their
outputs on these layouts (`owfRawStr_eq`), the cut is `splitCoins` (`ofFn_splitCoins_fst/snd`),
and `ofFn_padFin_eq_padStr`.
*Hard.* Fix `A' : NUPPT`. The reduction `collInverter L A'` (the advice and coins of `A'`) on
`⟨1^n, ⟨i, y⟩⟩` with coins `ρ` pads `⟨i, y⟩ ++ [true]` to `L(n)` bits (`padStr L`), runs `A'`
on it, drops the first `gen.coins(n)` bits of the answer, and runs `Sample(1^n, i)` on the rest
(`collInvRaw`, polynomial-time by `collInvRaw_poly`; activation `collInverter_runAt`). No length
check is needed: an answer of the wrong length already fails `g`'s typed experiment.
*Functional identity* (`collInverter_success`): if `A'` returns the encoding of `z'` with
`g(z') = g(r₁, r₂)`, then `G.evalSampled` gives `x` with `owfRaw n r₁ r₂ = ⟨i, f_i(x)⟩`,
`i = index n r₁`; `padFin_append_true_injective` (with `OutLenBound`) turns `g(z') = g(r₁, r₂)`
into `owfRaw n z'₁ z'₂ = owfRaw n r₁ r₂`, whose components give `index n z'₁ = i` and
`eval ⟨i, w'⟩ = f_i(x)` for `w' := Sample(1^n, i; z'₂)`; the reduction's answer on
`⟨i, f_i(x)⟩` is `w'` (the dropped prefix is `z'₁`, `ofFn_splitCoins_snd`), which decodes to
an `x'` with `f_i(x') = eval ⟨i, w'⟩ = f_i(x)` (`exists_decD_of_index_eq`).
*Probability* (`fiber_le`, `invProbAt_owfFamily_le`): for fixed `r₁` (index `i`), the
functional identity is a pointwise implication from the `g`-event on `(r₂, ρ)` to the event
"the sampled `x` is inverted by the reduction" (`uprob_mono`), and
`StatClose.abs_uprob_sub_le_prod` with `h.sampleClose` moves the sampled `x` to the ideal
uniform `x ∈ D_i` at the cost `δ(n)`; averaging over `r₁` (`uprob_comp_equiv` on `splitCoins`,
`uprob_prod`, `OneWay.uexp_add`, `OneWay.uexp_const`) gives
`(G.owfFamily L).invProbAt A' n ≤ G.invProbAt (collInverter L A') n + δ(n)`. Conclude by
`h.hard (collInverter L A')`, `Negligible.add` and `Negligible.mono` (`invProbAt_nonneg`). -/
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
