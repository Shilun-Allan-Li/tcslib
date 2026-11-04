## ===== briefs/pass-shelat-ch5-8/gates/01-p0/pack.md =====

# Gate 01 (Pass–shelat ch. 5–8, prong zero): external audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#183](https://github.com/Shilun-Allan-Li/tcslib/pull/183)
into `main`, at its head `789cf450527ff6b8c779161e555f04093080b88d` (base: `main` at
`06e61e912eedc2bce49b3ccff77bb9c4a7e18579`). One combined gate (statements, definitions, sketches,
proofs and docstring citations), by the user's ruling: the PR has no `sorry`, and its proofs are
short. The deliverable is **`gate01-p0-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source text is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010, as a PDF. The audited items are on PDF pp. 163–166 (book pp. 151–154,
§6.1) and PDF pp. 193–196 (book pp. 181–184, §8.3). Book page numbers are also the item numbers'
prefixes (for example, Definition 181.1 is on book p. 181).

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 change: definitions, theorem statements,
their docstrings and proof sketches, against the cited source. The proofs are machine-checked;
do not review tactic scripts for correctness, except where a disclosure below asks for it. The
failure modes you are hunting are:

1. **Infidelity:** a definition that does not mean what the cited source means.
2. **Trivialization:** a definition or statement satisfiable for degenerate reasons (vacuous
   hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Wrong strength:** a statement subtly weaker or stronger than the docstring claims. Check
   boundary cases: the empty type, `k ≤ 0`, `ε < 0`, an empty class of sources, one-point types.
4. **Missing hypotheses:** finiteness, nonemptiness, positivity.
5. **Debt:** duplication of existing proved material in the library (see the attestations).
6. **Attribution:** every source-derived declaration carries a `[Tag, location]`; every deviation
   from the source is declared, with its reason ([`policy.md`](policy.md) §2–3, in the bundle).

For **every definition** in scope: restate it in your own mathematical English *before* reading
its docstring, compare your restatement with the cited source item, and report any daylight. For
**every theorem**: say in 1–3 sentences whether the statement is what its docstring claims.
Attempt at least **three adversarial instantiations**: concrete pathological objects plugged into
the definitions, to check they behave as the theory intends. Propose machine-checkable sanity
theorems you think are missing.

Do not give a blanket approval. An empty findings table must come with the per-definition
restatements that justify it.

## Scope

| Item | Where |
|---|---|
| New Lean (all declarations audited) | `TCSlib/InformationTheory/Entropy.lean` (195 lines), `TCSlib/InformationTheory/Extractors.lean` (206 lines) |
| Facade (imports and contents list only) | `TCSlib/InformationTheory.lean` |
| Docstring-only edits (audit the added citations and deviation notes; code unchanged) | `TCSlib/Cryptography/SecretSharing/Defs.lean`, `TCSlib/Cryptography/SecretSharing/Shamir.lean`; the bundle also has the diff against `main` |
| Context, already on `main` (not under audit; read to check the new statements' meaning) | `TCSlib/InformationTheory/FinDist.lean`, `StatisticalDistance.lean`, `UniversalHashing.lean`, `LeftoverHash.lean`; `TCSlib/Cryptography/SecretSharing/Interpolation.lean` |
| Source | [PS10] §6.1 (Def 152.1, Lem 153.2, Fact 153.3, Prot 154.4, Prop 154.5) and §8.3 (Defs 181.1, 181.2, 182.3, 183.4, 183.5; §8.3.3) |
| Standards | `policy.md` (attribution and proof-sketch rules) |
| Out of scope | tactic proofs, except the disclosures below; the design of the context files |

### The new public declarations (33)

`Entropy.lean`, namespace `TCSlib.InformationTheory.FinDist`:
- **definitions:** `shannonEntropy` (Def 182.3), `maxProb`, `minEntropy` (Def 183.4), `IsSource`
  (Def 183.5), `IsFlatSource` (Def 183.5), `flat`;
- **theorems:** `shannonEntropy_nonneg`, `shannonEntropy_uniform`, `shannonEntropy_uniform_bits`,
  `le_maxProb`, `maxProb_le_iff`, `maxProb_pos`, `le_minEntropy_iff`, `isSource_iff_hasMinEntropy`,
  `IsSource.mono`, `IsFlatSource.isSource`, `flat_apply`, `isFlatSource_flat`, `isSource_uniform`.

`Extractors.lean`, namespace `TCSlib.InformationTheory`:
- **definitions:** `FinDist.probTrue`, `EpsClose` (Def 181.1), `IsExtractor` (Def 181.2),
  `IsStrongExtractor`, `seededSources`;
- **theorems:** `FinDist.probTrue_sub_probTrue`, `abs_probTrue_sub_le_statDist`,
  `statDist_le_of_epsClose`, `epsClose_iff_statDist_le`, `EpsClose.symm`, `EpsClose.trans`,
  `IsExtractor.mono`, `IsStrongExtractor.isExtractor_seeded`, `isStrongExtractor_of_isUniversal`
  (§8.3.3).

One private lemma: `sum_sub_eq_zero` (`Extractors.lean`).

## Attestations

Maintainer execution claims, stated so you can verify or challenge them. The evidence logs are in
the bundle under `evidence/`.

1. **Elaboration.** `scripts/lean_check_tree.sh` checked, one module at a time and into a fresh
   olean tree, the 18 modules of the touched files' downstream closure (without the root module
   `TCSlib`), in dependency order. All 18 passed: exit 0, no `error:` line and a fresh olean each,
   with 0 warnings and 0 `sorry` (`evidence/replay-head.log`).
2. **Axioms.** `#print axioms` for each of the 22 new theorems, and for `TCSlib.Shamir.correct`,
   `perfectPrivacy` and `natCard_coins_view`, prints exactly
   `[propext, Classical.choice, Quot.sound]` (`evidence/axioms.log`).
3. **Docstring-only.** For `SecretSharing/Defs.lean` and `Shamir.lean`, the text with comments
   stripped is byte-identical to `main` (`evidence/docstring-only.log`).
4. **Lint.** `scripts/style_lint.py` reports 0 findings on the two new files. The 8 findings on
   the other three touched files are on `main` already: the facade's three missing options, and
   five undocumented lemmas in the Shamir files (`evidence/style-lint.log`).
5. **Duplication.** The new names and concepts were searched across `main` and the branches
   `cryptography/pass-shelat-ch2-4`, `complexity/arora-barak-ch3-4` and `cryptography/garg-ch1-3`,
   and in the pinned Mathlib (`evidence/duplication.log`).
   - **No copy found.** Mathlib's total variation is measure-theoretic, not on `FinDist`.
   - **One parallel concept, disclosed:** `TCSlib.Cryptography.StatClose` on the unmerged ch. 2–4
     branch, a closeness of *samplers* (maps from uniform seeds into a possibly infinite type).
     `EpsClose` is a closeness of `FinDist`s. Different carriers; a bridge is owed when the ch. 2–4
     layer integrates with `main`.
6. **Line width.** No line over 100 characters in the touched files.

## Disclosures: definitions read through their bodies

The campaign's rule 10 asks proofs to read another file's TCSlib definitions only through
published equations. `main` has no such rule, but the departures are disclosed:
- `abs_probTrue_sub_le_statDist` and `statDist_le_of_epsClose` read
  `statDist p q = ½ ∑ |p a - q a|` by `rfl`. `StatisticalDistance.lean` publishes no equation.
- `IsStrongExtractor.isExtractor_seeded` uses that `hashPair f X` is definitionally the pushforward
  of `uniform S × X` along `(s, x) ↦ (s, f s x)`, as `LeftoverHash.lean` defines it.
- `le_minEntropy_iff` closes by `rfl` against `HasMinEntropy`'s body (`∀ a, p a ≤ 2 ^ (-k)`).

## Known deviations (declared in the docstrings; verify they are benign, and flag any others)

- `shannonEntropy`: base 2 only. [PS10] defines entropy for any base and calls base 2 Shannon
  entropy.
- `IsFlatSource`: defined as uniform on `2^k` points, with `k : ℕ`. [PS10]'s "additionally" (it
  is also a `k`-source) is proved, not assumed (`IsFlatSource.isSource`).
- `IsExtractor`: the domain and range are arbitrary finite types, not `{0,1}^n` and `{0,1}^m`.
- `IsStrongExtractor`: [PS10] §8.3.3 is a heading with no text. The definition follows
  [Vad12, Def 6.13], and `isExtractor_seeded` reads it in [PS10, Def 181.2]'s terms.
- `SecretSharing.Scheme`: [PS10] asks `Share` and `Recon` to be p.p.t.; efficiency is not
  modelled. [PS10]'s `Recon` takes `k` indexed shares; here it takes a set of parties and a share
  assignment, with `LocalReconstruct`.
- `Scheme.PerfectPrivacy`: a bijection of the coins, stronger than [PS10, Def 152.1, item 3]'s
  "statistically close".
- `Shamir.scheme`:
  - it works over any field, with every nonzero element a party. [PS10, Prot 154.4] uses `ℤ_p`,
    `p > n`, and the parties `1, …, n`; the docstring claims [PS10]'s scheme is a restriction of
    this one and its claims are special cases;
  - the typo in [PS10] (`n − 1` coefficients up to `a_n tⁿ`) is corrected to degree `k − 1`.

## Specific questions

1. **Def 152.1 versus `Scheme`, `Correct` and `PerfectPrivacy`.**
   - [PS10]'s privacy clause says "statistically close", with no security parameter in sight. Is
     perfect privacy (identical distributions) a faithful strengthening, or does [PS10] intend
     something the library's form misses?
   - Is the threshold `Correct` (any set of at least `k` parties) a faithful reading of item 2's
     "any `k` shares"?
2. **The restriction claim on `Shamir.scheme`.** Check that [PS10]'s statements for subsets of
   `{1, …, n}` really are instances of `correct` and `perfectPrivacy` when `F = ZMod p` with `p`
   prime and `n < p`. In particular, the labels `1, …, n` must be nonzero and distinct mod `p`,
   and "fewer than `k`" must match `¬ (k ≤ #B)`.
3. **`EpsClose` versus Def 181.1.** [PS10] quantifies over deterministic, unbounded distinguishers
   with outputs in `{0,1}`. Is `D : α → Bool` that class? Would allowing randomized distinguishers
   change anything? (It should not; argue it.)
4. **`epsClose_iff_statDist_le` at the boundary.** Check it for `ε < 0` (both sides false?),
   `ε = 0` (`p = q`?), and a one-point type.
5. **`IsExtractor` with degenerate classes:**
   - the empty class (every function is an extractor: intended?);
   - `ε ≥ 1` (every function is an extractor: intended?);
   - `β` with one element.

   Should any of these carry a hypothesis, or is the vacuity harmless and as in [PS10]?
6. **`minEntropy` and `le_minEntropy_iff`.** Does `-log₂(maxProb p)` equal [PS10]'s
   `minₓ log₂(1/Pr[X = x])`? Note that points of probability zero have infinite surprise, and the
   minimum is taken over all points.
7. **`IsSource` with a real `k`, `IsFlatSource` with a natural `k`.** Is this split faithful to
   Def 183.5? Is anything lost by not allowing flat sources for non-integer `k`?
8. **The leftover hash bridge.** Are the error bound `½ √(|β| · 2^(-k))` and the strong (seeded)
   form what a reader of [PS10] §8.3.3 would expect? Is `seededSources` with `isExtractor_seeded`
   a faithful way to see a seeded extractor as a [PS10, Def 181.2] extractor?
9. **Shannon entropy conventions.** Is `negMulLog` (`0 · log(1/0) = 0`) the right convention?
   [PS10] writes `H(x)` in places for `H(X)`; the Lean uses the distribution throughout.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  (failure mode 5) that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

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

## ===== TCSlib/InformationTheory/Entropy.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy, min-entropy and sources

Two measures of how much randomness a distribution on a finite type contains, and the classes of
"imperfect random sources" that extractors are asked to handle.

Shannon entropy is the expected surprise `∑ₓ Pr[X = x] · log₂ (1 / Pr[X = x])`. It is the wrong
measure for extraction from a single sample: a source that is constant with probability `0.99`
and uniform otherwise has Shannon entropy close to `n / 100` on `n`-bit strings, but a
deterministic extractor sees the constant almost always. Min-entropy, `log₂ (1 / maxₓ Pr[X = x])`,
is the right measure: it lower-bounds the surprise of *every* outcome. A `k`-source is a
distribution of min-entropy at least `k`; a `k`-flat source is uniform on `2^k` points.

The library already expresses "min-entropy at least `k`" as the bound
`FinDist.HasMinEntropy p k : ∀ a, p a ≤ 2 ^ (-k)`, which is what the leftover hash lemma consumes.
This file adds the min-entropy *value* that [PS10] defines and proves the two agree
(`FinDist.le_minEntropy_iff`).

## Main definitions

* `FinDist.shannonEntropy`: Shannon entropy in bits.
* `FinDist.maxProb`, `FinDist.minEntropy`: the largest point probability, and min-entropy in bits.
* `FinDist.IsSource k p`: `p` is a `k`-source (min-entropy at least `k`).
* `FinDist.IsFlatSource k p`: `p` is uniform on a set of `2^k` points.
* `FinDist.flat s`: the uniform distribution on a nonempty finite set `s`.

## Main results

* `FinDist.shannonEntropy_uniform`: the uniform distribution on `α` has Shannon entropy
  `log₂ |α|`; on `n`-bit strings, `n` (`FinDist.shannonEntropy_uniform_bits`).
* `FinDist.le_minEntropy_iff`: `k ≤ H∞(p)` exactly when every outcome has probability at most
  `2^(-k)`.
* `FinDist.IsFlatSource.isSource`: a `k`-flat source is a `k`-source.
* `FinDist.isFlatSource_flat`, `FinDist.isSource_uniform`: flat sources and `k`-sources exist.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.2 (Definitions 182.3, 183.4 and 183.5).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1.
-/

namespace TCSlib.InformationTheory

open Finset Real

namespace FinDist

variable {α : Type*} [Fintype α]

/-! ### Shannon entropy -/

/-- The **Shannon entropy** of `p` in bits: `H(p) = ∑ₓ p(x) · log₂ (1 / p(x))`, where an outcome of
probability zero contributes zero (`Real.negMulLog 0 = 0`). [PS10, Def 182.3]

**Deviation:** [PS10] defines entropy for a general logarithm and calls the base-2 case Shannon
entropy; only the base-2 case is defined here. -/
noncomputable def shannonEntropy (p : FinDist α) : ℝ :=
  ∑ a, negMulLog (p a) / log 2

/-- Shannon entropy is nonnegative: each term `-p log₂ p` is nonnegative for `0 ≤ p ≤ 1`. -/
theorem shannonEntropy_nonneg (p : FinDist α) : 0 ≤ shannonEntropy p :=
  sum_nonneg fun a _ =>
    div_nonneg (negMulLog_nonneg (p.nonneg a) (p.le_one a)) (log_nonneg one_le_two)

/-- The uniform distribution on `α` has Shannon entropy `log₂ |α|`. [PS10, p. 182, the uniform
example after Def 182.3]

**Proof sketch.** Every one of the `|α|` terms is `(1/|α|) · log₂ |α|`. -/
theorem shannonEntropy_uniform [Nonempty α] :
    shannonEntropy (uniform α) = logb 2 (Fintype.card α) := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [shannonEntropy, uniform_apply, negMulLog, log_inv, sum_const, card_univ,
    nsmul_eq_mul, logb]
  field_simp

/-- The uniform distribution on `n`-bit strings has Shannon entropy `n`. [PS10, p. 182] -/
theorem shannonEntropy_uniform_bits (n : ℕ) :
    shannonEntropy (uniform (Fin n → Bool)) = n := by
  rw [shannonEntropy_uniform]
  simp [Fintype.card_bool, Fintype.card_fin, Real.logb_pow]

/-! ### Min-entropy -/

/-- The largest probability of a single outcome, `maxₓ p(x)`. -/
noncomputable def maxProb (p : FinDist α) : ℝ :=
  univ.sup' (univ_nonempty_iff.2 (Fintype.card_pos_iff.1 p.card_pos)) p

/-- Every outcome's probability is at most the largest one. -/
theorem le_maxProb (p : FinDist α) (a : α) : p a ≤ maxProb p :=
  le_sup' (f := p.prob) (mem_univ a)

/-- The largest probability is at most `c` exactly when every outcome's probability is. -/
theorem maxProb_le_iff (p : FinDist α) {c : ℝ} : maxProb p ≤ c ↔ ∀ a, p a ≤ c := by
  simp [maxProb, sup'_le_iff]

/-- The most likely outcome has positive probability, since the probabilities sum to one. -/
theorem maxProb_pos (p : FinDist α) : 0 < maxProb p := by
  by_contra h
  have hle : ∀ a, p a ≤ 0 := (maxProb_le_iff p).1 (not_lt.1 h)
  have : ∑ a, p a ≤ 0 := sum_nonpos fun a _ => hle a
  rw [p.sum_prob] at this
  norm_num at this

/-- The **min-entropy** of `p` in bits: `H∞(p) = minₓ log₂ (1 / p(x)) = -log₂ (maxₓ p(x))`.
[PS10, Def 183.4] -/
noncomputable def minEntropy (p : FinDist α) : ℝ :=
  -logb 2 (maxProb p)

/-- **Min-entropy in bound form.** `H∞(p) ≥ k` exactly when every outcome has probability at most
`2^(-k)`, which is the library's `HasMinEntropy p k`. This is the "equivalently" of
[PS10, Def 183.4].

**Proof sketch.** `k ≤ -log₂ m ↔ log₂ m ≤ -k ↔ m ≤ 2^(-k)` for the positive maximum `m`, and
`m ≤ c` exactly when every point probability is at most `c`. -/
theorem le_minEntropy_iff (p : FinDist α) (k : ℝ) :
    k ≤ minEntropy p ↔ HasMinEntropy p k := by
  rw [minEntropy, le_neg, logb_le_iff_le_rpow one_lt_two (maxProb_pos p), maxProb_le_iff]
  rfl

/-! ### Sources -/

/-- `p` is a **`k`-source**: its min-entropy is at least `k`. [PS10, Def 183.5] -/
def IsSource (k : ℝ) (p : FinDist α) : Prop :=
  k ≤ minEntropy p

/-- A `k`-source is exactly a distribution with `HasMinEntropy p k`, so the leftover hash lemma
applies to `k`-sources. -/
theorem isSource_iff_hasMinEntropy {k : ℝ} {p : FinDist α} :
    IsSource k p ↔ HasMinEntropy p k :=
  le_minEntropy_iff p k

/-- A `k`-source is a `k'`-source for every `k' ≤ k`. -/
theorem IsSource.mono {k k' : ℝ} {p : FinDist α} (h : IsSource k p) (hk : k' ≤ k) :
    IsSource k' p :=
  hk.trans h

/-- `p` is a **`k`-flat source**: it is the uniform distribution on some set of `2^k` distinct
points. [PS10, Def 183.5]

**Deviation:** [PS10] requires a flat source to be a `k`-source as well; that is automatic
(`IsFlatSource.isSource`), so it is a theorem here rather than part of the definition. -/
def IsFlatSource [DecidableEq α] (k : ℕ) (p : FinDist α) : Prop :=
  ∃ s : Finset α, #s = 2 ^ k ∧ ∀ a, p a = if a ∈ s then ((2 : ℝ) ^ k)⁻¹ else 0

/-- A `k`-flat source is a `k`-source: every point has probability `2^(-k)` or `0`. -/
theorem IsFlatSource.isSource [DecidableEq α] {k : ℕ} {p : FinDist α} (h : IsFlatSource k p) :
    IsSource k p := by
  obtain ⟨s, -, hp⟩ := h
  refine isSource_iff_hasMinEntropy.2 fun a => ?_
  rw [hp a, rpow_neg zero_le_two, rpow_natCast]
  split_ifs
  · exact le_rfl
  · positivity

/-- The uniform distribution on a nonempty finite set `s`. -/
noncomputable def flat [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : FinDist α where
  prob a := if a ∈ s then (#s : ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_prob := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
    have : (#s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
    field_simp

/-- The flat distribution gives each point of `s` probability `1 / |s|` and every other point
probability zero. -/
@[simp] theorem flat_apply [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (a : α) :
    flat s hs a = if a ∈ s then (#s : ℝ)⁻¹ else 0 := rfl

/-- The uniform distribution on a set of `2^k` points is a `k`-flat source. -/
theorem isFlatSource_flat [DecidableEq α] {k : ℕ} (s : Finset α) (hs : #s = 2 ^ k) :
    IsFlatSource k (flat s (Finset.card_pos.1 (hs ▸ pow_pos two_pos k))) :=
  ⟨s, hs, fun a => by simp [hs]⟩

/-- The uniform distribution on `α` is a `log₂ |α|`-source; on `n`-bit strings, an `n`-source. -/
theorem isSource_uniform [Nonempty α] : IsSource (logb 2 (Fintype.card α)) (uniform α) := by
  refine isSource_iff_hasMinEntropy.2 fun a => ?_
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [uniform_apply, rpow_neg zero_le_two, rpow_logb two_pos (by norm_num) hc]

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/InformationTheory/Extractors.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.LeftoverHash

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closeness and deterministic extractors

An extractor turns a sample from an imperfect random source into bits that are close to uniform.
"Close" is `ε`-closeness: no distinguisher, however powerful, tells the two distributions apart
with advantage more than `ε`. This file defines closeness in that distinguisher form, proves that
it is the same as a bound on the library's statistical distance `statDist`, defines deterministic
extractors for a class of sources, and restates the leftover hash lemma in extractor terms: a
universal hash family is a *strong* extractor for every class of `k`-sources.

## Main definitions

* `FinDist.probTrue p D`: the probability that the test `D` accepts a sample of `p`.
* `EpsClose ε p q`: `p` and `q` are `ε`-close.
* `IsExtractor C ε Ext`: `Ext` is an `ε`-extractor for the class of sources `C`.
* `IsStrongExtractor C ε f`: the seeded family `f` is a strong `ε`-extractor for `C`: the pair
  (seed, output) is `ε`-close to uniform.
* `seededSources S C`: the sources that carry a uniform seed in `S` beside a sample of a source in
  `C`; the deterministic reading of a seeded extractor.

## Main results

* `abs_probTrue_sub_le_statDist`, `epsClose_iff_statDist_le`: `ε`-closeness is exactly
  `statDist ≤ ε`; the optimal distinguisher accepts the points where the first distribution is
  more likely.
* `isStrongExtractor_of_isUniversal`: **the leftover hash lemma as an extractor** — a universal
  family is a strong `½ √(|β| · 2^(-k))`-extractor for `k`-sources.
* `IsStrongExtractor.isExtractor_seeded`: a strong extractor is a deterministic extractor
  ([PS10, Def 181.2]) for its seeded sources.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.3.1 (Definitions 181.1 and 181.2) and §8.3.3 (the leftover hash lemma, heading only).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2 (Lemma 6.4, Def 6.13,
  Thm 6.18).
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999 (Lemma 4.8).
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {α β S : Type*} [Fintype α] [Fintype β] [Fintype S]

/-! ### Closeness -/

/-- The probability that the test `D` outputs `1` (`true`) on a sample of `p`:
`Pr[x ← p : D(x) = 1]`. -/
noncomputable def FinDist.probTrue (p : FinDist α) (D : α → Bool) : ℝ :=
  ∑ a ∈ univ.filter (fun a => D a = true), p a

/-- `p` and `q` are **`ε`-close**, written `p ≈_ε q`: every deterministic distinguisher `D`, with
no bound on its running time, has advantage at most `ε`,
`|Pr[x ← p : D(x) = 1] - Pr[y ← q : D(y) = 1]| ≤ ε`. [PS10, Def 181.1] -/
def EpsClose (ε : ℝ) (p q : FinDist α) : Prop :=
  ∀ D : α → Bool, |p.probTrue D - q.probTrue D| ≤ ε

/-- A distinguisher's advantage is a sum of probability differences over the points it accepts. -/
theorem FinDist.probTrue_sub_probTrue (p q : FinDist α) (D : α → Bool) :
    p.probTrue D - q.probTrue D = ∑ a ∈ univ.filter (fun a => D a = true), (p a - q a) := by
  simp only [FinDist.probTrue, sum_sub_distrib]

/-- The probability differences of two distributions sum to zero. -/
private theorem sum_sub_eq_zero (p q : FinDist α) : ∑ a, (p a - q a) = 0 := by
  rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]

/-- **No distinguisher beats statistical distance.** For every test `D`,
`|Pr_p[D = 1] - Pr_q[D = 1]| ≤ statDist p q`. [Vad12, Lemma 6.4]

**Proof sketch.** Let `d = p - q` and let `A` be the accepted set. Since `d` sums to zero, the sum
of `d` over `A` is minus its sum over the complement, so twice its absolute value is at most
`∑_A |d| + ∑_{Aᶜ} |d| = ∑ |d| = 2 · statDist p q`. -/
theorem abs_probTrue_sub_le_statDist (p q : FinDist α) (D : α → Bool) :
    |p.probTrue D - q.probTrue D| ≤ statDist p q := by
  rw [FinDist.probTrue_sub_probTrue]
  have hsplit := sum_filter_add_sum_filter_not univ (fun a => D a = true) (fun a => p a - q a)
  have hsplitabs :=
    sum_filter_add_sum_filter_not univ (fun a => D a = true) (fun a => |p a - q a|)
  rw [sum_sub_eq_zero] at hsplit
  have h1 := abs_sum_le_sum_abs (fun a => p a - q a) (univ.filter (fun a => D a = true))
  have h2 := abs_sum_le_sum_abs (fun a => p a - q a) (univ.filter (fun a => ¬ D a = true))
  have hc : ∑ a ∈ univ.filter (fun a => ¬ D a = true), (p a - q a)
      = -∑ a ∈ univ.filter (fun a => D a = true), (p a - q a) := by linarith
  rw [hc, abs_neg] at h2
  have hd : statDist p q = (1 / 2) * ∑ a, |p a - q a| := rfl
  linarith

/-- **The optimal distinguisher attains statistical distance.** If every test has advantage at
most `ε`, then `statDist p q ≤ ε`. [Vad12, Lemma 6.4]

**Proof sketch.** Test `D` accepting exactly the points where `p` is more likely than `q`. On the
accepted set `|p - q| = p - q`, off it `|p - q| = q - p`, and the two sums of `p - q` cancel, so
`∑ |p - q|` is twice `D`'s advantage. Hence `statDist p q` equals that advantage, which is at most
`ε`. -/
theorem statDist_le_of_epsClose {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) :
    statDist p q ≤ ε := by
  have key := h (fun a => decide (q a < p a))
  rw [FinDist.probTrue_sub_probTrue] at key
  have hpos : ∀ a ∈ univ.filter (fun a => decide (q a < p a) = true),
      |p a - q a| = p a - q a := fun a ha => by
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at ha
    exact abs_of_pos (by linarith)
  have hneg : ∀ a ∈ univ.filter (fun a => ¬ decide (q a < p a) = true),
      |p a - q a| = -(p a - q a) := fun a ha => by
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, not_lt] at ha
    exact abs_of_nonpos (by linarith)
  have hsplit :=
    sum_filter_add_sum_filter_not univ (fun a => decide (q a < p a) = true) (fun a => p a - q a)
  have hsplitabs :=
    sum_filter_add_sum_filter_not univ (fun a => decide (q a < p a) = true) (fun a => |p a - q a|)
  rw [sum_congr rfl hpos, sum_congr rfl hneg, sum_neg_distrib] at hsplitabs
  rw [sum_sub_eq_zero] at hsplit
  have hnn : 0 ≤ ∑ a ∈ univ.filter (fun a => decide (q a < p a) = true), (p a - q a) :=
    sum_nonneg fun a ha => by
      simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq] at ha
      linarith
  rw [abs_of_nonneg hnn] at key
  have hd : statDist p q = (1 / 2) * ∑ a, |p a - q a| := rfl
  linarith

/-- **`ε`-closeness is a statistical-distance bound.** `p ≈_ε q` in the distinguisher form of
[PS10, Def 181.1] exactly when `statDist p q ≤ ε`. [Vad12, Lemma 6.4] -/
theorem epsClose_iff_statDist_le {ε : ℝ} {p q : FinDist α} :
    EpsClose ε p q ↔ statDist p q ≤ ε :=
  ⟨statDist_le_of_epsClose, fun h D => (abs_probTrue_sub_le_statDist p q D).trans h⟩

/-- Closeness is symmetric. -/
theorem EpsClose.symm {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) : EpsClose ε q p := by
  rw [epsClose_iff_statDist_le] at h ⊢
  rwa [statDist_comm]

/-- Closeness composes: `p ≈_ε q` and `q ≈_δ r` give `p ≈_{ε+δ} r`. -/
theorem EpsClose.trans {ε δ : ℝ} {p q r : FinDist α} (h₁ : EpsClose ε p q)
    (h₂ : EpsClose δ q r) : EpsClose (ε + δ) p r := by
  rw [epsClose_iff_statDist_le] at *
  exact (statDist_triangle p q r).trans (add_le_add h₁ h₂)

/-! ### Extractors -/

/-- `Ext` is an **`ε`-extractor for the class of sources `C`**: a deterministic function whose
output on a sample of any source in `C` is `ε`-close to uniform, `Ext(X) ≈_ε U`.
[PS10, Def 181.2]

**Deviation:** [PS10] takes `Ext : {0,1}^n → {0,1}^m`; here the domain and range are any finite
types, the source's case being `α = Fin n → Bool` and `β = Fin m → Bool`. -/
def IsExtractor [DecidableEq β] [Nonempty β] (C : Set (FinDist α)) (ε : ℝ) (Ext : α → β) :
    Prop :=
  ∀ X ∈ C, EpsClose ε (X.map Ext) (uniform β)

/-- An extractor for a class is one for every subclass. -/
theorem IsExtractor.mono [DecidableEq β] [Nonempty β] {C C' : Set (FinDist α)} {ε : ℝ}
    {Ext : α → β} (h : IsExtractor C ε Ext) (hC : C' ⊆ C) : IsExtractor C' ε Ext :=
  fun X hX => h X (hC hX)

/-- The seeded family `f : S → α → β` is a **strong `ε`-extractor for `C`**: for every source `X`
in `C`, the pair `(s, f s x)` with a uniform seed `s` and `x ← X` is `ε`-close to uniform on
`S × β`. [Vad12, Def 6.13]; [PS10, §8.3.3] states the leftover hash lemma under this heading
without a definition. -/
def IsStrongExtractor [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S] [Nonempty β]
    (C : Set (FinDist α)) (ε : ℝ) (f : S → α → β) : Prop :=
  ∀ X ∈ C, EpsClose ε (hashPair f X) (uniform (S × β))

/-- The **seeded sources** over `C`: a uniform seed in `S` paired with an independent sample of a
source in `C`. A strong extractor is a deterministic extractor ([PS10, Def 181.2]) for exactly
these. -/
def seededSources [Nonempty S] (C : Set (FinDist α)) : Set (FinDist (S × α)) :=
  {Y | ∃ X ∈ C, Y = FinDist.prod (uniform S) X}

/-- A strong extractor `f` makes `(s, x) ↦ (s, f s x)` a deterministic `ε`-extractor
([PS10, Def 181.2]) for the seeded sources over `C`: the seed is part of the sample and is
output again. -/
theorem IsStrongExtractor.isExtractor_seeded [DecidableEq S] [DecidableEq α] [DecidableEq β]
    [Nonempty S] [Nonempty β] {C : Set (FinDist α)} {ε : ℝ} {f : S → α → β}
    (h : IsStrongExtractor C ε f) :
    IsExtractor (seededSources (S := S) C) ε (fun p : S × α => (p.1, f p.1 p.2)) := by
  rintro Y ⟨X, hX, rfl⟩
  exact h X hX

/-- **The leftover hash lemma as an extractor.** A universal hash family `f : S → α → β` is a
strong `½ √(|β| · 2^(-k))`-extractor for the `k`-sources on `α`. [PS10, §8.3.3],
[HILL99, Lemma 4.8], [Vad12, Thm 6.18]

**Proof sketch.** A `k`-source has `HasMinEntropy X k` (`isSource_iff_hasMinEntropy`), so the
library's `leftover_hash` bounds the statistical distance of `(s, f s x)` from uniform by
`½ √(|β| · 2^(-k))`, and statistical distance bounds every distinguisher's advantage
(`epsClose_iff_statDist_le`). -/
theorem isStrongExtractor_of_isUniversal [DecidableEq S] [DecidableEq α] [DecidableEq β]
    [Nonempty S] [Nonempty β] {f : S → α → β} (hf : IsUniversal f) (k : ℝ) :
    IsStrongExtractor {X : FinDist α | IsSource k X}
      ((1 / 2) * Real.sqrt (Fintype.card β * (2 : ℝ) ^ (-k))) f :=
  fun _ hX => epsClose_iff_statDist_le.2 (leftover_hash hf (isSource_iff_hasMinEntropy.1 hX))

end TCSlib.InformationTheory

## ===== TCSlib/InformationTheory.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import TCSlib.InformationTheory.StatisticalDistance
import TCSlib.InformationTheory.UniversalHashing
import TCSlib.InformationTheory.LeftoverHash
import TCSlib.InformationTheory.Entropy
import TCSlib.InformationTheory.Extractors

/-!
# Information theory

Finite distributions, statistical distance, entropy, and randomness extraction.

## Contents

* `TCSlib.InformationTheory.FinDist`: distributions on a finite type, collision probability,
  min-entropy.
* `TCSlib.InformationTheory.StatisticalDistance`: statistical distance and the `ℓ¹`–`ℓ²` bound.
* `TCSlib.InformationTheory.UniversalHashing`: universal hash families.
* `TCSlib.InformationTheory.LeftoverHash`: the leftover hash lemma.
* `TCSlib.InformationTheory.Entropy`: Shannon entropy, min-entropy, `k`-sources and flat sources.
* `TCSlib.InformationTheory.Extractors`: `ε`-closeness (equivalent to a statistical-distance
  bound), deterministic and strong extractors, and the leftover hash lemma as an extractor.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012.
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== TCSlib/Cryptography/SecretSharing/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secret sharing: access structures and security definitions

This file sets up the scheme-independent vocabulary of secret sharing: monotone access
structures, the data of a sharing scheme, and the two security requirements (correctness for
authorized sets, perfect privacy for unauthorized sets). Nothing here mentions polynomials;
`TCSlib.Cryptography.SecretSharing.Shamir` instantiates all of it.

Perfect privacy is stated in *randomness-bijection* form: for any unauthorized set `B` and any
two secrets there is a bijection of the randomness space carrying the one secret's `B`-view to
the other's. For uniformly distributed randomness this is equivalent to the usual statement
that the joint distribution of the shares held by `B` is independent of the secret, but it is
finiteness-free and measure-theory-free, and it is what a scheme's proof naturally produces.
`PerfectPrivacy.card_view_eq` extracts the counting consequence.

## Main definitions

* `SecretSharing.AccessStructure`: a monotone family of authorized sets of parties.
* `SecretSharing.AccessStructure.threshold`: the `k`-out-of-`n` access structure.
* `SecretSharing.Scheme`: the data of a scheme (a randomized sharing map and a reconstruction
  map).
* `SecretSharing.Scheme.Correct`, `SecretSharing.Scheme.PerfectPrivacy`: the two security
  requirements.
* `SecretSharing.Scheme.LocalReconstruct`: reconstruction from `A` only reads the shares of `A`.

## Main results

* `SecretSharing.Scheme.PerfectPrivacy.card_view_eq`: an unauthorized set's view has the same
  number of randomness preimages under every secret.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §1–2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.1.1 (Definition 152.1, `(k, n)` secret sharing).
-/

namespace TCSlib.SecretSharing

open Finset

variable {P : Type*}

/-- A monotone access structure on a party type `P`: a predicate `Auth` on finite sets of
parties, closed under taking supersets. `Auth A` means the parties in `A` are together allowed
to recover the secret. [Bei11, §1] -/
structure AccessStructure (P : Type*) where
  /-- The authorized sets. -/
  Auth : Finset P → Prop
  /-- Authorization is monotone: a superset of an authorized set is authorized. -/
  mono : ∀ {A B : Finset P}, A ⊆ B → Auth A → Auth B

/-- The `k`-out-of-`n` threshold access structure: a set of parties is authorized exactly when
it has at least `k` members. [Sha79, §1] -/
def AccessStructure.threshold (k : ℕ) : AccessStructure P where
  Auth A := k ≤ #A
  mono hAB hA := hA.trans (card_le_card hAB)

@[simp]
theorem AccessStructure.threshold_auth {k : ℕ} {A : Finset P} :
    (AccessStructure.threshold k).Auth A ↔ k ≤ #A := Iff.rfl

/-- The data of a secret sharing scheme: `share sec r i` is the share handed to party `i` when
the secret is `sec` and the dealer's coins are `r`, and `reconstruct A f` is the secret that the
set `A` computes from the share assignment `f`. Security is not part of the data; see
`Scheme.Correct` and `Scheme.PerfectPrivacy`. [Bei11, §1]; the pair `(Share, Recon)` of
[PS10, Def 152.1].

**Deviation:** [PS10] asks `Share` and `Recon` to be probabilistic polynomial-time; efficiency is
not modelled here, since the security notions are information-theoretic. [PS10]'s `Recon`
receives `k` shares with their indices; here it receives a set of parties and a share assignment,
and `LocalReconstruct` says it reads only the shares of that set. -/
structure Scheme (P Secret Share Rand : Type*) where
  /-- The dealer's sharing map. -/
  share : Secret → Rand → P → Share
  /-- The reconstruction map used by a set of parties. -/
  reconstruct : Finset P → (P → Share) → Secret

namespace Scheme

variable {Secret Share Rand : Type*} (S : Scheme P Secret Share Rand)

/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1]
For the threshold structure this is [PS10, Def 152.1, item 2]: any `k` shares reconstruct. -/
def Correct (Γ : AccessStructure P) : Prop :=
  ∀ A : Finset P, Γ.Auth A → ∀ (sec : Secret) (r : Rand), S.reconstruct A (S.share sec r) = sec

/-- Reconstruction by `A` only inspects the shares held by `A`. This is a well-formedness
condition on the syntax of the scheme, not a security property, but without it `Correct` could
be satisfied by a reconstruction map that peeks at shares outside `A`. -/
def LocalReconstruct : Prop :=
  ∀ (A : Finset P) (f g : P → Share), (∀ i ∈ A, f i = g i) → S.reconstruct A f = S.reconstruct A g

/-- Perfect privacy: for every unauthorized set `B` and every pair of secrets there is a
bijection `e` of the randomness space such that sharing `sec'` with coins `e r` gives the
parties of `B` exactly the shares they would have received had the secret been `sec` with coins
`r`. With uniform coins this says the `B`-view is distributed independently of the secret.
[Bei11, §1], [Sha79, §2]

For the threshold structure this gives [PS10, Def 152.1, item 3]: the shares of fewer than `k`
parties have the same distribution for any two secrets, so they are statistically close at
distance zero. **Deviation:** stated as a bijection of the coins rather than as closeness of
distributions; this is the stronger, perfect form, and the one Shamir's scheme achieves
(`card_view_eq` gives the counting consequence). -/
def PerfectPrivacy (Γ : AccessStructure P) : Prop :=
  ∀ B : Finset P, ¬ Γ.Auth B → ∀ sec sec' : Secret,
    ∃ e : Rand ≃ Rand, ∀ (r : Rand), ∀ i ∈ B, S.share sec' (e r) i = S.share sec r i

variable {S}

/-- The counting form of perfect privacy: for an unauthorized set `B` and any candidate view
`w`, the number of coin tosses producing that view is the same for every secret. In particular
an unbounded adversary holding the shares of `B` learns nothing about the secret.

**Proof sketch.** The privacy bijection `e` sending `sec`-coins to `sec'`-coins restricts to a
bijection between the two fibres, since it preserves the `B`-view by construction. -/
theorem PerfectPrivacy.card_view_eq {Γ : AccessStructure P} (h : S.PerfectPrivacy Γ)
    {B : Finset P} (hB : ¬ Γ.Auth B) (sec sec' : Secret) (w : P → Share) :
    Nat.card {r : Rand // ∀ i ∈ B, S.share sec r i = w i} =
      Nat.card {r : Rand // ∀ i ∈ B, S.share sec' r i = w i} := by
  obtain ⟨e, he⟩ := h B hB sec sec'
  refine Nat.card_congr ⟨fun r => ⟨e r.1, fun i hi => (he r.1 i hi).trans (r.2 i hi)⟩,
    fun r => ⟨e.symm r.1, fun i hi => ?_⟩, fun r => by simp, fun r => by simp⟩
  have := he (e.symm r.1) i hi
  rw [e.apply_symm_apply] at this
  exact this ▸ r.2 i hi

end Scheme

end TCSlib.SecretSharing

## ===== TCSlib/Cryptography/SecretSharing/Shamir.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import TCSlib.Cryptography.SecretSharing.Defs
import TCSlib.Cryptography.SecretSharing.Interpolation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shamir's `k`-out-of-`n` secret sharing scheme

The dealer holding a secret `sec ∈ F` picks a uniformly random polynomial
`p = sec + a₁X + ⋯ + a_{k-1}X^{k-1}` and hands party `a` the share `p(a)`, where the parties are
labelled by *nonzero* field elements. Any `k` parties recover `sec = p(0)` by Lagrange
interpolation; any `k - 1` or fewer learn nothing at all.

The randomness is modelled as the polynomial `q` with `p = sec + X · q`, i.e. as an element of
`degreeLT F (k-1)`, so that "uniform coins" means "uniform `q`" and the privacy bijection is
literally translation by a fixed polynomial.

## Main definitions

* `TCSlib.Shamir.Party`: the parties, labelled by nonzero elements of `F`.
* `TCSlib.Shamir.poly`, `TCSlib.Shamir.scheme`: the dealer's polynomial and the scheme itself.

## Main results

* `TCSlib.Shamir.correct`: any `k` parties reconstruct the secret.
* `TCSlib.Shamir.perfectPrivacy`: any at most `k - 1` parties have a view independent of the
  secret; combined with `Scheme.PerfectPrivacy.card_view_eq`, every view has equally many coin
  preimages under every secret.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979, §2–3.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §2.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.1.2–6.1.3 (Lemma 153.2, Fact 153.3, Protocol 154.4, Proposition 154.5).
-/

namespace TCSlib.Shamir

open Finset Polynomial TCSlib.SecretSharing

variable {F : Type*} [Field F] {k : ℕ}

/-- The parties of Shamir's scheme, labelled by the nonzero elements of `F`; the label `0` is
reserved for the secret. -/
abbrev Party (F : Type*) [Field F] := {a : F // a ≠ 0}

/-- The labels of the parties, as evaluation nodes. -/
abbrev label : Party F → F := Subtype.val

theorem label_injective : Function.Injective (label (F := F)) := Subtype.val_injective

/-- The dealer's polynomial for secret `sec` and coins `q`: `sec + X · q`, of degree `< k`.
[Sha79, §2] -/
noncomputable def poly (sec : F) (q : degreeLT F (k - 1)) : F[X] := C sec + X * q.1

@[simp]
theorem poly_eval_zero (sec : F) (q : degreeLT F (k - 1)) : (poly sec q).eval 0 = sec := by
  simp [poly]

theorem poly_eval (sec : F) (q : degreeLT F (k - 1)) (a : F) :
    (poly sec q).eval a = sec + a * q.1.eval a := by simp [poly]

/-- The dealer's polynomial really has degree `< k`. -/
theorem degree_poly_lt (hk : 0 < k) (sec : F) (q : degreeLT F (k - 1)) :
    (poly sec q).degree < (k : WithBot ℕ) := by
  have hq : q.1.degree < ((k - 1 : ℕ) : WithBot ℕ) := mem_degreeLT.1 q.2
  have hXq : (X * q.1 : F[X]).degree < (k : WithBot ℕ) := by
    rcases eq_or_ne q.1 0 with h0 | h0
    · rw [h0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hlt : q.1.natDegree < k - 1 := by
        rw [degree_eq_natDegree h0] at hq; exact_mod_cast hq
      have h2 : 1 + q.1.natDegree < k := by omega
      rw [degree_mul, degree_X, degree_eq_natDegree h0]
      exact_mod_cast h2
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ hXq)
  exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hk)

/-- Shamir's scheme: share `sec` as the evaluations of a random degree-`< k` polynomial with
constant term `sec`, and reconstruct by Lagrange interpolation at `0`. [Sha79, §2],
[PS10, Prot 154.4]; the interpolation step is [PS10, Lem 153.2] (Mathlib's
`Lagrange.interpolate`).

**Deviations from [PS10, Prot 154.4].** [PS10] works over `ℤ_p` for a prime `p > n` and gives
shares only to the parties `1, …, n`; here the field is arbitrary and every nonzero element is a
party. [PS10]'s `n`-party scheme is this one with the other parties' shares discarded, and its
correctness and privacy claims, which concern sets of those parties, are special cases of
`correct` and `perfectPrivacy`. [PS10] draws `n − 1` random coefficients and writes the
polynomial up to `a_n tⁿ`, a typo: threshold `k` needs degree `k − 1` and the `k − 1` random
coefficients that the coins `q` carry here. -/
noncomputable def scheme (k : ℕ) (F : Type*) [Field F] [DecidableEq F] :
    Scheme (Party F) F F (degreeLT F (k - 1)) where
  share sec q a := (poly sec q).eval (label a)
  reconstruct A f := (Lagrange.interpolate A label f).eval 0

theorem scheme_share [DecidableEq F] (sec : F) (q : degreeLT F (k - 1)) (a : Party F) :
    (scheme k F).share sec q a = (poly sec q).eval (label a) := rfl

/-- Reconstruction only reads the shares of the reconstructing set. -/
theorem localReconstruct [DecidableEq F] : (scheme k F).LocalReconstruct := by
  intro A f g hfg
  simp only [scheme]
  congr 1
  exact Lagrange.interpolate_eq_of_values_eq_on _ _ hfg

/-- **Correctness.** Any `k` (or more) parties reconstruct the secret exactly, whatever the
dealer's coins were. [Sha79, §2]; the reconstruction half of [PS10, Prop 154.5], which [PS10]
leaves as an exercise.

**Proof sketch.** The dealer's polynomial `p` has degree `< k ≤ #A`, and it agrees with the
shares on the `#A` distinct nodes of `A`, so by uniqueness of Lagrange interpolation it *is*
the interpolant of those shares. Evaluating at `0` returns its constant term, the secret. -/
theorem correct [DecidableEq F] (hk : 0 < k) :
    (scheme k F).Correct (AccessStructure.threshold k) := by
  intro A hA sec q
  have hinj : Set.InjOn label (A : Set (Party F)) := label_injective.injOn
  have hdeg : (poly sec q).degree < (#A : WithBot ℕ) :=
    lt_of_lt_of_le (degree_poly_lt hk sec q) (by exact_mod_cast hA)
  have : Lagrange.interpolate A label ((scheme k F).share sec q) = poly sec q :=
    (Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg (fun i _ => rfl)).symm
  change (Lagrange.interpolate A label ((scheme k F).share sec q)).eval 0 = sec
  rw [this, poly_eval_zero]

/-- **Perfect privacy.** For any set `B` of at most `k - 1` parties and any two secrets there is
a bijection of the dealer's coins carrying one secret's `B`-view to the other's; so the shares
held by `B` carry no information whatsoever about the secret. [Sha79, §3]; the privacy half of
[PS10, Prop 154.5], in its perfect form (see `Scheme.PerfectPrivacy`).

**Proof sketch.** Let `δ = sec - sec'`. Interpolate through the `#B ≤ k - 1` points
`(b, δ / b)` (legitimate: party labels are nonzero) to get `r` of degree `< #B ≤ k - 1`, and
translate the coins by `r`. Then for `b ∈ B`,
`sec' + b·(q + r)(b) = sec' + b·q(b) + δ = sec + b·q(b)`, which is exactly the share `b` would
have received from `sec`. Translation by a fixed element is a bijection, so no view is gained
or lost. -/
theorem perfectPrivacy [DecidableEq F] :
    (scheme k F).PerfectPrivacy (AccessStructure.threshold k) := by
  intro B hB sec sec'
  have hBcard : #B < k := by simpa using lt_of_not_ge (by simpa using hB)
  have hinj : Set.InjOn label (B : Set (Party F)) := label_injective.injOn
  set r : F[X] := Lagrange.interpolate B label (fun b => (sec - sec') / label b) with hr
  have hrdeg : r ∈ degreeLT F (k - 1) := by
    refine mem_degreeLT.2 (lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ hinj) ?_)
    exact_mod_cast Nat.le_sub_one_of_lt hBcard
  refine ⟨Equiv.addRight (⟨r, hrdeg⟩ : degreeLT F (k - 1)), fun q b hb => ?_⟩
  have hb0 : (label b) ≠ 0 := b.2
  have hrb : r.eval (label b) = (sec - sec') / label b :=
    Lagrange.eval_interpolate_at_node _ hinj hb
  simp only [scheme_share, poly_eval, Equiv.coe_addRight]
  have : ((⟨r, hrdeg⟩ : degreeLT F (k - 1)) + q).1 = q.1 + r := by
    simp [add_comm]
  rw [show (q + (⟨r, hrdeg⟩ : degreeLT F (k - 1))).1 = q.1 + r from rfl]
  rw [eval_add, hrb]
  field_simp
  ring

/-- **Perfect privacy, counting form.** Over a finite field, for a set `B` of at most `k - 1`
parties and *any* candidate view `w`, the number of coin choices producing that view is
`|F| ^ (k - 1 - #B)` — the same number for every secret and every view. So the adversary's view
is uniform on all of `(B → F)` and carries no information.

**Proof sketch.** Writing the dealer's polynomial as `sec + X · q`, party `b` receiving the share
`w b` pins down `q(b) = (w b - sec) / b` (party labels are nonzero). So the coin choices
consistent with the view are the polynomials of degree `< k - 1` through `#B` prescribed points,
and `Interpolation.natCard_degreeLT_eval_eq` counts these as `|F| ^ (k - 1 - #B)`, a count not
depending on the prescribed values and hence not on `sec`. -/
theorem natCard_coins_view [DecidableEq F] [Fintype F] (hk : 0 < k) (hkF : k ≤ Fintype.card F)
    {B : Finset (Party F)} (hB : #B < k) (sec : F) (w : Party F → F) :
    Nat.card {q : degreeLT F (k - 1) // ∀ b ∈ B, (scheme k F).share sec q b = w b} =
      Nat.card F ^ (k - 1 - #B) := by
  -- Pick a set `s` of `k - 1` parties containing `B` to serve as interpolation nodes.
  have hcard : Fintype.card (Party F) = Fintype.card F - 1 := by
    simp
  have hBle : #B ≤ k - 1 := Nat.le_sub_one_of_lt hB
  obtain ⟨s, hBs, -, hs⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ B) hBle
      (by rw [Finset.card_univ, hcard]; omega)
  have hinj : Set.InjOn label (s : Set (Party F)) := label_injective.injOn
  -- Consistency with the view is exactly a prescription of `q`'s values on `B`.
  have hiff : ∀ q : degreeLT F (k - 1),
      (∀ b ∈ B, (scheme k F).share sec q b = w b) ↔
        (∀ b ∈ B, eval (label b) q.1 = (w b - sec) / label b) := by
    intro q
    refine forall_congr' fun b => forall_congr' fun hb => ?_
    have hb0 : label b ≠ 0 := b.2
    rw [scheme_share, poly_eval]
    constructor
    · intro h; rw [eq_div_iff hb0, ← h]; ring
    · intro h; rw [h]; field_simp; ring
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  have := Interpolation.natCard_degreeLT_eval_eq (v := label) (s := s) (t := B) hinj hBs
    (fun b => (w b - sec) / label b)
  rw [hs] at this
  rw [this]

end TCSlib.Shamir

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/docstring-and-facade.diff =====

diff --git a/TCSlib/Cryptography/SecretSharing/Defs.lean b/TCSlib/Cryptography/SecretSharing/Defs.lean
index 783dc079..0beec863 100644
--- a/TCSlib/Cryptography/SecretSharing/Defs.lean
+++ b/TCSlib/Cryptography/SecretSharing/Defs.lean
@@ -44,6 +44,8 @@ finiteness-free and measure-theory-free, and it is what a scheme's proof natural
 
 * [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
 * [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §1–2.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.1.1 (Definition 152.1, `(k, n)` secret sharing).
 -/
 
 namespace TCSlib.SecretSharing
@@ -74,7 +76,13 @@ theorem AccessStructure.threshold_auth {k : ℕ} {A : Finset P} :
 /-- The data of a secret sharing scheme: `share sec r i` is the share handed to party `i` when
 the secret is `sec` and the dealer's coins are `r`, and `reconstruct A f` is the secret that the
 set `A` computes from the share assignment `f`. Security is not part of the data; see
-`Scheme.Correct` and `Scheme.PerfectPrivacy`. [Bei11, §1] -/
+`Scheme.Correct` and `Scheme.PerfectPrivacy`. [Bei11, §1]; the pair `(Share, Recon)` of
+[PS10, Def 152.1].
+
+**Deviation:** [PS10] asks `Share` and `Recon` to be probabilistic polynomial-time; efficiency is
+not modelled here, since the security notions are information-theoretic. [PS10]'s `Recon`
+receives `k` shares with their indices; here it receives a set of parties and a share assignment,
+and `LocalReconstruct` says it reads only the shares of that set. -/
 structure Scheme (P Secret Share Rand : Type*) where
   /-- The dealer's sharing map. -/
   share : Secret → Rand → P → Share
@@ -85,7 +93,8 @@ namespace Scheme
 
 variable {Secret Share Rand : Type*} (S : Scheme P Secret Share Rand)
 
-/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1] -/
+/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1]
+For the threshold structure this is [PS10, Def 152.1, item 2]: any `k` shares reconstruct. -/
 def Correct (Γ : AccessStructure P) : Prop :=
   ∀ A : Finset P, Γ.Auth A → ∀ (sec : Secret) (r : Rand), S.reconstruct A (S.share sec r) = sec
 
@@ -99,7 +108,13 @@ def LocalReconstruct : Prop :=
 bijection `e` of the randomness space such that sharing `sec'` with coins `e r` gives the
 parties of `B` exactly the shares they would have received had the secret been `sec` with coins
 `r`. With uniform coins this says the `B`-view is distributed independently of the secret.
-[Bei11, §1], [Sha79, §2] -/
+[Bei11, §1], [Sha79, §2]
+
+For the threshold structure this gives [PS10, Def 152.1, item 3]: the shares of fewer than `k`
+parties have the same distribution for any two secrets, so they are statistically close at
+distance zero. **Deviation:** stated as a bijection of the coins rather than as closeness of
+distributions; this is the stronger, perfect form, and the one Shamir's scheme achieves
+(`card_view_eq` gives the counting consequence). -/
 def PerfectPrivacy (Γ : AccessStructure P) : Prop :=
   ∀ B : Finset P, ¬ Γ.Auth B → ∀ sec sec' : Secret,
     ∃ e : Rand ≃ Rand, ∀ (r : Rand), ∀ i ∈ B, S.share sec' (e r) i = S.share sec r i
diff --git a/TCSlib/Cryptography/SecretSharing/Shamir.lean b/TCSlib/Cryptography/SecretSharing/Shamir.lean
index 74288535..42fc43f3 100644
--- a/TCSlib/Cryptography/SecretSharing/Shamir.lean
+++ b/TCSlib/Cryptography/SecretSharing/Shamir.lean
@@ -38,6 +38,8 @@ literally translation by a fixed polynomial.
 
 * [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979, §2–3.
 * [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §2.1.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
+  §6.1.2–6.1.3 (Lemma 153.2, Fact 153.3, Protocol 154.4, Proposition 154.5).
 -/
 
 namespace TCSlib.Shamir
@@ -83,7 +85,17 @@ theorem degree_poly_lt (hk : 0 < k) (sec : F) (q : degreeLT F (k - 1)) :
   exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hk)
 
 /-- Shamir's scheme: share `sec` as the evaluations of a random degree-`< k` polynomial with
-constant term `sec`, and reconstruct by Lagrange interpolation at `0`. [Sha79, §2] -/
+constant term `sec`, and reconstruct by Lagrange interpolation at `0`. [Sha79, §2],
+[PS10, Prot 154.4]; the interpolation step is [PS10, Lem 153.2] (Mathlib's
+`Lagrange.interpolate`).
+
+**Deviations from [PS10, Prot 154.4].** [PS10] works over `ℤ_p` for a prime `p > n` and gives
+shares only to the parties `1, …, n`; here the field is arbitrary and every nonzero element is a
+party. [PS10]'s `n`-party scheme is this one with the other parties' shares discarded, and its
+correctness and privacy claims, which concern sets of those parties, are special cases of
+`correct` and `perfectPrivacy`. [PS10] draws `n − 1` random coefficients and writes the
+polynomial up to `a_n tⁿ`, a typo: threshold `k` needs degree `k − 1` and the `k − 1` random
+coefficients that the coins `q` carry here. -/
 noncomputable def scheme (k : ℕ) (F : Type*) [Field F] [DecidableEq F] :
     Scheme (Party F) F F (degreeLT F (k - 1)) where
   share sec q a := (poly sec q).eval (label a)
@@ -100,7 +112,8 @@ theorem localReconstruct [DecidableEq F] : (scheme k F).LocalReconstruct := by
   exact Lagrange.interpolate_eq_of_values_eq_on _ _ hfg
 
 /-- **Correctness.** Any `k` (or more) parties reconstruct the secret exactly, whatever the
-dealer's coins were. [Sha79, §2]
+dealer's coins were. [Sha79, §2]; the reconstruction half of [PS10, Prop 154.5], which [PS10]
+leaves as an exercise.
 
 **Proof sketch.** The dealer's polynomial `p` has degree `< k ≤ #A`, and it agrees with the
 shares on the `#A` distinct nodes of `A`, so by uniqueness of Lagrange interpolation it *is*
@@ -118,7 +131,8 @@ theorem correct [DecidableEq F] (hk : 0 < k) :
 
 /-- **Perfect privacy.** For any set `B` of at most `k - 1` parties and any two secrets there is
 a bijection of the dealer's coins carrying one secret's `B`-view to the other's; so the shares
-held by `B` carry no information whatsoever about the secret. [Sha79, §3]
+held by `B` carry no information whatsoever about the secret. [Sha79, §3]; the privacy half of
+[PS10, Prop 154.5], in its perfect form (see `Scheme.PerfectPrivacy`).
 
 **Proof sketch.** Let `δ = sec - sec'`. Interpolate through the `#B ≤ k - 1` points
 `(b, δ / b)` (legitimate: party labels are nonzero) to get `r` of degree `< #B ≤ k - 1`, and
diff --git a/TCSlib/InformationTheory.lean b/TCSlib/InformationTheory.lean
index 12437b49..737a9b19 100644
--- a/TCSlib/InformationTheory.lean
+++ b/TCSlib/InformationTheory.lean
@@ -6,11 +6,13 @@ import TCSlib.InformationTheory.FinDist
 import TCSlib.InformationTheory.StatisticalDistance
 import TCSlib.InformationTheory.UniversalHashing
 import TCSlib.InformationTheory.LeftoverHash
+import TCSlib.InformationTheory.Entropy
+import TCSlib.InformationTheory.Extractors
 
 /-!
 # Information theory
 
-Finite distributions, statistical distance, and randomness extraction.
+Finite distributions, statistical distance, entropy, and randomness extraction.
 
 ## Contents
 
@@ -19,10 +21,14 @@ Finite distributions, statistical distance, and randomness extraction.
 * `TCSlib.InformationTheory.StatisticalDistance`: statistical distance and the `ℓ¹`–`ℓ²` bound.
 * `TCSlib.InformationTheory.UniversalHashing`: universal hash families.
 * `TCSlib.InformationTheory.LeftoverHash`: the leftover hash lemma.
+* `TCSlib.InformationTheory.Entropy`: Shannon entropy, min-entropy, `k`-sources and flat sources.
+* `TCSlib.InformationTheory.Extractors`: `ε`-closeness (equivalent to a statistical-distance
+  bound), deterministic and strong extractors, and the leftover hash lemma as an extractor.
 
 ## References
 
 * [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012.
 * [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
   one-way function*, SICOMP 28(4), 1999.
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
 -/

## ===== TCSlib/InformationTheory/FinDist.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributions on a finite type

A lightweight, real-valued model of a probability distribution on a finite type: a nonnegative
function summing to one. This is deliberately not `PMF`, whose `ℝ≥0∞` values make subtraction
truncated and Cauchy–Schwarz awkward — and the arguments this file supports (collision
probability, the `ℓ¹`–`ℓ²` bound, the leftover hash lemma) are all differences of real numbers.

## Main definitions

* `TCSlib.InformationTheory.FinDist α`: a distribution on a finite type.
* `FinDist.uniform`, `FinDist.map`, `FinDist.prod`: the uniform distribution, pushforward along a
  function, and the product (independent pair) of two distributions.
* `FinDist.collision`: the collision probability `∑ p a ^ 2`, i.e. the chance that two
  independent samples agree.
* `FinDist.HasMinEntropy p k`: every outcome has probability at most `2 ^ (-k)`.

## Main results

* `FinDist.collision_le_of_hasMinEntropy`: min-entropy `k` bounds the collision probability by
  `2 ^ (-k)`.
* `FinDist.collision_uniform`, `FinDist.inv_card_le_collision`: the uniform distribution
  minimizes collision probability.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset

/-- A probability distribution on a finite type: nonnegative weights summing to one. -/
structure FinDist (α : Type*) [Fintype α] where
  /-- The probability assigned to each outcome. -/
  prob : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Probabilities sum to one. -/
  sum_prob : ∑ a, prob a = 1

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

instance : CoeFun (FinDist α) (fun _ => α → ℝ) := ⟨FinDist.prob⟩

@[simp] theorem coe_mk (f : α → ℝ) (h₁ : ∀ a, 0 ≤ f a) (h₂ : ∑ a, f a = 1) (a : α) :
    (⟨f, h₁, h₂⟩ : FinDist α) a = f a := rfl

@[ext] theorem ext {p q : FinDist α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; simpa using funext h

theorem le_one (p : FinDist α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_prob]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

theorem card_pos (p : FinDist α) : 0 < Fintype.card α := by
  by_contra hcon
  have hzero : Fintype.card α = 0 := by omega
  haveI : IsEmpty α := Fintype.card_eq_zero_iff.1 hzero
  have hsum := p.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  norm_num at hsum

instance (p : FinDist α) : Nonempty α := Fintype.card_pos_iff.1 p.card_pos

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FinDist α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp

@[simp] theorem uniform_apply [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- The pushforward of a distribution along a function. -/
def map [DecidableEq β] (f : α → β) (p : FinDist α) : FinDist β where
  prob b := ∑ a ∈ univ.filter (fun a => f a = b), p a
  nonneg _ := sum_nonneg fun a _ => p.nonneg a
  sum_prob := by
    rw [← p.sum_prob]
    exact sum_fiberwise_eq_sum_filter univ univ f p.prob ▸ (sum_fiberwise _ _ _)

@[simp] theorem map_apply [DecidableEq β] (f : α → β) (p : FinDist α) (b : β) :
    map f p b = ∑ a ∈ univ.filter (fun a => f a = b), p a := rfl

/-- The product of two distributions: an independent pair. -/
def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  prob x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, p.sum_prob, q.sum_prob]

@[simp] theorem prod_apply (p : FinDist α) (q : FinDist β) (x : α × β) :
    prod p q x = p x.1 * q x.2 := rfl

/-- The collision probability of `p`: the probability that two independent samples from `p`
are equal. [Vad12, §6.1] -/
def collision (p : FinDist α) : ℝ := ∑ a, p a ^ 2

theorem collision_nonneg (p : FinDist α) : 0 ≤ collision p :=
  sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem collision_uniform [Nonempty α] :
    collision (uniform α) = (Fintype.card α : ℝ)⁻¹ := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [collision, uniform_apply, Finset.sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Uniform is the distribution of least collision probability. -/
theorem inv_card_le_collision (p : FinDist α) : (Fintype.card α : ℝ)⁻¹ ≤ collision p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast p.card_pos
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := p.prob)
  rw [p.sum_prob, card_univ] at h
  have h2 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * collision p := by
    simpa [collision] using h
  rw [inv_le_iff_one_le_mul₀ hc]
  linarith [mul_comm (Fintype.card α : ℝ) (collision p)]

/-- `p` has min-entropy at least `k` when no outcome has probability more than `2 ^ (-k)`.
Stated as this bound rather than as `-logb 2 (⨆ a, p a)` so that no logarithms appear in the
hypotheses of the results that use it. [Vad12, §6.2] -/
def HasMinEntropy (p : FinDist α) (k : ℝ) : Prop := ∀ a, p a ≤ (2 : ℝ) ^ (-k)

/-- Min-entropy `k` bounds the collision probability by `2 ^ (-k)`: the chance of a collision is
at most the chance of hitting any single most-likely point.

**Proof sketch.** `∑ p a ^ 2 ≤ (max p) · ∑ p a = max p ≤ 2 ^ (-k)`. -/
theorem collision_le_of_hasMinEntropy {p : FinDist α} {k : ℝ} (h : HasMinEntropy p k) :
    collision p ≤ (2 : ℝ) ^ (-k) := by
  calc collision p = ∑ a, p a * p a := by simp [collision, sq]
    _ ≤ ∑ a, (2 : ℝ) ^ (-k) * p a :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) (p.nonneg a)
    _ = (2 : ℝ) ^ (-k) := by rw [← Finset.mul_sum, p.sum_prob, mul_one]

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/InformationTheory/StatisticalDistance.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical distance

The statistical (total variation) distance between two distributions on a finite type, and the
`ℓ¹`–`ℓ²` bound that turns a collision-probability estimate into a statistical-distance estimate.

That bound, `statDist_uniform_le_sqrt`, is the engine of the leftover hash lemma and of
smoothing/extractor arguments generally: collision probability is a quadratic quantity and so is
easy to compute exactly, while statistical distance is an `ℓ¹` quantity and is what security
definitions speak in; Cauchy–Schwarz is the bridge.

## Main definitions

* `TCSlib.InformationTheory.statDist`: `½ ∑ |p a - q a|`.

## Main results

* `statDist_nonneg`, `statDist_comm`, `statDist_self`, `statDist_triangle`: metric properties.
* `statDist_uniform_le_sqrt`: `statDist p uniform ≤ ½ √(|α| · collision p - 1)`.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {α : Type*} [Fintype α]

/-- The statistical distance (total variation distance) between two distributions:
`½ ∑ |p a - q a|`. [Vad12, §6.1] -/
noncomputable def statDist (p q : FinDist α) : ℝ := (1 / 2) * ∑ a, |p a - q a|

theorem statDist_nonneg (p q : FinDist α) : 0 ≤ statDist p q := by
  refine mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _)

theorem statDist_comm (p q : FinDist α) : statDist p q = statDist q p := by
  simp only [statDist]
  exact congrArg _ (sum_congr rfl fun a _ => abs_sub_comm _ _)

@[simp] theorem statDist_self (p : FinDist α) : statDist p p = 0 := by simp [statDist]

theorem statDist_triangle (p q r : FinDist α) : statDist p r ≤ statDist p q + statDist q r := by
  simp only [statDist, ← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) (by norm_num)
  exact abs_sub_le _ _ _

/-- **The `ℓ¹`–`ℓ²` bound.** A distribution whose collision probability is close to the uniform
value `1/|α|` is close to uniform in statistical distance.

**Proof sketch.** Write `d a = p a - 1/n` with `n = |α|`. Expanding the square and using
`∑ p a = 1` gives `∑ d a ^ 2 = collision p - 1/n`. Cauchy–Schwarz (Chebyshev's sum inequality in
the form `(∑ |d|) ^ 2 ≤ n ∑ d ^ 2`) then bounds `∑ |d a|` by `√(n · collision p - 1)`, and
statistical distance is half of that sum. -/
theorem statDist_uniform_le_sqrt [Nonempty α] (p : FinDist α) :
    statDist p (uniform α) ≤ (1 / 2) * Real.sqrt (Fintype.card α * collision p - 1) := by
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  have hn : (0 : ℝ) < n := by rw [hn_def]; exact_mod_cast p.card_pos
  have hn0 : n ≠ 0 := ne_of_gt hn
  -- `∑ (p a - 1/n) ^ 2 = collision p - 1/n`
  have hexp : ∑ a, (p a - n⁻¹) ^ 2 = collision p - n⁻¹ := by
    simp only [collision]
    have hterm : ∀ a : α, (p a - n⁻¹) ^ 2 = p a ^ 2 - 2 * n⁻¹ * p a + n⁻¹ ^ 2 := fun a => by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_prob,
      Finset.sum_const, card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  -- Cauchy–Schwarz
  have cs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := fun a => |p a - n⁻¹|)
  rw [card_univ, ← hn_def] at cs
  have habs : ∑ a, |p a - n⁻¹| ^ 2 = collision p - n⁻¹ := by
    rw [← hexp]
    exact sum_congr rfl fun a _ => sq_abs _
  rw [habs] at cs
  have hsq : (∑ a, |p a - n⁻¹|) ^ 2 ≤ n * collision p - 1 := by
    refine cs.trans (le_of_eq ?_)
    field_simp
  have hle : ∑ a, |p a - n⁻¹| ≤ Real.sqrt (n * collision p - 1) :=
    Real.le_sqrt_of_sq_le hsq
  simp only [statDist, uniform_apply, ← hn_def]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

end TCSlib.InformationTheory

## ===== TCSlib/InformationTheory/UniversalHashing.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal hash families

A family `f : S → α → β` of hash functions is *universal* when a random member maps any two
distinct points to the same image with probability at most `1 / |β|` — the collision probability
of a truly random function. Universality is a purely combinatorial (counting) condition, which is
why it can be met unconditionally, and it is exactly the hypothesis the leftover hash lemma needs.

## Main definitions

* `TCSlib.InformationTheory.IsUniversal`: the defining collision bound.

## Main results

* `isUniversal_affine`: the affine family `x ↦ a * x + b` over a field is universal.
* `sum_sq_fiber`: the combinatorial identity converting a sum of squared fibre weights into a sum
  over colliding pairs; this is what lets a universality hypothesis bound a collision
  probability.

## References

* [CW79] J.L. Carter, M.N. Wegman, *Universal classes of hash functions*, JCSS 18(2), 1979.
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §3.5, §6.2.
-/

namespace TCSlib.InformationTheory

open Finset

variable {S α β : Type*} [Fintype S] [Fintype α] [Fintype β]

/-- `f` is a universal family of hash functions: for any two distinct points, the fraction of
seeds under which they collide is at most `1 / |β|`. [CW79], [Vad12, §3.5] -/
def IsUniversal [DecidableEq β] (f : S → α → β) : Prop :=
  ∀ x y : α, x ≠ y →
    ((univ.filter (fun s => f s x = f s y)).card : ℝ) ≤ (Fintype.card S : ℝ) / Fintype.card β

/-- **The affine family is universal.** Over a field, `(a, b) ↦ (x ↦ a * x + b)` is a universal
family; two distinct points collide only when `a = 0`, which is a `1 / |F|` fraction of seeds.
[CW79], [Vad12, §3.5] -/
theorem isUniversal_affine (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsUniversal (S := F × F) (α := F) (β := F) (fun s x => s.1 * x + s.2) := by
  intro x y hxy
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x⟩
  have hset : (univ.filter (fun s : F × F => s.1 * x + s.2 = s.1 * y + s.2))
      = ({(0 : F)} ×ˢ (univ : Finset F)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · intro h
      have : a * (x - y) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with ha | hxy'
      · exact ⟨ha, trivial⟩
      · exact absurd (sub_eq_zero.1 hxy') hxy
    · rintro ⟨rfl, -⟩
      ring
  rw [hset, card_product, card_singleton, card_univ, one_mul, Fintype.card_prod]
  push_cast
  rw [le_div_iff₀ hcard]

/-- Grouping a weighted sum by the fibres of `g` and squaring is the same as summing the weight
products over all colliding pairs. This is the identity that turns a collision-probability
computation into a counting problem about the hash family. -/
theorem sum_sq_fiber [DecidableEq β] (g : α → β) (w : α → ℝ) :
    ∑ y, (∑ x ∈ univ.filter (fun x => g x = y), w x) ^ 2
      = ∑ x, ∑ x', if g x = g x' then w x * w x' else 0 := by
  have h1 : ∀ y : β, (∑ x ∈ univ.filter (fun x => g x = y), w x)
      = ∑ x, if g x = y then w x else 0 := fun y => Finset.sum_filter _ _
  simp_rw [h1, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, if_true]
  by_cases h : g x = g x' <;> simp [h, eq_comm]

end TCSlib.InformationTheory

## ===== TCSlib/InformationTheory/LeftoverHash.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.StatisticalDistance
import TCSlib.InformationTheory.UniversalHashing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The leftover hash lemma

Hashing a source of min-entropy `k` with a universal family extracts almost-uniform randomness:
the pair `(seed, hash of the source)` is statistically close to uniform, with error
`½ √(|β| · 2^(-k))`. The seed is published alongside the output, so the family is a *strong*
extractor; this is the standard tool for privacy amplification, key derivation from imperfect
sources, and randomness extraction generally.

The proof is the classical collision-probability argument in three steps: universality bounds the
collision probability of `(seed, hash)`, the `ℓ¹`–`ℓ²` bound turns that into a statistical
distance bound, and min-entropy bounds the source's own collision probability.

## Main definitions

* `TCSlib.InformationTheory.hashPair`: the distribution of `(seed, f seed x)` for a uniform seed
  and `x` drawn from the source.

## Main results

* `collision_hashPair_le`: universality bounds the collision probability of `(seed, hash)` by
  `(1/|S|)(collision X + 1/|β|)`.
* `leftover_hash`: **the leftover hash lemma**.

## References

* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999 (Lemma 4.8, the leftover hash lemma).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, Thm 6.18.
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {S α β : Type*} [Fintype S] [Fintype α] [Fintype β]
  [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S] [Nonempty β]

/-- The distribution of the pair `(seed, f seed x)` where the seed is uniform and `x` is drawn
from the source `X`, independently. Closeness of this pair to uniform — rather than of the hash
value alone — is what makes a universal family a *strong* extractor. [Vad12, Thm 6.18] -/
noncomputable def hashPair (f : S → α → β) (X : FinDist α) : FinDist (S × β) :=
  FinDist.map (fun p => (p.1, f p.1 p.2)) (FinDist.prod (uniform S) X)

omit [DecidableEq α] [Nonempty β] in
theorem hashPair_apply (f : S → α → β) (X : FinDist α) (s : S) (y : β) :
    hashPair f X (s, y)
      = (Fintype.card S : ℝ)⁻¹ * ∑ x ∈ univ.filter (fun x => f s x = y), X x := by
  simp only [hashPair, map_apply, Finset.sum_filter, Fintype.sum_prod_type, FinDist.prod_apply,
    Prod.mk.injEq]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single_of_mem s (mem_univ s)]
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : f s x = y <;> simp [h]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [hb]

/-- **Universality bounds the collision probability of the hashed pair.**

**Proof sketch.** Expanding, the collision probability of `(seed, hash)` is
`|S|⁻² ∑_seed ∑_y (weight of the fibre over y)²`. By `sum_sq_fiber` the inner double sum counts
colliding pairs `(x, x')`, and summing over seeds replaces each pair by the number of seeds under
which it collides. Diagonal pairs contribute `|S| · collision X`; off-diagonal pairs contribute at
most `|S|/|β|` times `(∑ X)² = 1`, by universality. -/
theorem collision_hashPair_le {f : S → α → β} (hf : IsUniversal f) (X : FinDist α) :
    collision (hashPair f X)
      ≤ (Fintype.card S : ℝ)⁻¹ * (collision X + (Fintype.card β : ℝ)⁻¹) := by
  set N : ℝ := (Fintype.card S : ℝ) with hN_def
  set M : ℝ := (Fintype.card β : ℝ) with hM_def
  have hN : (0 : ℝ) < N := by rw [hN_def]; exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < M := by rw [hM_def]; exact_mod_cast Fintype.card_pos
  set c : α → α → ℝ := fun x x' => ((univ.filter (fun s => f s x = f s x')).card : ℝ) with hc_def
  -- Step 1: expand the collision probability over seeds and fibres.
  have hexpand : collision (hashPair f X)
      = N⁻¹ ^ 2 * ∑ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2 := by
    simp only [collision, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hashPair_apply, mul_pow]
  -- Step 2: rewrite the fibre sums as sums over colliding pairs, then count seeds.
  have hpairs : ∀ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2
      = ∑ x, ∑ x', if f s x = f s x' then X x * X x' else 0 := fun s => sum_sq_fiber _ _
  have hswap : ∑ s : S, ∑ x, ∑ x', (if f s x = f s x' then X x * X x' else 0)
      = ∑ x, ∑ x', c x x' * (X x * X x') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Step 3: split the diagonal off and apply universality to the rest.
  have hdiag : ∀ x : α, c x x = N := by
    intro x
    simp [hc_def, hN_def]
  have hoff : ∀ x x' : α, x ≠ x' → c x x' ≤ N / M := fun x x' h => hf x x' h
  have hkey : ∑ x, ∑ x', c x x' * (X x * X x') ≤ N * collision X + N / M := by
    have hsplit : ∀ x : α, ∑ x', c x x' * (X x * X x')
        = c x x * (X x * X x) + ∑ x' ∈ univ.erase x, c x x' * (X x * X x') :=
      fun x => (Finset.add_sum_erase _ _ (mem_univ x)).symm
    have hstep : ∀ x : α, ∑ x', c x x' * (X x * X x')
        ≤ N * (X x * X x) + (N / M) * ∑ x', X x * X x' := by
      intro x
      rw [hsplit x, hdiag x]
      refine add_le_add_left ?_ _
      rw [Finset.mul_sum]
      have h1 : ∑ x' ∈ univ.erase x, c x x' * (X x * X x')
          ≤ ∑ x' ∈ univ.erase x, (N / M) * (X x * X x') :=
        Finset.sum_le_sum fun x' hx' => mul_le_mul_of_nonneg_right
          (hoff x x' (Ne.symm (mem_erase.1 hx').1)) (mul_nonneg (X.nonneg x) (X.nonneg x'))
      refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
      intro x' _ _
      exact mul_nonneg (le_of_lt (div_pos hN hM)) (mul_nonneg (X.nonneg x) (X.nonneg x'))
    calc ∑ x, ∑ x', c x x' * (X x * X x')
        ≤ ∑ x, (N * (X x * X x) + (N / M) * ∑ x', X x * X x') :=
          Finset.sum_le_sum fun x _ => hstep x
      _ = N * collision X + (N / M) * ((∑ x, X x) * (∑ x', X x')) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_mul_sum]
          simp only [collision, sq]
      _ = N * collision X + N / M := by rw [X.sum_prob]; ring
  -- Combine.
  rw [hexpand]
  have hfinal : ∑ s : S, ∑ y : β, (∑ x ∈ univ.filter (fun x => f s x = y), X x) ^ 2
      ≤ N * collision X + N / M := by
    rw [Finset.sum_congr rfl fun s _ => hpairs s, hswap]
    exact hkey
  have hsq : (0 : ℝ) ≤ N⁻¹ ^ 2 := sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hfinal hsq) (le_of_eq ?_)
  field_simp

/-- **The leftover hash lemma.** If `f` is a universal hash family into `β` and the source `X` has
min-entropy at least `k`, then `(seed, f seed X)` is within statistical distance
`½ √(|β| · 2^(-k))` of uniform. [HILL99, Lemma 4.8], [Vad12, Thm 6.18]

**Proof sketch.** By the `ℓ¹`–`ℓ²` bound it suffices to bound
`|S × β| · collision (seed, hash) - 1`. Universality gives
`collision ≤ |S|⁻¹ (collision X + |β|⁻¹)`, so that quantity is at most `|β| · collision X`, and
min-entropy `k` bounds `collision X` by `2^(-k)`. -/
theorem leftover_hash {f : S → α → β} {k : ℝ} (hf : IsUniversal f) {X : FinDist α}
    (hX : HasMinEntropy X k) :
    statDist (hashPair f X) (uniform (S × β))
      ≤ (1 / 2) * Real.sqrt (Fintype.card β * (2 : ℝ) ^ (-k)) := by
  refine (statDist_uniform_le_sqrt (hashPair f X)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  have hN : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hc := collision_hashPair_le hf X
  have hCP := collision_le_of_hasMinEntropy hX
  have hstep : (Fintype.card (S × β) : ℝ) * collision (hashPair f X)
      ≤ (Fintype.card β : ℝ) * collision X + 1 := by
    rw [Fintype.card_prod]
    push_cast
    calc (Fintype.card S : ℝ) * (Fintype.card β : ℝ) * collision (hashPair f X)
        ≤ (Fintype.card S : ℝ) * (Fintype.card β : ℝ) *
            ((Fintype.card S : ℝ)⁻¹ * (collision X + (Fintype.card β : ℝ)⁻¹)) := by
          exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (Fintype.card β : ℝ) * collision X + 1 := by field_simp
  have hCPnn : (0 : ℝ) ≤ Fintype.card β := le_of_lt hM
  nlinarith [mul_le_mul_of_nonneg_left hCP hCPnn]

/-- The leftover hash lemma for the affine family over a finite field: if `X` has min-entropy at
least `k` on `F`, then `((a, b), a · X + b)` for a uniform seed `(a, b)` is within
`½ √(|F| · 2^(-k))` of uniform. A concrete witness that the hypotheses of `leftover_hash` are
satisfiable. [Vad12, Thm 6.18] -/
theorem leftover_hash_affine (F : Type*) [Field F] [Fintype F] [DecidableEq F] {k : ℝ}
    {X : FinDist F} (hX : HasMinEntropy X k) :
    statDist (hashPair (fun s : F × F => fun x : F => s.1 * x + s.2) X) (uniform ((F × F) × F))
      ≤ (1 / 2) * Real.sqrt (Fintype.card F * (2 : ℝ) ^ (-k)) :=
  leftover_hash (isUniversal_affine F) hX

end TCSlib.InformationTheory

## ===== TCSlib/Cryptography/SecretSharing/Interpolation.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counting low-degree polynomials through prescribed points

Mathlib's `Lagrange.funEquivDegreeLT` says that a polynomial of degree `< #s` is the same data as
its values on a set `s` of `#s` distinct nodes. This file draws the consequence that secret
sharing (and, more generally, any "polynomial as a random object" argument) actually uses: if you
fix the values at only *some* of the nodes, the remaining polynomials are in bijection with the
free coordinates, so there are exactly `|F| ^ (#s - #t)` of them — a count that does not depend
on *which* values were prescribed.

Everything here is about polynomials only; no secret sharing notions appear. Shamir's scheme is
the special case `t = {0} ∪ (adversary's nodes)`.

## Main definitions

* `TCSlib.Interpolation.fixedEvalEquiv`: polynomials of degree `< #s` with prescribed values on
  `t ⊆ s` are in bijection with functions `↥(s \ t) → F`.

## Main results

* `TCSlib.Interpolation.exists_unique_degreeLT_eval_eq`: unique interpolation through `#s` nodes.
* `TCSlib.Interpolation.natCard_degreeLT_eval_eq`: there are exactly `|F| ^ (#s - #t)` such
  polynomials, independently of the prescribed values.
* `TCSlib.Interpolation.surjective_eval_of_subset`: any prescription on `t ⊆ s` is realizable.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Mathlib] `Mathlib/LinearAlgebra/Lagrange.lean`.
-/

namespace TCSlib.Interpolation

open Finset Polynomial

variable {F ι : Type*} [Field F] [DecidableEq ι] {v : ι → F} {s t : Finset ι}

/-- Through any prescription of values at `#s` distinct nodes there passes exactly one
polynomial of degree `< #s`, namely the Lagrange interpolant. [Mathlib, `Lagrange`] -/
theorem exists_unique_degreeLT_eval_eq (hvs : Set.InjOn v s) (w : ι → F) :
    ∃! p : F[X], p.degree < #s ∧ ∀ i ∈ s, p.eval (v i) = w i := by
  refine ⟨Lagrange.interpolate s v w, ⟨Lagrange.degree_interpolate_lt _ hvs,
    fun i hi => Lagrange.eval_interpolate_at_node _ hvs hi⟩, fun q hq => ?_⟩
  exact Lagrange.eq_interpolate_of_eval_eq _ hvs hq.1 hq.2

/-- Prescribing the values of a polynomial on a subset `t` of the nodes leaves exactly the
freedom of choosing its values on the remaining nodes: the polynomials of degree `< #s` taking
the values `w` on `t` correspond bijectively to functions `↥(s \ t) → F`.

**Proof sketch.** Transport the constraint along `Lagrange.funEquivDegreeLT`, which identifies
degree-`< #s` polynomials with their value vectors on `s`; the constraint becomes "this
coordinate vector is `w` on `t`", and such vectors are exactly arbitrary vectors on `s \ t`. -/
noncomputable def fixedEvalEquiv (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    {p : degreeLT F #s // ∀ i ∈ t, eval (v i) p.1 = w i} ≃ (↥(s \ t) → F) where
  toFun p j := (Lagrange.funEquivDegreeLT hvs p.1) ⟨j.1, (mem_sdiff.1 j.2).1⟩
  invFun g :=
    ⟨(Lagrange.funEquivDegreeLT hvs).symm
      (fun i => if hi : i.1 ∈ t then w i.1 else g ⟨i.1, mem_sdiff.2 ⟨i.2, hi⟩⟩), by
        intro i hi
        have h := (Lagrange.funEquivDegreeLT hvs).apply_symm_apply
          (fun i : ↥s => if hi : i.1 ∈ t then w i.1 else g ⟨i.1, mem_sdiff.2 ⟨i.2, hi⟩⟩)
        have := congrFun h ⟨i, hts hi⟩
        simpa [Lagrange.funEquivDegreeLT, hi] using this⟩
  left_inv := by
    rintro ⟨p, hp⟩
    apply Subtype.ext
    apply (Lagrange.funEquivDegreeLT hvs).injective
    rw [(Lagrange.funEquivDegreeLT hvs).apply_symm_apply]
    funext i
    by_cases hi : i.1 ∈ t
    · simpa [hi, Lagrange.funEquivDegreeLT] using (hp i.1 hi).symm
    · simp [hi]
  right_inv := by
    intro g
    funext j
    have hj := mem_sdiff.1 j.2
    dsimp only
    rw [(Lagrange.funEquivDegreeLT hvs).apply_symm_apply]
    simp [hj.2]

/-- Every prescription of values on a subset `t` of the nodes is realized by some polynomial of
degree `< #s`. -/
theorem surjective_eval_of_subset (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    ∃ p : F[X], p.degree < #s ∧ ∀ i ∈ t, p.eval (v i) = w i := by
  obtain ⟨p, hp⟩ := (fixedEvalEquiv hvs hts w).symm (fun _ => 0)
  exact ⟨p.1, mem_degreeLT.1 p.2, hp⟩

/-- **The count.** Over a finite field with `q` elements there are exactly `q ^ (#s - #t)`
polynomials of degree `< #s` taking prescribed values on `t ⊆ s`. The count is the same for
every prescription `w`; this uniformity is the whole content of perfect privacy for Shamir's
scheme. -/
theorem natCard_degreeLT_eval_eq (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    Nat.card {p : degreeLT F #s // ∀ i ∈ t, eval (v i) p.1 = w i} = Nat.card F ^ (#s - #t) := by
  rw [Nat.card_congr (fixedEvalEquiv hvs hts w), Nat.card_fun, Nat.card_eq_finsetCard,
    Finset.card_sdiff, Finset.inter_eq_left.2 hts]

end TCSlib.Interpolation

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/replay-head.log =====

# replay of PR head 789cf450527ff6b8c779161e555f04093080b88d, 2026-11-04T22:20:21Z, fresh olean tree, 18 modules
=== TCSlib/Cryptography/SecretSharing/Defs start 22:20:21
=== TCSlib/Cryptography/SecretSharing/Defs end 22:20:26 rc=0
=== TCSlib/Cryptography/SecretSharing/Interpolation start 22:20:26
=== TCSlib/Cryptography/SecretSharing/Interpolation end 22:20:30 rc=0
=== TCSlib/Cryptography/SecretSharing/Shamir start 22:20:30
=== TCSlib/Cryptography/SecretSharing/Shamir end 22:20:33 rc=0
=== TCSlib/Cryptography/SecretSharing/Sharing start 22:20:33
=== TCSlib/Cryptography/SecretSharing/Sharing end 22:20:36 rc=0
=== TCSlib/Cryptography/SecretSharing/Vector start 22:20:36
=== TCSlib/Cryptography/SecretSharing/Vector end 22:20:39 rc=0
=== TCSlib/Cryptography/SecretSharing start 22:20:39
=== TCSlib/Cryptography/SecretSharing end 22:20:41 rc=0
=== TCSlib/Cryptography/MPC/ArithmeticCircuit start 22:20:41
=== TCSlib/Cryptography/MPC/ArithmeticCircuit end 22:20:43 rc=0
=== TCSlib/Cryptography/MPC/BGW/Protocol start 22:20:43
=== TCSlib/Cryptography/MPC/BGW/Protocol end 22:20:45 rc=0
=== TCSlib/Cryptography/MPC/BGW/Privacy start 22:20:45
=== TCSlib/Cryptography/MPC/BGW/Privacy end 22:20:48 rc=0
=== TCSlib/Cryptography/MPC/BGW start 22:20:48
=== TCSlib/Cryptography/MPC/BGW end 22:20:50 rc=0
=== TCSlib/Cryptography/MPC start 22:20:50
=== TCSlib/Cryptography/MPC end 22:20:52 rc=0
=== TCSlib/InformationTheory/FinDist start 22:20:52
=== TCSlib/InformationTheory/FinDist end 22:20:55 rc=0
=== TCSlib/InformationTheory/Entropy start 22:20:55
=== TCSlib/InformationTheory/Entropy end 22:20:59 rc=0
=== TCSlib/InformationTheory/StatisticalDistance start 22:20:59
=== TCSlib/InformationTheory/StatisticalDistance end 22:21:03 rc=0
=== TCSlib/InformationTheory/UniversalHashing start 22:21:03
=== TCSlib/InformationTheory/UniversalHashing end 22:21:05 rc=0
=== TCSlib/InformationTheory/LeftoverHash start 22:21:05
=== TCSlib/InformationTheory/LeftoverHash end 22:21:09 rc=0
=== TCSlib/InformationTheory/Extractors start 22:21:09
=== TCSlib/InformationTheory/Extractors end 22:21:13 rc=0
=== TCSlib/InformationTheory start 22:21:13
=== TCSlib/InformationTheory end 22:21:16 rc=0
# done 2026-11-04T22:21:16Z
pass: 18 / 18; FAIL: 0; error: 0; warning: 0; sorry: 0

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/replay-order.txt =====

TCSlib/Cryptography/SecretSharing/Defs
TCSlib/Cryptography/SecretSharing/Interpolation
TCSlib/Cryptography/SecretSharing/Shamir
TCSlib/Cryptography/SecretSharing/Sharing
TCSlib/Cryptography/SecretSharing/Vector
TCSlib/Cryptography/SecretSharing
TCSlib/Cryptography/MPC/ArithmeticCircuit
TCSlib/Cryptography/MPC/BGW/Protocol
TCSlib/Cryptography/MPC/BGW/Privacy
TCSlib/Cryptography/MPC/BGW
TCSlib/Cryptography/MPC
TCSlib/InformationTheory/FinDist
TCSlib/InformationTheory/Entropy
TCSlib/InformationTheory/StatisticalDistance
TCSlib/InformationTheory/UniversalHashing
TCSlib/InformationTheory/LeftoverHash
TCSlib/InformationTheory/Extractors
TCSlib/InformationTheory

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/axioms.log =====

# axioms at PR head 789cf450527ff6b8c779161e555f04093080b88d (olean tree from replay-head.log)
'TCSlib.InformationTheory.FinDist.shannonEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.shannonEntropy_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.shannonEntropy_uniform_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.InformationTheory.FinDist.le_maxProb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.maxProb_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.maxProb_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.le_minEntropy_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.isSource_iff_hasMinEntropy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.IsSource.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.IsFlatSource.isSource' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.flat_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.isFlatSource_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.isSource_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.FinDist.probTrue_sub_probTrue' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.abs_probTrue_sub_le_statDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.statDist_le_of_epsClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.epsClose_iff_statDist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.EpsClose.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.EpsClose.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.IsExtractor.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.InformationTheory.IsStrongExtractor.isExtractor_seeded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.InformationTheory.isStrongExtractor_of_isUniversal' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Shamir.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Shamir.perfectPrivacy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Shamir.natCard_coins_view' depends on axioms: [propext, Classical.choice, Quot.sound]
# exit 0

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/docstring-only.log =====

# docstring-only check: comment-stripped code, PR head 789cf450527ff6b8c779161e555f04093080b88d vs main 06e61e912eedc2bce49b3ccff77bb9c4a7e18579
TCSlib/Cryptography/SecretSharing/Defs.lean: CODE IDENTICAL
TCSlib/Cryptography/SecretSharing/Shamir.lean: CODE IDENTICAL
# the tool (comment stripper):
import sys
def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j+1]); i = j + 1; continue
        out.append(src[i]); i += 1
    return '\n'.join(l.rstrip() for l in ''.join(out).splitlines() if l.strip())
a, b = (open(p, encoding='utf-8').read() for p in sys.argv[1:3])
print('CODE IDENTICAL' if strip(a) == strip(b) else 'CODE DIFFERS')

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/style-lint.log =====

# scripts/style_lint.py at PR head 789cf450527ff6b8c779161e555f04093080b88d

8 findings in 5 files


TCSlib/InformationTheory.lean: missing `set_option maxHeartbeats 0`
TCSlib/InformationTheory.lean: missing `set_option relaxedAutoImplicit false`
TCSlib/InformationTheory.lean: missing `set_option autoImplicit false`
TCSlib/Cryptography/SecretSharing/Defs.lean:73: public `theorem AccessStructure.threshold_auth` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:58: public `theorem label_injective` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:65: public `theorem poly_eval_zero` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:68: public `theorem poly_eval` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:104: public `theorem scheme_share` has no docstring
# same linter on main 06e61e912eedc2bce49b3ccff77bb9c4a7e18579 (detached worktree) for the three pre-existing files:

8 findings in 3 files
TCSlib/InformationTheory.lean: missing `set_option maxHeartbeats 0`
TCSlib/InformationTheory.lean: missing `set_option relaxedAutoImplicit false`
TCSlib/InformationTheory.lean: missing `set_option autoImplicit false`
TCSlib/Cryptography/SecretSharing/Defs.lean:71: public `theorem AccessStructure.threshold_auth` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:56: public `theorem label_injective` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:63: public `theorem poly_eval_zero` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:66: public `theorem poly_eval` has no docstring
TCSlib/Cryptography/SecretSharing/Shamir.lean:92: public `theorem scheme_share` has no docstring

## ===== briefs/pass-shelat-ch5-8/gates/01-p0/evidence/duplication.log =====

# duplication screen, 2026-11-04T22:22:14Z
# pattern (git grep -E over TCSlib/*.lean): (def|structure|abbrev|theorem|lemma|class) +(\w+\.)*(StatClose|statClose|EpsClose|epsClose|IsExtractor|isExtractor\w*|IsStrongExtractor|isStrongExtractor\w*|seededSources|minEntropy|maxProb|shannonEntropy\w*|IsSource|isSource\w*|IsFlatSource|isFlatSource\w*|probTrue\w*|statDist_le_of_epsClose|abs_probTrue\w*|le_minEntropy_iff|flat|tvDist|totalVariation)\b
== origin/main 06e61e912eedc2bce49b3ccff77bb9c4a7e18579
== origin/cryptography/pass-shelat-ch2-4 0cd203344e9c97b8a1f55f31e8be3eec9eed748a
TCSlib/Cryptography/Asymptotic/Sampling.lean:109:def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
TCSlib/Cryptography/Asymptotic/Sampling.lean:117:theorem StatClose.abs_uprob_sub_le {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
TCSlib/Cryptography/Asymptotic/Sampling.lean:123:theorem StatClose.uprob_le_add {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
TCSlib/Cryptography/Asymptotic/Sampling.lean:128:theorem StatClose.nonneg {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) : 0 ≤ δ :=
TCSlib/Cryptography/Asymptotic/Sampling.lean:132:theorem StatClose.refl (X : σ → γ) : StatClose X X 0 := fun _ => by
TCSlib/Cryptography/Asymptotic/Sampling.lean:136:theorem StatClose.symm {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) :
TCSlib/Cryptography/Asymptotic/Sampling.lean:142:theorem StatClose.mono {X : σ → γ} {Y : τ → γ} {δ δ' : ℝ} (h : StatClose X Y δ) (hδ : δ ≤ δ') :
TCSlib/Cryptography/Asymptotic/Sampling.lean:146:theorem StatClose.trans {X : σ → γ} {Y : τ → γ} {Z : υ → γ} {δ δ' : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:153:theorem StatClose.map {σ τ γ γ' : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:158:theorem StatClose.comp_equiv_left {σ' : Type*} [Fintype σ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:164:theorem StatClose.comp_equiv_right {τ' : Type*} [Fintype τ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:181:theorem StatClose.comp_pushesUniform {Ω : Type*} [Fintype Ω] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:208:theorem StatClose.abs_uprob_sub_le_prod {ρ : Type*} [Fintype ρ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
TCSlib/Cryptography/Asymptotic/Sampling.lean:233:theorem StatClose.prod {σ σ' τ τ' γ γ' : Type*} [Fintype σ] [Fintype σ'] [Fintype τ] [Fintype τ']
== origin/complexity/arora-barak-ch3-4 aa162208b7f8704fb9dd706c7e3db7b6c5f0ad17
== origin/cryptography/garg-ch1-3 e946ed240f1e8e1a5cfb03b438ce268c622ec801
== PR head 789cf450527ff6b8c779161e555f04093080b88d (the new declarations themselves)
TCSlib/InformationTheory/Entropy.lean:70:noncomputable def shannonEntropy (p : FinDist α) : ℝ :=
TCSlib/InformationTheory/Entropy.lean:74:theorem shannonEntropy_nonneg (p : FinDist α) : 0 ≤ shannonEntropy p :=
TCSlib/InformationTheory/Entropy.lean:82:theorem shannonEntropy_uniform [Nonempty α] :
TCSlib/InformationTheory/Entropy.lean:90:theorem shannonEntropy_uniform_bits (n : ℕ) :
TCSlib/InformationTheory/Entropy.lean:98:noncomputable def maxProb (p : FinDist α) : ℝ :=
TCSlib/InformationTheory/Entropy.lean:119:noncomputable def minEntropy (p : FinDist α) : ℝ :=
TCSlib/InformationTheory/Entropy.lean:128:theorem le_minEntropy_iff (p : FinDist α) (k : ℝ) :
TCSlib/InformationTheory/Entropy.lean:136:def IsSource (k : ℝ) (p : FinDist α) : Prop :=
TCSlib/InformationTheory/Entropy.lean:141:theorem isSource_iff_hasMinEntropy {k : ℝ} {p : FinDist α} :
TCSlib/InformationTheory/Entropy.lean:146:theorem IsSource.mono {k k' : ℝ} {p : FinDist α} (h : IsSource k p) (hk : k' ≤ k) :
TCSlib/InformationTheory/Entropy.lean:155:def IsFlatSource [DecidableEq α] (k : ℕ) (p : FinDist α) : Prop :=
TCSlib/InformationTheory/Entropy.lean:159:theorem IsFlatSource.isSource [DecidableEq α] {k : ℕ} {p : FinDist α} (h : IsFlatSource k p) :
TCSlib/InformationTheory/Entropy.lean:169:noncomputable def flat [DecidableEq α] (s : Finset α) (hs : s.Nonempty) : FinDist α where
TCSlib/InformationTheory/Entropy.lean:183:theorem isFlatSource_flat [DecidableEq α] {k : ℕ} (s : Finset α) (hs : #s = 2 ^ k) :
TCSlib/InformationTheory/Entropy.lean:188:theorem isSource_uniform [Nonempty α] : IsSource (logb 2 (Fintype.card α)) (uniform α) := by
TCSlib/InformationTheory/Extractors.lean:62:noncomputable def FinDist.probTrue (p : FinDist α) (D : α → Bool) : ℝ :=
TCSlib/InformationTheory/Extractors.lean:68:def EpsClose (ε : ℝ) (p q : FinDist α) : Prop :=
TCSlib/InformationTheory/Extractors.lean:72:theorem FinDist.probTrue_sub_probTrue (p q : FinDist α) (D : α → Bool) :
TCSlib/InformationTheory/Extractors.lean:86:theorem abs_probTrue_sub_le_statDist (p q : FinDist α) (D : α → Bool) :
TCSlib/InformationTheory/Extractors.lean:108:theorem statDist_le_of_epsClose {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) :
TCSlib/InformationTheory/Extractors.lean:141:theorem EpsClose.symm {ε : ℝ} {p q : FinDist α} (h : EpsClose ε p q) : EpsClose ε q p := by
TCSlib/InformationTheory/Extractors.lean:146:theorem EpsClose.trans {ε δ : ℝ} {p q r : FinDist α} (h₁ : EpsClose ε p q)
TCSlib/InformationTheory/Extractors.lean:159:def IsExtractor [DecidableEq β] [Nonempty β] (C : Set (FinDist α)) (ε : ℝ) (Ext : α → β) :
TCSlib/InformationTheory/Extractors.lean:164:theorem IsExtractor.mono [DecidableEq β] [Nonempty β] {C C' : Set (FinDist α)} {ε : ℝ}
TCSlib/InformationTheory/Extractors.lean:172:def IsStrongExtractor [DecidableEq S] [DecidableEq α] [DecidableEq β] [Nonempty S] [Nonempty β]
TCSlib/InformationTheory/Extractors.lean:179:def seededSources [Nonempty S] (C : Set (FinDist α)) : Set (FinDist (S × α)) :=
TCSlib/InformationTheory/Extractors.lean:185:theorem IsStrongExtractor.isExtractor_seeded [DecidableEq S] [DecidableEq α] [DecidableEq β]
TCSlib/InformationTheory/Extractors.lean:200:theorem isStrongExtractor_of_isUniversal [DecidableEq S] [DecidableEq α] [DecidableEq β]
== Mathlib at the pinned rev 029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e: files mentioning tvDist / totalVariation / statistical distance
Mathlib/MeasureTheory/VectorMeasure/Decomposition/Lebesgue.lean
Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean
Mathlib/MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean
== conclusion: no copy of a new declaration; one parallel concept, TCSlib.Cryptography.StatClose (ch. 2-4 branch, sampler carrier)
