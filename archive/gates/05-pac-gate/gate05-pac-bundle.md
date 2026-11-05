## ===== briefs/pass-shelat-ch5-8/gates/05-pac/pack.md =====

# Gate 05 (Pass–shelat ch. 5–8, S3d layer 1): external audit pack

**Status: ready to dispatch** (staged 2026-11-05; the user ruled on Q-4 that the PAC layer is
gated before it lands on `main`). The evidence is under `evidence/` and
`../../evidence/pac-2026-11-05/`.

**What is audited:** PR [Shilun-Allan-Li/tcslib#194](https://github.com/Shilun-Allan-Li/tcslib/pull/194)
into `main`, at its head `44d27f39c233849a3a30a117bf15434610e485e9` (base: `main` at
`7d36bbc27dfabd4988ee1702bc342049a1f3e006`). This is one combined gate (statements, definitions,
sketches, proofs and docstring citations), as for P0: the PR has no `sorry`, and its proofs are
short. The deliverable is **`gate05-pac-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The sources are attached separately:**
- [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010 (PDF). The item is on
  PDF p. 191 (book p. 179, §8.1, the learning question before Thm 179.1).
- [KV94] Kearns–Vazirani §1.2 and §4, and [SSBD14] Shalev-Shwartz–Ben-David ch. 3 (the second
  sources for PAC learning), if available to the auditor. Otherwise, standard knowledge of them.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 change: definitions, theorem statements, their
docstrings and proof sketches, against the cited sources. The proofs are machine-checked; do not
review tactic scripts. The failure modes you are hunting are:
1. **Infidelity:** a definition that does not mean what the cited source means.
2. **Trivialization:** a definition or statement satisfiable for degenerate reasons (empty domain,
   empty class, `m = 0`, `ε ≥ 1`, `δ ≥ 1`).
3. **Wrong strength:** a statement weaker or stronger than its docstring claims.
4. **Missing hypotheses:** nonemptiness, finiteness.
5. **Debt:** duplication of existing proved material in the library (`FinDist` and its expectation;
   `BooleanAnalysis`'s expectations are on other carriers).
6. **Attribution:** every source-derived declaration carries a `[Tag, location]`; every deviation
   is declared, with its reason ([`policy.md`](policy.md)).

For **every definition**, restate it in your own words before reading its docstring and compare.
For **every theorem**, say in 1–3 sentences whether the statement is what its docstring claims.
Attempt at least **three adversarial instantiations**. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| New Lean (all declarations audited) | `TCSlib/InformationTheory/Samples.lean` (152 lines), `TCSlib/LearningTheory/PAC/Defs.lean` (228), `TCSlib/LearningTheory/PAC/Prediction.lean` (227) |
| Facades (imports and contents lists only) | `TCSlib/LearningTheory/PAC.lean`, `TCSlib/InformationTheory.lean`, `TCSlib.lean` |
| Context, already on `main` (not under audit) | `TCSlib/InformationTheory/FinDist.lean`, `StatisticalDistance.lean` |
| Design | `design/S3d-pac-learning.md` §"Layer 1" (the intended notions; ruling R-3) |
| Out of scope | tactic proofs; layer 2 (efficient learners and Thm 179.1, prong D) |

## Specific questions

1. **PAC learning.** Is `PACLearnsUnder`/`PACLearns` the definition of [KV94] §1.2 and [SSBD14]
   Def 3.1, apart from the declared deviation? The deviation: `PACLearnable` fixes `m, ε, δ` and
   asks for some learner at those values, where the sources ask for one algorithm for all `ε, δ`
   with a sample bound (and [KV94], efficiency). Is that deviation stated where it matters, and is
   "weaker, so impossibility results are stronger" correct?
2. **Weak learning.** Is `WeakLearnsUnder` [KV94] §4's notion (error `≤ ½ − γ`) at a fixed
   distribution?
3. **The prediction game.** Is `predictSuccess` [PS10]'s learning question on p. 179, read
   uniformly: a random concept, labelled uniform samples, and a fresh uniform point? Is the fresh
   point allowed to coincide with a sample, as in the source?
4. **The bridge and its consequences.** Is `predictSuccess_eq_one_sub_expectedErr` exactly true as
   stated? Does `not_weakLearnsUnder_of_predictAdv_le` say what Thm 179.1(c) needs: no weak learning
   with `γ' > γ + δ` when the prediction advantage is at most `γ`?
5. **`Samples.lean`.** Is `FinDist.iid` the product of `m` copies? Is
   `expect_le_add_of_le_one` stated with the right hypotheses?

## Attestations (maintainer execution claims; evidence under `evidence/`)

At `44d27f39c233849a3a30a117bf15434610e485e9` (`evidence/pac-2026-11-05/` on the records branch):
- **Elaboration:** the upstream `InformationTheory` modules and the five new or changed modules,
  each checked alone into a fresh olean tree: all pass, with 0 errors and 0 warnings.
- **`sorry`:** none.
- **Axioms:** all 38 theorems of the new files print within `propext`, `Classical.choice` and
  `Quot.sound`.
- **Lint:** `scripts/style_lint.py`, rerun by the maintainer at staging on each of
  `Samples.lean`, `PAC/Defs.lean`, `PAC/Prediction.lean` and the `PAC.lean` facade: 0 findings
  (`evidence/lint.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

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

## ===== briefs/pass-shelat-ch5-8/design/S3d-pac-learning.md =====

# S3d design note: PAC learning in `TCSlib/LearningTheory` (decision D-5)

Status: **draft, 2026-11-04.** D-5 (user): Def 179.a and Thm 179.1 are built on a PAC framework in
`TCSlib/LearningTheory`, not on a crypto-style one-off game. No PAC development exists in the
pinned Mathlib or on any branch (`main`, ch. 2–4, ch. 3–4, Garg), so this is new. `main`'s
`LearningTheory` has online learning (`MistakeBounds`, `Hedge`), Johnson–Lindenstrauss and
minimax, by other authors; their files are not touched.

## What [PS10] §8.1 says (PDF p. 191, book p. 179)

- **The learning question** (Def 179.a, informal):
  - a space `S ⊆ {0,1}^n` and concepts `C_i ⊆ S` for `i ∈ I`;
  - for a random `i`, given samples `(x_j, b_j)` with `b_j = [x_j ∈ C_i]`, decide whether a new
    `x` is in `C_i`.
- **Thm 179.1:** there is a p.p.t.-decidable concept class that cannot be learned. The proof
  sketch is: `S = {0,1}^n`, `I = {0,1}^n`, `C_i = {x : f_i(x)|₁ = 1}` for a PRF `{f_i}`; no
  non-uniform PPT predicts membership of a new sample better than `½ + ε`.
- **Left implicit** (recorded as deviations when stated):
  - the sample distribution: uniform on `S` is the reading under which the sketch works;
  - "a new sample": uniform and independent;
  - "better than `½ + ε`": `ε` non-negligible.

## Two layers

### Layer 1: information-theoretic PAC (`TCSlib/LearningTheory/PAC/`, no machines)

Second source: [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning
Theory*, MIT Press 1994, §1.2 (PAC), §4 (weak learning), and [SSBD14] S. Shalev-Shwartz,
S. Ben-David, *Understanding Machine Learning*, ch. 3. The definitions:

- **Basic objects:** a finite domain `X`; a concept `c : X → Bool`; a concept class, indexed as
  `C : I → X → Bool` (which matches [PS10]'s `{C_i}`).
- **Distributions:** `D : FinDist X`, `main`'s `InformationTheory.FinDist`, reused, so samples,
  products and `statDist` are shared with #183.
- **Error:** `err D h c := ∑_{x : h x ≠ c x} D x`.
- **Samples:** a labelled sample of size `m` is `Fin m → X × Bool`, drawn as `D^m`, labelled by
  `c`.
- **Learners:** a (randomized) learner is `L : (Fin m → X × Bool) → ρ → (X → Bool)`, with finite
  coins `ρ`.
- **PAC learning:** `PACLearns C L m ε δ :=` for every `i` and every `D`, with probability
  `≥ 1 − δ` over the sample and the coins, `err D (L S r) (C i) ≤ ε`. Variants:
  - weak learning: `ε = ½ − γ` [KV94, §4];
  - learning under a fixed distribution: `D` fixed to uniform, the case [PS10] needs.
- **The prediction game (Def 179.a):** sample `i`, `m` examples and a fresh `x`, all uniform;
  the learner predicts `C i x`.
- **The bridge (proved here):** the prediction success equals `1 − E_{i,S,r}[err_U(L S r, C i)]`.
  The fresh point is independent of the sample, so no fresh-point collision issue arises. Hence
  a learner with prediction advantage `≤ γ` cannot weakly PAC-learn with any `γ' > γ`, at a
  stated `δ` (Markov on the error).

### Layer 2: efficient learning and Thm 179.1 (prong D, `TCSlib/Cryptography/Randomness/`)

- **Efficient learner.** A learner is a NUPPT, run through the S2 framework:
  - the **example oracle** `EX(C i, U)` is a handler that samples `x ← U` and answers
    `(x, C i x)`;
  - the learner queries it polynomially often, then receives the challenge `x` and outputs a bit;
  - asymptotically, the learner is decoded by `NUPPT.toComp`.

  This is the PAC model's own example oracle, so the efficient prediction game is an S2 game,
  and its concrete probability is layer 1's prediction game (a bridge).
- **Thm 179.1, stated:** for a PRF `F` (Frederick's `PRF`), the class `C_n(k) = {x : F n k x 0 =
  true}`:
  - (a) is p.p.t.-decidable given `k` (from `PRF.easy`);
  - (b) for every NUPPT learner and polynomial sample count, the prediction advantage
    `|Pr[correct] − ½|` is negligible;
  - (c) as a corollary through layer 1's bridge, no efficient learner weakly PAC-learns `C` under
    the uniform distribution with a noticeable `γ`.
- **Proof route (for the S4 sketch):**
  1. replace the PRF by a random function (S2 §5's oracle substitution: the reduction answers the
     example oracle with PRF queries at uniform points, and the challenge with one more query);
  2. against a random function, the fresh `x`'s label is a uniform bit independent of the view
     unless `x` was sampled, with probability `≤ m · 2^{-n}`;
  3. so the advantage is at most `negl + m · 2^{-n}`.

## Placement and landing

- **Layer 1** needs nothing from ch. 2–4. **Ruled (R-3):** it lands on `main` by its own PR, like
  P0 (D-1), with its own gate. That depends on `main`'s `FinDist` only. Since all of S2 stays on the
  ch. 2–4 branch (ruled 2026-11-04), layer 1 does not refer to S2; the bridge from its prediction
  game to S2's example-oracle game is part of layer 2.
- **Layer 2** needs `NUPPT`, `PRF` and S2, so it lives on the ch. 2–4 branch in prong D.
- **Size estimate:** layer 1 about 400–700 lines; layer 2 about 300–600, beyond S2.

## Decision for the user (ruled 2026-11-04: R-3, its own PR to `main`, written after S2 settles)

- **R-3:** where the information-theoretic PAC layer lands: on `main` by its own PR, now or after
  S2 (recommended, as for P0), or with prong D on the ch. 2–4 branch.

## ===== TCSlib/InformationTheory/Samples.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Extractors

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expectations and independent samples

Two operations on finite distributions that sampling arguments need: the expectation of a
real-valued function, and the distribution of `m` independent samples. With them, a probability
`probTrue` is the expectation of an indicator, and an expectation over a product distribution is
an iterated expectation.

## Main definitions

* `FinDist.expect p f`: the expectation `E_{a ← p}[f a] = ∑ a, p a · f a`.
* `FinDist.iid p m`: `m` independent samples of `p`, a distribution on `Fin m → α`.

## Main results

* `FinDist.probTrue_eq_expect`: a probability is the expectation of an indicator.
* `FinDist.expect_prod`: an expectation over a product distribution is an iterated expectation.
* `FinDist.expect_le_expect`, `FinDist.expect_const`, `FinDist.expect_add`,
  `FinDist.expect_const_mul`, `FinDist.expect_one_sub`: linearity and monotonicity.
* `FinDist.probTrue_not`: the complement rule `Pr[¬D] = 1 − Pr[D]`.
* `FinDist.expect_le_add_of_le_one`: a function with values in `[0, 1]` has expectation at most
  `ε + Pr[f > ε]`, for `ε ≥ 0`.

## References

* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, §3.1 (the i.i.d. sample `S ~ D^m`).
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1.
-/

namespace TCSlib.InformationTheory

open Finset

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Expectation -/

/-- The **expectation** `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
noncomputable def expect (p : FinDist α) (f : α → ℝ) : ℝ := ∑ a, p a * f a

/-- The expectation as a weighted sum: `E_{a ← p}[f a] = ∑ a, p a · f a`. -/
theorem expect_eq (p : FinDist α) (f : α → ℝ) : p.expect f = ∑ a, p a * f a := rfl

/-- The expectation of a constant is the constant: `E_p[c] = c`. -/
theorem expect_const (p : FinDist α) (c : ℝ) : p.expect (fun _ => c) = c := by
  rw [expect_eq, ← Finset.sum_mul, p.sum_prob, one_mul]

/-- The expectation is additive: `E_p[f + g] = E_p[f] + E_p[g]`. -/
theorem expect_add (p : FinDist α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp only [expect_eq, mul_add, Finset.sum_add_distrib]

/-- The expectation commutes with scaling: `E_p[c · f] = c · E_p[f]`. -/
theorem expect_const_mul (p : FinDist α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simp only [expect_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The expectation of `1 − f` is `1 − E_p[f]`. -/
theorem expect_one_sub (p : FinDist α) (f : α → ℝ) :
    p.expect (fun a => 1 - f a) = 1 - p.expect f := by
  simp only [expect_eq, mul_sub, mul_one, Finset.sum_sub_distrib, p.sum_prob]

/-- The expectation is monotone: `f ≤ g` pointwise gives `E_p[f] ≤ E_p[g]`. -/
theorem expect_le_expect (p : FinDist α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (p : FinDist α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ p.expect f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (h a)

/-- **A probability is the expectation of an indicator**:
`Pr_{a ← p}[D a] = E_{a ← p}[1_{D a}]`. -/
theorem probTrue_eq_expect (p : FinDist α) (D : α → Bool) :
    p.probTrue D = p.expect (fun a => if D a = true then 1 else 0) := by
  rw [probTrue_eq, expect_eq, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- **The complement rule**: `Pr_p[¬D] = 1 − Pr_p[D]`. -/
theorem probTrue_not (p : FinDist α) (D : α → Bool) :
    p.probTrue (fun a => !D a) = 1 - p.probTrue D := by
  rw [probTrue_eq_expect, probTrue_eq_expect, ← expect_one_sub]
  congr 1
  funext a
  cases D a <;> simp

/-- The probability of the always-accepting test is `1`. -/
theorem probTrue_true (p : FinDist α) : p.probTrue (fun _ => true) = 1 := by
  rw [probTrue_eq_expect]
  simpa using p.expect_const 1

/-- **Iterated expectation over a product**:
`E_{(a, b) ← p × q}[f (a, b)] = E_{a ← p}[E_{b ← q}[f (a, b)]]`. -/
theorem expect_prod (p : FinDist α) (q : FinDist β) (f : α × β → ℝ) :
    (p.prod q).expect f = p.expect (fun a => q.expect (fun b => f (a, b))) := by
  simp only [expect_eq, Fintype.sum_prod_type, prod_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **A `[0, 1]`-valued function has expectation at most `ε + Pr[f > ε]`**, for `ε ≥ 0`: on the
event `f ≤ ε` it contributes at most `ε`, elsewhere at most `1`.

**Proof sketch.** Pointwise `f a ≤ ε + 1_{f a > ε}`, since `f a ≤ 1` and `ε ≥ 0`; take expectations
(`expect_le_expect`, `expect_add`, `expect_const`, `probTrue_eq_expect`). -/
theorem expect_le_add_of_le_one (p : FinDist α) {f : α → ℝ} (hf : ∀ a, f a ≤ 1) {ε : ℝ}
    (hε : 0 ≤ ε) :
    p.expect f ≤ ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
  have key : ∀ a, f a ≤ ε + (if (!decide (f a ≤ ε)) = true then 1 else 0) := by
    intro a
    by_cases h : f a ≤ ε
    · simp [h]
    · simp [h]
      linarith [hf a]
  calc p.expect f
      ≤ p.expect (fun a => ε + (if (!decide (f a ≤ ε)) = true then 1 else 0)) :=
        p.expect_le_expect key
    _ = ε + p.probTrue (fun a => !decide (f a ≤ ε)) := by
        rw [expect_add p (fun _ => ε), expect_const, probTrue_eq_expect]

/-! ### Independent samples -/

/-- **`m` independent samples** of `p`: the distribution on `Fin m → α` with
`Pr[s] = ∏ j, p (s j)` ([SSBD14, §3.1], `S ~ D^m`). -/
def iid (p : FinDist α) (m : ℕ) : FinDist (Fin m → α) where
  prob s := ∏ j, p (s j)
  nonneg s := Finset.prod_nonneg fun j _ => p.nonneg (s j)
  sum_prob := by
    have h := Finset.prod_univ_sum (fun _ : Fin m => (univ : Finset α)) (fun _ a => p a)
    rw [Fintype.piFinset_univ] at h
    rw [← h]
    simp only [p.sum_prob, Finset.prod_const_one]

/-- The probability of a sample is the product of the probabilities of its entries:
`Pr_{p^m}[s] = ∏ j, p (s j)`. -/
theorem iid_apply (p : FinDist α) (m : ℕ) (s : Fin m → α) : p.iid m s = ∏ j, p (s j) := rfl

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/LearningTheory/PAC/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.Samples

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning over a finite domain

Probably approximately correct (PAC) learning in the realizable setting, information-theoretic
(learners are arbitrary functions, with finite random coins): a concept class `C : I → X → Bool`
over a finite domain `X`, the error of a hypothesis under a distribution, labelled samples of `m`
independent examples, and PAC, weak and fixed-distribution learning.

**Conventions.**
- A concept is a function `X → Bool`, and the class is indexed, `C : I → X → Bool`, as in
  [PS10, §8.1] (`{C_i}_{i ∈ I}`).
- A learner with `m` examples and coins `ρ` is a function
  `L : (Fin m → X × Bool) → ρ → (X → Bool)`; its coins are uniform on the finite type `ρ`.
- Distributions are `InformationTheory.FinDist`: real-valued, on a finite type.

**Deviations from [KV94, §1.2] and [SSBD14, Def 3.1].**
- **Fixed parameters.** `PACLearns C m L ε δ` fixes the sample size `m`, the accuracy `ε` and
  the confidence `δ`. The sources ask for one algorithm that works for all `ε, δ`, with a sample
  size polynomial in `1/ε`, `1/δ` (and, in [KV94], in the instance size), and efficiency is part
  of [KV94]'s definition. Here `PACLearnable C m ε δ` asks only for some learner at the given
  parameters. That notion is weaker, so impossibility results stated with it are stronger.
  Efficiency is layer 2's (the cryptographic statement of [PS10, Thm 179.1]).
- **Finite domains.** `X` is a finite type, so the "instance size" of [KV94] is not modelled.
  With `X` empty there is no distribution on `X`, so every PAC statement holds vacuously.

## Main definitions

* `PAC.err D h c`: the error `Pr_{x ← D}[h x ≠ c x]` of `h` against the target `c`.
* `PAC.label c s`: the sample `s` labelled by `c`.
* `PAC.accuracyProb D c m L ε`: the probability, over `m` examples from `D` and the coins, that
  the learner's hypothesis has error at most `ε`.
* `PAC.PACLearnsUnder D C m L ε δ`, `PAC.PACLearns C m L ε δ`: PAC learning under a fixed
  distribution and under every distribution.
* `PAC.WeakLearnsUnder`, `PAC.WeakLearns`: weak learning, accuracy `½ − γ` [KV94, §4].
* `PAC.PACLearnable C m ε δ`: some learner PAC-learns `C` at these parameters.

## Main results

* `PAC.err_nonneg`, `PAC.err_le_one`, `PAC.err_self`, `PAC.err_not`: basic properties; `err_not`
  says the complementary hypothesis has the complementary error.
* `PAC.pacLearns_const`: a class with one concept is PAC-learnable from no examples
  (non-vacuity).
* `PAC.not_pacLearnsUnder_of_neg`: no learner reaches a negative accuracy with confidence
  `δ < 1` (the definition does not hold trivially).

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2 (PAC learning) and §4 (weak learning).
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3 (Definition 3.1).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X]

/-! ### Error and samples -/

/-- The **error** of the hypothesis `h` against the target concept `c` under `D`:
`err_D(h, c) = Pr_{x ← D}[h x ≠ c x]` [KV94, §1.2]. -/
noncomputable def err (D : FinDist X) (h c : X → Bool) : ℝ := D.probTrue fun x => h x != c x

/-- The error is the probability of disagreement: `err_D(h, c) = Pr_{x ← D}[h x ≠ c x]`. -/
theorem err_eq (D : FinDist X) (h c : X → Bool) :
    err D h c = D.probTrue (fun x => h x != c x) := rfl

/-- The error is nonnegative. -/
theorem err_nonneg (D : FinDist X) (h c : X → Bool) : 0 ≤ err D h c := by
  rw [err_eq, FinDist.probTrue_eq]
  exact Finset.sum_nonneg fun x _ => D.nonneg x

/-- The error is at most `1`. -/
theorem err_le_one (D : FinDist X) (h c : X → Bool) : err D h c ≤ 1 := by
  rw [err_eq, FinDist.probTrue_eq, ← D.sum_prob]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun x _ _ => D.nonneg x

/-- The target has error `0` against itself. -/
theorem err_self (D : FinDist X) (c : X → Bool) : err D c c = 0 := by
  rw [err_eq, FinDist.probTrue_eq]
  simp

/-- The complementary hypothesis has the complementary error:
`err_D(¬h, c) = 1 − err_D(h, c)`. -/
theorem err_not (D : FinDist X) (h c : X → Bool) :
    err D (fun x => !h x) c = 1 - err D h c := by
  rw [err_eq, err_eq, ← FinDist.probTrue_not]
  congr 1
  funext x
  cases h x <;> cases c x <;> rfl

/-- The **labelled sample** `((x_j, c(x_j)))_j` of the examples `s` under the target `c`. -/
def label (c : X → Bool) {m : ℕ} (s : Fin m → X) : Fin m → X × Bool := fun j => (s j, c (s j))

omit [Fintype X] in
/-- The `j`-th labelled example is `(s j, c (s j))`. -/
theorem label_apply (c : X → Bool) {m : ℕ} (s : Fin m → X) (j : Fin m) :
    label c s j = (s j, c (s j)) := rfl

/-! ### PAC learning -/

variable [Fintype ρ] [Nonempty ρ]

/-- The **accuracy probability** of the learner `L` with `m` examples: over `m` independent
examples from `D`, labelled by the target `c`, and uniform coins, the probability that the
hypothesis has error at most `ε`. -/
noncomputable def accuracyProb (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) : ℝ :=
  ((D.iid m).prod (FinDist.uniform ρ)).probTrue
    fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)

/-- The accuracy probability as a probability over the examples and the coins. -/
theorem accuracyProb_eq (D : FinDist X) (c : X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε : ℝ) :
    accuracyProb D c m L ε = ((D.iid m).prod (FinDist.uniform ρ)).probTrue
      (fun sr => decide (err D (L (label c sr.1) sr.2) c ≤ ε)) := rfl

/-- **PAC learning under the distribution `D`** (fixed-distribution learning): for every concept
of the class, with probability at least `1 − δ` the hypothesis has error at most `ε`. -/
def PACLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) : Prop :=
  ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε

/-- `PACLearnsUnder` unfolded. -/
theorem pacLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    PACLearnsUnder D C m L ε δ ↔ ∀ i, 1 - δ ≤ accuracyProb D (C i) m L ε := Iff.rfl

/-- **PAC learning** [KV94, §1.2], [SSBD14, Def 3.1], at fixed `m`, `ε`, `δ`: for every
distribution `D` on `X` and every concept `C i`, with probability at least `1 − δ` over `m`
examples from `D` labelled by `C i` and the learner's coins, the hypothesis has error at most `ε`
under `D`. -/
def PACLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (ε δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, PACLearnsUnder D C m L ε δ

/-- `PACLearns` unfolded. -/
theorem pacLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (ε δ : ℝ) : PACLearns C m L ε δ ↔ ∀ D, PACLearnsUnder D C m L ε δ := Iff.rfl

/-- **Weak learning under `D`** [KV94, §4]: PAC learning under `D` with accuracy `½ − γ`, a
hypothesis better than a fair coin by `γ`. -/
def WeakLearnsUnder (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) : Prop :=
  PACLearnsUnder D C m L (1 / 2 - γ) δ

/-- `WeakLearnsUnder` unfolded. -/
theorem weakLearnsUnder_iff (D : FinDist X) (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    WeakLearnsUnder D C m L γ δ ↔ PACLearnsUnder D C m L (1 / 2 - γ) δ := Iff.rfl

/-- **Weak learning** [KV94, §4]: under every distribution, accuracy `½ − γ`. -/
def WeakLearns (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) (γ δ : ℝ) :
    Prop :=
  ∀ D : FinDist X, WeakLearnsUnder D C m L γ δ

/-- `WeakLearns` unfolded. -/
theorem weakLearns_iff (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool)
    (γ δ : ℝ) : WeakLearns C m L γ δ ↔ ∀ D, WeakLearnsUnder D C m L γ δ := Iff.rfl

omit [Fintype ρ] [Nonempty ρ] in
/-- **PAC-learnability at fixed parameters**: some learner, with finite nonempty coins, learns `C`
from `m` examples with accuracy `ε` and confidence `δ`. -/
def PACLearnable (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) : Prop :=
  ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ') (L : (Fin m → X × Bool) → ρ' → X → Bool),
    PACLearns C m L ε δ

omit [Fintype ρ] [Nonempty ρ] in
/-- `PACLearnable` unfolded. -/
theorem pacLearnable_iff (C : I → X → Bool) (m : ℕ) (ε δ : ℝ) :
    PACLearnable C m ε δ ↔
      ∃ (ρ' : Type) (_ : Fintype ρ') (_ : Nonempty ρ')
        (L : (Fin m → X × Bool) → ρ' → X → Bool), PACLearns C m L ε δ := Iff.rfl

/-! ### Non-vacuity -/

/-- **A class with one concept is PAC-learnable from no examples** (non-vacuity of
`PACLearns`): if every `C i` is `c₀`, the learner that outputs `c₀` has error `0`, so it learns
at every accuracy `ε ≥ 0` and confidence `δ ≥ 0`. -/
theorem pacLearns_const {C : I → X → Bool} {c₀ : X → Bool} (hC : ∀ i, C i = c₀) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    PACLearns C 0 (fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) ε δ := by
  intro D i
  rw [accuracyProb_eq, hC i]
  have h : (fun sr : (Fin 0 → X) × ρ =>
      decide (err D ((fun (_ : Fin 0 → X × Bool) (_ : ρ) => c₀) (label c₀ sr.1) sr.2) c₀ ≤ ε)) =
      fun _ => true := by
    funext sr
    simp only [err_self, hε, decide_true]
  rw [h, FinDist.probTrue_true]
  linarith

/-- **No learner reaches a negative accuracy with confidence `δ < 1`**: the error is
nonnegative, so the accuracy event is empty and its probability `0 < 1 − δ`. `PACLearns` is
therefore not trivially satisfied. -/
theorem not_pacLearnsUnder_of_neg (D : FinDist X) {C : I → X → Bool} [Nonempty I] {m : ℕ}
    (L : (Fin m → X × Bool) → ρ → X → Bool) {ε δ : ℝ} (hε : ε < 0) (hδ : δ < 1) :
    ¬ PACLearnsUnder D C m L ε δ := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := h i
  rw [accuracyProb_eq] at h1
  have h0 : (fun sr : (Fin m → X) × ρ => decide (err D (L (label (C i) sr.1) sr.2) (C i) ≤ ε)) =
      fun _ => false := by
    funext sr
    have := err_nonneg D (L (label (C i) sr.1) sr.2) (C i)
    simp only [decide_eq_false_iff_not, not_le]
    linarith
  rw [h0, FinDist.probTrue_eq] at h1
  simp at h1
  linarith

end TCSlib.LearningTheory.PAC

## ===== TCSlib/LearningTheory/PAC/Prediction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The prediction game, and its bridge to PAC learning

[PS10, §8.1] (Def 179.a of the inventory) asks whether a learner, given labelled examples of a
random concept `C_i`, can predict the label of a fresh point. Under the uniform distribution
(the reading under which the source's Theorem 179.1 works) the game is:
`i ← I`, `m` examples `s ← X^m`, coins `r ← ρ`, a fresh point `x ← X`, all uniform and
independent; the learner wins when `L(s labelled by C_i, r)(x) = C_i(x)`.

**The bridge.** The fresh point is independent of the sample, so for fixed `(i, s, r)` the
probability of a correct prediction is `1 − err_U(h, C_i)` for the hypothesis `h = L(s, r)`.
So the prediction success is `1 − E_{i,s,r}[err_U(L(s, r), C_i)]`
(`predictSuccess_eq_one_sub_expectedErr`), with no collision issue between the fresh point and
the sample. A learner that PAC-learns under the uniform distribution with accuracy `ε` and
confidence `δ` has expected error at most `ε + δ`, hence prediction success at least `1 − ε − δ`.
So a learner whose prediction advantage is at most `γ` cannot weakly learn under the uniform
distribution with `γ' > γ + δ` at confidence `δ` (`not_weakLearnsUnder_of_predictAdv_le`). This is
how layer 2 turns [PS10, Thm 179.1] into "the class is not weakly learnable".

**Source notes.** [PS10] leaves the sample distribution and "a new sample" implicit; uniform
and independent is the reading (design note S3d). "Better than `½ + ε`" is the advantage
`|Pr[correct] − ½|`.

## Main definitions

* `PAC.trialDist X I ρ m`: the joint law of the concept index, the examples and the coins.
* `PAC.predictSuccess C m L`, `PAC.predictAdv C m L`: the success probability of the prediction
  game, and its advantage over `½`.
* `PAC.expectedErr C m L`: the expected uniform error of the learner's hypothesis.

## Main results

* `PAC.predictSuccess_eq_one_sub_expectedErr`: **the bridge**, success `= 1 − E[err]`.
* `PAC.expectedErr_le_of_pacLearnsUnder`, `PAC.one_sub_sub_le_predictSuccess`: PAC learning
  under the uniform distribution gives expected error at most `ε + δ` and success at least
  `1 − ε − δ`.
* `PAC.sub_le_predictAdv_of_weakLearnsUnder`, `PAC.not_weakLearnsUnder_of_predictAdv_le`: weak
  learning with `γ'` gives advantage at least `γ' − δ`; so advantage at most `γ` rules out weak
  learning with `γ' > γ + δ`.
* `PAC.predictSuccess_coin`: the learner that outputs its coin succeeds with probability exactly
  `½` (non-vacuity).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1 (book p. 179).
* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994, §1.2 and §4.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014, ch. 3.
-/

namespace TCSlib.LearningTheory.PAC

open TCSlib.InformationTheory Finset

variable {X I ρ : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I] [Fintype ρ]
  [Nonempty ρ]

/-! ### The game -/

variable (X I ρ) in
/-- The joint law of a trial of the prediction game: a uniform concept index, `m` uniform
independent examples and uniform coins. -/
noncomputable def trialDist (m : ℕ) : FinDist (I × ((Fin m → X) × ρ)) :=
  (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))

/-- The trial law is the product of the uniform index, the `m` uniform examples and the uniform
coins. -/
theorem trialDist_eq (m : ℕ) :
    trialDist X I ρ m =
      (FinDist.uniform I).prod (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ)) := rfl

/-- **The prediction game** [PS10, §8.1]: the probability that the learner `L`, given `m`
uniform examples labelled by a uniform concept `C_i` and uniform coins, predicts the label of a
fresh uniform point. -/
noncomputable def predictSuccess (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
    fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2

/-- The success probability as a probability over a trial and a fresh point. -/
theorem predictSuccess_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = ((trialDist X I ρ m).prod (FinDist.uniform X)).probTrue
      (fun w => L (label (C w.1.1) w.1.2.1) w.1.2.2 w.2 == C w.1.1 w.2) := rfl

/-- The **prediction advantage** `|Pr[correct] − ½|`. -/
noncomputable def predictAdv (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  |predictSuccess C m L - 1 / 2|

/-- The prediction advantage is `|predictSuccess − ½|`. -/
theorem predictAdv_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictAdv C m L = |predictSuccess C m L - 1 / 2| := rfl

/-- The **expected error** `E_{i,s,r}[err_U(L(s labelled by C_i, r), C_i)]` of the learner's
hypothesis under the uniform distribution. -/
noncomputable def expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) : ℝ :=
  (trialDist X I ρ m).expect
    fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)

/-- The expected error as an expectation over a trial. -/
theorem expectedErr_eq (C : I → X → Bool) (m : ℕ) (L : (Fin m → X × Bool) → ρ → X → Bool) :
    expectedErr C m L = (trialDist X I ρ m).expect
      (fun t => err (FinDist.uniform X) (L (label (C t.1) t.2.1) t.2.2) (C t.1)) := rfl

/-! ### The bridge -/

/-- **The bridge: prediction success is one minus the expected error.**

**Proof sketch.** Split the fresh point off the trial (`expect_prod`). For a fixed trial with
hypothesis `h`, the correct-prediction indicator is one minus the disagreement indicator, so its
expectation over the uniform fresh point is `1 − err_U(h, C_i)` (`expect_one_sub`); then take the
expectation over the trial. -/
theorem predictSuccess_eq_one_sub_expectedErr (C : I → X → Bool) (m : ℕ)
    (L : (Fin m → X × Bool) → ρ → X → Bool) :
    predictSuccess C m L = 1 - expectedErr C m L := by
  rw [predictSuccess_eq, FinDist.probTrue_eq_expect, FinDist.expect_prod, expectedErr_eq,
    ← FinDist.expect_one_sub]
  congr 1
  funext t
  dsimp only
  rw [err_eq, FinDist.probTrue_eq_expect, ← FinDist.expect_one_sub]
  congr 1
  funext x
  cases L (label (C t.1) t.2.1) t.2.2 x <;> cases C t.1 x <;> simp

/-- **PAC learning under the uniform distribution bounds the expected error** by `ε + δ`
(for `ε ≥ 0`).

**Proof sketch.** For each concept `C_i`, the error is at most `1`, and at most `ε` except with
probability at most `δ` (the hypothesis `PACLearnsUnder`), so its expectation over the examples
and coins is at most `ε + δ` (`expect_le_add_of_le_one`, `probTrue_not`); average over `i`. -/
theorem expectedErr_le_of_pacLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    expectedErr C m L ≤ ε + δ := by
  rw [expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  calc _ ≤ (FinDist.uniform I).expect (fun _ => ε + δ) := FinDist.expect_le_expect _ fun i => ?_
    _ = ε + δ := FinDist.expect_const _ _
  dsimp only
  have h1 := FinDist.expect_le_add_of_le_one (((FinDist.uniform X).iid m).prod
    (FinDist.uniform ρ)) (f := fun b => err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i))
    (fun b => err_le_one _ _ _) hε
  have h2 := h i
  rw [accuracyProb_eq] at h2
  have h3 := FinDist.probTrue_not (((FinDist.uniform X).iid m).prod (FinDist.uniform ρ))
    (fun b => decide (err (FinDist.uniform X) (L (label (C i) b.1) b.2) (C i) ≤ ε))
  dsimp only at h1 h2 h3
  linarith

/-- **PAC learning under the uniform distribution gives prediction success at least
`1 − ε − δ`** (for `ε ≥ 0`): the bridge and `expectedErr_le_of_pacLearnsUnder`. -/
theorem one_sub_sub_le_predictSuccess {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {ε δ : ℝ}
    (h : PACLearnsUnder (FinDist.uniform X) C m L ε δ) (hε : 0 ≤ ε) :
    1 - ε - δ ≤ predictSuccess C m L := by
  rw [predictSuccess_eq_one_sub_expectedErr]
  linarith [expectedErr_le_of_pacLearnsUnder h hε]

/-- **Weak learning under the uniform distribution gives prediction advantage at least
`γ − δ`** (for `γ ≤ ½`): success is at least `1 − (½ − γ) − δ = ½ + γ − δ`. -/
theorem sub_le_predictAdv_of_weakLearnsUnder {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ δ : ℝ}
    (h : WeakLearnsUnder (FinDist.uniform X) C m L γ δ) (hγ : γ ≤ 1 / 2) :
    γ - δ ≤ predictAdv C m L := by
  have hs := one_sub_sub_le_predictSuccess ((weakLearnsUnder_iff _ _ _ _ _ _).1 h)
    (by linarith)
  rw [predictAdv_eq]
  exact le_trans (by linarith) (le_abs_self _)

/-- **Small prediction advantage rules out weak learning**: if the learner's prediction
advantage is at most `γ`, it does not weakly learn the class under the uniform distribution with
any `γ' ≤ ½` such that `γ + δ < γ'`, at confidence `δ`. -/
theorem not_weakLearnsUnder_of_predictAdv_le {C : I → X → Bool} {m : ℕ}
    {L : (Fin m → X × Bool) → ρ → X → Bool} {γ γ' δ : ℝ} (hadv : predictAdv C m L ≤ γ)
    (hlt : γ + δ < γ') (hγ' : γ' ≤ 1 / 2) :
    ¬ WeakLearnsUnder (FinDist.uniform X) C m L γ' δ := fun h => by
  have := sub_le_predictAdv_of_weakLearnsUnder h hγ'
  linarith

/-! ### Non-vacuity -/

omit [Nonempty X] [Fintype I] [Nonempty I] in
/-- Against any target, the two constant hypotheses have errors summing to one, so a fair coin
between them has expected error `½`. -/
theorem expect_err_coin (D : FinDist X) (c : X → Bool) :
    (FinDist.uniform Bool).expect (fun r => err D (fun _ => r) c) = 1 / 2 := by
  have hnot : err D (fun _ => true) c = 1 - err D (fun _ => false) c := by
    simpa using err_not D (fun _ => false) c
  rw [FinDist.expect_eq, Fintype.sum_bool]
  simp only [FinDist.uniform_apply, Fintype.card_bool]
  rw [hnot]
  push_cast
  ring

/-- **The coin-flipping learner predicts with probability exactly `½`** (non-vacuity of the
game): the learner that ignores its examples and outputs its coin.

**Proof sketch.** By the bridge, the success is one minus the expected error; for every concept
and every sample, the error averaged over the coin is `½` (`expect_err_coin`). -/
theorem predictSuccess_coin (C : I → X → Bool) (m : ℕ) :
    predictSuccess C m (fun (_ : Fin m → X × Bool) (r : Bool) (_ : X) => r) = 1 / 2 := by
  rw [predictSuccess_eq_one_sub_expectedErr, expectedErr_eq, trialDist_eq, FinDist.expect_prod]
  dsimp only
  have hin : ∀ i, (((FinDist.uniform X).iid m).prod (FinDist.uniform Bool)).expect
      (fun b => err (FinDist.uniform X) (fun _ => b.2) (C i)) = 1 / 2 := by
    intro i
    rw [FinDist.expect_prod]
    dsimp only
    simp only [expect_err_coin]
    exact FinDist.expect_const _ _
  simp only [hin, FinDist.expect_const]
  norm_num

end TCSlib.LearningTheory.PAC

## ===== TCSlib/LearningTheory/PAC.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC.Defs
import TCSlib.LearningTheory.PAC.Prediction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PAC learning

Probably approximately correct learning over a finite domain, information-theoretic (learners
are arbitrary functions with finite coins), and the prediction game of [PS10, §8.1] with its
bridge to PAC learning.

## Contents

* `TCSlib.LearningTheory.PAC.Defs`: error, labelled samples, PAC, weak and fixed-distribution
  learning, PAC-learnability at fixed parameters.
* `TCSlib.LearningTheory.PAC.Prediction`: the prediction game; success `= 1 − E[err]`, so
  a small prediction advantage rules out weak learning under the uniform distribution.

## References

* [KV94] M. Kearns, U. Vazirani, *An Introduction to Computational Learning Theory*, MIT Press,
  1994.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

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
import TCSlib.InformationTheory.Samples

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
* `TCSlib.InformationTheory.Samples`: expectations, the complement rule, iterated expectations
  over products, and `m` independent samples.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012.
* [HILL99] J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A pseudorandom generator from any
  one-way function*, SICOMP 28(4), 1999.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [SSBD14] S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*, Cambridge University Press, 2014.
-/

## ===== TCSlib.lean =====

import TCSlib.ErrorCorrectingCodes.Basic
import TCSlib.ErrorCorrectingCodes.SingletonBound
import TCSlib.ErrorCorrectingCodes.HammingBound
import TCSlib.ErrorCorrectingCodes.Entropy
import TCSlib.ErrorCorrectingCodes.LinearCodes
import TCSlib.ErrorCorrectingCodes.GilbertVarshamov
import TCSlib.ErrorCorrectingCodes.ListDecoding
import TCSlib.ErrorCorrectingCodes.QuantumSingleton
import TCSlib.ErrorCorrectingCodes.QuantumHamming
import TCSlib.ErrorCorrectingCodes.JohnsonBound
import TCSlib.ErrorCorrectingCodes.MRRW

import TCSlib.BooleanAnalysis.BLR
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.ArrowTheorem
import TCSlib.BooleanAnalysis.Hypercontractivity
import TCSlib.BooleanAnalysis.GaussianSpace
import TCSlib.BooleanAnalysis.Switching
import TCSlib.BooleanAnalysis.ThresholdFunctions
import TCSlib.BooleanAnalysis.polylogIndep

import TCSlib.CommunicationComplexity.DeterministicCC
import TCSlib.CommunicationComplexity.NewmanTheorem

import TCSlib.Programs

import TCSlib.Complexity.CircuitComplexity
import TCSlib.Complexity.Expanders
import TCSlib.Complexity.NPReductions
import TCSlib.Complexity.Randomized
import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.Uncomputability
import TCSlib.Complexity.ClassP
import TCSlib.Complexity.Formulas
import TCSlib.Complexity.FormulaKit
import TCSlib.Complexity.CookLevin
import TCSlib.Complexity.RAMSimulation
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.ClassOracle
import TCSlib.Complexity.Diagonalization
import TCSlib.Complexity.ClassPSPACE
import TCSlib.Complexity.PolyHierarchy
import TCSlib.Complexity.TimeHierarchy
import TCSlib.Complexity.SpaceComplexity

import TCSlib.ComputationalModels

import TCSlib.Cryptography.SchnorrProtocol
import TCSlib.Cryptography.SecretSharing
import TCSlib.Cryptography.MPC

import TCSlib.InformationTheory

import TCSlib.GraphTheory.Kruskal

import TCSlib.KikuchiLDC.Main

import TCSlib.LearningTheory.MistakeBounds
import TCSlib.LearningTheory.Hedge
import TCSlib.LearningTheory.JohnsonLindenstrauss
import TCSlib.LearningTheory.Minimax
import TCSlib.LearningTheory.PAC

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
