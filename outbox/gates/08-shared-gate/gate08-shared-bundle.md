## ===== briefs/pass-shelat-ch5-8/gates/08-shared/pack.md =====

# Gate 08 (Pass–shelat): shared lemmas for the landed fills (S1) and the rejection-loop host contract

**What is audited:** PR [Shilun-Allan-Li/tcslib#227](https://github.com/Shilun-Allan-Li/tcslib/pull/227)
at its head `c6affb3a92535d3f1de2e0a52c205a84c0cff551`, on base `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`
(`cryptography/pass-shelat-ch2-4`; later base commits are records only). 14 commits, 15 Lean files,
`+572 −906` (`evidence/pr.diff.txt`).

**Why it exists.**
- The eight fill units landed in #224–#226 (Candidates DL, factoring, RSA, Rabin; 3-colouring) carry
  private copies of each other's helpers, of private library lemmas and of Mathlib lemmas
  (`duplication-ledger.md` DL-23…DL-29).
- The design (`fills/shared-lemmas/design.md`) gives one public home per group.
- User rulings of 2026-11-07:
  - **Q1 (A):** this one gate round audits S1's new statements and S2's host **contract** before
    its proof.
  - **Q3 (A):** the host lives in `Candidates/Concrete.lean`.
  - **Q4 (B):** the host's proof is an external fill after this gate.
  - **Q5 (A):** the four tier-2 lemmas are included.
  - **Q6 (A):** `ColZK.pushesUniform_restrict` is deleted.
  - **Q8 (A):** numeral constants and calculi stay private.
- Policy §1, rule 10, applies: no proof reads another file's definition. Notation by user ruling is
  never sealed: `PolyExpr.eval` and `glNeed`.

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`; book page = PDF page − 12). You need it
for the host's citations (Theorems 52.3, 53.2, 61.7, 63.10).

- **The deliverable:** **`gate08-shared-findings.md`**, committed as `inbox/gate08-shared-findings.md`
  on the exchange branch `exchange/pass-shelat-ch5-8` and pushed (protocol: that branch's `README.md`;
  write only that file, `git pull --rebase` first, never force-push, no PR).

## Brief for the auditor

1. **The 22 new public lemmas and the 2 visibility changes** (`evidence/statement-diff.txt`; the PR
   description's table). For each, check that:
   - it is **true and exactly stated**: no missing hypothesis, edge cases (`n = 0`, empty lists,
     modulus 0) handled as stated;
   - it is **proved without reading another file's definition**, through published equations only;
   - it sits in the design's home, which every consumer imports;
   - it is public, not `@[simp]`, and has a docstring with the formula;
   - it **duplicates nothing** already public in TCSlib or Mathlib. Grep: a public copy found here is a
     finding.

   The two visibility changes (`foldl_bits_eq`, `abs_uexp_sub_le`) must keep their statements.
2. **The host contract** `Candidates.polyTimeComputable_rejectBlocksL` (`Concrete.lean`, sorried).
   - Is it **true**?
   - Is it **sufficient** for its four consumers? They are dl-a's `polyTimeComputable_expSampleRaw`,
     dl-c's three generator/encryption machines, rsa's `polyTimeComputable_unitSampleStr`/`rsaGenRaw`
     and rabin's generators; the design's §4 maps them.
   - Can each consumer use it reading only published equations (`sampleBelowL_eq_rejectBlocksL`,
     `rejectBlocksL_eq`, `sampleUnitL_eq`, `unitSampleStr_eq`, rabin's `samplePrimePL`)?
   - Is the existential form right, given that its machine is hidden so that no consumer can read
     it?
   - Is the length bound adequate?
   - Are the citations and the deviation note (truncation to `T` trials) accurate?
   - Is the **Proof sketch** followable by a fill worker?
3. **Re-points and deletions** (`evidence/pr.diff.txt`).
   - Every re-pointed fill proof keeps its statement; no statement changes at all (`CHANGED: none`).
   - The deletion of `ColZK.pushesUniform_restrict` and of the `PublicKeyLemmas` copy leaves no
     dangling use.
   - rsa's E4 is applied as reviewed.
   - Docstrings that named a deleted helper are updated, and no other docstring changes.
4. **Rule-10 evidence** (`evidence/seal/`): the touched list, the collection from elaborated terms
   (89 names), the whole-file seals, and the base control.
   - Six untouched base declarations fail sealed, identically at the base: `primesPairEquiv_apply_val`,
     `ExpGroupGen.FullLength.exists_fullLengthExcept`, `rabinCollection_index`,
     `rabinBlumTrapdoor_index`, `uexp_mono`, `exists_plantFactorer`. Is that classification right?
   - Check 13 controls and the unfold scan.
5. **Checks** (`evidence/`): `replay.log` (97 + Checks), the `sorry` census (+1, the host), axioms,
   lint and line counts.
6. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence/`, `REPORT.md`)

- **Replay:** 98/98, 0 errors.
- **`sorry`:** 507 → 508 in `TCSlib/`, the host only.
- **Statements:** 25 ADDED (18 tier 1, 4 tier 2, 1 host, 2 visibility), 2 REMOVED, 0 CHANGED.
- **Axioms:** standard on all touched and new declarations except the host's `sorryAx`.
- **Seal:** touched declarations clean; the six failures are untouched and identical at the base;
  13/13 controls.
- **Lint:** only the approved size lines; all six fill-owned files shrink.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity: **blocker** (a false or unusable statement, or a change outside scope), **major** (a wrong
or insufficient interface, a duplicate of an existing public lemma, a rule-10 read in a touched
declaration, evidence that does not show what it claims), **minor** (docstring, naming, presentation),
**note**. The gate closes at **0 blockers and 0 majors**.

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

## ===== briefs/pass-shelat-ch5-8/fills/shared-lemmas/design.md =====

# Shared-lemma PR: design (DRAFT, not implemented)

**Status: design draft, 2026-11-07** (decision log: "shared-lemma PR design started"). No Lean has been changed, committed or pushed. Nothing here is
issued. Rulings Q1–Q8 (§6) are pending.

- **Base read:** `origin/cryptography/pass-shelat-ch2-4` at
  `7018d13e243df4d8b54b99444c34c934199755f5` ("Records: post-landing work started"). Its Lean
  sources are those of the merged base after #224, #225 and #226.
- **Method.** Every declaration name and line number below was read from that commit
  (`git archive` into the scratch area, then `grep`). The import closures come from a script over
  the `import` lines of the same snapshot. Mathlib names were checked by grep in
  `.lake/packages/mathlib/Mathlib`, core names in the Lean v4.25.0 toolchain sources. Similarity
  figures ("1.00", "0.97") come from a normalized text comparison of the declaration bodies, with
  the unit prefixes (`dla_`, `dlc_`, `rsa_`, `rabin_`, `dlb_`, `fac_`) and the loop infixes
  (`ss`, `us`, `rb`) removed. No Lean was run.
- **Sources:** `duplication-ledger.md` (DL-23 to DL-29); the eight delivery reviews and their D1/D2
  sections; rsa's deferred edit E4 (`fills/factoring-candidates/review-rsa-evidence/edits/conditional-harvest-edits.diff`,
  with `harvest-stubs.lean` and `mk_harvest.py`); `policy.md`; `MAINTAINER-HANDOFF.md`;
  `fills/cleanup-part2/brief-draft.md`; `machine-library-design.md` §14.

## 0. Summary

Twenty-six groups of duplicated material were found across the eight landed units, the library and
Mathlib (§1). The proposal has three parts.

1. **PR S1, the shared-lemma PR** (the hand-off's "H1"). It holds proved lemmas only: no `sorry`,
   no new definitions and no target statement changes.
   - It publishes 18 new lemmas in tier 1 and up to 4 more in tier 2 (5 under Q5 (C)), in 8
     existing files.
   - Two private lemmas become public: `foldl_bits_eq` and `abs_uexp_sub_le` in `Sampling.lean`.
   - It deletes 2 public duplicates: `ColZK.pushesUniform_restrict` and `PublicKeyLemmas`'
     `abs_uexp_sub_le`.
   - It applies rsa's E4, which is clean at the base as text. It re-points the copies in the other
     seven landed fill files.
   - Net about −260 lines (−300 with tier 2). The replay covers 98 modules.
2. **PR S2, the host PR** (the hand-off's "H2"). It adds one statement-gated host,
   `polyTimeComputable_rejectBlocksL`, in `Candidates/Concrete.lean`, with registry row H15. It
   retires the four copied rejection loops of dl-a, dl-c, rsa and rabin. Net about −425 lines. The
   replay covers 8 modules.
3. **Clean-up part 2 additions.** These are re-points of copies that live in base files. Each one
   either touches a declaration that clean-up part 2 already rewrites, or touches a file that #195
   edits (§5.4).

Overall, S1 and S2 remove about 1,200 lines of copied material and add about 500 (net about −690).

## 1. Inventory

Format: *copy* = `file:line name` at the base. Paths are relative to `TCSlib/Cryptography/` unless
they start with `TCSlib/`. "Private" is marked (p). The **relation** column uses:
- **verbatim**: identical after renaming;
- **near-verbatim**: the same proof text with small edits;
- **same statement**: equal up to form, with a different proof.

### G1. The rejection-block trial loop (DL-27, DL-28, DL-29; four copies)

| Unit | Copies (all private) | Relation |
|---|---|---|
| dl-a | `Candidates/DiscreteLog.lean`: `dla_ssStart` 738, `dla_ssStep` 744, `dla_ssBlock` 749, `dla_ssAcc` 753, `dla_ssOut` 758, `dla_ssStep_poly` 761, `dla_ssBlock_poly` 773, `dla_ssAcc_poly` 783, `dla_ssOut_poly` 800, `dla_ssStep_iterate` 805, `dla_length_ssStep_le` 816, `dla_length_ssStep_ssStep_le` 823, `dla_length_ssStep_iterate_le` 830, `dla_ssFind_eq` 853, `dla_ssStart_poly` 907 (162 lines) | the first copy |
| dl-c | `Candidates/ElGamal.lean`: `dlc_ssStep` 818, `dlc_ssBlock` 823, `dlc_ssAcc` 827, `dlc_ssOut` 832, `dlc_ssLoop` 835, `dlc_ssStep_poly` 840, `dlc_ssBlock_poly` 850, `dlc_ssAcc_poly` 858, `dlc_ssOut_poly` 866, `dlc_ssStep_iterate` 870, the three `dlc_length_ssStep_*` 880/886/892, `dlc_ssLoop_poly` 906, `dlc_ssLoop_eq` 966, `dlc_numPoly_sample` 1009 (155 lines without G2) | step, block, out, acc, `_iterate` and the three length bounds are **verbatim** dl-a (1.00). `_poly` 0.90–0.92 (`congrArg … .mp` in place of `convert`). `dlc_ssLoop_eq` is `dla_ssFind_eq` generalized (any `u`, `ks`, `ms`, `c`), read through `sampleBelowL_eq_rejectBlocksL` |
| rsa | `Candidates/RSA.lean`: `rsa_usStart` 728, `rsa_usStep` 735, `rsa_usBlock` 741, `rsa_usOut` 757, `rsa_usStep_poly` 766, `rsa_usBlock_poly` 779, `rsa_usOut_poly` 856, `rsa_usStep_iterate` 861, the three `rsa_length_usStep_*` 872/880/887, `rsa_usLoop` 903, `rsa_usLoop_poly` 910, `rsa_usFind_eq` 933, `rsa_usStart_poly` 981 (162 lines). Kept, because they are rsa's test: `rsa_unitTest_eq` 703, `rsa_usGcd` 745, `rsa_usAcc` 750, `rsa_usAcc_poly` 809 | step, block, out, the `_poly` lemmas, `_iterate` and the length bounds are **verbatim** dl-a (1.00). `rsa_usLoop` writes the host's `match` as `Option.elim`. `rsa_usFind_eq` has the same statement shape as rabin's |
| rabin | `Candidates/Rabin.lean`: `rabin_rbStep` 577, `rabin_rbBlock` 583, `rabin_rbAcc` 587, `rabin_rbOut` 591, `rabin_rbLoop` 594, `rabin_rbStep_poly` 599, `rabin_rbBlock_poly` 612, `rabin_rbAcc_poly` 622, `rabin_rbOut_poly` 637, `rabin_rbStep_iterate` 641, the three `rabin_length_rbStep_*` 652/660/667, `rabin_rbLoop_poly` 680, `rabin_rbFind_eq` 695; consumers `rabin_spStart` 755, `rabin_spOut` 759, `rabin_spOut_eq` 766, `rabin_spOut_poly` 785 (136 + 44 lines) | step, out, `_iterate` and `_step_poly` are **verbatim** dl-a. block 0.95 and `block_poly` 0.64: the header is `⟨1^B, 1^k⟩`, and the test is a parameter `acc0`. `rabin_rbFind_eq` is the most general correctness lemma (any `E`, any header), so it is the template of the host |
| origin | `NumberTheory/Primality.lean` (p): `spStep` 704, `spOut` 709, `spAcc` 713, `spStep_iterate` 728, `length_spStep_le` 741, `length_spStep_spStep_le` 747, `length_spStep_iterate_le` 755 (consumer `exists_samplePrime_nuppt` 899) | the length triple is **near-verbatim** with all four copies (constant `2` in place of `4`). The state has two components, not three |

### G2. Search lemmas: `find?` and `findSome?` (DL-27, DL-28)

| Statement | Copies | Relation and existing forms |
|---|---|---|
| `findSome?` of a guarded map is `find?` then map | `dla_findSome?_ite` (DiscreteLog 700, p), `dlc_findSome?_ite` (ElGamal 920, p), `rsa_findSome?_ite` (RSA 661, p) | **verbatim** (1.00). It follows from core `List.findSome?_guard` + `List.map_findSome?` (`Init/Data/List/Find.lean` 94, 128), which `rabin_rbFind_eq` already cites. The general public form is `TCSlib.Cryptography.OneWay.findSome?_eq_bind_find?` (`Asymptotic/OneWayLemmas.lean` 217, outside `Concrete`'s closure) |
| a search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)` | `dla_find?_range_lt` (DiscreteLog 714), `dlc_find?_range_lt` (ElGamal 933), `rsa_find?_range_lt` (RSA 676), `rabin_find?_range_lt` (Rabin 555), all p | **verbatim** (1.00). Near: `OneWay.find?_range_eq_map_find?_finRange` (OneWayLemmas 228), `Complexity.StateLoop.find?_range_eq_some` (`TCSlib/Complexity/Randomized/Build/StateLoop.lean` 170), core `List.find?_range_eq_some`/`_none` (`Init/Data/List/Nat/Range.lean` 254/258). None is a drop-in |
| 3-colouring searches | `ColZK.findSome?_map_option` (`ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` 248, already `List.map_findSome?.symm` by landing edit E3), `ColZK.findSome?_range_eq_finRange` (253) | same statement as core (`List.map_findSome?`; `List.map_coe_finRange` + `List.findSome?_map`) |

### G3. `listToNat`: the defining-equation family (DL-23, DL-25, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `listToNat [] = 0` | `dla_listToNat_nil` (DiscreteLog 671), `dlc_listToNat_nil` (ElGamal 600), `rsa_listToNat_nil` (RSA 656) | **verbatim** |
| `⟦a ++ b⟧ = ⟦a⟧·2^{\|b\|} + ⟦b⟧` | `dla_listToNat_append` (DiscreteLog 656), `dlc_listToNat_append` (ElGamal 605), `rsa_listToNat_append` (RSA 2391), `rabin_listToNat_append` (Rabin 1568); `dlb_foldl_bits` (`Candidates/DiscreteLogHardcore.lean` 1950) with `dlb_listToNat_cons` (1961); source of record `TCSlib.Cryptography.foldl_bits_eq` (`Asymptotic/Sampling.lean` 318, p) | the four `_append` are **verbatim** (1.00); each inlines `foldl_bits_eq` as `key`. `dlb_foldl_bits` is **near-verbatim** `foldl_bits_eq` (0.81) |
| `listToNat [true] = 1` | `dlc_listToNat_true` (ElGamal 620), `rsa_listToNat_one` (RSA 651), `rabin_listToNat_one` (Rabin 728); inline `hone` in `fac_polyTimeComputable_isOne` (`Candidates/Factoring.lean` 223) | **near-verbatim** (`rw [listToNat_eq]; rfl`) |

`listToNat` is `TCSlib.Cryptography.NumberTheory.listToNat` (`NumberTheory/Primality.lean` 663), and
its only equation is `listToNat_eq` (667).

### G4. Numerals and widths: `natToList`, `subStr`, `mulStr` (DL-23, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧` | `dlc_listToNat_zeros_append` (ElGamal 631), `rsa_listToNat_zeros_append` (RSA 2406), `rabin_listToNat_zeros_append` (Rabin 1583); `hval` inside `dla_drop_natToList_zero_append` | rsa = rabin **verbatim**; dlc 0.98 |
| width normalization `(⟦0⟧_W ++ b).drop \|b\| = ⟦⟦b⟧⟧_W` | `dla_drop_natToList_zero_append` (DiscreteLog 678), `dlc_drop_natToList_zero_append` (ElGamal 636), `rsa_drop_zeros_append` (RSA 2412), `rabin_drop_zeros_append` (Rabin 1588) | rsa = rabin **verbatim**; dla 0.95 (near-verbatim); dlc is the **same statement** restructured (0.37) |
| `⟦N mod 2^k⟧_k = ⟦N⟧_k` | `dlc_natToList_mod` (ElGamal 625), `fac_natToList_mod` (Factoring 1087, reversed); inline `hnum` in `dla_`/`rsa_`/`rabin_` width lemmas | **same statement** (0.63) |
| `subStr ⟨a, a⟩ = ⟦0⟧_{\|a\|}` | `dlc_subStr_self` (ElGamal 652), `rsa_subStr_self` (RSA 2433) | **near-verbatim** (0.97) |
| `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧·⟦b⟧` | `rsa_listToNat_mulStr` (RSA 1067), `rabin_listToNat_mulStr` (Rabin 2707); inline in `dlc_numPoly_mul` (ElGamal 692) | **near-verbatim** (0.97) |
| `⟦1^k⟧ = 2^k − 1` | `rsa_listToNat_ones` (RSA 1047) | one copy; requested by rsa (REPORT request) and used by E4 |
| `⟦0^j⟧ = 0` and leading zeros | `fac_foldl_replicate_false` (Factoring 185), `fac_natToList_lead` (193) | same content as the zeros-append row, in fold form |

### G5. Numeral constants

`rsa_listToNat_two`/`_three` (RSA 1057/1062); `rabin_listToNat_two`/`_three`/`_four`/`_five`/`_seven`
(Rabin 803/807/811/1080/1084); `dlb_listToNat_one`/`_two`/`_four` (DiscreteLogHardcore 1005–1007,
stated on `natToList`); the inline `(by rw [listToNat_eq]; rfl)` in `Factoring.lean` (about line 1346).
These are **same-statement** two-liners, each an instance of the published `listToNat_eq`.

### G6. Polynomial time in applied form, and transfer along pointwise equality (DL-10, DL-25, DL-27, DL-28, DL-29)

| Statement | Copies | Relation |
|---|---|---|
| `PolyTimeComputable fun x => g (f x)` | fills: `rsa_comp` (RSA 761, 42 uses), `rabin_comp` (Rabin 550, 56 uses), `dlb_ptc` (DiscreteLogHardcore 994, 46 uses). Base: private `ptc_comp` in `TCSlib/Complexity/Randomized/Closure.lean` 171 (27 uses), `Asymptotic/Collections.lean` 772, `Asymptotic/UniversalLemmas.lean` 66, `Asymptotic/Universal.lean` 346, `Asymptotic/EnsemblesLemmas.lean` 175. Public: `ColMachines.ptc_comp` (`ZeroKnowledge/ThreeColoring/Machines.lean` 93), `TCSlib.Cryptography.ptcComp` (`Asymptotic/HardCoreLoops.lean` 367) | **verbatim** (`hg.comp hf`); rsa = rabin 1.00, dlb 0.97 |
| `PolyTimeComputable f → (∀ x, f x = g x) → PolyTimeComputable g` | fills: `rsa_ptc_congr` (RSA 1081), and `ElGamal.lean`'s base private `polyTimeComputable_of_forall_eq` (1269, 3 occurrences); inline `(congrArg PolyTimeComputable (funext …)).mp` in dl-a, dl-c, rsa, rabin and dl-b. Public with the **reversed** hypothesis `∀ w, g w = f w`: `ColMachines.ptc_congr` (Machines 84), `ColSimMachine.ptc_congr` (`ThreeColoring/SimulatorMachine.lean` 58), `GI.ptc_congr` (`ZeroKnowledge/GraphIsomorphism/Efficiency.lean` 71); private: `ptc_congr` (`ZeroKnowledge/GraphIsomorphismZK/Simulator.lean` 126) | **same statement** (0.76); the base four are **verbatim** among themselves |

### G7. `2^{size m} ≤ 2m` (DL-25)

| Copy | Relation |
|---|---|
| `dlb_two_pow_size_le` (DiscreteLogHardcore 2717, p): `0 < m → 2 ^ Nat.size m ≤ 2 * m` | the statement |
| inline `hk2` in `statClose_sampleBelowL` (DiscreteLog 616) | **same statement**, inline |
| inline `h2` in `statClose_sampleEdgeIdx` (`ZeroKnowledge/ThreeColoring/Language.lean` 430, base) | **same statement**, inline |
| `h1` inside `rsa_two_pow_size_le` (RSA 448, a different statement) | the same step, `2^{size N − 1} ≤ N` |
| public `TCSlib.Cryptography.two_pow_permBits_le` (`Asymptotic/Permutations.lean` 452) | **same statement** through `permBits n := Nat.size n` (no `permBits` equation is published) |
| public `+1` forms `TCSlib.Cryptography.two_pow_size_le` (`Asymptotic/HardCoreGL.lean` 773) and `TCSlib.Cryptography.two_pow_size_le_two_mul_succ` (`ZeroKnowledge/Encoding.lean` 492) | the **same statement** as each other (a pre-existing public pair) |

Mathlib (`Mathlib/Data/Nat/Size.lean`) has `Nat.size_le` (92), `Nat.lt_size` (111),
`Nat.size_pos` (114) and `Nat.lt_size_self` (81), but not this bound.

### G8. `StatClose X Y 1` (DL-29)

`dla_statClose_one` (DiscreteLog 1139, p) and `rabin_statClose_one` (Rabin 1447, p): **verbatim**
(1.00). No public form exists.

### G9. `abs_uexp_sub_le` (DL-12, DL-28)

| Copy | Relation |
|---|---|
| `TCSlib.Cryptography.abs_uexp_sub_le` (`Asymptotic/Sampling.lean` 204, p) | source. Its proof reads `uexp` by `unfold uexp`: rule-10 row (b) in `gates/07-eqlemmas/evidence-r2/r6c/cleanup-b.tsv` |
| `TCSlib.Cryptography.abs_uexp_sub_le` (`Asymptotic/PublicKeyLemmas.lean` 842, public; **same full name**) | **near-verbatim** (0.97), with the same (b) row |
| `dlc_abs_uexp_sub_le` (ElGamal 1896, p) | **same statement** with `[Nonempty α]` in place of `0 ≤ c`; a different proof (`uexp_mono`, `uexp_const`) |

### G10. `PushesUniform` restrictions (DL-24, DL-25, DL-26)

| Copy | Relation |
|---|---|
| `dla_pushesUniform_restrict` (`Candidates/Concrete.lean` 569, p; codomain `Bool`) | **near-verbatim** with col-b's (0.84) |
| `ColZK.pushesUniform_restrict` (ColZKLemmas 59, public; any codomain `O`) | the general form |
| `TCSlib.Cryptography.pushesUniform_comp_injective` (`Asymptotic/MultiMessage.lean` 231, public; `J = Fin (q + 1)`) | the same proof, specialised. **The file is edited by #195** |
| `GIZK.pushesUniform_castLE` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean` 105), `ColProofs.pushesUniform_castLE` (`ThreeColoring/ProtocolProofs.lean` 382), `GI.pushesUniform_castLE` (`GraphIsomorphism/Proofs.lean` 611); all public, base | GI = ColProofs **verbatim**; GIZK 0.96 (any codomain). Each is the case `r = Fin.castLE h` |
| `dlb_cut` (DiscreteLogHardcore 2469) with `dlb_guess_pushesUniform` (2485) | the same argument (prefix of a uniform string) |

### G11. Coin strings along a length cast (DL-23, DL-28)

`fac_arrowCongr`/`fac_arrowCongr_ofFn` (Factoring 1598/1602, p) and `dlc_castEquiv`/`dlc_castEquiv_ofFn`
(ElGamal 1620/1624, p) are **near-verbatim** (0.91). Both are literally the Mathlib term
`Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)`, with `List.ofFn_congr`
(`Mathlib/Data/List/OfFn.lean` 47). The public relative is `TCSlib.Cryptography.finCastEquiv`/`ofFn_finCastEquiv`
(`Asymptotic/HardCoreLemmas.lean` 95/102, a `Fin.cast` body). It is not in either file's closure.

### G12. Four-move iterations (DL-26)

`ColRep.exec_four_mul` (`ZeroKnowledge/ThreeColoring/ColRepSound.lean` 101, public) against
`GI.exec_repViews` (`ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean` 72, public). They have
different statements; the induction step is the same argument (four `exec_succ`, `moverIsV_false`).
`ColRep.chView` (66) is the counterpart of `GI.PsOf` (130).

### G13. Tape windows and blocks (DL-9, DL-23, DL-26)

| Copy | Relation |
|---|---|
| `dla_take_drop_ofFn` with `dla_blockPos`/`dla_blockPos_injective` (Concrete 615/588/597, p) | the block-`t` window, `k ≤ B` |
| `ColZK.ofFn_drop_take`, `ofFn_drop_eq`, `ofFn_take_drop` (ColZKLemmas 216/225/235, public) | general windows at any offset |
| `ColRep.drop_take_ofFn_blockRead` (ColRepSound 195, public) | the castLE form |
| `fac_ofFn_halves` (Factoring 211, p) | half is `OneWay.ofFn_block_eq_take_drop` (`Asymptotic/OneWayLemmas.lean` 74) at `q = 2` |
| `fac_chunkEquiv` (Factoring 1186, p), `fac_blocks_eq_blocksE` (698, p) | the latter is **near-verbatim** the private `blocks_eq_blocksE` (`Asymptotic/OneWay.lean` 626); both belong to DL-9 (`FunFamily.blocks`, `Asymptotic/OneWay.lean` 243) |
| private `ofFn_chunk` (Primality 768); `EnsembleLemmas.take_drop_ofFn_blocks` | relatives |

### G14. Table positions

`ColZK.table_index_lt`/`table_index_inj` (ColZKLemmas 75/83, public) restate the range and the
injectivity of Mathlib's `finProdFinEquiv` (`Mathlib/Logic/Equiv/Fin/Basic.lean` 325, `@[simps]`,
`j + k·i` order); `dla_blockPos` likewise. **Same statement** up to order.

### G15. The unit sampler's total value (DL-29)

`rsa_one_mod_spec`/`rsa_getD_spec` (RSA 393/401, p) and `rabin_one_mod_spec`/`rabin_getD_spec`
(Rabin 1244/1252, p) are the **same statement**, with different proofs (0.60–0.77).

### G16. Arithmetic-bundle wrappers in applied form (DL-29)

`rsa_le_poly` (RSA 791) and `rabin_le_poly` (Rabin 815) are the **same statement** (0.67).
`rsa_prime_poly` (RSA 1155; any word `a`) and `rabin_prime_poly` (Rabin 823; `a = id`) are the
**same statement** (0.80). Relatives: `dlc_poly_le` (ElGamal 744, numeral-calculus form) and
`fac_polyTimeComputable_isOne` (Factoring 223).

### G17. `((e : ZMod 0)⁻¹).val ≤ 1`

`rsa_val_inv_zero_le` (RSA 2437) and `rabin_val_inv_zero_le` (Rabin 2701), both p: **verbatim** (1.00).

### G18. Averages under a statistical switch (DL-29)

`rabin_uexp_le` (Rabin 1887, p) and the device of `rsa_uprob_pi_eval` (RSA 2184, p) with
`rsa_step_ii`: the **same argument**.

### G19. Selecting a `DistinctPrimes` from two numbers (DL-27, DL-29)

`fac_pairDec`/`fac_pairDec_pq` (Factoring 1608/1625); `rsa_zsel`/`rsa_zOf`/`rsa_zOf_pq`/`rsa_zOf_self`
(RSA 1993/2013/2019/2027); `rabin_mkDP`/`_p`/`_q`/`rabin_zOf` (Rabin 2031–2046). All are private.
They share an idea, but the fallbacks differ (`some default`, `DistinctPrimes.default hk`, a given
`z0`).

### G20. The factor-check words (DL-29)

`rsa_fS`/`rsa_fQ`/`rsa_fTest` (RSA 2443/2448/2452) and `rabin_rS`/`rabin_rQ`/`rabin_rTest`
(Rabin 3558/3562/3566), all p: **near-verbatim** data definitions (0.90–0.99).

### G21. Zero padding

`rabin_pad`/`_eq`/`_poly` (Rabin 732/736/742) and `rabin_zpad`/`rabin_listToNat_zpad`/`rabin_length_zpad`/`rabin_zpad_poly`
(2715–2726), all p, against the width normalization of G4. Same purpose; different statements.

### G22. Guarded state iteration (DL-11, DL-25)

`dlb_stateIterate_poly` (DiscreteLogHardcore 1119, p) is the body of the public
`TCSlib.Cryptography.polyTimeComputable_stateIterate` (`Asymptotic/HardCoreLoops.lean` 70, outside
the closure) at `out = pairSndD`: **near-verbatim**.

### G23. Counting `true`s in `List.ofFn` (DL-25)

`dlb_count_ofFn` (DiscreteLogHardcore 1967, p) against the public `TCSlib.Cryptography.count_true_ofFn`
(`Asymptotic/HardCoreGL.lean` 75): **near-verbatim** (0.97). There is also the general
`List.count_ofFn` (`TCSlib/Programs/Util/List.lean` 396, on `main`, namespace `List`). None is in the
closure. Mathlib has none.

### G24. Numeral calculi on the arithmetic bundle (DL-25, DL-28)

These are the **same pattern**, not copies:
- `dlc_NumPoly` and its closure lemmas (ElGamal 656–806);
- dl-b's fixed-width layer `dlb_{mulMod,powMod,invMod,quot,rem}` with `_poly` and `_natToList`
  (DiscreteLogHardcore 1010–1077);
- `dlc_poly_take`/`dlc_poly_drop` (ElGamal 1023/1030) against `dlb_take_poly`/`dlb_drop_poly` (1088/1094);
- `dlc_numPoly_ite` against `dlb_ite_poly` (1108).

### G25. 3-colouring near-copies (DL-24)

- `ColZK.polyTimeComputable_next` (`ThreeColoring/ColZKMachine.lean` 196) has the proof of
  `ColSimMachine.reply_poly` (`SimulatorMachine.lean` 443) with the tape generic.
- `ColZK.distAdv_seed_to_coins` has the content of `distAdv_sunglassRed`
  (`Pseudorandom/Indistinguishability.lean` 130), which cannot be cited: `sunglassRed` has no
  published equations.
- `ColZK.field_encodeMsgs` (ColZKMachine 142) is `ColMachines.getD_eq_pairFstD_iterate`
  (Machines 949) reversed.

### G26. Injectivity of reading

`fac_listToNat_inj` (Factoring 1351, p; an iff, 4 lines from the public `natToList_length_listToNat`)
against the private `listToNat_inj` (Sampling 337; fold form). **Same statement**, different proof (0.16).

**Already resolved at landing** (not in scope):
- `rsa_appendEquiv` and `rabin_appendEquiv` are now Mathlib's `Fin.appendEquiv`;
- `rabin_pushesUniform_prod` is now `PushesUniform.prodMap`;
- `dlb_statClose_pi` is now `OneWay.statClose_pi`;
- `colRep_xor_poly` is now `StateLoop.xor_poly`;
- `eq_of_xor_eq_false` is now core `bne_eq_false_iff_eq`;
- `pushesUniform_blockRead`'s inline block bijection is now `EnsembleLemmas.blocks`;
- `ColZK.acceptProb_seed_to_coins` is now `acceptProb_bind`.

Each was checked absent at the base (0 occurrences), except `rabin_pushesUniform_prod`, which E2
kept with the new body.

## 2. Import graph: where a home can be

Each home must be in the import closure of every consumer, and must not import a consumer. The
closures were computed from the base's `import` lines.

| Candidate home | Reaches | Does not reach | Note |
|---|---|---|---|
| `TCSlib/Complexity/Randomized/Closure.lean` | all 7 candidate files, all 3-colouring fill files, and every base G6 copy (`Collections`, `UniversalLemmas`, `Universal`, `EnsemblesLemmas`, `HardCoreLoops`, `ThreeColoring/Machines`, `SimulatorMachine`, `GI/Efficiency`, `GIZK/Simulator`) | — | campaign-owned (not on `main`); the home ruled for DL-10 (G3-5) |
| `TCSlib/Complexity/ClassNP/PolyTime.lean` | everything | — | **a `main` file** (identical on `main`); about 341 downstream modules. Avoided |
| `TCSlib/Complexity/Randomized/Build/IterateFind.lean` | all candidate and 3-colouring files | — | campaign-owned |
| `NumberTheory/Primality.lean` | all 7 candidate files | 3-colouring (no consumer there) | 922 lines; it imports `Asymptotic/Sampling.lean` |
| `Candidates/Arithmetic.lean` | all 7 candidate files | 3-colouring | 385 lines |
| `Candidates/Concrete.lean` | the 6 downstream candidate files | 3-colouring, `Primality` | **Cycle:** `Concrete → Arithmetic → Primality`, so `Primality` can never cite a lemma in `Concrete` (see Q3) |
| `Asymptotic/Sampling.lean` | all candidate and 3-colouring files, `Primality`, `Permutations`, `Encoding`, `HardCoreGL`, `PublicKeyLemmas`, `Language` | — | 856 lines |
| `HardcoreBit/Basic.lean` | all candidate and 3-colouring files, `MultiMessage`, `GIZK/Closeness`, `ProtocolProofs`, `GI/Proofs` | — | 266 lines |
| `Asymptotic/HardCoreLemmas.lean`, `HardCoreGL.lean`, `PublicKeyLemmas.lean`, `EnsemblesLemmas.lean`, `ZeroKnowledge/Encoding.lean` | — | every candidate file | so their public lemmas (`finCastEquiv`, `count_true_ofFn`, `two_pow_size_le`, `abs_uexp_sub_le`, …) cannot be cited from the fills |
| `Asymptotic/OneWayLemmas.lean` | the candidate files except `Concrete` | `Concrete` | — |

**Overlap with the open #195** (`cryptography/pass-shelat-ch5-8-s2b`, 25 Lean files against its
merge base `3436321b`). #195 edits `Asymptotic/MultiMessage.lean` and
`ZeroKnowledge/Interaction.lean`, among others. S1 and S2 touch neither file. So the
`pushesUniform_comp_injective` re-point and any move of `exec_four_mul` into `Interaction.lean` go
to clean-up part 2, which runs after #195.

## 3. Homes, statements and decisions

The decision legend:
- **Publish**: new public API, so it needs a statement audit (Q1).
- **Cite**: cite an existing public lemma.
- **Leave**: leave private, for the reason given.
- **Defer**: clean-up part 2.

No new lemma carries `@[simp]`. Every docstring opens with a natural-language statement and gives
its formula (policy §1–§2). Lemmas with long proofs carry a `**Proof sketch.**` (§3). These are
glue lemmas with no textbook counterpart, so they carry no `[PS10, …]` tag. The host (§4) does.

### 3.1 Decisions

| Group | Decision | PR |
|---|---|---|
| G1 trial loop | **Publish** the host `polyTimeComputable_rejectBlocksL` (§4) and delete the four loops | S2 |
| G2 search | **Publish** `IterateFind.find?_range_and_lt` and `rejectBlocksL_eq_find?`. The three `findSome?_ite` go through the latter, which is proved from **core** `List.findSome?_guard`, `List.map_findSome?` and `Option.guard_apply`. **Leave** the two `ColZK` searches (already public one-liners) | S1 |
| G3 `listToNat` equations | **Publish** `listToNat_nil`, `listToNat_cons`, `listToNat_append` and `listToNat_singleton_true` in `Primality.lean`. Make `foldl_bits_eq` public in `Sampling.lean` (a visibility change) | S1 |
| G4 widths | **Publish** `natToList_mod_two_pow`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`, `listToNat_mulStr`, `listToNat_replicate_true` and `listToNat_replicate_false` in `Arithmetic.lean` | S1 |
| G5 constants | **Leave** (Q8). They are instances of the published `listToNat_eq`, not copied proofs. Record them in the ledger as accepted | — |
| G6 `comp'`/`congr` | **Publish** `PolyTimeComputable.comp'` and `.congr` in `Closure.lean`. Re-point the fill copies (`rsa_comp`, `rabin_comp`, `dlb_ptc`, `rsa_ptc_congr`, `polyTimeComputable_of_forall_eq`) in S1. **Defer** `Closure`'s own private `ptc_comp` and the base copies to clean-up part 2 (DL-10; §5.3 explains why) | S1 + C2 |
| G7 `2^{size}` | **Publish** `two_pow_size_le_two_mul` in `Sampling.lean`. Re-point `dlb_two_pow_size_le` and dl-a's `hk2` in S1. **Defer** `Language`'s `h2`, `two_pow_permBits_le` and the `+1` pair | S1 + C2 |
| G8 `statClose_one` | **Publish** in `Sampling.lean` | S1 |
| G9 `abs_uexp_sub_le` | **Publish**: make the `Sampling.lean` one public, with `rw [uexp_def]` in place of `unfold uexp`. Delete the `PublicKeyLemmas` copy (same full name, so its users resolve unchanged). Re-point `dlc_abs_uexp_sub_le`. This takes DL-12 over from clean-up part 2 and retires two (b) rows | S1 |
| G10 restrictions | **Publish** `HardcoreBit.pushesUniform_restrict` in `HardcoreBit/Basic.lean`. Re-point `dla_pushesUniform_restrict` and `ColZK.pushesUniform_restrict` (Q6). **Defer**: the `castLE` triple (as corollaries), `dlb_cut`, and `pushesUniform_comp_injective` (#195's file) | S1 + C2 |
| G11 casts | **Cite Mathlib**: `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` and `List.ofFn_congr`. Moving `finCastEquiv` would make `dlc_splitEquiv_symm_ofFn`'s `subst h; exact …` a definitional read of another file's definition. Mathlib definitions may reduce there (§5.5) | S1 |
| G12 four moves | **Leave** (public already). An optional move into `Interaction.lean` waits for #195 | C2 (optional) |
| G13 windows | **Defer** to clean-up part 2 item A with DL-9 (the `blocks` family). `ColZK.ofFn_drop_take` is the natural public form; a move to `Asymptotic/CollectionsHelpers.lean` would serve `Concrete` | C2 |
| G14 table positions | **Defer**: cite `finProdFinEquiv` (optional) | C2 |
| G15 unit fallback | **Publish** `sampleUnitL_getD_spec` in `RSA.lean` (tier 2, Q5) | S1 |
| G16 bundle wrappers | **Publish** `ArithmeticFP.le_poly` and `ArithmeticFP.prime_poly` in `Arithmetic.lean` (tier 2, Q5) | S1 |
| G17 `ZMod 0` inverse | **Publish** `val_inv_natCast_zmod_zero_le` in `Arithmetic.lean`, beside `xgcdStr_pairEncode` (tier 2, Q5) | S1 |
| G18 average switch | **Defer** `uexp_le_of_statClose` (`Sampling.lean`; tier 2, Q5) | C2 |
| G19 selectors | **Leave**. A public selector is a new definition with equation lemmas, and its fallback must be designed first | — |
| G20 factor-check words | **Leave**. They are the words of each reduction (rabin review, finding 5) | — |
| G21 padding | **Leave**. After S2, `rabin_pad` is used only by the restricted prime sampler | — |
| G22 state iteration | **Defer** to DL-11 (clean-up part 2 item A: move `polyTimeComputable_stateIterate` into `Complexity.StateLoop`) | C2 |
| G23 counting | **Defer**. Move `count_true_ofFn` to a low file, then re-point `dlb_count_ofFn` | C2 |
| G24 numeral calculi | **Leave** (Q8) | — |
| G25 3-colouring | **Defer** (re-derive `reply_poly` from `polyTimeComputable_next`). **Leave** `distAdv_seed_to_coins`, which needs `sunglassRed`'s equations (a request to that file's owner) | C2 |
| G26 injectivity | **Leave**: 4 lines from a published lemma, with one consumer | — |

"C2" means clean-up part 2.

### 3.2 Exact statements (S1)

**`TCSlib/Complexity/Randomized/Closure.lean`**, namespace `Complexity`, placed after `open Turing`
and before `namespace NUPPT` (line 87):

```lean
/-- **Composition in applied form**: if `g` and `f` are polynomial-time, so is `x ↦ g (f x)`.
This is `PolyTimeComputable.comp` stated without `Function.comp`, so that unification never has
to unfold a composite against a lambda (hand-off pitfall: such matches can unfold bundle string
functions). -/
theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
  hg.comp hf

/-- **Polynomial time transfers along pointwise equality**: if `f` is polynomial-time and
`f x = g x` for every `x`, then `g` is polynomial-time (Mathlib's `Continuous.congr`
orientation). -/
theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
    (e : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext e : f = g) ▸ h
```

**`TCSlib/Complexity/Randomized/Build/IterateFind.lean`**, namespace `Complexity.IterateFind`,
beside `find?_congr_of_mem` (227):

```lean
/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.

**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p
```

**`NumberTheory/Primality.lean`**, namespace `TCSlib.Cryptography.NumberTheory`, beside
`listToNat_eq` (667). Each is proved from `listToNat_eq` and `List.foldl_*`, with `foldl_bits_eq`
from `Sampling.lean`, which is upstream. The file grows from 922 to about 952 lines.

```lean
/-- The empty word reads as `0`: `listToNat [] = 0`. -/
theorem listToNat_nil : listToNat [] = 0

/-- **Prepending a bit** (most significant first): `⟦b :: l⟧ = [b] · 2^{|l|} + ⟦l⟧`, with
`[b] = 1` if `b` and `0` otherwise. -/
theorem listToNat_cons (b : Bool) (l : List Bool) :
    listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l

/-- **Concatenation** (most significant first): `⟦a ++ b⟧ = ⟦a⟧ · 2^{|b|} + ⟦b⟧`. -/
theorem listToNat_append (a b : List Bool) :
    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b

/-- The one-bit word `[true]` reads as `1`. -/
theorem listToNat_singleton_true : listToNat [true] = 1
```

- **Audit point (`listToNat_cons`):** `(if b then 1 else 0)` matches dl-b's form and the fold. The
  alternative is `b.toNat`.

**`Asymptotic/Sampling.lean`**, namespace `TCSlib.Cryptography`. The file grows from 856 to about
885 lines.

```lean
/-- **The binary fold with an accumulator** (visibility change only; statement unchanged): the
fold of `listToNat` started at `a` is `a · 2^{|l|}` plus the fold started at `0`. -/
theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- **Averages of pointwise `c`-close functions are `c`-close** (visibility change; the proof
reads `uexp` through `uexp_def`): for `0 ≤ c` and `|f a − g a| ≤ c` for all `a`,
`|uexp f − uexp g| ≤ c`. -/
theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c

/-- **Any two samplers are `1`-close**: `StatClose X Y 1`, since both probabilities of every test
lie in `[0, 1]` (`statClose_iff`, `uprob_nonneg`, `uprob_le_one`). -/
theorem statClose_one {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) :
    StatClose X Y 1

/-- **A positive number is at least half the next power of two**: for `0 < m`,
`2 ^ Nat.size m ≤ 2 m` (the top bit of `m` is bit `size m − 1`: `Nat.lt_size`, `Nat.size_pos`). -/
theorem two_pow_size_le_two_mul {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m
```

- **Audit point (name):** the name is kept out of Mathlib's `Nat` namespace (policy §1,
  Namespaces).

**`Candidates/Arithmetic.lean`**, namespace `TCSlib.Cryptography.Candidates`, beside
`natToList_length_listToNat` (161), `subStr_pairEncode` (291) and `mulStr_pairEncode` (274). The
file grows from 385 to about 460 lines.

```lean
/-- **A numeral keeps the low bits**: `⟦N mod 2^k⟧_k = ⟦N⟧_k`. -/
theorem natToList_mod_two_pow (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N

/-- **Leading zeros do not change the value**: `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧`. -/
theorem listToNat_natToList_zero_append (k : ℕ) (w : List Bool) :
    listToNat (natToList k 0 ++ w) = listToNat w

/-- **Width normalization by truncation**: the last `|b|` bits of `⟦0⟧_W ++ b` are the
`W`-bit numeral of `⟦b⟧`, `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W` (the low `W` bits, also when
`⟦b⟧ ≥ 2^W`).

**Proof sketch.** The word `w = ⟦0⟧_W ++ b` reads as `⟦b⟧` (leading zeros), and splitting it after
its first `|b|` bits gives `⟦w⟧ = ⟦w.take |b|⟧ · 2^W + ⟦w.drop |b|⟧` (`listToNat_append`), where the
second summand is below `2^W`. So `⟦w.drop |b|⟧ = ⟦b⟧ mod 2^W`, and a word of length `W` is the
numeral of its value (`natToList_length_listToNat`, `natToList_mod_two_pow`). -/
theorem natToList_zero_append_drop (W : ℕ) (b : List Bool) :
    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b)

/-- **Subtracting a word from itself** gives the zero numeral of its width:
`subStr ⟨a, a⟩ = ⟦0⟧_{|a|}`. -/
theorem subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0

/-- **The product word reads back exactly**: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧` (the product fits in
`|a| + |b|` bits). -/
theorem listToNat_mulStr (a b : List Bool) :
    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b

/-- **The all-ones word** `1^k` reads as `2^k − 1`. -/
theorem listToNat_replicate_true (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1

/-- **The all-zeros word** `0^k` reads as `0`. -/
theorem listToNat_replicate_false (k : ℕ) : listToNat (List.replicate k false) = 0
```

**`Candidates/Concrete.lean`**, namespace `TCSlib.Cryptography.Candidates`, beside
`rejectBlocksL_eq` (547):

```lean
/-- **Block rejection sampling as a search followed by the value read**: `rejectBlocksL E k B T r`
is the first trial `t < T` whose value `v_t = ⟦(r.drop (t B)).take k⟧` passes `E`, mapped to
`v_t` (core `List.findSome?_guard`, `List.map_findSome?`, `Option.guard_apply`). -/
theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r =
      ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map
        fun t => listToNat ((r.drop (t * B)).take k)
```

- **Proof correction (rule 10).** The stub in `harvest-stubs.lean` closes with
  `simp [Option.guard, ht]`. That passes a core definition to `simp`, which the 2026-10-23 rule
  forbids. The landed proof uses core's `Option.guard_apply` (`Init/Data/Option/Lemmas.lean` 668).

**`HardcoreBit/Basic.lean`**, namespace `TCSlib.Cryptography.HardcoreBit`, after `pushesUniform_fst`
(204). Add `import Mathlib.Logic.Equiv.Set` if `Equiv.Set.sumCompl` is not already reachable. The
file grows from 266 to about 292 lines.

```lean
/-- **Restricting a uniform table along an injection gives a uniform table**: for an injective
`r : J → I`, the map `R ↦ R ∘ r` pushes the uniform distribution on `I → O` to the uniform
distribution on `J → O`.

**Proof sketch.** Split `I` into the image of `r` and its complement (`Equiv.ofInjective`,
`Equiv.Set.sumCompl`). A table is the pair of its two restrictions (`Equiv.sumArrowEquivProdArrow`),
and `R ∘ r` is the first one (`pushesUniform_equiv`, `pushesUniform_fst`). -/
theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) :
    PushesUniform (fun R : I → O => fun j => R (r j))
```

**Tier 2** (Q5):

```lean
-- Candidates/RSA.lean, beside sampleUnitL_spec (387)
/-- **The total unit sampler gives a unit**: for `0 < N`, the value
`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N` (`sampleUnitL_spec`, or the
fallback `1 mod N`). -/
theorem sampleUnitL_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
    (sampleUnitL N k B T r).getD (1 % N) < N ∧
      Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N

-- Candidates/Arithmetic.lean, beside ArithmeticFP (250) and xgcdStr_pairEncode (353)
/-- **Comparisons are polynomial-time tests**: for polynomial-time words `a`, `b`, the bit
`[⟦a x⟧ ≤ ⟦b x⟧]` is polynomial-time (`H.le`, read through `leStr_pairEncode`). -/
theorem ArithmeticFP.le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))]

/-- **Primality of a polynomial-time word is a polynomial-time test** (`H.prime`, `primeStr_eq`). -/
theorem ArithmeticFP.prime_poly (H : ArithmeticFP) {a : List Bool → List Bool}
    (ha : PolyTimeComputable a) : PolyTimeComputable fun x => [decide (listToNat (a x)).Prime]

/-- In `Z_0 = ℤ` the inverse of a natural number is its sign, so its value is at most `1`
(the `N = 0` case of `xgcdStr_pairEncode`'s inverse). -/
theorem val_inv_natCast_zmod_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1
```

`uexp_le_of_statClose` (the statement of `rabin_uexp_le`) is deferred: it has one consumer, and
rsa uses the device inline.

All of these names were checked: none exists in TCSlib or Mathlib at the base. The one exception is
`pushesUniform_restrict`, which exists only as the `ColZK` copy that S1 removes (Q6).

**E4 compatibility.** rsa's E4 cites these names unqualified:
- `listToNat_nil`, `listToNat_singleton_true`, `listToNat_append`, `listToNat_replicate_true`,
  `listToNat_mulStr`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`;
- `rejectBlocksL_eq_find?`, `IterateFind.find?_range_and_lt`, `PolyTimeComputable.comp'`,
  `PolyTimeComputable.congr`.

`RSA.lean` sits in `TCSlib.Cryptography.Candidates` with `open Complexity Turing NumberTheory`, so
all of them resolve. That holds although the four `listToNat_*` live in `NumberTheory` rather than
in the stubs' `Candidates`. `git apply --check` of the E4 diff on the base `RSA.lean` is clean (text
only; −177/+64 lines).

## 4. The host: `polyTimeComputable_rejectBlocksL` (PR S2)

**Home:** `Candidates/Concrete.lean`, namespace `TCSlib.Cryptography.Candidates`, after
`rejectBlocksL_spec` (555). It is the file of `rejectBlocksL` (539), so the host's own proof may use
`rejectBlocksL_eq_find?`. Every consumer imports it: `DiscreteLog` and `Factoring` directly, and
`ElGamal`, `RSA` and `Rabin` through them. Registry: a new row **H15** in
`machine-library-design.md` §14 (records). This is the host of policy §1, **Hosts come first**.
- **Time:** its contract is `PolyTimeComputable`.
- **No head envelope:** this is a string-function host over the repetition host
  `Complexity.polyTimeComputable_iterateFind` (machine layer H14), so there is no head envelope to
  state.

### 4.1 Statement

```lean
/-- **Block rejection sampling is polynomial-time** (host H15) [PS10, Theorems 52.3, 53.2, 61.7
and 63.10: "the domain is easy to sample"]. Let `E a v` be a test on a parameter `a` and a value
`v`, decided on words by a polynomial-time bit `acc`, so that `acc ⟨w, b⟩ = [E ⟦w⟧ ⟦b⟧]`. Take
polynomial-time words `par z` (the parameter), `kw z`, `bw z` and `tw z`, whose lengths are the
trial width `k`, the block length `B` and the trial count `T`, and `c z` (the coins). Then some
polynomial-time `g` computes the sampler `rejectBlocksL (E ⟦par z⟧) k B T (c z)`:
- `g z = []` when every trial is rejected;
- otherwise `g z = true :: b`, where `b` reads as the accepted value and has at most `k` bits.

In particular `(rejectBlocksL …).getD 0 = ⟦(g z).tail⟧`. The statement is existential: the trial
loop that realizes it is internal, and no consumer reads it.

**Proof sketch.**
- **The loop.** The state is `⟨⟨⟨1^B, 1^k⟩, w⟩, ⟨1^T, r⟩⟩`. One step keeps the header, drops one
  bit of the counter and one block of `B` coins (`polyTimeComputable_tail`,
  `polyTimeComputable_pairDropPoly`). The test accepts iff the counter is nonempty and
  `acc ⟨w, first k coins⟩` holds (`polyTimeComputable_isNil`, `polyTimeComputable_pairTakePoly`).
  The payload is `true` followed by the first `k` coins.
- **Polynomial time.** One step at most doubles the length, and from the second step on the state
  only shrinks (`StateLoop.length_pairFstD_add_pairSndD_le`). So the repetition host
  `Complexity.polyTimeComputable_iterateFind`, with `R = var` and orbit bound `2n + 4`, makes the
  loop polynomial-time. Its `match` is split by its equation lemmas (`split`), never matched by
  definitional unfolding.
- **Correctness.** After `i` steps the coins have lost `i` blocks, so trial `i` reads the `k`-bit
  prefix of block `i`. The search over the first `|start| + 1 ≥ T` rounds is therefore the search
  over `[0, T)` (`IterateFind.find?_range_and_lt`), which is `rejectBlocksL` read as a search
  followed by its value (`rejectBlocksL_eq_find?`). -/
theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)]
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x])
    (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b)))
    {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par)
    (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw)
    (hc : PolyTimeComputable c) :
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z,
      (g z).tail.length ≤ (kw z).length ∧
      rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) =
        if g z = [] then none else some (listToNat (g z).tail)
```

### 4.2 Design choices for the statement audit

- **Existential output.** A public loop function would be a new definition. It would then need its
  own equation lemmas, and consumers would be tempted to read it. The existential publishes exactly
  what the four consumers use:
  - emptiness ↔ rejection;
  - the value read from the tail;
  - the length bound, which rabin's padding needs.

  `getD 0` follows by cases, since `[].tail = []` reads `0` (`listToNat_nil`).
- **A parameter-dependent test** `E : ℕ → ℕ → Prop`, decided on `⟨w, b⟩`:
  - dl-a and dl-c use `E a v := v < a` with `par` = the modulus numeral;
  - rsa uses `E a v := v < a ∧ v.Coprime a`;
  - rabin uses `E _ v := v.Prime ∧ P v` (the parameter is ignored).

  The test is given in the repetition host's convention (`acc : List Bool → Bool`,
  `PolyTimeComputable fun x => [acc x]`).
- **Lengths of words** `kw`, `bw`, `tw` rather than numbers. Every consumer has its sizes as unary
  words already:
  - `sizeStr ⟦m⟧`, whose length is `Nat.size` (`length_sizeStr`);
  - `1^n` from `inParam`;
  - `polyTimeComputable_unaryPoly rsaBlock` and `rabinTrials`.
- **Instances.** `rejectBlocksL (E (listToNat (par z)))` is a β-redex. Consumers `beta_reduce` the
  hypothesis before rewriting it against `sampleBelowL_eq_rejectBlocksL` or `sampleUnitL_eq`. The
  `DecidablePred` instance then agrees up to β (to be confirmed in the fill).

### 4.3 What each consumer cites

| Consumer | Published equations it reads | Re-proved | Deleted |
|---|---|---|---|
| dl-a (`DiscreteLog.lean`) | `sampleBelowL_eq_rejectBlocksL` (578, own file), `natToList_zero_append_drop`, `subStr_self`, `listToNat_nil`, `length_sizeStr` | `polyTimeComputable_expSampleRaw` (proof and sketch). Test `fun x => !decide (⟦pairFstD x⟧ ≤ ⟦pairSndD x⟧)` by `H.le` | the 15 `dla_ss*` (162 lines) |
| dl-c (`ElGamal.lean`) | `sampleBelowL_eq_rejectBlocksL` (**foreign**: published beside `sampleBelowL` in `DiscreteLog.lean`), `length_sizeStr` | `dlc_numPoly_sample` (it becomes `⟨fun z => (g z).tail, …⟩`) | `dlc_ss*`, `dlc_ssLoop*` (155 lines) |
| rsa (`RSA.lean`) | `sampleUnitL_eq` (383, own), `unitSampleStr_eq` (536, own), `sampleUnitL_spec` | `rsa_ptc_unitSampleStr`; the test `rsa_usAcc`/`rsa_usGcd`/`rsa_usAcc_poly`/`rsa_unitTest_eq` restated on `⟨w, b⟩` (rsa-specific, kept private) | the loop: `rsa_usStart`, `_usStep`, `_usBlock`, `_usOut`, `_usLoop`, the `_poly`/`_iterate`/length lemmas, `rsa_usFind_eq`, `rsa_usStart_poly` (162 lines) |
| rabin (`Rabin.lean`) | `rejectBlocksL` through the host only; `samplePrimePL` (477, own file); `rabin_oddAcc_spec`/`rabin_blumAcc_spec` as `hspec` (test `acc0 ∘ pairSndD`); its unit sampler through rsa's public `polyTimeComputable_unitSampleStr` (unchanged) | `rabin_spOut_eq`, `rabin_spOut_poly` (the padding uses the length clause) | the `rabin_rb*` loop and `rabin_rbFind_eq` (136 lines) |

`Primality.lean`'s private `spStep` host, the origin of all four copies, **cannot** cite the host:
`Concrete` imports `Arithmetic`, which imports `Primality`. See Q3 for the two-layer alternative.

## 5. PR plan

### 5.1 Order

1. **S1, the shared-lemma PR**, on `cryptography/pass-shelat-ch2-4`. It needs neither #195 nor
   gate 04, and its files are disjoint from #195's. It applies rsa's E4, as the rsa review planned
   for the case where rsa lands before H1.
2. **The S2 contract gate**, then **S2**, the host PR. S2 depends on S1 for `rejectBlocksL_eq_find?`,
   `find?_range_and_lt`, `natToList_zero_append_drop` and `PolyTimeComputable.comp'`/`.congr`.
3. **#195** is re-merged after each of S1 and S2. There are no textual conflicts: the downstream
   replay of its 25 files is enough.
4. **Clean-up part 2**, after #195 and gate 04, with the additions in §5.4.

### 5.2 Estimated lines per file

These are estimates from the measured spans of the deleted declarations. "+" counts new lemmas with
their docstrings.

**S1**

| File | Removed | Added | Result |
|---|---|---|---|
| `Complexity/Randomized/Closure.lean` | 0 | +14 | 456 → ~470 |
| `Complexity/Randomized/Build/IterateFind.lean` | 0 | +28 | 531 → ~559 |
| `Cryptography/NumberTheory/Primality.lean` | 0 | +30 | 922 → ~952 |
| `Cryptography/Asymptotic/Sampling.lean` | 0 (the `abs_uexp_sub_le` proof changes in place) | +29 | 856 → ~885 |
| `Cryptography/Candidates/Arithmetic.lean` | 0 | +75 (tier 2: +25) | 385 → ~460 (~485) |
| `Cryptography/HardcoreBit/Basic.lean` | 0 | +26 | 266 → ~292 |
| `Cryptography/Candidates/Concrete.lean` | −19 (`dla_pushesUniform_restrict`) | +14 | 691 → ~686 |
| `Cryptography/Asymptotic/PublicKeyLemmas.lean` | −15, plus docstring lines 41 and 67 | 0 | 856 → ~841 |
| `Cryptography/Candidates/DiscreteLog.lean` | −90: G2/G3/G4 helpers (73), `dla_statClose_one` (11), `hk2` (6) | +4 | 1446 → ~1360 |
| `Cryptography/Candidates/ElGamal.lean` | −107: numerals (49), G2 (33), `polyTimeComputable_of_forall_eq` (6), `dlc_abs_uexp_sub_le` (11), casts (8) | +8 | 2391 → ~2292 |
| `Cryptography/Candidates/RSA.lean` | E4 −177; tier 2: `rsa_getD_spec`/`_one_mod_spec` −19 and `rsa_le_poly`/`_prime_poly`/`_val_inv_zero_le` −25 | E4 +64; tier 2: `sampleUnitL_getD_spec` +13 | 2762 → ~2649 (~2618) |
| `Cryptography/Candidates/Rabin.lean` | −85: the G2/G3/G4/G6/G8 helpers; tier 2: `rabin_getD_spec`/`_one_mod_spec`/`_le_poly`/`_prime_poly`/`_val_inv_zero_le` −33 | +6 | 3813 → ~3734 (~3701) |
| `Cryptography/Candidates/Factoring.lean` | −22: `fac_natToList_mod`, `fac_foldl_replicate_false`, `fac_arrowCongr`/`_ofFn`, `hone` | +4 | 1851 → ~1833 |
| `Cryptography/Candidates/DiscreteLogHardcore.lean` | −29: `dlb_ptc` (46 uses renamed), `dlb_foldl_bits`, `dlb_listToNat_cons`, `dlb_two_pow_size_le` | +2 | 3091 → ~3064 |
| `Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` | −23 (Q6) | +2 | 328 → ~307 |

Net S1: about −260 lines (−300 with tier 2). The replay covers 98 modules (those downstream of the
15 changed files). The homes stay under 1000 lines (`Primality` ~952; `Concrete` ~876 after S2).
The files above 1000 (`DiscreteLog`, `ElGamal`, `DiscreteLogHardcore`, `Factoring`, `RSA`,
`Rabin`) are fill-owned files under the standing size rule, and S1 and S2 only shrink them.

**S2**

| File | Removed | Added | Result |
|---|---|---|---|
| `Candidates/Concrete.lean` | 0 | +190: the host with its docstring (~35), the private loop (~120), the proof (~35) | ~686 → ~876 |
| `Candidates/DiscreteLog.lean` | −162 | +12 | ~1360 → ~1210 |
| `Candidates/ElGamal.lean` | −155 | +5 | ~2292 → ~2142 |
| `Candidates/RSA.lean` | −162 | −13 net on the restated test and `rsa_ptc_unitSampleStr` | ~2649 → ~2474 |
| `Candidates/Rabin.lean` | −136 | −4 net on `rabin_spOut*` | ~3734 → ~3594 |

Net S2: about −425 lines. The replay covers 8 modules. S2 also carries docstring-only sketch
refreshes of six public declarations that name the private loop (Q7):
- `polyTimeComputable_expSampleRaw` (DiscreteLog 931);
- `polyTimeComputable_egGenRaw` (ElGamal 1109);
- `polyTimeComputable_egEncRaw` (ElGamal 1236);
- `polyTimeComputable_unitSampleStr` (RSA 1444);
- `polyTimeComputable_oddGenRaw` (Rabin 1099);
- `polyTimeComputable_blumGenRaw` (Rabin 1125).

### 5.3 Gates and checks per PR (the user decides the gate: Q1)

**S1**
- **Statement surface.** `decls2.py` against the base must show only:
  - **ADDED** (18 in tier 1, up to 4 in tier 2);
  - **REMOVED**: `ColZK.pushesUniform_restrict` (or kept as an alias, Q6), and the `PublicKeyLemmas`
    copy of `abs_uexp_sub_le`, whose name survives in `Sampling`;
  - visibility changes: `foldl_bits_eq` and `abs_uexp_sub_le`.

  It changes no target statement and adds no definition, so there is no equation-lemma obligation
  and no check-8 change. The statement audit covers the new statements (a gate round, or the
  clean-up audit: Q1).
- **Gated packs affected.** S1 adds public lemmas to files of packs 03a (`Closure`, `Sampling`),
  03l (`IterateFind`) and others. The re-staged 03d/03h–03k packs will see them, and whichever
  audit Q1 chooses covers them.
- **Checks** (as clean-up part 1):
  - replay with `downstream2.py`; `sorry` counts equal to the base's;
  - full axiom prints of the changed files;
  - a seal of every touched file, with names collected from the elaborated terms plus matchers,
    and controls;
  - the explicit-unfold scan;
  - `style_lint.py` and `campaign_style_lint.py --check8b`;
  - E4 re-checked against the real lemmas with rsa's 50-name seal.

**S2**
- **The host contract** is statement-gated before the PR merges (policy §1). The gate checks:
  - the statement of §4.1;
  - its docstring and its `[PS10, …]` tag;
  - the existential design;
  - the registry row H15.

  The proof is a harvest of rabin's `rabin_rb*` and `rabin_rbFind_eq`, generalized by the header
  word (Q4).
- **Checks** as S1, plus:
  - the six sketch refreshes (docstring-only);
  - a seal control that `polyTimeComputable_iterateFind.match_1` stays sealed (dl-a review
    finding 3).

### 5.4 Clean-up part 2: what changes in its brief

- **Item A, DL-10.** S1 publishes `PolyTimeComputable.comp'`/`.congr` in `Closure.lean`. Clean-up
  part 2 then deletes `Closure`'s private `ptc_comp` and re-points its 27 uses, and re-points the
  other G6 base copies (G6 has the list). The base `ptc_congr`s take the reversed hypothesis, so
  they re-point with `fun w => (h w).symm`.
  - **Why not in S1.** `ptc_comp`'s eight users in `Closure` are `Computes.polyTimeComputable`,
    `exists_comp`, `exists_compParam`, `exists_reparam`, `exists_reparam_advice`, `exists_seq`,
    `exists_split` and `exists_withAdvice`. Item C rewrites exactly these declarations
    (`simp [runAtL, advInput, coinLen, …]`). Touching them in S1 would bring their reads into S1's
    seal.
- **Item A, DL-12.** Done by S1: drop it.
- **New item N: base-file re-points of this design's deferred groups.**
  - G7: `Language.lean`'s `h2`; `two_pow_permBits_le` as a corollary; one of the public pair
    `two_pow_size_le`/`two_pow_size_le_two_mul_succ` kept and the other re-pointed.
  - G10: the `castLE` triple as corollaries of `HardcoreBit.pushesUniform_restrict`
    (`Fin.castLE_injective`, `Mathlib/Data/Fin/SuccPred.lean` 86); `dlb_cut`;
    `pushesUniform_comp_injective` (after #195).
  - G13 with DL-9.
  - G14.
  - G22 with DL-11.
  - G23.
  - G25.
  - G12, optionally (after #195).
  - G18, if Q5 defers it.
- **Item M (DL-21).** `Candidates/*` rows of the Mathlib overlap. These files are now landed and
  edited by S1/S2. Item M runs after S2 so that the two do not edit the same proofs.

### 5.5 Rule-10 consequences (no proof reads another file's definition)

1. **Every new lemma is proved through published equations only.** Each one sits beside its
   definition or reads it through that definition's lemma:
   - `listToNat_eq`, `natToList_eq`/`natToList_length_listToNat`, `subStr_pairEncode`,
     `mulStr_pairEncode`, `leStr_pairEncode`, `primeStr_eq`, `rejectBlocksL_eq`, `statClose_iff`;
   - `uexp_def`, which replaces `Sampling`'s `unfold uexp` (the (b) row at `Sampling.lean` 207; the
     `PublicKeyLemmas` row at 845 goes with its deletion);
   - `pushesUniform_equiv`/`_fst`.

   Core definitions are read only through their lemmas (`Option.guard_apply`, not
   `simp [Option.guard]`; the latter is in rsa's stub and in `rabin_rbFind_eq`, which S2 deletes).
2. **A citation must not create a read.**
   - Re-pointing `dlc_castEquiv` to `finCastEquiv` would turn `dlc_splitEquiv_symm_ofFn`'s
     `subst h; exact ofFn_splitCoins_symm …` into a definitional read of `HardCoreLemmas`'
     definition. Mathlib's `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` may reduce there,
     so G11 cites Mathlib.
   - In general, a deleted private definition that was read by `rfl`/`show` in its own file may be
     replaced only by a Mathlib/core term or a lemma, never by another file's definition.
3. **Statements only.**
   - dl-c reads `sampleBelowL` only through `sampleBelowL_eq_rejectBlocksL`.
   - rsa and rabin read their own samplers. rabin reads rsa's unit sampler only through
     `polyTimeComputable_unitSampleStr`.
   - No consumer unfolds `rejectBlocksL` (foreign to every consumer).
   - The host's existential hides its machine, so no consumer can read it.
4. **Matchers.** The host's proof splits the repetition host's `match` by `split` (the dl-a E1
   pattern). The seal includes `polyTimeComputable_iterateFind.match_1`.
5. **"Touched" is computed against the PR base.** It covers every changed file. S1 touches only the
   new lemmas, the deleted copies, the re-pointed fill declarations (which were seal-clean at
   landing) and `Sampling`'s `abs_uexp_sub_le` (fixed). It deliberately avoids `Closure`'s
   `ptc_comp` users (§5.4).

## 6. Questions for the user (recommended option first)

**Q1. How are S1's new public statements audited?**
- **(A) Recommended.** One statement-gate round, `08-shared`, covers S1's 18–22 new statements and
  2 visibility changes (proved) and S2's host contract (§4.1, before its proof). It is staged before either PR merges.
  S1 can be opened in parallel, and stays "Not yet clear to merge" until the round closes. S2
  needs a gate anyway, so S1 adds little to it.
- (B) S1 merges after the maintainer's review. Its statements ride in clean-up part 2's statement
  diff and gate; only S2's host gets a round now.
- (C) Two separate rounds: S1 now, S2's contract later.

**Q2. Fold the work into clean-up part 2?**
- **(A) Recommended.** No. S1 and S2 go first, as their own PRs; they need neither #195 nor
  gate 04. The clean-up part 2 brief is updated as in §5.4: DL-12 dropped, DL-10 reduced to the
  re-points, and new item N.
- (B) Fold S1 into clean-up part 2. That is one PR, but it waits for #195 and gate 04, and so do
  rsa's E4 and the fill re-points.
- (C) Fold clean-up part 2's item A (DL-9 to DL-15) into S1. S1 grows and changes the statements of
  packs 03h/03i/03k, which must then be re-staged first.

**Q3. Where does the host live?**
- **(A) Recommended.** In `Candidates/Concrete.lean` only: one public lemma (§4.1) with a private
  loop. It retires the four copies.
- (B) Two layers. A generic `Complexity.polyTimeComputable_blockSearch` goes in
  `Randomized/Repetition.lean` (a `find?` over fixed-width blocks, with no `rejectBlocksL`). The
  Concrete lemma becomes its corollary. Then `Primality.lean`'s private `spStep` host, the origin
  of the copies, can be retired too; `Primality` cannot import `Concrete` (§2). The cost is a
  second gated statement and a re-proof of `exists_samplePrime_nuppt`.

**Q4. Who writes S2's proof?**
- **(A) Recommended.** The maintainer, as a harvest after the contract gate. The proof exists: it is
  rabin's `rabin_rb*`/`rabin_rbFind_eq` generalized by a header word, plus dl-a's `split` step.
- (B) An external fill, with a brief, dispatched by the user.

**Q5. Tier-2 publications.**
- **(A) Recommended.** Include the verbatim or same-statement cross-unit copies in S1:
  `sampleUnitL_getD_spec`, `ArithmeticFP.le_poly`, `ArithmeticFP.prime_poly` and
  `val_inv_natCast_zmod_zero_le`. Defer `uexp_le_of_statClose` (one consumer) to clean-up part 2.
- (B) Tier 1 only in S1; all tier 2 to clean-up part 2.
- (C) All tier 2, including `uexp_le_of_statClose`, in S1.

**Q6. `ColZK.pushesUniform_restrict`** (public, landed with col-b; a copy of the new
`HardcoreBit.pushesUniform_restrict`)
- **(A) Recommended.** Delete it, re-point its two uses (ColZKLemmas 122 and 164) and update the
  module docstring. The statement diff shows it as REMOVED.
- (B) Keep it as a one-line alias.

**Q7. Proof sketches that name the deleted loops** (six public docstrings, §5.2)
- **(A) Recommended.** Docstring-only refresh in S2, under the standing sketch-refresh ruling.
  Statements are unchanged.
- (B) Leave them, and record "sketch refresh owed" for the next docstring window.

**Q8. Numeral constants (G5) and numeral calculi (G24)**
- **(A) Recommended.** Leave them private, and record them in the ledger as accepted. They are
  instances of published equations and fill-specific bundle readings, not copied proofs.
- (B) Publish a numeral calculus (dl-c's `dlc_NumPoly`, or dl-b's fixed-width layer) in
  `Arithmetic.lean` in clean-up part 2. Which one is a design choice to rule on then.

**Not yet clear to merge — design draft only; no PR exists; rulings Q1–Q8 pending.**

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/REPORT.md =====

# S1, the shared-lemma PR, with the S2 host contract: implementation report

- **Branch:** `wip/shared-s1` (local, not pushed), worktree `$SP/wt-shared-s1`.
- **Base:** `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`, the last base commit touching `TCSlib/`.
- **Head:** `c6affb3a92535d3f1de2e0a52c205a84c0cff551` (tree `80f4e6fc09e2746958f05cf3130036c28aa87284`), 14 commits. Patch series in `patches/`.
- **Design followed:** `fills/shared-lemmas/design.md`, with rulings Q1–Q8 (A, A, A, B, A, A, A, A).
- `$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## 1. Results in short

| Check | Result | Evidence |
|---|---|---|
| Replay: the 97 modules downstream of the 15 changed files, then `audits/pass-shelat/Checks` | 98/98 rc=0, **0 errors** | `replay.log`, `tools/order.txt` |
| `sorry` census (code tokens, all of `TCSlib/`) | 507 → 508, **exactly +1**: the host in `Candidates/Concrete.lean` | `sorry-census-{base,head}.txt` |
| Statement diff (`decls2.py` against the base) | 25 ADDED (18 tier 1, 4 tier 2, 1 host, 2 visibility changes), 2 REMOVED, **0 CHANGED** | `statement-diff.txt` |
| Axioms | All 146 touched declarations and all 25 new or visibility-changed ones use the standard axioms or fewer; only the host has `sorryAx`. `Checks` has the same 4 `sorryAx` records as the post-landing base (`decides_of_decidesWithAdviceInTime`, `lemma_64_3`, `theorem_63_1`, `exists_canonizerExp`) | `axioms-touched.tsv`, `axioms-new.log`, `checks-axioms-head.log` |
| Rule 10 seal | 15 whole-file seals, collected from the elaborated terms. No touched declaration fails. The 6 failures are in untouched base declarations and fail the same way in the base control. Controls pass 13/13 | `seal/` |
| Explicit-unfold scan | 0 `unfold`, `delta` or `.eq_N` added; no foreign definition used as a rewrite or simp rule | `seal/unfold-scan.txt` |
| `style_lint.py` | Only the 6 size lines of the fill-owned files, as at the base; all 6 files shrink | `style-lint-{base,head}.log` |
| `campaign_style_lint.py --check8b` | No FAIL or WARN change on `TCSlib/Cryptography` or `TCSlib/Complexity/Randomized`; only the INFO declaration counts move | `campaign-lint-*.log` |
| Lines | +572 / −906 over 15 files (net −334, host contract included) | `line-counts.tsv` |

## 2. Per design group

| Group | Done | Deviations |
|---|---|---|
| **G1** trial loop (S2) | The **host contract** `polyTimeComputable_rejectBlocksL` (Q3 (A), Q4 (B)) is in `Concrete.lean` after `rejectBlocksL_spec`. The statement is design §4.1 verbatim; the proof is `sorry`. The docstring has the formula, the tag `[PS10, Theorems 52.3, 53.2, 61.7 and 63.10]` and a deviation note (truncation to `T` trials, register #15). Its **Proof sketch.** has three parts (the loop, polynomial time, correctness), harvested from rabin's `rabin_rb*`/`rabin_rbFind_eq` and dl-a's `split` step. It names the published lemmas a fill worker needs: `IterateFind.find?_range_and_lt`, `rejectBlocksL_eq_find?`, `StateLoop.length_pairFstD_add_pairSndD_le` and `polyTimeComputable_iterateFind`. The four loops are **not** retired; that is S2's landing. The module docstring gets a main-results entry, and its References get the four theorem numbers | none |
| **G2** search | `IterateFind.find?_range_and_lt`, proved through `find?_congr_of_mem`. `rejectBlocksL_eq_find?`, proved from core `List.findSome?_guard`, `List.map_findSome?` and `Option.guard_apply` (the design's proof correction; no `simp [Option.guard]`). Re-pointed: the four `*_find?_range_lt` copies (dla, dlc, rsa via E4, rabin) and the three `*_findSome?_ite` copies (dla, dlc, rsa via E4). The `ColZK` searches are left | `rabin_rbFind_eq` now reads `rejectBlocksL` through `rejectBlocksL_eq_find?`, as E4 does for rsa. That also removes its `simp only [Function.comp_apply, Option.guard]`, which passed a core definition to `simp` |
| **G3** `listToNat` equations | `listToNat_nil`, `_cons` (in the `(if b then 1 else 0)` form), `_append` and `_singleton_true` in `Primality.lean` (922 → 944 lines); `foldl_bits_eq` made public. All copies re-pointed: the four `*_listToNat_append`, the `_nil` and `_one`/`_true` copies, `dlb_foldl_bits` with `dlb_listToNat_cons`, and fac's inline `hone` | none |
| **G4** widths | The 7 lemmas in `Arithmetic.lean` (385 → 482 lines). Re-pointed: `dlc_natToList_mod`; `fac_natToList_mod` (reversed, `← natToList_mod_two_pow`); the zeros-append, drop-zeros, `subStr_self` and `mulStr` copies, including the inline one in `dlc_numPoly_mul`; `rsa_listToNat_ones` (E4); `fac_foldl_replicate_false`, whose 3 uses now go through `listToNat_append`/`listToNat_replicate_false` | `fac_natToList_lead` is kept (a different statement); only its proof is re-pointed |
| **G5** constants | Left (Q8) | — |
| **G6** `comp'`/`congr` | `PolyTimeComputable.comp'` and `.congr` in `Closure.lean`. Re-pointed: `rsa_comp` and `rsa_ptc_congr` (E4), `rabin_comp` (64 occurrences), `dlb_ptc` (56), and ElGamal's `polyTimeComputable_of_forall_eq`. `Closure`'s own `ptc_comp` and the base copies are deferred to clean-up part 2 | The inline `(congrArg PolyTimeComputable …).mp` uses are left; they are not in the design's re-point list |
| **G7** `2^{size}` | `two_pow_size_le_two_mul` in `Sampling.lean`; `dlb_two_pow_size_le` and dl-a's `hk2` re-pointed | `Sampling.lean` needed `import Mathlib.Data.Nat.Size`, which it could not reach before |
| **G8** `statClose_one` | In `Sampling.lean`; `dla_statClose_one` and `rabin_statClose_one` re-pointed | — |
| **G9** `abs_uexp_sub_le` | `Sampling`'s copy made public, with `rw [uexp_def]` in place of `unfold uexp`. The `PublicKeyLemmas` copy is deleted; its user `PublicKey.lean` resolves unchanged, and docstring lines 41 and 67 are updated. `dlc_abs_uexp_sub_le` re-pointed as `abs_uexp_sub_le (by positivity)` | none |
| **G10** restrictions | `HardcoreBit.pushesUniform_restrict` in `HardcoreBit/Basic.lean`; no new import was needed. `dla_pushesUniform_restrict` deleted. Q6 (A): `ColZK.pushesUniform_restrict` deleted, its 2 uses re-pointed, and the module docstring and the two sketches that named it updated | — |
| **G11** casts | Mathlib's `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)` and `List.ofFn_congr` replace `dlc_castEquiv`/`_ofFn` and `fac_arrowCongr`/`_ofFn` | Factoring needs a 2-line local `hofn` to rewrite with |
| **G12–G14, G18–G26** | As ruled: left or deferred | — |
| **G15** (tier 2) | `sampleUnitL_getD_spec` made public in `RSA.lean`. `rsa_getD_spec` and `rabin_getD_spec` re-pointed; `rabin_one_mod_spec` deleted | **`rsa_one_mod_spec` stays private**, because `statClose_sampleUnitL` also uses it directly. The design counted it as deleted (−19), so the actual saving is smaller |
| **G16** (tier 2) | `ArithmeticFP.le_poly` and `ArithmeticFP.prime_poly`. `rsa_`/`rabin_le_poly` and `rsa_`/`rabin_prime_poly` re-pointed | `rabin_prime_poly` (the case `a = id`) becomes `H.prime_poly polyTimeComputable_id` |
| **G17** (tier 2) | `val_inv_natCast_zmod_zero_le` beside `xgcdStr_pairEncode`; both copies re-pointed | — |
| **E4** | rsa's `conditional-harvest-edits.diff` (SHA-256 `445928bd6fa469e1db486ab12dff17f831d2101eac73589292ce03d974f3976e`) applied **unchanged** (`git apply --check` clean), in its own commit. The tier-2 commit after it changes what E4 left (`rsa_le_poly`, `rsa_prime_poly` → the bundle lemmas). Under rsa's 50-name review seal, RSA has 0 errors (`seal/SealedRSA-review50.out`) | none |

**Q7.** The six S2 sketch refreshes were not done. Docstrings changed only where a re-point made a name false:
- `rsaSampler_spec` (public): `rsa_getD_spec` → `sampleUnitL_getD_spec`.
- `polyTimeComputable_egDecStr` (public): `polyTimeComputable_of_forall_eq` → `PolyTimeComputable.congr`.
- `ColZK.pushesUniform_offsetTable` and `_blockFields`: the restriction lemma's new name.
- Private sketches: `dla_ssFind_eq`, `dlc_ssLoop_eq`, `rabin_rbFind_eq`, `dlc_hyb3`, and E4's own.

No statement changed.

## 3. Statement surface (`statement-diff.txt`)

- **ADDED, tier 1 (18):**
  - `Complexity.PolyTimeComputable.comp'`, `.congr`;
  - `Complexity.IterateFind.find?_range_and_lt`;
  - `NumberTheory.listToNat_nil`, `_cons`, `_append`, `_singleton_true`;
  - `Candidates.natToList_mod_two_pow`, `listToNat_natToList_zero_append`, `natToList_zero_append_drop`, `subStr_self`, `listToNat_mulStr`, `listToNat_replicate_true`, `listToNat_replicate_false`;
  - `Candidates.rejectBlocksL_eq_find?`;
  - `statClose_one`, `two_pow_size_le_two_mul`;
  - `HardcoreBit.pushesUniform_restrict`.
- **ADDED, tier 2 (4):** `Candidates.sampleUnitL_getD_spec`, `ArithmeticFP.le_poly`, `ArithmeticFP.prime_poly`, `val_inv_natCast_zmod_zero_le`.
- **ADDED, host (1, sorried):** `Candidates.polyTimeComputable_rejectBlocksL`.
- **Visibility changes (2):** `foldl_bits_eq` and `abs_uexp_sub_le`, shown as ADDED in `Sampling.lean`; their statements are unchanged.
- **REMOVED (2):**
  - `ColZK.pushesUniform_restrict` (Q6);
  - the `PublicKeyLemmas` copy of `TCSlib.Cryptography.abs_uexp_sub_le`, whose full name survives in `Sampling.lean` (G9).
- **CHANGED:** none.
- No new definition and no `@[simp]`. Every new lemma has a docstring with its formula. `natToList_zero_append_drop`, `find?_range_and_lt`, `pushesUniform_restrict` and the host also carry a **Proof sketch.**

## 4. Rule 10 (`seal/`)

- **Touched declarations** (`touched-*.txt`, `tools/touched.py`): every head declaration whose text contains an added line or a deletion point of `git diff -U0` against the base, over all 15 files. That is 146 declarations. It over-includes neighbours of deleted blocks, which only makes the seal stricter.
- **Collection** (`Collect.lean`, `collect.log`, `tools/collect_body.lean`):
  - Input: the elaborated types and values of the touched constants and their auxiliaries, plus the types of everything reached and the bodies of own-module definitions, transitively.
  - Kept: TCSlib definitions from other modules that are not instances; non-reducible ones, plus matchers whatever their status.
  - `PolyExpr.eval` and `glNeed` are left unsealed.
  - Result: 89 names in all (`names-*.txt`). The only foreign matcher reached is `polyTimeComputable_iterateFind.match_1` (DiscreteLog, ElGamal). IterateFind and Primality reach no foreign definition.
- **Whole-file seals** (`Sealed*.lean/.out`, `seal-summary.tsv`): 9 files are clean. There are 6 failures, all in **untouched** declarations. Each fails the same way when the **base** file gets the same seal (`base-control/`):
  - `primesPairEquiv_apply_val` (Concrete), `ExpGroupGen.FullLength.exists_fullLengthExcept` (DiscreteLog), `rabinCollection_index` and `rabinBlumTrapdoor_index` (Rabin), and `uexp_mono` (HardcoreBit/Basic). All five are rows of `gates/07-eqlemmas/evidence-r2/r6c/cleanup-b.tsv` (clean-up part 2).
  - `exists_plantFactorer` (Factoring): the `NUPPT.coinLen` defeq reading recorded in the fac delivery review, finding 1 (forced by `ans_layout`'s published coin type). It is not in the `cleanup-b` rows, which predate the fac landing.
- **Controls** (`Controls.lean/.out`): C1–C13 read each of these by its body:
  - `natToList`, `listToNat`, `rejectBlocksL`, `StatClose`, `uexp`, `PushesUniform`, `PolyTimeComputable`;
  - `sampleUnitL`, `subStr`, the matcher `polyTimeComputable_iterateFind.match_1`, `sampleBelowL`, `bitsToNat`, `mulStr`.

  All 13 close unsealed and fail sealed (13 errors, all "Type mismatch").
- **Explicit-unfold scan** (`unfold-scan.txt`):
  - 70 rewrite and simp lists in the added code, and no `unfold`, `delta` or `.eq_N`.
  - The one lexical hit is `show listToNat [false] = 0 by rw [listToNat_eq]`, a G5 constant whose rule is the published `listToNat_eq`.
  - Core and Mathlib definitions reduce only in `rfl`, `show` or `exact` steps: `Option.guard_apply`, the `show` through `ZMod 0 = ℤ` in `val_inv_natCast_zmod_zero_le`, and the `arrowCongr`/`finCongr` casts.

## 5. Lines per file (`line-counts.tsv`)

| File | + | − | base → head |
|---|---|---|---|
| `Complexity/Randomized/Build/IterateFind.lean` | 23 | 0 | 531 → 554 |
| `Complexity/Randomized/Closure.lean` | 18 | 0 | 456 → 474 |
| `Asymptotic/PublicKeyLemmas.lean` | 5 | 20 | 856 → 841 |
| `Asymptotic/Sampling.lean` | 30 | 6 | 856 → 880 |
| `Candidates/Arithmetic.lean` | 97 | 0 | 385 → 482 |
| `Candidates/Concrete.lean` | 81 | 21 | 691 → 751 (the host contract is about 57 of the +81) |
| `Candidates/DiscreteLog.lean` | 11 | 109 | 1446 → 1348 |
| `Candidates/DiscreteLogHardcore.lean` | 50 | 83 | 3091 → 3058 |
| `Candidates/ElGamal.lean` | 21 | 143 | 2391 → 2269 |
| `Candidates/Factoring.lean` | 12 | 35 | 1851 → 1828 |
| `Candidates/RSA.lean` | 88 | 240 | 2762 → 2610 |
| `Candidates/Rabin.lean` | 80 | 215 | 3813 → 3678 |
| `HardcoreBit/Basic.lean` | 26 | 0 | 266 → 292 |
| `NumberTheory/Primality.lean` | 22 | 0 | 922 → 944 |
| `ZeroKnowledge/ThreeColoring/ColZKLemmas.lean` | 8 | 34 | 328 → 302 |
| **Total** | **572** | **906** | net −334 |

The homes stay under 1000 lines (`Primality` 944, `Concrete` 751). The six files over 1000 lines are fill-owned under the standing size rule, and each one shrinks.

## 6. Deviations and notes (no ruling needed)

1. `Sampling.lean` gains `import Mathlib.Data.Nat.Size`, for `two_pow_size_le_two_mul`.
2. `rsa_one_mod_spec` stays private in `RSA.lean`, because it has a second direct user.
3. `rabin_rbFind_eq` was re-pointed to `rejectBlocksL_eq_find?` rather than only swapping `rabin_find?_range_lt`. It loses a `simp only [Option.guard]`; S2 deletes the lemma anyway.
4. Two candidates for clean-up part 2 were kept out of S1, as they are outside the design's lists:
   - the inline `StatClose … 1` proof in `factoringCollection_sampleClose` (the `n < 2` branch);
   - the inline `congrArg PolyTimeComputable` transports.
5. `audits/pass-shelat/run2-census.md` (records) still names the deleted `polyTimeComputable_of_forall_eq`. It is a historical census and was not edited.
6. Every check ran directly on `$SP/postland-oleans`, one Lean process at a time. That tree now holds the head's oleans for the 97 replayed modules plus `Checks`. No `lake build`, no cache fetch.

## 7. Evidence index

- `replay.log`; `sorry-census-{base,head}.txt`; `statement-diff.txt`.
- Axioms: `axioms-touched.tsv`, `Axioms.lean`/`axioms-new.log`, `checks-axioms-head.log`.
- `seal/`: touched lists, `Collect.lean`, `collect.log`, `names-*.txt`, `Sealed*.lean/.out`, `base-control/`, `Controls.lean/.out`, `seal-summary.tsv`, `unfold-scan.txt`, `SealedRSA-review50.*`.
- Lints: `style-lint-{base,head}.log`, `campaign-lint-{base,head}-*.log`.
- `line-counts.tsv`; `logs/` (the per-module checks run during the work); `tools/`; `patches/`; `BASE.txt`, `HEAD.txt`.

**Not yet clear to merge — S1 is not yet a PR, and gate 08 (Q1 (A)) must audit the 22 new statements, the 2 visibility changes and the host contract first.**

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/statement-diff.txt =====

ADDED	TCSlib/Complexity/Randomized/Build/IterateFind.lean:246	Complexity.IterateFind.find?_range_and_lt	theorem	theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) : (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p
ADDED	TCSlib/Complexity/Randomized/Closure.lean:94	Complexity.PolyTimeComputable.comp'	theorem	theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g) (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x)
ADDED	TCSlib/Complexity/Randomized/Closure.lean:101	Complexity.PolyTimeComputable.congr	theorem	theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f) (e : ∀ x, f x = g x) : PolyTimeComputable g
REMOVED	TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean:842	TCSlib.Cryptography.abs_uexp_sub_le	theorem	theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:210	TCSlib.Cryptography.abs_uexp_sub_le	theorem	theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:333	TCSlib.Cryptography.foldl_bits_eq	theorem	theorem foldl_bits_eq (l : List Bool) (a : ℕ) : l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a = a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:224	TCSlib.Cryptography.statClose_one	theorem	theorem statClose_one (X : σ → γ) (Y : τ → γ) : StatClose X Y 1
ADDED	TCSlib/Cryptography/Asymptotic/Sampling.lean:407	TCSlib.Cryptography.two_pow_size_le_two_mul	theorem	theorem two_pow_size_le_two_mul {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:459	TCSlib.Cryptography.Candidates.ArithmeticFP.le_poly	theorem	theorem ArithmeticFP.le_poly (H : ArithmeticFP) {a b : List Bool → List Bool} (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) : PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))]
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:466	TCSlib.Cryptography.Candidates.ArithmeticFP.prime_poly	theorem	theorem ArithmeticFP.prime_poly (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) : PolyTimeComputable fun x => [decide (listToNat (a x)).Prime]
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:351	TCSlib.Cryptography.Candidates.listToNat_mulStr	theorem	theorem listToNat_mulStr (a b : List Bool) : listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:191	TCSlib.Cryptography.Candidates.listToNat_natToList_zero_append	theorem	theorem listToNat_natToList_zero_append (k : ℕ) (w : List Bool) : listToNat (natToList k 0 ++ w) = listToNat w
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:230	TCSlib.Cryptography.Candidates.listToNat_replicate_false	theorem	theorem listToNat_replicate_false (k : ℕ) : listToNat (List.replicate k false) = 0
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:220	TCSlib.Cryptography.Candidates.listToNat_replicate_true	theorem	theorem listToNat_replicate_true (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:185	TCSlib.Cryptography.Candidates.natToList_mod_two_pow	theorem	theorem natToList_mod_two_pow (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:203	TCSlib.Cryptography.Candidates.natToList_zero_append_drop	theorem	theorem natToList_zero_append_drop (W : ℕ) (b : List Bool) : (natToList W 0 ++ b).drop b.length = natToList W (listToNat b)
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:418	TCSlib.Cryptography.Candidates.subStr_self	theorem	theorem subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0
ADDED	TCSlib/Cryptography/Candidates/Arithmetic.lean:438	TCSlib.Cryptography.Candidates.val_inv_natCast_zmod_zero_le	theorem	theorem val_inv_natCast_zmod_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:633	TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL	theorem	theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)] {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x]) (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b))) {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par) (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw) (hc : PolyTimeComputable c) : ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z, (g z).tail.length ≤ (kw z).length ∧ rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) = if g z = [] then none else some (listToNat (g z).tail)
ADDED	TCSlib/Cryptography/Candidates/Concrete.lean:563	TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find?	theorem	theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : rejectBlocksL E k B T r = ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map fun t => listToNat ((r.drop (t * B)).take k)
ADDED	TCSlib/Cryptography/Candidates/RSA.lean:402	TCSlib.Cryptography.Candidates.sampleUnitL_getD_spec	theorem	theorem sampleUnitL_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) : (sampleUnitL N k B T r).getD (1 % N) < N ∧ Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N
ADDED	TCSlib/Cryptography/HardcoreBit/Basic.lean:219	TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict	theorem	theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) : PushesUniform (fun R : I → O => fun j => R (r j))
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:687	TCSlib.Cryptography.NumberTheory.listToNat_append	theorem	theorem listToNat_append (a b : List Bool) : listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:682	TCSlib.Cryptography.NumberTheory.listToNat_cons	theorem	theorem listToNat_cons (b : Bool) (l : List Bool) : listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:677	TCSlib.Cryptography.NumberTheory.listToNat_nil	theorem	theorem listToNat_nil : listToNat [] = 0
ADDED	TCSlib/Cryptography/NumberTheory/Primality.lean:692	TCSlib.Cryptography.NumberTheory.listToNat_singleton_true	theorem	theorem listToNat_singleton_true : listToNat [true] = 1
REMOVED	TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean:59	TCSlib.Cryptography.ColZK.pushesUniform_restrict	theorem	theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) : HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j))

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/pr.diff.txt =====

diff --git a/TCSlib/Complexity/Randomized/Build/IterateFind.lean b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
index 82acba88..45597594 100644
--- a/TCSlib/Complexity/Randomized/Build/IterateFind.lean
+++ b/TCSlib/Complexity/Randomized/Build/IterateFind.lean
@@ -78,6 +78,8 @@ assembly through `Turing.FinTM.exists_loopFindTM`.
   polynomial-time computable.
 * `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
   values on the list (used to identify the guarded orbit with `g^[i] x`).
+* `Complexity.IterateFind.find?_range_and_lt` — a search over `[0, L)` whose test also demands
+  `i < N` is the search over `[0, N)`, for `N ≤ L`.
 
 ## References
 
@@ -234,6 +236,27 @@ theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
     · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
       exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))
 
+/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
+the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
+`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.
+
+**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
+`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
+it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
+theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
+    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
+  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
+  rw [List.range_add, List.find?_append,
+    find?_congr_of_mem _ (fun i hi => by rw [decide_eq_true (List.mem_range.1 hi), Bool.true_and])]
+  have hnone : (List.map (fun x => N + x) (List.range d)).find?
+      (fun i => decide (i < N) && p i) = none := by
+    rw [List.find?_eq_none]
+    intro x hx
+    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
+    rw [decide_eq_false (by omega), Bool.false_and]
+    exact Bool.false_ne_true
+  rw [hnone, Option.or_none]
+
 /-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
 `T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
 majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.
diff --git a/TCSlib/Complexity/Randomized/Closure.lean b/TCSlib/Complexity/Randomized/Closure.lean
index 79f76687..3a893b30 100644
--- a/TCSlib/Complexity/Randomized/Closure.lean
+++ b/TCSlib/Complexity/Randomized/Closure.lean
@@ -69,6 +69,8 @@ Not in this file (they are FP-level facts the campaign uses directly): negation
   gives `f ∘ advInput` as a polynomial-time function (coins hard-wired to `1^{coins n}`).
 * `Complexity.NUPPT.polyTimeComputable_layout` and the projection lemmas — the FP calculus of
   the layout.
+* `Complexity.PolyTimeComputable.comp'`, `Complexity.PolyTimeComputable.congr` — composition in
+  applied form, and transfer of polynomial time along a pointwise equality.
 
 ## References
 
@@ -84,6 +86,22 @@ namespace Complexity
 
 open Turing
 
+/-! ### Composition in applied form and transfer along pointwise equality -/
+
+/-- **Composition in applied form**: if `g` and `f` are polynomial-time, so is `x ↦ g (f x)`.
+This is `PolyTimeComputable.comp` stated without `Function.comp`, so that unification never has
+to unfold a composite against a lambda (such matches can unfold bundle string functions). -/
+theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
+    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
+  hg.comp hf
+
+/-- **Polynomial time transfers along pointwise equality**: if `f` is polynomial-time and
+`f x = g x` for every `x`, then `g` is polynomial-time (Mathlib's `Continuous.congr`
+orientation). -/
+theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
+    (e : ∀ x, f x = g x) : PolyTimeComputable g :=
+  (funext e : f = g) ▸ h
+
 namespace NUPPT
 
 /-! ### The raw input layout and its projections -/
diff --git a/TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean b/TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean
index 58a4a989..3874e1d8 100644
--- a/TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean
@@ -38,8 +38,9 @@ reductions encrypt the other positions of the tuple themselves under the public
   `distAdv_multi_le_sum`), the samplers `singleDist`/`multiDist` and the single-machine hybrid
   bound `exists_hybridBound`;
 * glue: `acceptProb_distinguisherL_coins` (a machine's acceptance probability through a
-  bijection of its coins), `abs_uexp_sub_le` (averages of pointwise close functions) and the
-  averaging identities `uexp_half_add`/`uexp_half_sub` of the prediction lemma.
+  bijection of its coins) and the averaging identities `uexp_half_add`/`uexp_half_sub` of the
+  prediction lemma (averages of pointwise close functions are `abs_uexp_sub_le` of
+  `Asymptotic/Sampling.lean`).
 
 ## Main definitions
 
@@ -64,8 +65,8 @@ reductions encrypt the other positions of the tuple themselves under the public
 * `TCSlib.Cryptography.exists_hybridMachine`, `exists_hybridBound` — the hybrid machine of the
   single ⇒ multi-message and bitwise theorems and the resulting bound `K(n) · ε`.
 * `TCSlib.Cryptography.tdpPredictor_runAtL`, `uprob_tdpPredictor` — the predictor machine.
-* `TCSlib.Cryptography.acceptProb_distinguisherL_coins`, `abs_uexp_sub_le`, `uexp_half_add`,
-  `uexp_half_sub`, `ofFn_fin_one` — glue.
+* `TCSlib.Cryptography.acceptProb_distinguisherL_coins`, `uexp_half_add`, `uexp_half_sub`,
+  `ofFn_fin_one` — glue.
 
 ## References
 
@@ -837,20 +838,4 @@ theorem uexp_half_sub {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ)
   rw [e, uexp_half_add]
   ring
 
-/-- Averages of pointwise `c`-close functions are `c`-close (`0 ≤ c` covers the empty type;
-copy of the private lemma of `TCSlib.Cryptography.Asymptotic.Sampling`). -/
-theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
-    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
-  rw [← HardcoreBit.uexp_sub]
-  unfold uexp
-  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
-  · rw [h0]
-    simpa using hc
-  · have hc' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
-    rw [abs_div, abs_of_pos hc', div_le_iff₀ hc']
-    calc |∑ a, (f a - g a)| ≤ ∑ a, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
-      _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => h a
-      _ = c * Fintype.card α := by
-        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
-
 end TCSlib.Cryptography
diff --git a/TCSlib/Cryptography/Asymptotic/Sampling.lean b/TCSlib/Cryptography/Asymptotic/Sampling.lean
index 211981f0..55fa8f50 100644
--- a/TCSlib/Cryptography/Asymptotic/Sampling.lean
+++ b/TCSlib/Cryptography/Asymptotic/Sampling.lean
@@ -8,6 +8,7 @@ import TCSlib.Cryptography.OneWayFunctions.Basic
 import TCSlib.Cryptography.HardcoreBit.Basic
 import Mathlib.Data.List.FinRange
 import Mathlib.Logic.Equiv.Fin.Basic
+import Mathlib.Data.Nat.Size
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -84,6 +85,10 @@ added for the permutation sampler, whose section moved to `Asymptotic/Permutatio
   conditioned on success, made total by a default, is close to uniform within its failure
   probability (C4 in abstract form).
 * `TCSlib.Cryptography.one_sub_inv_pow_le_half` — `(1 - 1/m)^m ≤ 1/2`.
+* `TCSlib.Cryptography.statClose_one`, `TCSlib.Cryptography.abs_uexp_sub_le`,
+  `TCSlib.Cryptography.foldl_bits_eq`, `TCSlib.Cryptography.two_pow_size_le_two_mul` — glue:
+  any two samplers are `1`-close, averages of pointwise close functions are close, the binary
+  fold with an accumulator, and `2^{size m} ≤ 2m`.
 
 ## References
 
@@ -200,11 +205,11 @@ theorem StatClose.comp_pushesUniform {Ω : Type*} [Fintype Ω] {X : σ → γ} {
   rw [hπ.uprob_eq (fun s => T (X s))]
   exact h T
 
-/-- Averages of pointwise `c`-close functions are `c`-close (`0 ≤ c` covers the empty type). -/
-private theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
+/-- **Averages of pointwise `c`-close functions are `c`-close**: for `0 ≤ c` and
+`|f a − g a| ≤ c` for all `a`, `|uexp f − uexp g| ≤ c` (`0 ≤ c` covers the empty type). -/
+theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
     (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
-  rw [← HardcoreBit.uexp_sub]
-  unfold uexp
+  rw [← HardcoreBit.uexp_sub, uexp_def]
   rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
   · rw [h0]
     simpa using hc
@@ -214,6 +219,14 @@ private theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c
       _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => h a
       _ = c * Fintype.card α := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
 
+/-- **Any two samplers are `1`-close**: `StatClose X Y 1`, since both probabilities of every
+test lie in `[0, 1]` (`statClose_iff`, `uprob_nonneg`, `uprob_le_one`). -/
+theorem statClose_one (X : σ → γ) (Y : τ → γ) : StatClose X Y 1 :=
+  (statClose_iff X Y 1).2 fun T => by
+    rw [abs_le]
+    constructor <;> linarith [uprob_nonneg (fun s => T (X s)), uprob_le_one (fun s => T (X s)),
+      uprob_nonneg (fun t => T (Y t)), uprob_le_one (fun t => T (Y t))]
+
 /-- The statistical-switch lemma (C10 of the Chapter 2 inventory): replacing a sampler by a
 `δ`-close one changes the success probability of any experiment that also uses independent
 auxiliary coins `r : ρ` by at most `δ`. [Gar26, Lemma 3.1] in the sup-over-test-sets form.
@@ -314,8 +327,10 @@ theorem pushesUniform_of_card_fiber_le {Ω γ : Type*} [Fintype Ω] [Fintype γ]
 def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ :=
   (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0
 
-/-- The digit fold with an arbitrary accumulator `a` contributes `a · 2^{|l|}`. -/
-private theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
+/-- **The binary fold with an accumulator**: the fold of `listToNat` started at `a` is
+`a · 2^{|l|}` plus the fold started at `0`,
+`foldl (a ↦ c ↦ 2a + [c]) a l = a · 2^{|l|} + foldl (a ↦ c ↦ 2a + [c]) 0 l`. -/
+theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
     l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
       a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
   induction l generalizing a with
@@ -387,6 +402,15 @@ theorem uprob_bitsToNat_lt {m k : ℕ} (hk : m ≤ 2 ^ k) :
   push_cast
   rfl
 
+/-- **A positive number is at least half the next power of two**: for `0 < m`,
+`2 ^ Nat.size m ≤ 2 m` (the top bit of `m` is bit `size m − 1`: `Nat.lt_size`, `Nat.size_pos`). -/
+theorem two_pow_size_le_two_mul {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m := by
+  have hpos : 0 < Nat.size m := Nat.size_pos.2 hm
+  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (Nat.sub_lt hpos one_pos)
+  calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
+        rw [← pow_succ', Nat.sub_add_cancel hpos]
+    _ ≤ 2 * m := Nat.mul_le_mul_left 2 h1
+
 /-- One rejection trial: `k` bits read as a number, accepted iff below `m`. -/
 def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m) :=
   if h : bitsToNat b < m then some ⟨_, h⟩ else none
diff --git a/TCSlib/Cryptography/Candidates/Arithmetic.lean b/TCSlib/Cryptography/Candidates/Arithmetic.lean
index 8c9f7e47..d635c8f2 100644
--- a/TCSlib/Cryptography/Candidates/Arithmetic.lean
+++ b/TCSlib/Cryptography/Candidates/Arithmetic.lean
@@ -63,6 +63,18 @@ computability on strings is a hypothesis, discharged by a future machine-buildin
   `TCSlib.Cryptography.Candidates.listToNat_subStr` — addition and truncated subtraction of
   numerals are lossless at the widths of the bundle.
 * `TCSlib.Cryptography.Candidates.val_units_pow` — `(x^e).val = x.val^e mod M` in `Z_M^*`.
+* `TCSlib.Cryptography.Candidates.natToList_mod_two_pow`,
+  `TCSlib.Cryptography.Candidates.listToNat_natToList_zero_append`,
+  `TCSlib.Cryptography.Candidates.natToList_zero_append_drop`,
+  `TCSlib.Cryptography.Candidates.listToNat_replicate_true`,
+  `TCSlib.Cryptography.Candidates.listToNat_replicate_false` — widths, leading zeros and the
+  constant words.
+* `TCSlib.Cryptography.Candidates.subStr_self`,
+  `TCSlib.Cryptography.Candidates.listToNat_mulStr`,
+  `TCSlib.Cryptography.Candidates.val_inv_natCast_zmod_zero_le` — readings of the bundle's words.
+* `TCSlib.Cryptography.Candidates.ArithmeticFP.le_poly`,
+  `TCSlib.Cryptography.Candidates.ArithmeticFP.prime_poly` — comparisons and primality tests of
+  polynomial-time words are polynomial-time.
 
 ## References
 
@@ -169,6 +181,58 @@ theorem natToList_val_natCast {k M : ℕ} {w : List Bool} (hk : w.length = k)
     (hM : listToNat w < M) : natToList k ((listToNat w : ZMod M).val) = w := by
   rw [ZMod.val_cast_of_lt hM, ← hk, natToList_length_listToNat]
 
+/-- **A numeral keeps the low bits**: `⟦N mod 2^k⟧_k = ⟦N⟧_k`. -/
+theorem natToList_mod_two_pow (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N := by
+  have h := natToList_length_listToNat (natToList k N)
+  rw [length_natToList, listToNat_natToList_eq_mod] at h
+  exact h
+
+/-- **Leading zeros do not change the value**: `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧`. -/
+theorem listToNat_natToList_zero_append (k : ℕ) (w : List Bool) :
+    listToNat (natToList k 0 ++ w) = listToNat w := by
+  rw [listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]
+
+/-- **Width normalization by truncation**: the last `|b|` bits of `⟦0⟧_W ++ b` are the
+`W`-bit numeral of `⟦b⟧`, `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W` (the low `W` bits, also when
+`⟦b⟧ ≥ 2^W`).
+
+**Proof sketch.** The word `w = ⟦0⟧_W ++ b` reads as `⟦b⟧` (leading zeros), and splitting it after
+its first `|b|` bits gives `⟦w⟧ = ⟦w.take |b|⟧ · 2^W + ⟦w.drop |b|⟧` (`listToNat_append`), where the
+second summand is below `2^W`. So `⟦w.drop |b|⟧ = ⟦b⟧ mod 2^W`, and a word of length `W` is the
+numeral of its value (`natToList_length_listToNat`, `natToList_mod_two_pow`). -/
+theorem natToList_zero_append_drop (W : ℕ) (b : List Bool) :
+    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
+  set w := natToList W 0 ++ b with hw
+  have hlen : (w.drop b.length).length = W := by
+    rw [List.length_drop, hw, List.length_append, length_natToList]
+    omega
+  have hval : listToNat w = listToNat b := listToNat_natToList_zero_append W b
+  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
+    conv_lhs => rw [← List.take_append_drop b.length w]
+    rw [listToNat_append, hlen]
+  have hlt := listToNat_lt_two_pow (w.drop b.length)
+  rw [hlen] at hlt
+  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
+    rw [← hval, hsplit, Nat.mul_add_mod_of_lt hlt]
+  rw [← natToList_mod_two_pow, hmod, ← hlen, natToList_length_listToNat]
+
+/-- **The all-ones word** `1^k` reads as `2^k − 1`: `listToNat (1^k) = 2^k − 1`. -/
+theorem listToNat_replicate_true (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1 := by
+  induction k with
+  | zero => rw [List.replicate_zero, listToNat_nil, pow_zero, Nat.sub_self]
+  | succ k ih =>
+    rw [List.replicate_succ', listToNat_append, ih, listToNat_singleton_true,
+      List.length_singleton, pow_succ]
+    have := Nat.one_le_two_pow (n := k)
+    omega
+
+/-- **The all-zeros word** `0^k` reads as `0`: `listToNat (0^k) = 0`. -/
+theorem listToNat_replicate_false (k : ℕ) : listToNat (List.replicate k false) = 0 := by
+  induction k with
+  | zero => rw [List.replicate_zero, listToNat_nil]
+  | succ k ih =>
+    rw [List.replicate_succ, listToNat_cons, ih, if_neg Bool.false_ne_true, zero_mul, add_zero]
+
 /-! ## The string functions of the bundle -/
 
 /-- Binary multiplication: `⟨a, b⟩ ↦ a · b` as an `(|a| + |b|)`-bit numeral (lossless: the
@@ -282,6 +346,14 @@ theorem mulStr_natToList (k l M N : ℕ) (hM : M < 2 ^ k) (hN : N < 2 ^ l) :
   rw [mulStr_pairEncode, length_natToList, length_natToList, listToNat_natToList hM,
     listToNat_natToList hN]
 
+/-- **The product word reads back exactly**: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧` (the product fits in
+`|a| + |b|` bits). -/
+theorem listToNat_mulStr (a b : List Bool) :
+    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b := by
+  rw [mulStr_pairEncode, listToNat_natToList]
+  rw [pow_add]
+  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow a) (listToNat_lt_two_pow b)
+
 /-- `addStr` on an encoded pair. -/
 @[simp] theorem addStr_pairEncode (a b : List Bool) :
     addStr (pairEncode a b) = natToList (a.length + b.length) (listToNat a + listToNat b) := by
@@ -341,6 +413,11 @@ theorem listToNat_subStr (a b : List Bool) :
   rw [subStr_pairEncode]
   exact listToNat_natToList (lt_of_le_of_lt (Nat.sub_le _ _) (listToNat_lt_two_pow a))
 
+/-- **Subtracting a word from itself** gives the zero numeral of its width:
+`subStr ⟨a, a⟩ = ⟦0⟧_{|a|}`. -/
+theorem subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0 := by
+  rw [subStr_pairEncode, Nat.sub_self]
+
 /-- `divModStr` on an encoded pair: `divModStr ⟨a, b⟩ = ⟨⟦a / b⟧_{|a|}, ⟦a mod b⟧_{|b|}⟩`, the
 quotient as an `|a|`-bit and the remainder as a `|b|`-bit numeral (`a / 0 = 0`, `a mod 0 = a`). -/
 theorem divModStr_pairEncode (a b : List Bool) :
@@ -356,6 +433,13 @@ theorem xgcdStr_pairEncode (a b : List Bool) :
   unfold xgcdStr
   rw [pairFstD_pairEncode, pairSndD_pairEncode]
 
+/-- In `Z_0 = ℤ` the inverse of a natural number is its sign, so its value is at most `1`:
+`((e : Z_0)⁻¹).val ≤ 1` (the `N = 0` case of `xgcdStr_pairEncode`'s inverse). -/
+theorem val_inv_natCast_zmod_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1 := by
+  show (Int.sign (e : ℤ)).natAbs ≤ 1
+  rw [Int.natAbs_sign]
+  split_ifs <;> omega
+
 /-- `leStr` on an encoded pair. -/
 @[simp] theorem leStr_pairEncode (a b : List Bool) :
     leStr (pairEncode a b) = [decide (listToNat a ≤ listToNat b)] := by
@@ -370,6 +454,19 @@ theorem xgcdStr_pairEncode (a b : List Bool) :
 /-- `primeStr` is the primality test of `exists_samplePrime_nuppt`. -/
 theorem primeStr_eq : primeStr = fun w : List Bool => [decide (listToNat w).Prime] := rfl
 
+/-- **Comparisons are polynomial-time tests**: for polynomial-time words `a`, `b`, the bit
+`[⟦a x⟧ ≤ ⟦b x⟧]` is polynomial-time (`H.le`, read through `leStr_pairEncode`). -/
+theorem ArithmeticFP.le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
+    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
+    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))] :=
+  (PolyTimeComputable.comp' H.le (ha.pairEncode hb)).congr fun x => leStr_pairEncode (a x) (b x)
+
+/-- **Primality of a polynomial-time word is a polynomial-time test**: for a polynomial-time
+word `a`, the bit `[⟦a x⟧ is prime]` is polynomial-time (`H.prime`, `primeStr_eq`). -/
+theorem ArithmeticFP.prime_poly (H : ArithmeticFP) {a : List Bool → List Bool}
+    (ha : PolyTimeComputable a) : PolyTimeComputable fun x => [decide (listToNat (a x)).Prime] :=
+  (PolyTimeComputable.comp' H.prime ha).congr fun x => congrFun primeStr_eq (a x)
+
 /-- The residue of `x^e` is `x.val^e mod M` for a unit `x` of `Z_M` (any modulus `M ≠ 0`): the
 form in which the evaluators `modExpStr` compute the permutations `x ↦ x^e` and `x ↦ x²`
 (moved from `RSA.lean`, run-3 audit P7-6). -/
diff --git a/TCSlib/Cryptography/Candidates/Concrete.lean b/TCSlib/Cryptography/Candidates/Concrete.lean
index 8dc40a9a..5578b755 100644
--- a/TCSlib/Cryptography/Candidates/Concrete.lean
+++ b/TCSlib/Cryptography/Candidates/Concrete.lean
@@ -79,12 +79,17 @@ The concrete-layer content of the reductions of [PS10, §2.3–§2.4, §2.7] (Th
 * `TCSlib.Cryptography.Candidates.rejectBlocksL_spec`,
   `TCSlib.Cryptography.Candidates.statClose_rejectBlocksL` — accepted values satisfy the
   test; the total sampler is within `(1 − Pr[E])^T` of uniform on `E`.
+* `TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find?` — block rejection sampling as a
+  search followed by the value read.
+* `TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL` — block rejection sampling
+  is polynomial-time (host H15; statement only, its proof is an open fill).
 
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
   (§2.3.1–§2.3.2, Theorem 33.5, Algorithm 33.6; §2.4.2, Claim 36.2, Theorem 36.3,
-  Algorithm 37.4; §2.7, Theorem 51.1.)
+  Algorithm 37.4; §2.7, Theorem 51.1; Theorems 52.3, 53.2, 61.7 and 63.10, the samplers of
+  block rejection sampling.)
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
   draft of 22 January 2026, §2.3 (Theorem 2.1 and Figure 2.2: planting at a uniform
   position).
@@ -550,6 +555,23 @@ theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r :
       else none :=
   rfl
 
+/-- **Block rejection sampling as a search followed by the value read**: `rejectBlocksL E k B T r`
+is the first trial `t < T` whose value `v_t = ⟦(r.drop (t B)).take k⟧` passes `E`, mapped to
+`v_t`:
+`rejectBlocksL E k B T r = ((List.range T).find? fun t => decide (E v_t)).map fun t => v_t`
+(core `List.findSome?_guard`, `List.map_findSome?`, `Option.guard_apply`). -/
+theorem rejectBlocksL_eq_find? (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
+    rejectBlocksL E k B T r =
+      ((List.range T).find? fun t => decide (E (listToNat ((r.drop (t * B)).take k)))).map
+        fun t => listToNat ((r.drop (t * B)).take k) := by
+  rw [rejectBlocksL_eq, ← List.findSome?_guard, List.map_findSome?]
+  congr 1
+  funext t
+  rw [Function.comp_apply, Option.guard_apply]
+  by_cases ht : E (listToNat ((r.drop (t * B)).take k))
+  · rw [if_pos ht, decide_eq_true ht, if_pos rfl, Option.map_some]
+  · rw [if_neg ht, decide_eq_false ht, if_neg Bool.false_ne_true, Option.map_none]
+
 /-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
 bits, `listToNat_lt_two_pow`). -/
 theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
@@ -563,25 +585,62 @@ theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r
   refine ⟨hc, lt_of_lt_of_le (listToNat_lt_two_pow _) ?_⟩
   exact Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _)
 
-/-- Restricting a uniform coin table `I → Bool` along an injection `ι : α → I` gives a uniform
-table `α → Bool`: the restriction is the first projection of the splitting of `I` into the
-image of `ι` and its complement. -/
-private theorem dla_pushesUniform_restrict {α I : Type*} [Fintype α] [DecidableEq α] [Fintype I]
-    [DecidableEq I] {ι : α → I} (hι : Function.Injective ι) :
-    HardcoreBit.PushesUniform (fun R : I → Bool => fun a => R (ι a)) := by
-  classical
-  let e₁ : α ⊕ ((Set.range ι)ᶜ : Set I) ≃ I :=
-    (Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans
-      (Equiv.Set.sumCompl (Set.range ι))
-  let e : (I → Bool) ≃ (α → Bool) × (((Set.range ι)ᶜ : Set I) → Bool) :=
-    (Equiv.arrowCongr e₁.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
-  have he : (fun R : I → Bool => fun a => R (ι a)) = fun R => (e R).1 := by
-    funext R a
-    have h1 : e₁ (Sum.inl a) = ι a := rfl
-    show R (ι a) = R (e₁ (Sum.inl a))
-    rw [h1]
-  rw [he]
-  exact (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
+/-- **Block rejection sampling is polynomial-time** (host H15) [PS10, Theorems 52.3, 53.2, 61.7
+and 63.10: "the domain is easy to sample"]. Let `E a v` be a test on a parameter `a` and a value
+`v`, decided on words by a polynomial-time bit `acc`, so that `acc ⟨w, b⟩ = [E ⟦w⟧ ⟦b⟧]`. Take
+polynomial-time words `par z` (the parameter), `kw z`, `bw z` and `tw z`, whose lengths are the
+trial width `k`, the block length `B` and the trial count `T`, and `c z` (the coins). Then some
+polynomial-time `g` computes the sampler `rejectBlocksL (E ⟦par z⟧) k B T (c z)`:
+- `g z = []` when every trial is rejected;
+- otherwise `g z = true :: b`, where `b` reads as the accepted value and has at most `k` bits.
+
+That is, `(g z).tail.length ≤ k` and
+`rejectBlocksL (E ⟦par z⟧) k B T (c z) = if g z = [] then none else some ⟦(g z).tail⟧`.
+In particular `(rejectBlocksL …).getD 0 = ⟦(g z).tail⟧`, since `[].tail = []` reads as `0`
+(`listToNat_nil`). The statement is existential: the trial loop that realizes it is internal,
+and no consumer reads it.
+
+**Deviation:** [PS10] samples these domains exactly, in expected polynomial time; here the
+sampler is truncated to `T` trials (deviations register #15, `statClose_rejectBlocksL` carries
+the statistical term), and the host states only the polynomial-time computability of that
+truncated sampler on strings.
+
+**Proof sketch.**
+- **The loop.** The state is `⟨⟨⟨1^B, 1^k⟩, w⟩, ⟨1^T, r⟩⟩`, with `w = par z` and `r = c z`. One
+  step keeps the header `⟨⟨1^B, 1^k⟩, w⟩`, drops one bit of the counter `1^T` and one block of
+  `B` coins (`polyTimeComputable_tail`, `polyTimeComputable_pairDropPoly`). The trial word is
+  the first `k` coins (`polyTimeComputable_pairTakePoly`). The test accepts iff the counter is
+  nonempty and `acc ⟨w, trial word⟩` holds (`polyTimeComputable_isNil`, `polyTimeComputable_not`,
+  `polyTimeComputable_and`, with the tests given explicitly). The payload is `true` followed by
+  the trial word (`polyTimeComputable_prepend`). The start state is assembled from the given
+  words (`polyTimeComputable_unaryPoly`, or `List.replicate` of the lengths, and
+  `PolyTimeComputable.pairEncode`), and `g` is the loop on it, in applied form
+  (`PolyTimeComputable.comp'`).
+- **Polynomial time.** One step at most doubles the length (`|step x| ≤ 2|x| + 4`), and from the
+  second step on the state is a well-formed pair that only shrinks
+  (`StateLoop.length_pairFstD_add_pairSndD_le`), so every orbit point has length at most
+  `2|x| + 4`. The repetition host `Complexity.polyTimeComputable_iterateFind`, with `R = var` and
+  orbit bound `2n + 4`, therefore makes the loop polynomial-time. Its `match` on the search
+  result is split by `split` (its equation lemmas), never matched by definitional unfolding.
+- **Correctness.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (i B)⟩⟩` (induction on
+  `i`, `List.drop_drop`), so trial `i` reads the `k`-bit prefix `v_i = ⟦(r.drop (i B)).take k⟧`
+  of block `i`, and the test at step `i` is `i < T ∧ E ⟦w⟧ v_i` (`hspec`). The search over the
+  first `|start| + 1 ≥ T` rounds is therefore the search over `[0, T)`
+  (`IterateFind.find?_range_and_lt`), which is `rejectBlocksL` read as a search followed by its
+  value (`rejectBlocksL_eq_find?`). If the search fails, `g z = []`; otherwise
+  `g z = true :: trial word`, whose tail has at most `k` bits (`List.length_take_le`) and reads
+  as the accepted value. -/
+theorem polyTimeComputable_rejectBlocksL (E : ℕ → ℕ → Prop) [∀ a, DecidablePred (E a)]
+    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun x => [acc x])
+    (hspec : ∀ w b : List Bool, acc (pairEncode w b) = decide (E (listToNat w) (listToNat b)))
+    {par kw bw tw c : List Bool → List Bool} (hpar : PolyTimeComputable par)
+    (hkw : PolyTimeComputable kw) (hbw : PolyTimeComputable bw) (htw : PolyTimeComputable tw)
+    (hc : PolyTimeComputable c) :
+    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z,
+      (g z).tail.length ≤ (kw z).length ∧
+      rejectBlocksL (E (listToNat (par z))) (kw z).length (bw z).length (tw z).length (c z) =
+        if g z = [] then none else some (listToNat (g z).tail) := by
+  sorry
 
 /-- The position of bit `j < k` of block `t < T` in a string of `T · B` coins (`k ≤ B`):
 `t · B + j`. -/
@@ -655,7 +714,8 @@ theorem statClose_rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : 
   let π : (Fin (T * B) → Bool) → Fin T → Fin (2 ^ k) :=
     fun r t => bitsEquiv k (fun j => r (dla_blockPos hkB (t, j)))
   have hπ : HardcoreBit.PushesUniform π := by
-    have h1 := dla_pushesUniform_restrict (dla_blockPos_injective (T := T) hkB)
+    have h1 :=
+      HardcoreBit.pushesUniform_restrict (O := Bool) (dla_blockPos_injective (T := T) hkB)
     have h2 := HardcoreBit.pushesUniform_equiv
       ((Equiv.curry (Fin T) (Fin k) Bool).trans (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k))
     exact h1.comp h2
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 2b96a128..5beedf81 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -613,12 +613,7 @@ theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
   have hkn : Nat.size m ≤ n := Nat.size_le.2 hmn
   have hmk : m < 2 ^ Nat.size m := Nat.lt_size_self m
   -- `2^k ≤ 2m`: the top bit of `m` is bit `k − 1`
-  have hk2 : 2 ^ Nat.size m ≤ 2 * m := by
-    have hpos : 0 < Nat.size m := Nat.size_pos.2 hm
-    have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (Nat.sub_lt hpos one_pos)
-    calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
-          rw [← pow_succ', Nat.sub_add_cancel hpos]
-      _ ≤ 2 * m := Nat.mul_le_mul_left 2 h1
+  have hk2 : 2 ^ Nat.size m ≤ 2 * m := two_pow_size_le_two_mul hm
   -- the block sampler with the test `v < m` and the default `0`
   have h := statClose_rejectBlocksL (· < m) (Nat.size m) n n hkn (d := 0) hm
     (Nat.pow_pos two_pos)
@@ -652,86 +647,6 @@ def expSampleRaw (z : List Bool) : List Bool :=
 
 /-! ### The domain sampler as a trial loop (helpers of `polyTimeComputable_expSampleRaw`) -/
 
-/-- The number read from `a ++ b` is `⟦a⟧ · 2^{|b|} + ⟦b⟧` (most significant bit first). -/
-private theorem dla_listToNat_append (a b : List Bool) :
-    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
-  have key : ∀ (l : List Bool) (acc : ℕ),
-      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
-        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
-    intro l
-    induction l with
-    | nil => intro acc; simp
-    | cons c l ih =>
-      intro acc
-      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
-      ring
-  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]
-
-/-- The empty numeral reads as `0`. -/
-private theorem dla_listToNat_nil : listToNat [] = 0 := by
-  rw [listToNat_eq]
-  rfl
-
-/-- **Width normalization**: prefixing the `W`-bit numeral of `0` and keeping the last `W`
-bits gives the `W`-bit numeral of the number read from `b`:
-`(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`. -/
-private theorem dla_drop_natToList_zero_append (W : ℕ) (b : List Bool) :
-    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
-  set w := natToList W 0 ++ b with hw
-  have hlen : (w.drop b.length).length = W := by
-    rw [List.length_drop, hw, List.length_append, length_natToList]
-    omega
-  have hval : listToNat w = listToNat b := by
-    rw [hw, dla_listToNat_append, listToNat_natToList (Nat.two_pow_pos W), zero_mul, zero_add]
-  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
-    conv_lhs => rw [← List.take_append_drop b.length w]
-    rw [dla_listToNat_append, hlen]
-  have hlt := listToNat_lt_two_pow (w.drop b.length)
-  rw [hlen] at hlt
-  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
-    rw [← hval, hsplit, Nat.mul_add_mod_of_lt hlt]
-  have hnum : ∀ N : ℕ, natToList W N = natToList W (N % 2 ^ W) := fun N => by
-    have h := natToList_length_listToNat (natToList W N)
-    rw [length_natToList, listToNat_natToList_eq_mod] at h
-    exact h.symm
-  rw [hnum, hmod, ← hlen, natToList_length_listToNat]
-
-/-- `List.findSome?` of a filter-and-map is `List.find?` followed by the map. -/
-private theorem dla_findSome?_ite {α β : Type*} (p : α → Prop) [DecidablePred p] (h : α → β)
-    (l : List α) :
-    l.findSome? (fun t => if p t then some (h t) else none) = (l.find? fun t => decide (p t)).map h := by
-  induction l with
-  | nil => rfl
-  | cons a l ih =>
-    rw [List.findSome?_cons, List.find?_cons]
-    by_cases ha : p a
-    · rw [if_pos ha, decide_eq_true ha]
-      rfl
-    · rw [if_neg ha, decide_eq_false ha, ih]
-
-/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`, for
-`N ≤ L`. -/
-private theorem dla_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
-    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
-  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
-      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
-    intro l
-    induction l with
-    | nil => intro _; rfl
-    | cons a l ih =>
-      intro hl
-      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
-        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
-  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
-  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
-  have hnone : (List.map (fun x => N + x) (List.range d)).find?
-      (fun i => decide (i < N) && p i) = none := by
-    rw [List.find?_eq_none]
-    intro x hx
-    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
-    simp
-  rw [hnone, Option.or_none]
-
 /-- The start state of the trial loop on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`:
 `⟨⟨1^n, ⟨1^k, ⟦m⟧⟩⟩, ⟨1^n, r⟩⟩` with `⟦m⟧` the middle numeral of `i` and `1^k = sizeStr ⟦m⟧`
 its bit length (the header, then the trial counter and the remaining coins). -/
@@ -846,10 +761,11 @@ read from the loop's payload (marker dropped) is `sampleBelowL m k n n r` with t
 **Proof sketch.** After `i` steps the header is unchanged, the counter `1^n` has lost `i` bits
 and the coins have lost `i` blocks of `n` bits (`dla_ssStep_iterate`): the trial value is the
 `k`-bit prefix of block `i`, and the test accepts iff `i < n` and that value is below `m`. The search over the
-first `|start| + 1 ≥ n` rounds is therefore the search over `[0, n)` (`dla_find?_range_lt`),
-which is `sampleBelowL`'s `findSome?` read as a `find?` followed by the value
-(`dla_findSome?_ite`). In the `some i` case the payload with its marker dropped is the prefix of
-block `i`; in the `none` case both sides read `0` (`dla_listToNat_nil`). -/
+first `|start| + 1 ≥ n` rounds is therefore the search over `[0, n)`
+(`IterateFind.find?_range_and_lt`), which is `sampleBelowL` read as a `find?` followed by the
+value (`sampleBelowL_eq_rejectBlocksL`, `rejectBlocksL_eq_find?`). In the `some i` case the
+payload with its marker dropped is the prefix of block `i`; in the `none` case both sides read `0`
+(`listToNat_nil`). -/
 private theorem dla_ssFind_eq (z : List Bool) :
     listToNat ((match (List.range ((dla_ssStart z).length + 1)).find?
         (fun i => dla_ssAcc (dla_ssStep^[i] (dla_ssStart z))) with
@@ -890,15 +806,13 @@ private theorem dla_ssFind_eq (z : List Bool) :
       (List.range u.length).find? (fun i => decide (val i < listToNat ms)) := by
     rw [show (fun i => dla_ssAcc (dla_ssStep^[i] (dla_ssStart z))) =
       fun i => decide (i < u.length) && decide (val i < listToNat ms) from funext hacc]
-    exact dla_find?_range_lt _ hrange
+    exact IterateFind.find?_range_and_lt _ hrange
   have hsample : sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z))) u.length u.length c =
       ((List.range u.length).find? (fun i => decide (val i < listToNat ms))).map val := by
-    rw [hm]
-    unfold sampleBelowL
-    exact dla_findSome?_ite (fun i => val i < listToNat ms) val _
+    rw [hm, sampleBelowL_eq_rejectBlocksL, rejectBlocksL_eq_find?]
   rw [hfind, hsample]
   rcases hf : (List.range u.length).find? (fun i => decide (val i < listToNat ms)) with _ | i
-  · exact dla_listToNat_nil
+  · exact listToNat_nil
   · show listToNat ((dla_ssOut (dla_ssStep^[i] (dla_ssStart z))).drop 1) = val i
     rw [dla_ssOut, List.singleton_append, List.drop_one, List.tail_cons, hblock]
 
@@ -945,7 +859,7 @@ theorem polyTimeComputable_expSampleRaw (H : ArithmeticFP) : PolyTimeComputable
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hq
   simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
     subStr_pairEncode, Nat.sub_self]
-  rw [dla_drop_natToList_zero_append]
+  rw [natToList_zero_append_drop]
   unfold expSampleRaw dlW
   congr 1
   have hF := dla_ssFind_eq z
@@ -1135,18 +1049,6 @@ theorem expCollection_D {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGrou
     (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
     (expCollection H G hV).D i = ZMod (expOrd i) := rfl
 
-/-- Any two samplers are `1`-close (probabilities lie in `[0, 1]`). -/
-private theorem dla_statClose_one {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) :
-    StatClose X Y 1 := by
-  rw [statClose_iff]
-  intro T
-  have h1 := uprob_nonneg (fun s => T (X s))
-  have h2 := uprob_le_one (fun s => T (X s))
-  have h3 := uprob_nonneg (fun t => T (Y t))
-  have h4 := uprob_le_one (fun t => T (Y t))
-  rw [abs_le]
-  constructor <;> linarith
-
 /-- **The decoded domain sampler is `(1/2)^n`-close to uniform on `Z_m`** at a valid index of
 width `n`: `statClose_sampleBelowL` on the sampler's `n · n` coins (read through
 `NUPPT.coinsEquivPoly`), mapped through the decoder, which reads the numeral back exactly.
@@ -1227,7 +1129,7 @@ theorem expCollection_sampleClose {V : List Bool → Prop} (H : ArithmeticFP) (G
     intro n r
     by_cases hn : n < G.n₀
     · rw [if_pos hn]
-      exact dla_statClose_one _ _
+      exact statClose_one _ _
     rw [if_neg hn]
     have hn' : G.n₀ ≤ n := not_lt.1 hn
     -- the generated index is valid and of width `n`
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
index 2c0e56f5..9a705a4c 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
@@ -990,11 +990,6 @@ its success at one good instance by `invProb_dlInverter_ge` minus the sampling l
 
 /-! ### Numeral arithmetic of the inverter machine -/
 
-/-- Composition of polynomial-time maps in applied form. -/
-private theorem dlb_ptc {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
-    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
-  hg.comp hf
-
 /-- The numeral `⟦1⟧_1`. -/
 private def dlb_one : List Bool := natToList 1 1
 /-- The numeral `⟦2⟧_2`. -/
@@ -1027,23 +1022,23 @@ variable {fa fb fc : List Bool → List Bool}
 
 private theorem dlb_mulMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb)
     (hc : PolyTimeComputable fc) : PolyTimeComputable fun z => dlb_mulMod (fa z) (fb z) (fc z) :=
-  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.divMod ((dlb_ptc H.mul (ha.pairEncode hb)).pairEncode hc))
+  PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod ((PolyTimeComputable.comp' H.mul (ha.pairEncode hb)).pairEncode hc))
 
 private theorem dlb_powMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb)
     (hc : PolyTimeComputable fc) : PolyTimeComputable fun z => dlb_powMod (fa z) (fb z) (fc z) :=
-  dlb_ptc H.modExp (ha.pairEncode (hb.pairEncode hc))
+  PolyTimeComputable.comp' H.modExp (ha.pairEncode (hb.pairEncode hc))
 
 private theorem dlb_invMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
     PolyTimeComputable fun z => dlb_invMod (fa z) (fb z) :=
-  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.xgcd (ha.pairEncode hb))
+  PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.xgcd (ha.pairEncode hb))
 
 private theorem dlb_quot_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
     PolyTimeComputable fun z => dlb_quot (fa z) (fb z) :=
-  dlb_ptc polyTimeComputable_pairFstD (dlb_ptc H.divMod (ha.pairEncode hb))
+  PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' H.divMod (ha.pairEncode hb))
 
 private theorem dlb_rem_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
     PolyTimeComputable fun z => dlb_rem (fa z) (fb z) :=
-  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.divMod (ha.pairEncode hb))
+  PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (ha.pairEncode hb))
 
 end Poly
 
@@ -1087,20 +1082,20 @@ end Sem
 
 private theorem dlb_take_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
     (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => (fb z).take (fa z).length := by
-  have h := dlb_ptc (polyTimeComputable_pairTakePoly .var) (ha.pairEncode hb)
+  have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly .var) (ha.pairEncode hb)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
 
 private theorem dlb_drop_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
     (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => (fb z).drop (fa z).length := by
-  have h := dlb_ptc (polyTimeComputable_pairDropPoly .var) (ha.pairEncode hb)
+  have h := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var) (ha.pairEncode hb)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
 
 /-- A one-bit equality test of two polynomial-time maps (`polyTimeComputable_pairEq`). -/
 private theorem dlb_eq_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
     (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => [decide (fa z = fb z)] := by
-  have h := dlb_ptc polyTimeComputable_pairEq (ha.pairEncode hb)
+  have h := PolyTimeComputable.comp' polyTimeComputable_pairEq (ha.pairEncode hb)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   simp only [pairFstD_pairEncode, pairSndD_pairEncode]
 
@@ -1123,7 +1118,7 @@ private theorem dlb_stateIterate_poly {start step : List Bool → List Bool}
   have hF := polyTimeComputable_iterate (StateLoop.gstep_poly hstep B) .var (StateLoop.gstepBound B)
     (fun w i _ => StateLoop.length_gstep_iterate_le step B w i)
   refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp
-    (dlb_ptc polyTimeComputable_pairSndD (dlb_ptc hF (polyTimeComputable_id.pairEncode hstart)))
+    (PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' hF (polyTimeComputable_id.pairEncode hstart)))
   simp only [PolyExpr.eval_var, id_eq]
 
 /-! ### The fixed data of the inverter's loops -/
@@ -1208,19 +1203,19 @@ private theorem dlb_vote_poly (H : ArithmeticFP) {ff fr fs fa : List Bool → Li
     (hf : PolyTimeComputable ff) (hr : PolyTimeComputable fr) (hs : PolyTimeComputable fs)
     (ha : PolyTimeComputable fa) :
     PolyTimeComputable fun z => [dlb_vote S A (ff z) (fr z) (fs z) (fa z)] := by
-  have hu := dlb_ptc dlb_fu_poly hf
-  have hi := dlb_ptc dlb_fi_poly hf
+  have hu := PolyTimeComputable.comp' dlb_fu_poly hf
+  have hi := PolyTimeComputable.comp' dlb_fi_poly hf
   have hw : PolyTimeComputable fun z => dlb_wS S (ff z) (fs z) :=
-    dlb_ptc S.polyTimeComputable_output
+    PolyTimeComputable.comp' S.polyTimeComputable_output
       (NUPPT.polyTimeComputable_layout hu hi (polyTimeComputable_const []) hs)
   have hzz : PolyTimeComputable fun z => dlb_zz S (ff z) (fr z) (fs z) :=
-    dlb_mulMod_poly H hr (dlb_powMod_poly H (dlb_ptc dlb_fg_poly hf) hw (dlb_ptc dlb_fp_poly hf))
-      (dlb_ptc dlb_fp_poly hf)
-  have hout := dlb_ptc A.polyTimeComputable_output
-    (NUPPT.polyTimeComputable_layout hu (hi.pairEncode hzz) (dlb_ptc dlb_fα_poly hf) ha)
+    dlb_mulMod_poly H hr (dlb_powMod_poly H (PolyTimeComputable.comp' dlb_fg_poly hf) hw (PolyTimeComputable.comp' dlb_fp_poly hf))
+      (PolyTimeComputable.comp' dlb_fp_poly hf)
+  have hout := PolyTimeComputable.comp' A.polyTimeComputable_output
+    (NUPPT.polyTimeComputable_layout hu (hi.pairEncode hzz) (PolyTimeComputable.comp' dlb_fα_poly hf) ha)
   have hab : PolyTimeComputable fun z => [dlb_aBit S A (ff z) (fr z) (fs z) (fa z)] :=
     dlb_eq_poly hout (polyTimeComputable_const [true])
-  have hh := dlb_ptc (polyTimeComputable_halfStr H) (hi.pairEncode hw)
+  have hh := PolyTimeComputable.comp' (polyTimeComputable_halfStr H) (hi.pairEncode hw)
   exact dlb_eq_poly hab hh
 
 end Trial
@@ -1273,17 +1268,17 @@ private theorem dlb_iStep_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_iSte
     polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
   have hV : PolyTimeComputable dlb_iVotes :=
     polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
-  have hS : PolyTimeComputable dlb_iSB := dlb_take_poly (dlb_ptc dlb_fuS_poly hF) hCs
-  have hCs1 : PolyTimeComputable dlb_iCs1 := dlb_drop_poly (dlb_ptc dlb_fuS_poly hF) hCs
-  have hA : PolyTimeComputable dlb_iAB := dlb_take_poly (dlb_ptc dlb_fuA_poly hF) hCs1
-  have hRest : PolyTimeComputable dlb_iRest := dlb_drop_poly (dlb_ptc dlb_fuA_poly hF) hCs1
+  have hS : PolyTimeComputable dlb_iSB := dlb_take_poly (PolyTimeComputable.comp' dlb_fuS_poly hF) hCs
+  have hCs1 : PolyTimeComputable dlb_iCs1 := dlb_drop_poly (PolyTimeComputable.comp' dlb_fuS_poly hF) hCs
+  have hA : PolyTimeComputable dlb_iAB := dlb_take_poly (PolyTimeComputable.comp' dlb_fuA_poly hF) hCs1
+  have hRest : PolyTimeComputable dlb_iRest := dlb_drop_poly (PolyTimeComputable.comp' dlb_fuA_poly hF) hCs1
   have hvote := dlb_vote_poly S A H hF hR hS hA
-  have hnil := dlb_ptc polyTimeComputable_isNil hC
-  have hnew := (dlb_ptc StateLoop.tail_poly hC).pairEncode (hRest.pairEncode (hvote.append hV))
+  have hnil := PolyTimeComputable.comp' polyTimeComputable_isNil hC
+  have hnew := (PolyTimeComputable.comp' StateLoop.tail_poly hC).pairEncode (hRest.pairEncode (hvote.append hV))
   exact dlb_ite_poly hnil polyTimeComputable_pairSndD hnew
 
 private theorem dlb_iStart_poly : PolyTimeComputable dlb_iStart :=
-  (dlb_ptc dlb_fuL_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
+  (PolyTimeComputable.comp' dlb_fuL_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
     (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))
 
 private theorem dlb_inner_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_inner S A) :=
@@ -1357,46 +1352,46 @@ private theorem dlb_oCs_poly : PolyTimeComputable dlb_oCs := polyTimeComputable_
 
 private theorem dlb_oQr_poly (H : ArithmeticFP) : PolyTimeComputable fun W => [dlb_oQr W] := by
   have hE : PolyTimeComputable dlb_oEul :=
-    dlb_powMod_poly H dlb_oY_poly (dlb_ptc dlb_feH_poly dlb_oF_poly) (dlb_ptc dlb_fp_poly dlb_oF_poly)
-  have hq1 := dlb_ptc polyTimeComputable_headD
-    (dlb_ptc H.le (hE.pairEncode (polyTimeComputable_const dlb_one)))
-  have hq2 := dlb_ptc polyTimeComputable_headD
-    (dlb_ptc H.le ((polyTimeComputable_const dlb_one).pairEncode hE))
+    dlb_powMod_poly H dlb_oY_poly (PolyTimeComputable.comp' dlb_feH_poly dlb_oF_poly) (PolyTimeComputable.comp' dlb_fp_poly dlb_oF_poly)
+  have hq1 := PolyTimeComputable.comp' polyTimeComputable_headD
+    (PolyTimeComputable.comp' H.le (hE.pairEncode (polyTimeComputable_const dlb_one)))
+  have hq2 := PolyTimeComputable.comp' polyTimeComputable_headD
+    (PolyTimeComputable.comp' H.le ((polyTimeComputable_const dlb_one).pairEncode hE))
   exact polyTimeComputable_and hq1 hq2
 
 private theorem dlb_oRoot_poly (H : ArithmeticFP) : PolyTimeComputable dlb_oRoot := by
-  have hp := dlb_ptc dlb_fp_poly dlb_oF_poly
+  have hp := PolyTimeComputable.comp' dlb_fp_poly dlb_oF_poly
   have hQ : PolyTimeComputable fun W => [decide (dlb_oQr W = true)] := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (dlb_oQr_poly H)
     simp only [Bool.decide_eq_true]
   have hBase : PolyTimeComputable dlb_oBase :=
     dlb_ite_poly (c := fun W => dlb_oQr W = true) hQ dlb_oY_poly
-      (dlb_mulMod_poly H dlb_oY_poly (dlb_ptc dlb_fgI_poly dlb_oF_poly) hp)
-  exact dlb_powMod_poly H hBase (dlb_ptc dlb_feR_poly dlb_oF_poly) hp
+      (dlb_mulMod_poly H dlb_oY_poly (PolyTimeComputable.comp' dlb_fgI_poly dlb_oF_poly) hp)
+  exact dlb_powMod_poly H hBase (PolyTimeComputable.comp' dlb_feR_poly dlb_oF_poly) hp
 
 private theorem dlb_oFin_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oFin S A) := by
-  have h := dlb_ptc (dlb_inner_poly S A H) ((dlb_oF_poly.pairEncode (dlb_oRoot_poly H)).pairEncode
+  have h := PolyTimeComputable.comp' (dlb_inner_poly S A H) ((dlb_oF_poly.pairEncode (dlb_oRoot_poly H)).pairEncode
     dlb_oCs_poly)
   unfold dlb_oFin
   exact h
 
 private theorem dlb_oNext_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oNext S A) := by
   have hV : PolyTimeComputable fun W => pairSndD (pairSndD (dlb_oFin S A W)) :=
-    dlb_ptc polyTimeComputable_pairSndD (dlb_ptc polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
-  have hB := dlb_ptc polyTimeComputable_majority hV
+    PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
+  have hB := PolyTimeComputable.comp' polyTimeComputable_majority hV
   have hB' : PolyTimeComputable fun W => [decide (dlb_oB S A W = true)] := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hB
     simp only [dlb_oB, dlb_oVotes, Bool.decide_eq_true]
   exact dlb_ite_poly (c := fun W => dlb_oB S A W = true) hB' (dlb_oRoot_poly H)
-    (dlb_ptc H.sub ((dlb_ptc dlb_fp_poly dlb_oF_poly).pairEncode (dlb_oRoot_poly H)))
+    (PolyTimeComputable.comp' H.sub ((PolyTimeComputable.comp' dlb_fp_poly dlb_oF_poly).pairEncode (dlb_oRoot_poly H)))
 
 private theorem dlb_oStep_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oStep S A) := by
-  have hnil := dlb_ptc polyTimeComputable_isNil dlb_oCnt_poly
+  have hnil := PolyTimeComputable.comp' polyTimeComputable_isNil dlb_oCnt_poly
   have hnq := polyTimeComputable_not (dlb_oQr_poly H)
-  have hcs := dlb_ptc polyTimeComputable_pairFstD
-    (dlb_ptc polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
+  have hcs := PolyTimeComputable.comp' polyTimeComputable_pairFstD
+    (PolyTimeComputable.comp' polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
   have hnew := (dlb_oNext_poly S A H).pairEncode ((hnq.append dlb_oAcc_poly).pairEncode
-    ((dlb_ptc StateLoop.tail_poly dlb_oCnt_poly).pairEncode hcs))
+    ((PolyTimeComputable.comp' StateLoop.tail_poly dlb_oCnt_poly).pairEncode hcs))
   exact dlb_ite_poly hnil polyTimeComputable_pairSndD hnew
 
 private theorem dlb_outer_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_outer S A) :=
@@ -1477,11 +1472,11 @@ private theorem dlb_zfix_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_zfix
   have hu := NUPPT.polyTimeComputable_inParam
   have hun : ∀ P : PolyExpr,
       PolyTimeComputable fun z => List.replicate (P.eval (NUPPT.inParam z).length) true :=
-    fun P => dlb_ptc (polyTimeComputable_unaryPoly P) hu
+    fun P => PolyTimeComputable.comp' (polyTimeComputable_unaryPoly P) hu
   have h := (hu.pairEncode (dlb_zi_poly.pairEncode dlb_zα_poly)).pairEncode
     (((dlb_invMod_poly H dlb_zg_poly dlb_zp_poly).pairEncode
       ((dlb_quot_poly H (dlb_zpm1_poly H) (polyTimeComputable_const dlb_two)).pairEncode
-        (dlb_ptc H.add ((dlb_quot_poly H dlb_zp_poly (polyTimeComputable_const dlb_four)).pairEncode
+        (PolyTimeComputable.comp' H.add ((dlb_quot_poly H dlb_zp_poly (polyTimeComputable_const dlb_four)).pairEncode
           (polyTimeComputable_const dlb_one))))).pairEncode
       ((hun S.coins).pairEncode ((hun A.coins).pairEncode (hun ℓP))))
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
@@ -1495,13 +1490,13 @@ private theorem dlb_zs0_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zs0 :=
   simp only [dlb_zs0]
 
 private theorem dlb_zacc_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_zacc S A ℓP) := by
-  have h := dlb_ptc polyTimeComputable_pairFstD (dlb_ptc polyTimeComputable_pairSndD
-    (dlb_ptc (dlb_outer_poly S A H) ((dlb_zfix_poly S A ℓP H).pairEncode (dlb_zs0_poly H))))
+  have h := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' polyTimeComputable_pairSndD
+    (PolyTimeComputable.comp' (dlb_outer_poly S A H) ((dlb_zfix_poly S A ℓP H).pairEncode (dlb_zs0_poly H))))
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   simp only [dlb_zacc]
 
 private theorem dlb_raw_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_raw S A ℓP) := by
-  have h := dlb_rem_poly H (dlb_ptc H.add ((dlb_zacc_poly S A ℓP H).pairEncode (dlb_zts_poly H)))
+  have h := dlb_rem_poly H (PolyTimeComputable.comp' H.add ((dlb_zacc_poly S A ℓP H).pairEncode (dlb_zts_poly H)))
     (dlb_zpm1_poly H)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   simp only [dlb_raw]
@@ -1947,22 +1942,6 @@ end RoundSem
 
 /-! ### Bits and counts -/
 
-private theorem dlb_foldl_bits (l : List Bool) (a : ℕ) :
-    l.foldl (fun a c => 2 * a + if c then 1 else 0) a =
-      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := by
-  induction l generalizing a with
-  | nil => simp
-  | cons b l ih =>
-    simp only [List.foldl_cons, List.length_cons]
-    rw [ih, ih (2 * 0 + _)]
-    ring
-
-/-- Prepending a bit to a numeral (most significant first): `⟦b :: l⟧ = b·2^{|l|} + ⟦l⟧`. -/
-private theorem dlb_listToNat_cons (b : Bool) (l : List Bool) :
-    listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l := by
-  rw [listToNat_eq, listToNat_eq, List.foldl_cons, dlb_foldl_bits]
-  simp
-
 /-- The number of `true`s in `List.ofFn v` is the number of indices where `v` is `true`. -/
 private theorem dlb_count_ofFn {M : ℕ} (v : Fin M → Bool) :
     (List.ofFn v).count true = #(univ.filter fun j : Fin M => v j = true) := by
@@ -2168,13 +2147,13 @@ private theorem dlb_roundsL_succ {S A : NUPPT} {n ℓ k : ℕ} (c : Fin (k + 1)
 
 /-- **The machine's rounds are the rounds of `dlLoop`**: after `k` rounds on `k` round blocks
 whose sampler blocks all decode, the bits read `dlLoop g (majOracle g A_i ℓ) k y c·2^{|acc|} + ⟦acc⟧`
-(induction on `k`, `dlb_oStep_round`, `dlLoop_succ`, `dlb_listToNat_cons`).
+(induction on `k`, `dlb_oStep_round`, `dlLoop_succ`, `listToNat_cons`).
 
 **Proof sketch.** Induction on `k`; nothing runs at `k = 0`. At `k + 1` the round
 coins are the first round's blocks followed by the others (`dlb_roundsL_succ`); one round
 (`dlb_oStep_round`) moves to `±dlRoot g y` as `majOracle` decides and prepends the parity bit
 `[y ∉ QR_p]` to `acc`. The induction hypothesis on the other `k` rounds, `dlLoop_succ` and
-`⟦b :: acc⟧ = b · 2^{|acc|} + ⟦acc⟧` (`dlb_listToNat_cons`) give the claim. -/
+`⟦b :: acc⟧ = b · 2^{|acc|} + ⟦acc⟧` (`listToNat_cons`) give the claim. -/
 private theorem dlb_loop_sem (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hodd : ℓ % 2 = 1)
     (hfu : dlb_fu f = List.replicate n true) (hfi : dlb_fi f = i) (hfα : dlb_fα f = A.advice n)
     (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
@@ -2199,7 +2178,7 @@ private theorem dlb_loop_sem (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hodd : ℓ % 2 =
     obtain ⟨yv, acc', h1, h2⟩ := dlb_loop_sem hp2 hpn hodd hfu hfi hfα hiP hiG hW hg hS hA hL hfeH hfeR
       hfgI s0 rest k _ ((!decide (y ∈ QR p)) :: acc) (fun j => c j.succ) (fun j => hdec j.succ)
     refine ⟨yv, acc', h1, ?_⟩
-    rw [h2, dlLoop_succ, dlb_listToNat_cons, List.length_cons, pow_succ]
+    rw [h2, dlLoop_succ, listToNat_cons, List.length_cons, pow_succ]
     by_cases hq : y ∈ QR p
     · simp only [hq, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
       ring
@@ -2713,18 +2692,6 @@ end Instance
 
 /-! ### Parameters for large `n` -/
 
-/-- `2^{Nat.size m} ≤ 2m` for `m ≥ 1`. -/
-private theorem dlb_two_pow_size_le {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m := by
-  have h := Nat.size_pos.2 hm
-  have h1 : 2 ^ (Nat.size m - 1) ≤ m := by
-    by_contra hlt
-    push_neg at hlt
-    have := Nat.size_le.2 hlt
-    omega
-  calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
-        rw [← pow_succ']; congr 1; omega
-    _ ≤ 2 * m := by omega
-
 /-- **The window parameters** of the reduction: for `P = p − 1 ≥ 16 n^c`, `s = ⌊P/(8n^c)⌋` and
 `T = 2^{Nat.size (16 n^c)} > 16 n^c` satisfy `s ≥ 1`, `4s ≤ P/(2n^c)` and `P ≤ T s`. -/
 private theorem dlb_window_params (c n P : ℕ) (hn : 0 < n) (h2D : 16 * n ^ c ≤ P) :
@@ -2835,7 +2802,7 @@ success to `G.gen`'s coins (`fullDLCollection_index`, `fullDLCollection_coinsEqu
 `good_instances` (with `2ε'`) and `hbig` (`ExpGroupGen.fullLengthExcept_iff`, `uprob_or_le`) the
 coins with success `≥ 1/2 + ε'` and `p ≥ 2^{n−1}` have probability `≥ ε'/2`. On each of them
 `16n^c ≤ p − 1`, so `dlb_window_params` gives the window, and `dlb_instance` with
-`dlb_arith_success` (`2^κ ≤ 32n^c`, `dlb_two_pow_size_le`) bounds `B`'s success below by
+`dlb_arith_success` (`2^κ ≤ 32n^c`, `two_pow_size_le_two_mul`) bounds `B`'s success below by
 `3/(128n^c) − n·ℓ·δ_S(n)`. `HardcoreBit.uprob_mul_le_uexp` averages over the good set, and
 `dlb_arith_loss` with `dlb_arith_final` give `3/(1024 n^{2c})` (`ExpGroupGen.dlProb_eq`). -/
 private theorem dlb_reduction (H : ArithmeticFP) (G : FullGroupGen)
@@ -2962,7 +2929,7 @@ private theorem dlb_reduction (H : ArithmeticFP) (G : FullGroupGen)
     refine le_trans ?_ h
     have hT0 : (0 : ℝ) < ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) := by positivity
     have hT32 : ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) ≤ 32 * X := by
-      have := dlb_two_pow_size_le (by omega : 0 < 16 * n ^ c)
+      have := two_pow_size_le_two_mul (by omega : 0 < 16 * n ^ c)
       have h' : ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) ≤ ((2 * (16 * n ^ c) : ℕ) : ℝ) := by exact_mod_cast this
       push_cast at h' ⊢; rw [hXdef]; linarith
     have := dlb_arith_success hX1 (by linarith : (1 : ℝ) ≤ n) hℓR hT0 hT32
diff --git a/TCSlib/Cryptography/Candidates/ElGamal.lean b/TCSlib/Cryptography/Candidates/ElGamal.lean
index e4fec92d..e796aea8 100644
--- a/TCSlib/Cryptography/Candidates/ElGamal.lean
+++ b/TCSlib/Cryptography/Candidates/ElGamal.lean
@@ -596,62 +596,6 @@ operations (lossless at the widths used here), under a polynomial-time `if`, and
 rejection sampler `sampleBelowL` (a trial loop, `Complexity.polyTimeComputable_iterateFind`);
 `dlc_poly_natToList` writes such a number as a numeral of a given width. -/
 
-/-- The empty numeral reads as `0`. -/
-private theorem dlc_listToNat_nil : listToNat [] = 0 := by
-  rw [listToNat_eq]
-  rfl
-
-/-- The number read from `a ++ b` is `⟦a⟧ · 2^{|b|} + ⟦b⟧` (most significant bit first). -/
-private theorem dlc_listToNat_append (a b : List Bool) :
-    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
-  have key : ∀ (l : List Bool) (acc : ℕ),
-      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
-        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
-    intro l
-    induction l with
-    | nil => intro acc; simp
-    | cons c l ih =>
-      intro acc
-      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
-      ring
-  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]
-
-/-- The one-bit numeral `1` reads as `1`. -/
-private theorem dlc_listToNat_true : listToNat [true] = 1 := by
-  rw [listToNat_eq]
-  rfl
-
-/-- The `k`-bit numeral keeps the `k` low-order bits: `⟦N mod 2^k⟧_k = ⟦N⟧_k`. -/
-private theorem dlc_natToList_mod (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N := by
-  have h := natToList_length_listToNat (natToList k N)
-  rw [length_natToList, listToNat_natToList_eq_mod] at h
-  exact h
-
-/-- Leading zeros do not change the number read. -/
-private theorem dlc_listToNat_zeros_append (k : ℕ) (b : List Bool) :
-    listToNat (natToList k 0 ++ b) = listToNat b := by
-  rw [dlc_listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]
-
-/-- **Width normalization**: `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`. -/
-private theorem dlc_drop_natToList_zero_append (W : ℕ) (b : List Bool) :
-    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
-  set w := natToList W 0 ++ b with hw
-  have hlen : (w.drop b.length).length = W := by
-    rw [List.length_drop, hw, List.length_append, length_natToList]
-    omega
-  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
-    conv_lhs => rw [← List.take_append_drop b.length w]
-    rw [dlc_listToNat_append, hlen]
-  have hlt := listToNat_lt_two_pow (w.drop b.length)
-  rw [hlen] at hlt
-  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
-    rw [← dlc_listToNat_zeros_append W b, ← hw, hsplit, Nat.mul_add_mod_of_lt hlt]
-  rw [← dlc_natToList_mod, hmod, ← hlen, natToList_length_listToNat]
-
-/-- The zero numeral of the width of `w`: `subStr ⟨w, w⟩ = ⟦0⟧_{|w|}`. -/
-private theorem dlc_subStr_self (w : List Bool) : subStr (pairEncode w w) = natToList w.length 0 := by
-  rw [subStr_pairEncode, Nat.sub_self]
-
 /-- `F z` is the number read from a polynomial-time string function of `z`. -/
 private def dlc_NumPoly (F : List Bool → ℕ) : Prop :=
   ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z, listToNat (g z) = F z
@@ -695,9 +639,7 @@ private theorem dlc_numPoly_mul (H : ArithmeticFP) {F G : List Bool → ℕ} (hF
   obtain ⟨g, hg, hgG⟩ := hG
   refine ⟨fun z => mulStr (pairEncode (f z) (g z)), H.mul.comp (hf.pairEncode hg), fun z => ?_⟩
   simp only
-  rw [mulStr_pairEncode, listToNat_natToList, hfF, hgG]
-  rw [pow_add]
-  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow _) (listToNat_lt_two_pow _)
+  rw [listToNat_mulStr, hfF, hgG]
 
 /-- Remainders (`H.divMod` on the modulus padded by `|a|` leading zeros, so that the
 remainder is lossless also for the modulus `0`). -/
@@ -709,7 +651,7 @@ private theorem dlc_numPoly_mod (H : ArithmeticFP) {F G : List Bool → ℕ} (hF
     polyTimeComputable_pairSndD.comp (H.divMod.comp (hf.pairEncode ((H.sub.comp (hf.pairEncode hf)).append hg))),
     fun z => ?_⟩
   simp only
-  rw [divModStr_pairEncode, pairSndD_pairEncode, dlc_subStr_self, dlc_listToNat_zeros_append,
+  rw [divModStr_pairEncode, pairSndD_pairEncode, subStr_self, listToNat_natToList_zero_append,
     listToNat_natToList, hfF, hgG]
   rw [List.length_append, length_natToList, pow_add]
   calc listToNat (f z) % listToNat (g z) ≤ listToNat (f z) := Nat.mod_le _ _
@@ -737,7 +679,7 @@ private theorem dlc_numPoly_two_pow (H : ArithmeticFP) {u : List Bool → List B
   refine ⟨fun z => [true] ++ subStr (pairEncode (u z) (u z)),
     (polyTimeComputable_prepend [true]).comp (H.sub.comp (hu.pairEncode hu)), fun z => ?_⟩
   simp only
-  rw [dlc_subStr_self, dlc_listToNat_append, dlc_listToNat_true, length_natToList,
+  rw [subStr_self, listToNat_append, listToNat_singleton_true, length_natToList,
     listToNat_natToList (Nat.two_pow_pos _), one_mul, add_zero]
 
 /-- Comparisons are polynomial-time tests (`H.le`). -/
@@ -781,7 +723,7 @@ private theorem dlc_poly_natToList (H : ArithmeticFP) {u : List Bool → List Bo
     (hb.pairEncode ((H.sub.comp (hu.pairEncode hu)).append hb))
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hq
   simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
-  rw [dlc_subStr_self, dlc_drop_natToList_zero_append, hbF]
+  rw [subStr_self, natToList_zero_append_drop, hbF]
 
 /-- The safe modulus: `M`, or `2^n` in place of the modulus `0`. -/
 private def dlc_safeMod (n M : ℕ) : ℕ := if M = 0 then 2 ^ n else M
@@ -799,7 +741,7 @@ private theorem dlc_natToList_mod_safeMod (n V M : ℕ) :
     natToList n (V % M) = natToList n (V % dlc_safeMod n M) := by
   unfold dlc_safeMod
   split_ifs with h
-  · rw [h, Nat.mod_zero, dlc_natToList_mod]
+  · rw [h, Nat.mod_zero, natToList_mod_two_pow]
   · rfl
 
 /-- The safe modulus of a polynomial-time number at the width of `u`. -/
@@ -916,53 +858,19 @@ private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLo
   next i hi => rw [hi]
   next hn => rw [hn]
 
-/-- `List.findSome?` of a filter-and-map is `List.find?` followed by the map. -/
-private theorem dlc_findSome?_ite {α β : Type*} (p : α → Prop) [DecidablePred p] (h : α → β)
-    (l : List α) :
-    l.findSome? (fun t => if p t then some (h t) else none) = (l.find? fun t => decide (p t)).map h := by
-  induction l with
-  | nil => rfl
-  | cons a l ih =>
-    rw [List.findSome?_cons, List.find?_cons]
-    by_cases ha : p a
-    · rw [if_pos ha, decide_eq_true ha]
-      rfl
-    · rw [if_neg ha, decide_eq_false ha, ih]
-
-/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`. -/
-private theorem dlc_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
-    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
-  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
-      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
-    intro l
-    induction l with
-    | nil => intro _; rfl
-    | cons a l ih =>
-      intro hl
-      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
-        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
-  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
-  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
-  have hnone : (List.map (fun x => N + x) (List.range d)).find?
-      (fun i => decide (i < N) && p i) = none := by
-    rw [List.find?_eq_none]
-    intro x hx
-    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
-    simp
-  rw [hnone, Option.or_none]
-
 /-- **The trial loop computes the rejection sampler**: from `⟨⟨u, ⟨1^k, m⟩⟩, ⟨u, c⟩⟩` with
 `k = Nat.size ⟦m⟧`, the number read from the payload (marker dropped) is
 `sampleBelowL ⟦m⟧ k |u| |u| c` with the fallback `0` (read through
-`sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq`).
+`sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq_find?`).
 
 **Proof sketch.** After `i` steps the header is unchanged, the counter `u` has lost `i` bits and the
 coins `i` blocks of `|u|` bits (`dlc_ssStep_iterate`), so the trial value is the `Nat.size ⟦m⟧`-bit
 prefix of block `i`, and the test accepts iff `i < |u|` and that value is below `⟦m⟧`. The search
-over the first `|x| + 1 ≥ |u|` rounds is the search over `[0, |u|)` (`dlc_find?_range_lt`), which is
-the search of `sampleBelowL` read through `sampleBelowL_eq_rejectBlocksL`, `rejectBlocksL_eq` and
-`dlc_findSome?_ite`. In the `some i` case the payload without its marker is the prefix of block `i`;
-in the `none` case both sides read `0` (`dlc_listToNat_nil`). -/
+over the first `|x| + 1 ≥ |u|` rounds is the search over `[0, |u|)`
+(`IterateFind.find?_range_and_lt`), which is the search of `sampleBelowL` read through
+`sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq_find?`. In the `some i` case the payload
+without its marker is the prefix of block `i`; in the `none` case both sides read `0`
+(`listToNat_nil`). -/
 private theorem dlc_ssLoop_eq (u ks ms c : List Bool) (hk : ks.length = Nat.size (listToNat ms)) :
     listToNat ((dlc_ssLoop (pairEncode (pairEncode u (pairEncode ks ms)) (pairEncode u c))).drop 1) =
       (sampleBelowL (listToNat ms) (Nat.size (listToNat ms)) u.length u.length c).getD 0 := by
@@ -991,16 +899,15 @@ private theorem dlc_ssLoop_eq (u ks ms c : List Bool) (hk : ks.length = Nat.size
       (List.range u.length).find? (fun i => decide (val i < listToNat ms)) := by
     rw [show (fun i => dlc_ssAcc (dlc_ssStep^[i] x0)) =
       fun i => decide (i < u.length) && decide (val i < listToNat ms) from funext hacc]
-    exact dlc_find?_range_lt _ hrange
+    exact IterateFind.find?_range_and_lt _ hrange
   have hsample : sampleBelowL (listToNat ms) (Nat.size (listToNat ms)) u.length u.length c =
       ((List.range u.length).find? (fun i => decide (val i < listToNat ms))).map val := by
-    rw [sampleBelowL_eq_rejectBlocksL, rejectBlocksL_eq]
-    exact dlc_findSome?_ite (fun i => val i < listToNat ms) val _
+    rw [sampleBelowL_eq_rejectBlocksL, rejectBlocksL_eq_find?]
   rw [hsample]
   unfold dlc_ssLoop
   rw [hfind]
   rcases hf : (List.range u.length).find? (fun i => decide (val i < listToNat ms)) with _ | i
-  · exact dlc_listToNat_nil
+  · exact listToNat_nil
   · show listToNat ((dlc_ssOut (dlc_ssStep^[i] x0)).drop 1) = val i
     rw [dlc_ssOut, List.singleton_append, List.drop_one, List.tail_cons, hblock]
 
@@ -1263,17 +1170,10 @@ def egDecStr (z : List Bool) : List Bool :=
         (pairFstD (pairFstD (pairFstD z))))))))
     (pairFstD (pairFstD (pairFstD z)))))
 
-/-- Transport of polynomial-time computability along a pointwise equation (used to avoid
-the unifier unfolding the arithmetic string functions when matching a composition chain
-against a definition; integration note, run 2). -/
-private theorem polyTimeComputable_of_forall_eq {f g : List Bool → List Bool}
-    (hf : PolyTimeComputable f) (h : ∀ x, f x = g x) : PolyTimeComputable g :=
-  (funext h : f = g) ▸ hf
-
 /-- **`Dec` is polynomial-time** given the arithmetic bundle (a composition of its functions).
 
 The chain is assembled in composition form and transported to `egDecStr` pointwise
-(`polyTimeComputable_of_forall_eq` with `Function.comp_apply`): matching the composition
+(`PolyTimeComputable.congr` with `Function.comp_apply`): matching the composition
 directly against the unfolded definition makes the unifier unfold `xgcdStr`/`modExpStr`
 and does not terminate in practice. -/
 theorem polyTimeComputable_egDecStr (H : ArithmeticFP) : PolyTimeComputable egDecStr := by
@@ -1284,7 +1184,7 @@ theorem polyTimeComputable_egDecStr (H : ArithmeticFP) : PolyTimeComputable egDe
   have hexp := H.modExp.comp (hc₁.pairEncode (ha.pairEncode hp))
   have hinv := polyTimeComputable_pairSndD.comp (H.xgcd.comp (hexp.pairEncode hp))
   have hmul := H.mul.comp (hc₂.pairEncode hinv)
-  refine polyTimeComputable_of_forall_eq
+  refine PolyTimeComputable.congr
     (polyTimeComputable_pairSndD.comp (H.divMod.comp (hmul.pairEncode hp))) (fun z => ?_)
   simp only [Function.comp_apply, egDecStr]
 
@@ -1616,21 +1516,11 @@ noncomputable def egGroupGen (H : ArithmeticFP) (G : SafePrimeGen) : SafePrimeGe
 
 /-! ### Helpers of `elGamal_secure` (unit dl-c) -/
 
-/-- A coin string read along a length cast. -/
-private def dlc_castEquiv {a L : ℕ} (h : a = L) : (Fin a → Bool) ≃ (Fin L → Bool) :=
-  Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)
-
-/-- The cast keeps the coin string. -/
-private theorem dlc_castEquiv_ofFn {a L : ℕ} (h : a = L) (u : Fin a → Bool) :
-    List.ofFn (dlc_castEquiv h u) = List.ofFn u := by
-  subst h
-  rfl
-
 /-- Splitting a coin string `Fin L → Bool` with `L = a + b` into its two segments: the length
 cast, then `TCSlib.Cryptography.splitCoins`. -/
 private def dlc_splitEquiv {L a b : ℕ} (h : L = a + b) :
     (Fin L → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
-  (dlc_castEquiv h).trans (splitCoins a b)
+  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)
 
 /-- The coin string of two joined segments is the concatenation of their coin strings
 (`ofFn_splitCoins_symm`). -/
@@ -1892,18 +1782,6 @@ private theorem dlc_uprob_shift {p q : ℕ} [NeZero q] {h c k : ℕ}
     rwa [Nat.mod_mod, Nat.mod_mod] at this
   rw [hval]
 
-/-- Averages of pointwise `c`-close functions are `c`-close. -/
-private theorem dlc_abs_uexp_sub_le {α : Type*} [Fintype α] [Nonempty α] {f g : α → ℝ} {c : ℝ}
-    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
-  rw [← HardcoreBit.uexp_sub, abs_le]
-  constructor
-  · have := HardcoreBit.uexp_mono (f := fun _ : α => -c) (g := fun a => f a - g a)
-      fun a => (abs_le.1 (h a)).1
-    rwa [HardcoreBit.uexp_const] at this
-  · have := HardcoreBit.uexp_mono (f := fun a => f a - g a) (g := fun _ : α => c)
-      fun a => (abs_le.1 (h a)).2
-    rwa [HardcoreBit.uexp_const] at this
-
 /-- The coin count of El Gamal's `Gen`: `G`'s coins, then `n · n` for `g` and `n · n` for `a`. -/
 private theorem dlc_egGen_coinLen (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
     (egGen H G).coinLen n = G.gen.coinLen n + (n * n + n * n) := by
@@ -1939,7 +1817,7 @@ private theorem dlc_genEquiv_ofFn (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ
 
 /-- The coins of `Enc` from one segment of `n · n` coins. -/
 private noncomputable def dlc_encEquiv (H : ArithmeticFP) (n : ℕ) : (Fin (n * n) → Bool) ≃ (egEnc H).Coins n :=
-  dlc_castEquiv (dlc_egEnc_coinLen H n).symm
+  Equiv.arrowCongr (finCongr (dlc_egEnc_coinLen H n).symm) (Equiv.refl Bool)
 
 /-- The coins of the derived generator from `G`'s coins and the segment of `g`. -/
 private noncomputable def dlc_grpEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
@@ -1949,7 +1827,7 @@ private noncomputable def dlc_grpEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n
 /-- The coin string of `Enc` read from its segment. -/
 private theorem dlc_encEquiv_ofFn (H : ArithmeticFP) (n : ℕ) (u : Fin (n * n) → Bool) :
     List.ofFn (dlc_encEquiv H n u) = List.ofFn u :=
-  dlc_castEquiv_ofFn _ _
+  (List.ofFn_congr (dlc_egEnc_coinLen H n).symm u).symm
 
 /-- **The challenge on split coins**: the keys are `egGenParts` on `G`'s output and the segments of
 `g` and `a`, the ciphertext is `egEncParts` on the segment of `b` (`egGen_runAt`, `egEnc_runAt`).
@@ -2258,7 +2136,7 @@ probabilities within `2 · (1/2)^n` (average of `dlc_hyb3_point` over the other
 
 **Proof sketch.** Relabel the seeds and the coins of `D_b` so that the coins `u₃` of `z` come last
 (`acceptProb_def`, `uprob_comp_equiv` with `E e_b`), split them off (`uprob_prod`), and bound the
-gap of the averages by the pointwise gap (`dlc_abs_uexp_sub_le`, `dlc_hyb3_point`). -/
+gap of the averages by the pointwise gap (`abs_uexp_sub_le`, `dlc_hyb3_point`). -/
 private theorem dlc_hyb3 (H : ArithmeticFP) (G : SafePrimeGen) (M D Db₀ Db₁ : NUPPT) {n : ℕ}
     (hn : G.n₀ ≤ n) (e₀ : M.Coins n × D.Coins n ≃ Db₀.Coins n)
     (he₀ : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
@@ -2279,7 +2157,7 @@ private theorem dlc_hyb3 (H : ArithmeticFP) (G : SafePrimeGen) (M D Db₀ Db₁
       right_inv := fun s => by simp }
   rw [acceptProb_def, acceptProb_def, ← uprob_comp_equiv (E e₀), ← uprob_comp_equiv (E e₁),
     uprob_prod, uprob_prod]
-  refine dlc_abs_uexp_sub_le fun ρ => ?_
+  refine abs_uexp_sub_le (by positivity) fun ρ => ?_
   obtain ⟨⟨r, u₁, u₂⟩, rM, rD⟩ := ρ
   exact dlc_hyb3_point H G M D Db₀ Db₁ hn e₀ he₀ e₁ he₁ r u₁ u₂ rM rD
 
diff --git a/TCSlib/Cryptography/Candidates/Factoring.lean b/TCSlib/Cryptography/Candidates/Factoring.lean
index b79e1c46..345fba19 100644
--- a/TCSlib/Cryptography/Candidates/Factoring.lean
+++ b/TCSlib/Cryptography/Candidates/Factoring.lean
@@ -181,20 +181,13 @@ theorem fmult_inv_factor {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : p <
   exact fmultNat_eq_mul_prime hp hq
     (natToBits_injOn (fmultNat_lt (bitsToNat_lt _) (bitsToNat_lt _)) hlt h)
 
-/-- Leading zeros read as `0`: the fold of `listToNat` over `0^m` from `0` is `0`. -/
-private theorem fac_foldl_replicate_false (m : ℕ) :
-    (List.replicate m false).foldl (fun a c => 2 * a + if c then 1 else 0) 0 = 0 := by
-  induction m with
-  | zero => rfl
-  | succ m ih => rw [List.replicate_succ, List.foldl_cons]; simpa using ih
-
 /-- **Leading zeros**: the `(j + |w|)`-bit numeral of the number read from `w` is `0^j w`
 (`natToList_length_listToNat` on `0^j w`, which reads as the same number). -/
 private theorem fac_natToList_lead (j : ℕ) (w : List Bool) :
     natToList (j + w.length) (listToNat w) = List.replicate j false ++ w := by
   have h := natToList_length_listToNat (List.replicate j false ++ w)
-  rw [List.length_append, List.length_replicate, listToNat_eq, List.foldl_append,
-    fac_foldl_replicate_false, ← listToNat_eq] at h
+  rw [List.length_append, List.length_replicate, listToNat_append, listToNat_replicate_false,
+    zero_mul, zero_add] at h
   exact h
 
 /-- The numeral of `1`: `natToList k 1 = (0^k ++ 1).drop 1` (`0^{k−1}1` for `k ≥ 1`, empty for
@@ -225,8 +218,7 @@ private theorem fac_polyTimeComputable_isOne (H : ArithmeticFP) {g : List Bool 
     PolyTimeComputable fun z => [decide (listToNat (g z) ≤ 1) && decide (1 ≤ listToNat (g z))] := by
   have h1 := H.le.comp (hg.pairEncode (polyTimeComputable_const [true]))
   have h2 := H.le.comp ((polyTimeComputable_const [true]).pairEncode hg)
-  have hone : listToNat [true] = 1 := by rw [listToNat_eq]; rfl
-  simp only [Function.comp_def, leStr_pairEncode, hone] at h1 h2
+  simp only [Function.comp_def, leStr_pairEncode, listToNat_singleton_true] at h1 h2
   exact polyTimeComputable_and h1 h2
 
 /-- **`f_mult` is easy to compute** [PS10, Theorem 33.5, "clearly computable in polynomial
@@ -703,7 +695,7 @@ private theorem fac_blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = O
 
 /-- The all-`false` string reads as `0`. -/
 private theorem fac_bitsToNat_false (k : ℕ) : bitsToNat (fun _ : Fin k => false) = 0 := by
-  rw [bitsToNat_eq_listToNat, List.ofFn_const, listToNat_eq, fac_foldl_replicate_false]
+  rw [bitsToNat_eq_listToNat, List.ofFn_const, listToNat_replicate_false]
 
 /-- Block `i` of `x` under `FunFamily.blocks` is the window `x (finProdFinEquiv (i, ·))`. -/
 private theorem fac_blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) :
@@ -1082,14 +1074,6 @@ def samplePrimeL (n : ℕ) (r : List Bool) : List Bool :=
   List.ofFn ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n (padFin (2 * n ^ 2 * n) r))).getD
     (natToBits n 2))
 
-/-- A numeral depends only on its value modulo `2^k`: `natToList k N = natToList k (N mod 2^k)`
-(`listToNat_natToList_eq_mod`, `natToList_length_listToNat`). -/
-private theorem fac_natToList_mod (k N : ℕ) : natToList k N = natToList k (N % 2 ^ k) := by
-  have h := natToList_length_listToNat (natToList k N)
-  have hl : (natToList k N).length = k := by rw [natToList_eq, List.length_ofFn]
-  rw [listToNat_natToList_eq_mod, hl] at h
-  exact h.symm
-
 /-- **The fallback numeral of `SamplePrime`**: the `k`-bit numeral of `2` is `0^{k+2}` followed
 by `10`, with its first two bits dropped (`0^{k−2}10` for `k ≥ 2`, `0` for `k = 1`, empty for
 `k = 0`). -/
@@ -1097,7 +1081,7 @@ private theorem fac_natToList_two (k : ℕ) :
     natToList k 2 = (List.replicate k false ++ [true, false]).drop 2 := by
   rcases k with _ | _ | m
   · rw [natToList_zero]; rfl
-  · rw [fac_natToList_mod]
+  · rw [← natToList_mod_two_pow]
     have h := natToList_length_listToNat [false]
     rw [listToNat_eq] at h
     exact h
@@ -1109,7 +1093,7 @@ private theorem fac_natToList_two (k : ℕ) :
       | succ m => simp [List.replicate_succ]
     rw [hw]
     have h := natToList_length_listToNat (List.replicate m false ++ [true, false])
-    rw [listToNat_eq, List.foldl_append, fac_foldl_replicate_false] at h
+    rw [listToNat_append, listToNat_replicate_false, zero_mul, zero_add, listToNat_eq] at h
     simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h
     exact h
 
@@ -1593,16 +1577,6 @@ theorem factoringCollection_index (H : ArithmeticFP) (n : ℕ)
   rw [Collection.index_eq]
   exact (congrArg pairFstD (factoringGen_runAt n r)).trans (pairFstD_pairEncode _ _)
 
-/-- Bit strings of two equal lengths, identified (`finCongr`); it keeps the coin string
-(`fac_arrowCongr_ofFn`). -/
-private def fac_arrowCongr {a b : ℕ} (h : a = b) : (Fin a → Bool) ≃ (Fin b → Bool) :=
-  Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)
-
-/-- `List.ofFn (fac_arrowCongr h r) = List.ofFn r`. -/
-private theorem fac_arrowCongr_ofFn {a b : ℕ} (h : a = b) (r : Fin a → Bool) :
-    List.ofFn (fac_arrowCongr h r) = List.ofFn r :=
-  (List.ofFn_congr h r).symm
-
 /-- The decoded pair read from two numbers: the pair itself when they are distinct primes below
 `2^n`, the default pair otherwise. -/
 private noncomputable def fac_pairDec (n : ℕ) (hn : 2 ≤ n) (v : ℕ × ℕ) : Option (DistinctPrimes n) :=
@@ -1703,12 +1677,15 @@ theorem factoringCollection_sampleClose (H : ArithmeticFP) :
   rw [factoringCollection_sample]
   have h1 := (fac_statClose_decode i.length (max i.length 2) (le_max_right _ _)
     (max_eq_left hn)).map (Option.map (factoringCollection_domEquiv H i).symm)
-  have h2 := (h1.comp_equiv_left (fac_arrowCongr hc)).comp_equiv_right
-    (factoringCollection_domEquiv H i)
+  have h2 := (h1.comp_equiv_left
+    (Equiv.arrowCongr (finCongr hc) (Equiv.refl Bool))).comp_equiv_right
+      (factoringCollection_domEquiv H i)
+  have hofn : ∀ s, List.ofFn (Equiv.arrowCongr (finCongr hc) (Equiv.refl Bool) s) = List.ofFn s :=
+    fun s => (List.ofFn_congr hc s).symm
   simp only [Option.map_some, Equiv.symm_apply_apply] at h2
   convert h2 using 1
   · funext s
-    rw [factoringCollection_decD, factoringSampler_runAt, fac_arrowCongr_ofFn]
+    rw [factoringCollection_decD, factoringSampler_runAt, hofn]
 
 /-- **The reduction from the collection to factoring** [PS10, proof of Theorem 51.1, "the
 factoring assumption states that inverting `f_i` is hard"]: `A_fact(1^n, N) :=
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index 7d14fd88..5689ef48 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -395,10 +395,11 @@ private theorem rsa_one_mod_spec {N : ℕ} (hN : 0 < N) : 1 % N < N ∧ Nat.Copr
   rw [Nat.Coprime, ← Nat.gcd_rec]
   exact Nat.gcd_one_right N
 
-/-- The fallback of the unit sampler is a unit: for `N > 0`, the value
-`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N` (`sampleUnitL_spec`, or
-the default, `rsa_one_mod_spec`). -/
-private theorem rsa_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
+/-- **The total unit sampler gives a unit**: for `0 < N`, the value
+`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N`:
+`(sampleUnitL N k B T r).getD (1 % N) < N ∧ gcd((sampleUnitL N k B T r).getD (1 % N), N) = 1`
+(`sampleUnitL_spec`, or the fallback `1 mod N`, which passes the unit test). -/
+theorem sampleUnitL_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
     (sampleUnitL N k B T r).getD (1 % N) < N ∧
       Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N := by
   cases h : sampleUnitL N k B T r with
@@ -647,53 +648,6 @@ remaining coins). The family follows the pattern of the discrete-log fill's priv
 (`dla_ss*`, `DiscreteLog.lean`), with the stride `B` read from the header and the unit test in
 place of the comparison. -/
 
-/-- The number read from `[true]` is `1`. -/
-private theorem rsa_listToNat_one : listToNat [true] = 1 := by
-  rw [listToNat_eq]
-  rfl
-
-/-- The empty numeral reads as `0`. -/
-private theorem rsa_listToNat_nil : listToNat [] = 0 := by
-  rw [listToNat_eq]
-  rfl
-
-/-- `List.findSome?` of a filter-and-map is `List.find?` followed by the map. -/
-private theorem rsa_findSome?_ite {α β : Type*} (p : α → Prop) [DecidablePred p] (h : α → β)
-    (l : List α) :
-    l.findSome? (fun t => if p t then some (h t) else none) =
-      (l.find? fun t => decide (p t)).map h := by
-  induction l with
-  | nil => rfl
-  | cons a l ih =>
-    rw [List.findSome?_cons, List.find?_cons]
-    by_cases ha : p a
-    · rw [if_pos ha, decide_eq_true ha]
-      rfl
-    · rw [if_neg ha, decide_eq_false ha, ih]
-
-/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`, for
-`N ≤ L`. -/
-private theorem rsa_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
-    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
-  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
-      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
-    intro l
-    induction l with
-    | nil => intro _; rfl
-    | cons a l ih =>
-      intro hl
-      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
-        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
-  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
-  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
-  have hnone : (List.map (fun x => N + x) (List.range d)).find?
-      (fun i => decide (i < N) && p i) = none := by
-    rw [List.find?_eq_none]
-    intro x hx
-    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
-    simp
-  rw [hnone, Option.or_none]
-
 /-- **The unit test by comparisons**: for `N = ⟦w⟧`, "`¬ (N ≤ v)`, and the `|w|`-bit numeral `g`
 of `gcd(v, N)` reads `≤ 1` and `≥ 1`" is the test `v < N ∧ gcd(v, N) = 1`.
 
@@ -705,7 +659,7 @@ private theorem rsa_unitTest_eq (v : ℕ) (w : List Bool) :
       decide (listToNat (natToList w.length (Nat.gcd v (listToNat w))) ≤ listToNat [true]) &&
       decide (listToNat [true] ≤ listToNat (natToList w.length (Nat.gcd v (listToNat w))))) =
       decide (v < listToNat w ∧ Nat.Coprime v (listToNat w)) := by
-  rw [rsa_listToNat_one]
+  rw [listToNat_singleton_true]
   by_cases h : v < listToNat w
   · have hg : Nat.gcd v (listToNat w) < 2 ^ w.length :=
       lt_of_le_of_lt (Nat.gcd_le_right _ (by omega)) (listToNat_lt_two_pow w)
@@ -756,12 +710,6 @@ private def rsa_usAcc (x : List Bool) : Bool :=
 /-- The payload: a `true` marker, then the accepted block. -/
 private def rsa_usOut (x : List Bool) : List Bool := [true] ++ rsa_usBlock x
 
-/-- Composition of polynomial-time functions in applied form, `x ↦ g (f x)` (so that the
-composite is stated up to `β` only, without `Function.comp`). -/
-private theorem rsa_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
-    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
-  hg.comp hf
-
 /-- The step is polynomial-time (`polyTimeComputable_tail`, `polyTimeComputable_pairDropPoly`). -/
 private theorem rsa_usStep_poly : PolyTimeComputable rsa_usStep := by
   have h := polyTimeComputable_pairFstD.pairEncode
@@ -786,25 +734,12 @@ private theorem rsa_usBlock_poly : PolyTimeComputable rsa_usBlock := by
   simp only [rsa_usBlock, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
     PolyExpr.eval_var]
 
-/-- A comparison `[⟦a x⟧ ≤ ⟦b x⟧]` of two polynomial-time numerals is polynomial-time
-(`H.le`, read through `leStr_pairEncode`). -/
-private theorem rsa_le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
-    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
-    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))] := by
-  have h := H.le.comp (ha.pairEncode hb)
-  have e : (leStr ∘ fun x => pairEncode (a x) (b x)) =
-      fun x => [decide (listToNat (a x) ≤ listToNat (b x))] := by
-    funext x
-    rw [Function.comp_apply, leStr_pairEncode]
-  rw [e] at h
-  exact h
-
 /-- The acceptance test is polynomial-time (`polyTimeComputable_isNil`, `H.le`, `H.xgcd`).
 
 **Proof sketch.** The gcd numeral is `H.xgcd` on `⟨block, w⟩` followed by `pairFstD`, stated in
-applied form (`rsa_comp`) and folded into `rsa_usGcd`; the four one-bit tests are
+applied form (`PolyTimeComputable.comp'`) and folded into `rsa_usGcd`; the four one-bit tests are
 `polyTimeComputable_isNil` (negated), `H.le` (negated) and two `H.le` against `[true]`
-(`rsa_le_poly`); they are combined by `polyTimeComputable_and` with the tests given explicitly,
+(`ArithmeticFP.le_poly`); they are combined by `polyTimeComputable_and` with the tests given explicitly,
 so that no bundle string function is unfolded by unification. -/
 private theorem rsa_usAcc_poly (H : ArithmeticFP) :
     PolyTimeComputable fun x => [rsa_usAcc x] := by
@@ -812,10 +747,10 @@ private theorem rsa_usAcc_poly (H : ArithmeticFP) :
     polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
   have hx : PolyTimeComputable fun x =>
       xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x)))) :=
-    rsa_comp H.xgcd (rsa_usBlock_poly.pairEncode hw)
+    PolyTimeComputable.comp' H.xgcd (rsa_usBlock_poly.pairEncode hw)
   have hg' : PolyTimeComputable fun x =>
       pairFstD (xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x))))) :=
-    rsa_comp polyTimeComputable_pairFstD hx
+    PolyTimeComputable.comp' polyTimeComputable_pairFstD hx
   have e : (fun x => pairFstD (xgcdStr (pairEncode (rsa_usBlock x)
       (pairSndD (pairSndD (pairFstD x)))))) = rsa_usGcd := by
     funext x
@@ -826,20 +761,20 @@ private theorem rsa_usAcc_poly (H : ArithmeticFP) :
   have hc : PolyTimeComputable fun x => pairFstD (pairSndD x) :=
     polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
   have t1 : PolyTimeComputable fun x => [decide (pairFstD (pairSndD x) = [])] :=
-    rsa_comp polyTimeComputable_isNil hc
+    PolyTimeComputable.comp' polyTimeComputable_isNil hc
   have t1' : PolyTimeComputable fun x => [!decide (pairFstD (pairSndD x) = [])] :=
     polyTimeComputable_not (p := fun x => decide (pairFstD (pairSndD x) = [])) t1
   have t2 : PolyTimeComputable fun x =>
       [decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
-    rsa_le_poly H hw rsa_usBlock_poly
+    H.le_poly hw rsa_usBlock_poly
   have t2' : PolyTimeComputable fun x =>
       [!decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
     polyTimeComputable_not
       (p := fun x => decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))) t2
   have t3 : PolyTimeComputable fun x => [decide (listToNat (rsa_usGcd x) ≤ listToNat [true])] :=
-    rsa_le_poly H hg (polyTimeComputable_const [true])
+    H.le_poly hg (polyTimeComputable_const [true])
   have t4 : PolyTimeComputable fun x => [decide (listToNat [true] ≤ listToNat (rsa_usGcd x))] :=
-    rsa_le_poly H (polyTimeComputable_const [true]) hg
+    H.le_poly (polyTimeComputable_const [true]) hg
   have t23 := polyTimeComputable_and
     (p := fun x => !decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x)))
     (q := fun x => decide (listToNat (rsa_usGcd x) ≤ listToNat [true])) t2' t3
@@ -927,9 +862,9 @@ is `true :: b`.
 **Proof sketch.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (i B)⟩⟩`
 (`rsa_usStep_iterate`), so trial `i` reads `(r.drop (i B)).take k` and the test is
 `i < T ∧ (v < N ∧ gcd(v, N) = 1)` (`rsa_unitTest_eq`, `xgcdStr_pairEncode`). The search over
-`[0, |x| + 1) ⊇ [0, T)` is then the search over `[0, T)` (`rsa_find?_range_lt`), and
+`[0, |x| + 1) ⊇ [0, T)` is then the search over `[0, T)` (`IterateFind.find?_range_and_lt`), and
 `sampleUnitL = rejectBlocksL` is that search followed by reading the block
-(`rejectBlocksL_eq`, `rsa_findSome?_ite`). -/
+(`rejectBlocksL_eq`, `rejectBlocksL_eq_find?`). -/
 private theorem rsa_usFind_eq (f : List Bool → List Bool) (z : List Bool) :
     sampleUnitL (listToNat (f z)) (Nat.size (listToNat (f z))) (rsaBlock.eval (NUPPT.inParam z).length)
         (rsaTrials.eval (NUPPT.inParam z).length) (NUPPT.inCoins z) =
@@ -970,9 +905,8 @@ private theorem rsa_usFind_eq (f : List Bool → List Bool) (z : List Bool) :
     rw [show (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) =
       fun i => decide (i < T) &&
         decide (val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w)) from funext hacc]
-    exact rsa_find?_range_lt _ hrange
-  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq,
-    rsa_findSome?_ite (fun i => val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w)) val]
+    exact IterateFind.find?_range_and_lt _ hrange
+  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq_find?]
   simp only [hblock]
   rfl
 
@@ -1001,11 +935,11 @@ private theorem rsa_ptc_unitSampleStr (H : ArithmeticFP) {f : List Bool → List
     PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
   -- the trial loop on the start state (the repetition host)
   have hL : PolyTimeComputable fun z => rsa_usLoop (rsa_usStart f z) :=
-    rsa_comp (rsa_usLoop_poly H) (rsa_usStart_poly H hf)
+    PolyTimeComputable.comp' (rsa_usLoop_poly H) (rsa_usStart_poly H hf)
   have hN : PolyTimeComputable fun z => [decide (rsa_usLoop (rsa_usStart f z) = [])] :=
-    rsa_comp polyTimeComputable_isNil hL
+    PolyTimeComputable.comp' polyTimeComputable_isNil hL
   have hT : PolyTimeComputable fun z => (rsa_usLoop (rsa_usStart f z)).drop 1 :=
-    rsa_comp polyTimeComputable_tail hL
+    PolyTimeComputable.comp' polyTimeComputable_tail hL
   -- the value block: the accepted block (marker dropped), or `[true]` (the fallback `1`)
   have hG : PolyTimeComputable fun z => if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
       else (rsa_usLoop (rsa_usStart f z)).drop 1 :=
@@ -1016,7 +950,7 @@ private theorem rsa_ptc_unitSampleStr (H : ArithmeticFP) {f : List Bool → List
   have hq : PolyTimeComputable fun z => pairSndD (divModStr (pairEncode
       (if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
         else (rsa_usLoop (rsa_usStart f z)).drop 1) (f z))) :=
-    rsa_comp polyTimeComputable_pairSndD (rsa_comp H.divMod (hG.pairEncode hf))
+    PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hG.pairEncode hf))
   have e : (fun z => pairSndD (divModStr (pairEncode
       (if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
         else (rsa_usLoop (rsa_usStart f z)).drop 1) (f z)))) =
@@ -1025,7 +959,7 @@ private theorem rsa_ptc_unitSampleStr (H : ArithmeticFP) {f : List Bool → List
     rw [divModStr_pairEncode, pairSndD_pairEncode, unitSampleStr_eq, rsa_usFind_eq f z, rsa_usLoop]
     rcases hres : (List.range ((rsa_usStart f z).length + 1)).find?
         (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) with _ | i
-    · rw [Option.elim_none, Option.map_none, Option.getD_none, if_pos (by rfl), rsa_listToNat_one]
+    · rw [Option.elim_none, Option.map_none, Option.getD_none, if_pos (by rfl), listToNat_singleton_true]
     · have hE : listToNat (rsa_usBlock (rsa_usStep^[i] (rsa_usStart f z))) < listToNat (f z) := by
         have hs := rsa_usFind_eq f z
         rw [hres, Option.map_some] at hs
@@ -1043,16 +977,6 @@ On `y = ⟨1^M, r⟩` with `M = max n 2`: the two prime runs (S1), the validity
 `H.sub`), the exponent (the unit sampler on a re-laid-out input), `d` (`H.xgcd`), and the
 `2M`-bit numerals as remainders modulo the all-ones word `1^{2M}` (`H.divMod`). -/
 
-/-- The all-ones numeral `1^k` reads as `2^k − 1`. -/
-private theorem rsa_listToNat_ones (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1 := by
-  induction k with
-  | zero => rw [List.replicate_zero, rsa_listToNat_nil]; rfl
-  | succ k ih =>
-    rw [List.replicate_succ', listToNat_eq, List.foldl_append, ← listToNat_eq, ih]
-    have := Nat.one_le_two_pow (n := k)
-    simp only [List.foldl_cons, List.foldl_nil, if_true, pow_succ]
-    omega
-
 /-- The numeral `[true, false]` reads as `2`. -/
 private theorem rsa_listToNat_two : listToNat [true, false] = 2 := by
   rw [listToNat_eq]
@@ -1063,26 +987,13 @@ private theorem rsa_listToNat_three : listToNat [true, true] = 3 := by
   rw [listToNat_eq]
   rfl
 
-/-- The product numeral reads as the product: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧`. -/
-private theorem rsa_listToNat_mulStr (a b : List Bool) :
-    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b := by
-  rw [mulStr_pairEncode, listToNat_natToList]
-  rw [pow_add]
-  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow a) (listToNat_lt_two_pow b)
-
 /-- **Width normalization**: the remainder of `⟦x⟧` modulo the all-ones word `1^k` is the
 `k`-bit numeral of `⟦x⟧` when `⟦x⟧ < 2^k − 1`. -/
 private theorem rsa_norm (x : List Bool) (k : ℕ) (h : listToNat x < 2 ^ k - 1) :
     pairSndD (divModStr (pairEncode x (List.replicate k true))) = natToList k (listToNat x) := by
-  rw [divModStr_pairEncode, pairSndD_pairEncode, List.length_replicate, rsa_listToNat_ones,
+  rw [divModStr_pairEncode, pairSndD_pairEncode, List.length_replicate, listToNat_replicate_true,
     Nat.mod_eq_of_lt h]
 
-/-- A function equal pointwise to a polynomial-time one is polynomial-time. -/
-private theorem rsa_ptc_congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
-    (e : ∀ x, f x = g x) : PolyTimeComputable g := by
-  rw [show g = f from (funext e).symm]
-  exact h
-
 /-- The first prime run: `samplePrimeL M` on the first `L = 2M³` coins of `y = ⟨1^M, r⟩`. -/
 private def rsa_gP (y : List Bool) : List Bool :=
   samplePrimeL (pairFstD y).length ((pairSndD y).take (samplePrimeCoins.eval (pairFstD y).length))
@@ -1136,7 +1047,7 @@ private theorem rsa_gP_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gP := by
   have hA : PolyTimeComputable fun y => pairEncode (pairFstD y)
       ((pairSndD y).take (samplePrimeCoins.eval (pairFstD y).length)) :=
     polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly samplePrimeCoins)
-  refine rsa_ptc_congr (rsa_comp (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
+  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
   rw [pairFstD_pairEncode, pairSndD_pairEncode, rsa_gP]
 
 /-- The second prime run is polynomial-time (S1 on `⟨1^M, (r.drop L).take L⟩`). -/
@@ -1144,35 +1055,26 @@ private theorem rsa_gQ_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gQ := by
   have hD : PolyTimeComputable fun y => pairEncode (pairFstD y)
       ((pairSndD y).drop (samplePrimeCoins.eval (pairFstD y).length)) :=
     polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairDropPoly samplePrimeCoins)
-  have hT := rsa_comp (polyTimeComputable_pairTakePoly samplePrimeCoins) hD
+  have hT := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly samplePrimeCoins) hD
   have hA := polyTimeComputable_pairFstD.pairEncode hT
-  refine rsa_ptc_congr (rsa_comp (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
+  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
   simp only [pairFstD_pairEncode, pairSndD_pairEncode]
   rw [rsa_gQ]
 
-/-- A primality test `[⟦a x⟧ prime]` of a polynomial-time word is polynomial-time (`H.prime`,
-read through `primeStr_eq`). -/
-private theorem rsa_prime_poly (H : ArithmeticFP) {a : List Bool → List Bool}
-    (ha : PolyTimeComputable a) :
-    PolyTimeComputable fun x => [decide (listToNat (a x)).Prime] := by
-  have h := rsa_comp H.prime ha
-  rw [primeStr_eq] at h
-  exact h
-
 /-- The validity test is polynomial-time.
 
-**Proof sketch.** Two primality tests (`rsa_prime_poly`, `H.prime`), the negated conjunction of
-the comparisons `p ≤ q`, `q ≤ p`, and the comparisons of `p`, `q` with `⟦1^M⟧` (`rsa_le_poly`),
+**Proof sketch.** Two primality tests (`ArithmeticFP.prime_poly`, `H.prime`), the negated conjunction of
+the comparisons `p ≤ q`, `q ≤ p`, and the comparisons of `p`, `q` with `⟦1^M⟧` (`ArithmeticFP.le_poly`),
 combined by `polyTimeComputable_and` and `polyTimeComputable_not` with explicit tests. -/
 private theorem rsa_gValid_poly (H : ArithmeticFP) : PolyTimeComputable fun y => [rsa_gValid y] := by
   have hP := rsa_gP_poly H
   have hQ := rsa_gQ_poly H
-  have t1 := rsa_prime_poly H hP
-  have t2 := rsa_prime_poly H hQ
-  have t3 := rsa_le_poly H hP hQ
-  have t4 := rsa_le_poly H hQ hP
-  have t5 := rsa_le_poly H hP polyTimeComputable_pairFstD
-  have t6 := rsa_le_poly H hQ polyTimeComputable_pairFstD
+  have t1 := H.prime_poly hP
+  have t2 := H.prime_poly hQ
+  have t3 := H.le_poly hP hQ
+  have t4 := H.le_poly hQ hP
+  have t5 := H.le_poly hP polyTimeComputable_pairFstD
+  have t6 := H.le_poly hQ polyTimeComputable_pairFstD
   have t34 := polyTimeComputable_not (polyTimeComputable_and
     (p := fun y => decide (listToNat (rsa_gP y) ≤ listToNat (rsa_gQ y)))
     (q := fun y => decide (listToNat (rsa_gQ y) ≤ listToNat (rsa_gP y))) t3 t4)
@@ -1206,9 +1108,9 @@ private theorem rsa_gPw_poly (H : ArithmeticFP) :
 
 /-- The word of `Φ` is polynomial-time (`H.sub`, `H.mul`). -/
 private theorem rsa_gPhi_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gPhi := by
-  have h1 := rsa_comp H.sub ((rsa_gPw_poly H).1.pairEncode (polyTimeComputable_const [true]))
-  have h2 := rsa_comp H.sub ((rsa_gPw_poly H).2.pairEncode (polyTimeComputable_const [true]))
-  have h := rsa_comp H.mul (h1.pairEncode h2)
+  have h1 := PolyTimeComputable.comp' H.sub ((rsa_gPw_poly H).1.pairEncode (polyTimeComputable_const [true]))
+  have h2 := PolyTimeComputable.comp' H.sub ((rsa_gPw_poly H).2.pairEncode (polyTimeComputable_const [true]))
+  have h := PolyTimeComputable.comp' H.mul (h1.pairEncode h2)
   unfold rsa_gPhi
   exact h
 
@@ -1217,7 +1119,7 @@ private theorem rsa_gPhi_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gPhi :
 private theorem rsa_gE_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gE := by
   have hl := NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD (rsa_gPhi_poly H)
     (polyTimeComputable_const []) (polyTimeComputable_pairDropPoly (.mul (.const 2) samplePrimeCoins))
-  refine rsa_ptc_congr (rsa_comp (rsa_ptc_unitSampleStr H NUPPT.polyTimeComputable_inArg) hl)
+  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (rsa_ptc_unitSampleStr H NUPPT.polyTimeComputable_inArg) hl)
     fun y => ?_
   rw [NUPPT.inArg_layout, NUPPT.inParam_layout, NUPPT.inCoins_layout, rsa_gE]
 
@@ -1225,16 +1127,16 @@ private theorem rsa_gE_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gE := by
 `polyTimeComputable_unaryPoly`). -/
 private theorem rsa_gNorm_poly (H : ArithmeticFP) {x : List Bool → List Bool}
     (hx : PolyTimeComputable x) : PolyTimeComputable fun y => rsa_gNorm y (x y) := by
-  have ho := rsa_comp (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) polyTimeComputable_pairFstD
-  have h := rsa_comp polyTimeComputable_pairSndD (rsa_comp H.divMod (hx.pairEncode ho))
+  have ho := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) polyTimeComputable_pairFstD
+  have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hx.pairEncode ho))
   unfold rsa_gNorm
   exact h
 
 /-- The generator's string computation is polynomial-time. -/
 private theorem rsa_genCore_poly (H : ArithmeticFP) : PolyTimeComputable rsa_genCore := by
-  have hN := rsa_comp H.mul ((rsa_gPw_poly H).1.pairEncode (rsa_gPw_poly H).2)
-  have hD := rsa_comp polyTimeComputable_pairSndD
-    (rsa_comp H.xgcd ((rsa_gE_poly H).pairEncode (rsa_gPhi_poly H)))
+  have hN := PolyTimeComputable.comp' H.mul ((rsa_gPw_poly H).1.pairEncode (rsa_gPw_poly H).2)
+  have hD := PolyTimeComputable.comp' polyTimeComputable_pairSndD
+    (PolyTimeComputable.comp' H.xgcd ((rsa_gE_poly H).pairEncode (rsa_gPhi_poly H)))
   have h := ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H (rsa_gE_poly H))).pairEncode
     ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H hD))
   unfold rsa_genCore
@@ -1246,7 +1148,7 @@ private theorem rsa_genCore_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gen
 **Proof sketch.** With `M = max n 2` and `L = 2M³`, `rsa_gP`, `rsa_gQ` are the two prime runs
 of `rsaGenParams`, and the validity test is its condition (`⟦1^M⟧ = 2^M − 1`; two comparisons
 for `p ≠ q`), so the prime words read as the primes of the parameters (`default_p`,
-`default_q` on the fallback). Then `⟦N⟧ = pq` (`rsa_listToNat_mulStr`), `⟦Φ⟧ = (p−1)(q−1) =
+`default_q` on the fallback). Then `⟦N⟧ = pq` (`listToNat_mulStr`), `⟦Φ⟧ = (p−1)(q−1) =
 Φ(pq)` (`listToNat_subStr`, `DistinctPrimes.totient_mul`), the exponent word reads as
 `e = sampleUnitL … .getD 1` (`unitSampleStr_eq`, `1 % Φ = 1` as `Φ ≥ 2`), `d` is the inverse
 (`xgcdStr_pairEncode`), and each of `N, e, d < 2^{2M} − 1` is normalized to its `2M`-bit numeral
@@ -1265,7 +1167,7 @@ private theorem rsa_genCore_spec (n : ℕ) (r : List Bool) :
     rw [rsa_gQ, hy1, hy2, List.length_replicate]
   have hones : listToNat (pairFstD (pairEncode (List.replicate (max n 2) true) r)) =
       2 ^ max n 2 - 1 := by
-    rw [hy1, rsa_listToNat_ones]
+    rw [hy1, listToNat_replicate_true]
   have hvalid : rsa_gValid (pairEncode (List.replicate (max n 2) true) r) =
       decide ((listToNat (samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2))))).Prime ∧
         (listToNat (samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
@@ -1310,15 +1212,15 @@ private theorem rsa_genCore_spec (n : ℕ) (r : List Bool) :
   generalize hy : pairEncode (List.replicate (max n 2) true) r = y at hy1 hy2 hP hQ hones hvalid hzp
   -- the modulus, `Φ`, `e` and `d` read from the words
   have hN : listToNat (mulStr (pairEncode (rsa_gPw y) (rsa_gQw y))) = (rsaGenParams n r).N := by
-    rw [rsa_listToNat_mulStr, ← hzp.1, ← hzp.2]
+    rw [listToNat_mulStr, ← hzp.1, ← hzp.2]
     rfl
   have hPhi : listToNat (rsa_gPhi y) =
       Nat.totient ((rsaGenParams n r).z.p * (rsaGenParams n r).z.q) := by
-    rw [rsa_gPhi, rsa_listToNat_mulStr, listToNat_subStr, listToNat_subStr, rsa_listToNat_one,
+    rw [rsa_gPhi, listToNat_mulStr, listToNat_subStr, listToNat_subStr, listToNat_singleton_true,
       ← hzp.1, ← hzp.2, DistinctPrimes.totient_mul]
   have hΦ1 := (rsaGenParams n r).z.one_lt_totient
   have he : listToNat (rsa_gE y) = (rsaGenParams n r).e := by
-    have hv := rsa_getD_spec (N := listToNat (rsa_gPhi y)) (by omega) (Nat.size (listToNat (rsa_gPhi y)))
+    have hv := sampleUnitL_getD_spec (N := listToNat (rsa_gPhi y)) (by omega) (Nat.size (listToNat (rsa_gPhi y)))
       (rsaBlock.eval (pairFstD y).length) (rsaTrials.eval (pairFstD y).length)
       ((pairSndD y).drop ((PolyExpr.mul (.const 2) samplePrimeCoins).eval (pairFstD y).length))
     rw [rsa_gE, unitSampleStr_eq, listToNat_natToList (hv.1.trans (listToNat_lt_two_pow _)), hPhi,
@@ -1378,18 +1280,18 @@ remainder of `H.divMod` modulo the all-ones word `1^{2m}`; pair the numerals. -/
 theorem polyTimeComputable_rsaGenRaw (H : ArithmeticFP) : PolyTimeComputable rsaGenRaw := by
   -- `1^{max n 2}`: `1^n` unless `n ≤ 1` (`polyTimeComputable_lenLe` against `[true]`)
   have hle : PolyTimeComputable fun z => [decide ((NUPPT.inParam z).length ≤ 1)] := by
-    refine rsa_ptc_congr (rsa_comp polyTimeComputable_lenLe
+    refine PolyTimeComputable.congr (PolyTimeComputable.comp' polyTimeComputable_lenLe
       ((polyTimeComputable_const [true]).pairEncode NUPPT.polyTimeComputable_inParam)) fun z => ?_
     rw [pairFstD_pairEncode, pairSndD_pairEncode, List.length_singleton]
   have hun : PolyTimeComputable fun z => List.replicate (NUPPT.inParam z).length true := by
-    refine rsa_ptc_congr (rsa_comp (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam)
+    refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam)
       fun z => ?_
     rw [PolyExpr.eval_var]
   have hu := polyTimeComputable_ite (p := fun z => decide ((NUPPT.inParam z).length ≤ 1))
     (f := fun _ => [true, true]) (g := fun z => List.replicate (NUPPT.inParam z).length true)
     hle (polyTimeComputable_const _) hun
-  have h := rsa_comp (rsa_genCore_poly H) (hu.pairEncode NUPPT.polyTimeComputable_inCoins)
-  refine rsa_ptc_congr h fun z => ?_
+  have h := PolyTimeComputable.comp' (rsa_genCore_poly H) (hu.pairEncode NUPPT.polyTimeComputable_inCoins)
+  refine PolyTimeComputable.congr h fun z => ?_
   have hm : (if decide ((NUPPT.inParam z).length ≤ 1) then [true, true]
       else List.replicate (NUPPT.inParam z).length true) =
       List.replicate (max (NUPPT.inParam z).length 2) true := by
@@ -1537,14 +1439,14 @@ private theorem rsa_sampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool)
 
 /-- At a generated index `⟨N, e⟩` the sampler's string decodes: `rsaDec` accepts
 `unitSampleStr` of the modulus numeral (it is the `2m`-bit numeral of a unit `v < N`,
-`rsa_getD_spec`). -/
+`sampleUnitL_getD_spec`). -/
 private theorem rsa_dec_unitSampleStr {m : ℕ} (P : RSAParams m) (n : ℕ) (r : List Bool) :
     ∃ x, rsaDec (rsaIndexOf m P) (unitSampleStr (pairFstD (rsaIndexOf m P)) n r) = some x := by
   have hw : pairFstD (rsaIndexOf m P) = natToList (2 * m) P.N := by
     rw [rsaIndexOf, pairFstD_pairEncode]
   have hN : listToNat (natToList (2 * m) P.N) = P.N := listToNat_natToList P.N_lt
   have hpos : 0 < P.N := NeZero.pos (P.z.p * P.z.q)
-  have hv := rsa_getD_spec hpos (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r
+  have hv := sampleUnitL_getD_spec hpos (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r
   set v := (sampleUnitL P.N (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r).getD (1 % P.N)
   have hval : listToNat (natToList (2 * m) v) = v := listToNat_natToList (hv.1.trans P.N_lt)
   have hM := rsaMod_indexOf m P
@@ -1564,7 +1466,7 @@ evaluator clause.
 **Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`, `rsaSampleRaw`,
 `unitSampleStr`, `rsaGen_runAt`), case on `sampleUnitL`; `rsaDec`'s test is discharged by
 `length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp. the
-default `1 % N` (`rsa_getD_spec`, `rsa_dec_unitSampleStr`); the decoded unit `x` re-encodes to the
+default `1 % N` (`sampleUnitL_getD_spec`, `rsa_dec_unitSampleStr`); the decoded unit `x` re-encodes to the
 sampler's string (`rsaEnc_of_rsaDec`), so `rsaEval_spec` applies. -/
 theorem rsaSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n)
     (s : (rsaSampler H).Coins n) :
@@ -2385,60 +2287,6 @@ def rsaFromFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
 
 /-! ### `A'` as a string computation (helpers of `polyTimeComputable_rsaFromFactorRaw`) -/
 
-/-- The number read from `a ++ b` is `⟦a⟧ · 2^{|b|} + ⟦b⟧` (most significant bit first). This is
-the fold identity of `listToNat` (the private `foldl_bits_eq` of `Asymptotic/Sampling.lean`,
-and the discrete-log fill's private `dla_listToNat_append`). -/
-private theorem rsa_listToNat_append (a b : List Bool) :
-    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
-  have key : ∀ (l : List Bool) (acc : ℕ),
-      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
-        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
-    intro l
-    induction l with
-    | nil => intro acc; simp
-    | cons c l ih =>
-      intro acc
-      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
-      ring
-  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]
-
-/-- Leading zeros do not change the number read: `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧`. -/
-private theorem rsa_listToNat_zeros_append (k : ℕ) (w : List Bool) :
-    listToNat (natToList k 0 ++ w) = listToNat w := by
-  rw [rsa_listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]
-
-/-- **Width normalization by truncation**: `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`, the low `W` bits
-(the discrete-log fill's private `dla_drop_natToList_zero_append`, re-proved). -/
-private theorem rsa_drop_zeros_append (W : ℕ) (b : List Bool) :
-    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
-  set w := natToList W 0 ++ b with hw
-  have hlen : (w.drop b.length).length = W := by
-    rw [List.length_drop, hw, List.length_append, length_natToList]
-    omega
-  have hval : listToNat w = listToNat b := rsa_listToNat_zeros_append W b
-  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
-    conv_lhs => rw [← List.take_append_drop b.length w]
-    rw [rsa_listToNat_append, hlen]
-  have hlt := listToNat_lt_two_pow (w.drop b.length)
-  rw [hlen] at hlt
-  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
-    rw [← hval, hsplit, Nat.mul_add_mod_of_lt hlt]
-  have hnum : ∀ N : ℕ, natToList W N = natToList W (N % 2 ^ W) := fun N => by
-    have h := natToList_length_listToNat (natToList W N)
-    rw [length_natToList, listToNat_natToList_eq_mod] at h
-    exact h.symm
-  rw [hnum, hmod, ← hlen, natToList_length_listToNat]
-
-/-- `subStr ⟨a, a⟩` is the `|a|`-bit numeral of `0`. -/
-private theorem rsa_subStr_self (a : List Bool) : subStr (pairEncode a a) = natToList a.length 0 := by
-  rw [subStr_pairEncode, Nat.sub_self]
-
-/-- In `Z_0 = ℤ` the inverse of a natural number is its sign, so its value is at most `1`. -/
-private theorem rsa_val_inv_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1 := by
-  show (Int.sign (e : ℤ)).natAbs ≤ 1
-  rw [Int.natAbs_sign]
-  split_ifs <;> omega
-
 /-- The answer of `A` on `⟨1^n, N⟩` (coins and advice of the outer input). -/
 private def rsa_fS (A : NUPPT) (z : List Bool) : List Bool :=
   A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
@@ -2487,7 +2335,7 @@ private def rsa_fOut (A : NUPPT) (z : List Bool) : List Bool :=
 `H.mul`, `H.le`, `H.sub`, `H.xgcd`, `H.modExp`, `polyTimeComputable_pairDropPoly`).
 
 **Proof sketch.** Each word is one bundle field applied to pairs of earlier words, in applied
-form (`rsa_comp`) and folded into its definition: the answer of `A` on the re-laid-out input
+form (`PolyTimeComputable.comp'`) and folded into its definition: the answer of `A` on the re-laid-out input
 (`NUPPT.polyTimeComputable_layout`), the cofactor (`H.divMod`), the product (`H.mul`) and the
 test (two `H.le`, `polyTimeComputable_and`), `Φ` (`H.sub`, `H.mul`, a constant prefix), `d`
 (`H.xgcd`), `y^d mod N` (`H.modExp`, with the zero prefix `H.sub ⟨1y, 1y⟩`), and the `2n`-bit
@@ -2495,51 +2343,51 @@ truncation (`polyTimeComputable_unaryPoly`, `H.sub`, `polyTimeComputable_pairDro
 `polyTimeComputable_ite` selects the output. -/
 private theorem rsa_fOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputable (rsa_fOut A) := by
   have hN : PolyTimeComputable fun z => pairFstD (NUPPT.inArg z) :=
-    rsa_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg
+    PolyTimeComputable.comp' polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg
   have he : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
-    rsa_comp polyTimeComputable_pairFstD (rsa_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
+    PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
   have hy : PolyTimeComputable fun z => pairSndD (pairSndD (NUPPT.inArg z)) :=
-    rsa_comp polyTimeComputable_pairSndD (rsa_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
+    PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
   have hS : PolyTimeComputable (rsa_fS A) := by
-    have h := rsa_comp A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
+    have h := PolyTimeComputable.comp' A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
       NUPPT.polyTimeComputable_inParam hN NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
     unfold rsa_fS
     exact h
   have hQ : PolyTimeComputable (rsa_fQ A) := by
-    have h := rsa_comp polyTimeComputable_pairFstD (rsa_comp H.divMod (hN.pairEncode hS))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' H.divMod (hN.pairEncode hS))
     unfold rsa_fQ
     exact h
-  have hM := rsa_comp H.mul (hS.pairEncode hQ)
+  have hM := PolyTimeComputable.comp' H.mul (hS.pairEncode hQ)
   have hT : PolyTimeComputable fun z => [rsa_fTest A z] := by
     have h := polyTimeComputable_and
       (p := fun z => decide (listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z))) ≤
         listToNat (pairFstD (NUPPT.inArg z))))
       (q := fun z => decide (listToNat (pairFstD (NUPPT.inArg z)) ≤
         listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z)))))
-      (rsa_le_poly H hM hN) (rsa_le_poly H hN hM)
+      (H.le_poly hM hN) (H.le_poly hN hM)
     unfold rsa_fTest
     exact h
   have hPhi : PolyTimeComputable (rsa_fPhi A) := by
-    have h1 := rsa_comp H.sub (hS.pairEncode (polyTimeComputable_const [true]))
-    have h2 := rsa_comp H.sub (hQ.pairEncode (polyTimeComputable_const [true]))
-    have h0 := rsa_comp H.sub ((polyTimeComputable_const [true]).pairEncode
+    have h1 := PolyTimeComputable.comp' H.sub (hS.pairEncode (polyTimeComputable_const [true]))
+    have h2 := PolyTimeComputable.comp' H.sub (hQ.pairEncode (polyTimeComputable_const [true]))
+    have h0 := PolyTimeComputable.comp' H.sub ((polyTimeComputable_const [true]).pairEncode
       (polyTimeComputable_const [true]))
-    have h := h0.append (rsa_comp H.mul (h1.pairEncode h2))
+    have h := h0.append (PolyTimeComputable.comp' H.mul (h1.pairEncode h2))
     unfold rsa_fPhi
     exact h
   have hD : PolyTimeComputable (rsa_fD A) := by
-    have h := rsa_comp polyTimeComputable_pairSndD (rsa_comp H.xgcd (he.pairEncode hPhi))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.xgcd (he.pairEncode hPhi))
     unfold rsa_fD
     exact h
   have hV : PolyTimeComputable (rsa_fV A) := by
     have h1y := (polyTimeComputable_prepend [true]).comp hy
-    have hz := rsa_comp H.sub (h1y.pairEncode h1y)
-    have h := rsa_comp H.modExp (hy.pairEncode (hD.pairEncode (hz.append hN)))
+    have hz := PolyTimeComputable.comp' H.sub (h1y.pairEncode h1y)
+    have h := PolyTimeComputable.comp' H.modExp (hy.pairEncode (hD.pairEncode (hz.append hN)))
     unfold rsa_fV
     exact h
-  have hO := rsa_comp (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) NUPPT.polyTimeComputable_inParam
-  have hZ := rsa_comp H.sub (hO.pairEncode hO)
-  have hW := rsa_comp (polyTimeComputable_pairDropPoly .var) (hV.pairEncode (hZ.append hV))
+  have hO := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) NUPPT.polyTimeComputable_inParam
+  have hZ := PolyTimeComputable.comp' H.sub (hO.pairEncode hO)
+  have hW := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var) (hV.pairEncode (hZ.append hV))
   have h := polyTimeComputable_ite (p := rsa_fTest A) hT hW (polyTimeComputable_const [])
   unfold rsa_fOut
   exact h
@@ -2548,12 +2396,12 @@ private theorem rsa_fOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputabl
 
 **Proof sketch.** With `s = ⟦p'⟧`, `N`, `e`, `y` read from the input: the cofactor word reads as
 `N / s` (`divModStr_pairEncode`, `N / s ≤ N`), so the test is `s (N / s) = N`; the word of `Φ`
-reads as `Φ = (s − 1)(N / s − 1)` (leading zero, `listToNat_subStr`, `rsa_listToNat_mulStr`); the
+reads as `Φ = (s − 1)(N / s − 1)` (leading zero, `listToNat_subStr`, `listToNat_mulStr`); the
 word of `d` reads as `d = (e : Z_Φ)⁻¹.val` exactly (`xgcdStr_pairEncode`; `d < Φ` if `Φ ≠ 0`,
-and `d ≤ 1` in `Z_0 = ℤ`, `rsa_val_inv_zero_le`); `modExpStr` at the modulus word with
+and `d ≤ 1` in `Z_0 = ℤ`, `val_inv_natCast_zmod_zero_le`); `modExpStr` at the modulus word with
 `|y| + 1` leading zeros reads as `y^d mod N` exactly (`y^d mod N < N` if `N ≠ 0`; if `N = 0` then
 `Φ = 0`, `d ≤ 1` and `y^d < 2^{|y| + 1}`); and the truncation is the `2n`-bit numeral
-(`rsa_drop_zeros_append`). -/
+(`natToList_zero_append_drop`). -/
 private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFromFactorRaw A z := by
   unfold rsa_fOut rsa_fTest rsa_fV rsa_fD rsa_fPhi rsa_fQ rsaFromFactorRaw rsaFromFactorStep
   rw [show A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
@@ -2569,7 +2417,7 @@ private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFrom
       listToNat_natToList ((Nat.div_le_self _ _).trans_lt (listToNat_lt_two_pow Nw))]
   have hprod : listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))) =
       listToNat S * (listToNat Nw / listToNat S) := by
-    rw [rsa_listToNat_mulStr, hQ]
+    rw [listToNat_mulStr, hQ]
   have htest : (decide (listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))) ≤
         listToNat Nw) && decide (listToNat Nw ≤
         listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))))) =
@@ -2591,13 +2439,13 @@ private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFrom
       mulStr (pairEncode (subStr (pairEncode S [true]))
         (subStr (pairEncode (pairFstD (divModStr (pairEncode Nw S))) [true])))) =
       (listToNat S - 1) * (listToNat Nw / listToNat S - 1) := by
-    rw [rsa_subStr_self, rsa_listToNat_zeros_append, rsa_listToNat_mulStr, listToNat_subStr,
-      listToNat_subStr, rsa_listToNat_one, hQ]
+    rw [subStr_self, listToNat_natToList_zero_append, listToNat_mulStr, listToNat_subStr,
+      listToNat_subStr, listToNat_singleton_true, hQ]
   set Φw := subStr (pairEncode [true] [true]) ++
       mulStr (pairEncode (subStr (pairEncode S [true]))
         (subStr (pairEncode (pairFstD (divModStr (pairEncode Nw S))) [true]))) with hΦw
   have hΦlen : 1 ≤ Φw.length := by
-    rw [hΦw, List.length_append, rsa_subStr_self, length_natToList, List.length_singleton]
+    rw [hΦw, List.length_append, subStr_self, length_natToList, List.length_singleton]
     omega
   have hD : listToNat (pairSndD (xgcdStr (pairEncode ew Φw))) =
       ((listToNat ew : ZMod ((listToNat S - 1) * (listToNat Nw / listToNat S - 1)))⁻¹).val := by
@@ -2605,26 +2453,26 @@ private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFrom
     apply listToNat_natToList
     by_cases hΦ : (listToNat S - 1) * (listToNat Nw / listToNat S - 1) = 0
     · rw [hΦ]
-      calc _ ≤ 1 := rsa_val_inv_zero_le _
+      calc _ ≤ 1 := val_inv_natCast_zmod_zero_le _
         _ < 2 ^ Φw.length := Nat.one_lt_two_pow (by omega)
     · haveI : NeZero ((listToNat S - 1) * (listToNat Nw / listToNat S - 1)) := ⟨hΦ⟩
       exact (ZMod.val_lt _).trans (hPhi ▸ listToNat_lt_two_pow Φw)
   have hNw : listToNat (subStr (pairEncode ([true] ++ yw) ([true] ++ yw)) ++ Nw) = listToNat Nw := by
-    rw [rsa_subStr_self, rsa_listToNat_zeros_append]
+    rw [subStr_self, listToNat_natToList_zero_append]
   have hV : listToNat (modExpStr (pairEncode yw (pairEncode (pairSndD (xgcdStr (pairEncode ew Φw)))
       (subStr (pairEncode ([true] ++ yw) ([true] ++ yw)) ++ Nw)))) =
       listToNat yw ^ ((listToNat ew : ZMod ((listToNat S - 1) *
         (listToNat Nw / listToNat S - 1)))⁻¹).val % listToNat Nw := by
     rw [modExpStr_pairEncode, hD, hNw]
     apply listToNat_natToList
-    rw [List.length_append, rsa_subStr_self, length_natToList, List.length_append,
+    rw [List.length_append, subStr_self, length_natToList, List.length_append,
       List.length_singleton]
     rcases Nat.eq_zero_or_pos (listToNat Nw) with h0 | h0
     · -- `N = 0`: then `Φ = 0`, `d ≤ 1` and `y^d ≤ max 1 y < 2^{|y| + 1}`
       have hΦ : (listToNat S - 1) * (listToNat Nw / listToNat S - 1) = 0 := by
         rw [h0, Nat.zero_div, Nat.zero_sub, mul_zero]
       rw [hΦ, h0, Nat.mod_zero]
-      have hd := rsa_val_inv_zero_le (listToNat ew)
+      have hd := val_inv_natCast_zmod_zero_le (listToNat ew)
       have hyl := listToNat_lt_two_pow yw
       have h2 : 2 ^ (1 + yw.length) ≤ 2 ^ (1 + yw.length + Nw.length) :=
         Nat.pow_le_pow_right (by norm_num) (by omega)
@@ -2639,8 +2487,8 @@ private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFrom
         _ < 2 ^ Nw.length := listToNat_lt_two_pow Nw
         _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
   rw [pairSndD_pairEncode, pairFstD_pairEncode, PolyExpr.eval_var,
-    rsa_subStr_self (List.replicate _ true), List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
-    rsa_drop_zeros_append, hV]
+    subStr_self (List.replicate _ true), List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
+    natToList_zero_append_drop, hV]
 
 /-- **`A'` is polynomial-time** [PS10, Theorem 55.2, "the running time of `A'` is essentially
 the running time of `A` plus `O(log³ n)`"] given the arithmetic bundle.
@@ -2658,7 +2506,7 @@ the degenerate inputs `Φ = 0` (where `d ≤ 1`) and `N = 0` (where `y^d mod N =
 (`H.sub ⟨1^{2n}, 1^{2n}⟩`, `polyTimeComputable_pairDropPoly var`), and `polyTimeComputable_ite`
 selects it or `[]` by the test. The word computation equals `rsaFromFactorRaw A`
 (`rsa_fOut_eq`: `divModStr_pairEncode`, `xgcdStr_pairEncode`, `modExpStr_pairEncode`,
-`listToNat_subStr`, `rsa_drop_zeros_append`). -/
+`listToNat_subStr`, `natToList_zero_append_drop`). -/
 theorem polyTimeComputable_rsaFromFactorRaw (H : ArithmeticFP) (A : NUPPT) :
     PolyTimeComputable (rsaFromFactorRaw A) := by
   have h := rsa_fOut_poly H A
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index bad0995f..108f0af4 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -546,33 +546,6 @@ def rabinGenRaw (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams
     (z : List Bool) : List Bool :=
   rabinGenOut P dflt (NUPPT.inParam z).length (NUPPT.inCoins z)
 
-/-- Composition of polynomial-time functions in applied form, `x ↦ g (f x)` (fill notes, item 7: composites are stated applied, never as `∘` matched against a lambda). -/
-private theorem rabin_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
-    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
-  hg.comp hf
-
-/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`, for `N ≤ L`. -/
-private theorem rabin_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
-    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
-  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
-      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
-    intro l
-    induction l with
-    | nil => intro _; rfl
-    | cons a l ih =>
-      intro hl
-      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
-        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
-  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
-  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
-  have hnone : (List.map (fun x => N + x) (List.range d)).find?
-      (fun i => decide (i < N) && p i) = none := by
-    rw [List.find?_eq_none]
-    intro x hx
-    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
-    simp
-  rw [hnone, Option.or_none]
-
 /-- One trial of the block loop on the state `⟨⟨1^B, 1^k⟩, ⟨counter, coins⟩⟩`: keep the header, decrement the counter, drop one block of `B` coins. -/
 private def rabin_rbStep (x : List Bool) : List Bool :=
   pairEncode (pairFstD x)
@@ -625,11 +598,11 @@ private theorem rabin_rbAcc_poly {acc0 : List Bool → Bool}
   have hc : PolyTimeComputable fun x => pairFstD (pairSndD x) :=
     polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
   have t1 : PolyTimeComputable fun x => [decide (pairFstD (pairSndD x) = [])] :=
-    rabin_comp polyTimeComputable_isNil hc
+    PolyTimeComputable.comp' polyTimeComputable_isNil hc
   have t1' : PolyTimeComputable fun x => [!decide (pairFstD (pairSndD x) = [])] :=
     polyTimeComputable_not (p := fun x => decide (pairFstD (pairSndD x) = [])) t1
   have t2 : PolyTimeComputable fun x => [acc0 (rabin_rbBlock x)] :=
-    rabin_comp hacc0 rabin_rbBlock_poly
+    PolyTimeComputable.comp' hacc0 rabin_rbBlock_poly
   exact polyTimeComputable_and (p := fun x => !decide (pairFstD (pairSndD x) = []))
     (q := fun x => acc0 (rabin_rbBlock x)) t1' t2
 
@@ -691,7 +664,7 @@ private theorem rabin_rbLoop_poly {acc0 : List Bool → Bool}
 
 /-- **The block loop computes `rejectBlocksL`**: on the start state `⟨⟨1^B, 1^k⟩, ⟨1^T, r⟩⟩`, the host's search finds trial `i` exactly as `rejectBlocksL E k B T r` does, and the accepted value is the number read from the trial word.
 
-**Proof sketch.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (iB)⟩⟩` (`rabin_rbStep_iterate`), so trial `i` reads `(r.drop (iB)).take k` and the test is `i < T ∧ E v` (`hspec`). The search over `[0, |x| + 1) ⊇ [0, T)` is the search over `[0, T)` (`rabin_find?_range_lt`), and `rejectBlocksL` is that search followed by reading the word (`rejectBlocksL_eq`, `List.findSome?_guard`, `List.map_findSome?`). -/
+**Proof sketch.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (iB)⟩⟩` (`rabin_rbStep_iterate`), so trial `i` reads `(r.drop (iB)).take k` and the test is `i < T ∧ E v` (`hspec`). The search over `[0, |x| + 1) ⊇ [0, T)` is the search over `[0, T)` (`IterateFind.find?_range_and_lt`), and `rejectBlocksL` is that search followed by reading the word (`rejectBlocksL_eq_find?`). -/
 private theorem rabin_rbFind_eq (E : ℕ → Prop) [DecidablePred E] {acc0 : List Bool → Bool}
     (hspec : ∀ w, acc0 w = decide (E (listToNat w))) (hB hk r : List Bool) (T : ℕ) :
     rejectBlocksL E hk.length hB.length T r =
@@ -717,16 +690,8 @@ private theorem rabin_rbFind_eq (E : ℕ → Prop) [DecidablePred E] {acc0 : Lis
     simp only [x0, length_pairEncode, List.length_replicate]
     omega
   rw [show (fun i => rabin_rbAcc acc0 (rabin_rbStep^[i] x0)) = _ from funext hacc,
-    rabin_find?_range_lt _ hrange, rejectBlocksL_eq, ← List.findSome?_guard, List.map_findSome?]
+    IterateFind.find?_range_and_lt _ hrange, rejectBlocksL_eq_find?]
   simp only [hblock]
-  congr 1
-  funext t
-  simp only [Function.comp_apply, Option.guard]
-  split_ifs with h1 h2 h2 <;> simp_all
-
-/-- `[true]` reads as `1`. -/
-private theorem rabin_listToNat_one : listToNat [true] = 1 := by
-  rw [listToNat_eq]; rfl
 
 /-- Zero-padding of a word `b` to the width of `u`: `⟦0⟧_{|u| − |b|}` (`subStr ⟨d, d⟩`, `d = u.drop |b|`) added to `b` (`addStr`). -/
 private def rabin_pad (u b : List Bool) : List Bool :=
@@ -742,14 +707,14 @@ private theorem rabin_pad_eq {u b : List Bool} (h : b.length ≤ u.length) :
 private theorem rabin_pad_poly (H : ArithmeticFP) {fu fb : List Bool → List Bool}
     (hu : PolyTimeComputable fu) (hb : PolyTimeComputable fb) :
     PolyTimeComputable fun z => rabin_pad (fu z) (fb z) := by
-  have hD' := rabin_comp (polyTimeComputable_pairDropPoly .var) (hb.pairEncode hu)
+  have hD' := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var) (hb.pairEncode hu)
   have hD : PolyTimeComputable fun z => (fu z).drop (fb z).length := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hD'
     simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
   have hS : PolyTimeComputable fun z =>
       subStr (pairEncode ((fu z).drop (fb z).length) ((fu z).drop (fb z).length)) :=
-    rabin_comp H.sub (hD.pairEncode hD)
-  exact rabin_comp H.add (hS.pairEncode hb)
+    PolyTimeComputable.comp' H.sub (hD.pairEncode hD)
+  exact PolyTimeComputable.comp' H.add (hS.pairEncode hb)
 
 /-- The start state `⟨⟨U, U⟩, ⟨1^{4m²}, c⟩⟩` of the restricted prime loop, `m = |U|`. -/
 private def rabin_spStart (U c : List Bool) : List Bool :=
@@ -787,13 +752,13 @@ private theorem rabin_spOut_poly (H : ArithmeticFP) {acc0 : List Bool → Bool}
     (hU : PolyTimeComputable fU) (hds : PolyTimeComputable fds) (hc : PolyTimeComputable fc) :
     PolyTimeComputable fun z => rabin_spOut acc0 (fU z) (fds z) (fc z) := by
   have hS : PolyTimeComputable fun z => rabin_spStart (fU z) (fc z) :=
-    (hU.pairEncode hU).pairEncode ((rabin_comp (polyTimeComputable_unaryPoly rabinTrials) hU).pairEncode hc)
+    (hU.pairEncode hU).pairEncode ((PolyTimeComputable.comp' (polyTimeComputable_unaryPoly rabinTrials) hU).pairEncode hc)
   have hL : PolyTimeComputable fun z => rabin_rbLoop acc0 (rabin_spStart (fU z) (fc z)) :=
-    rabin_comp (rabin_rbLoop_poly hacc0) hS
+    PolyTimeComputable.comp' (rabin_rbLoop_poly hacc0) hS
   have hN : PolyTimeComputable fun z => [decide (rabin_rbLoop acc0 (rabin_spStart (fU z) (fc z)) = [])] :=
-    rabin_comp polyTimeComputable_isNil hL
+    PolyTimeComputable.comp' polyTimeComputable_isNil hL
   have hT : PolyTimeComputable fun z => (rabin_rbLoop acc0 (rabin_spStart (fU z) (fc z))).drop 1 :=
-    rabin_comp polyTimeComputable_tail hL
+    PolyTimeComputable.comp' polyTimeComputable_tail hL
   exact polyTimeComputable_ite (p := fun z => decide (rabin_rbLoop acc0 (rabin_spStart (fU z) (fc z)) = []))
     (f := fun z => rabin_pad (fU z) (fds z))
     (g := fun z => rabin_pad (fU z) ((rabin_rbLoop acc0 (rabin_spStart (fU z) (fc z))).drop 1)) hN
@@ -811,26 +776,11 @@ private theorem rabin_listToNat_three : listToNat [true, true] = 3 := by
 private theorem rabin_listToNat_four : listToNat [true, false, false] = 4 := by
   rw [listToNat_eq]; rfl
 
-/-- A comparison `[⟦a x⟧ ≤ ⟦b x⟧]` of two polynomial-time numerals is polynomial-time (`H.le`, `leStr_pairEncode`). -/
-private theorem rabin_le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
-    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
-    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))] := by
-  have h := rabin_comp H.le (ha.pairEncode hb)
-  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp h
-  rw [leStr_pairEncode]
-
-/-- The primality test `[decide (⟦w⟧ prime)]` is polynomial-time (`H.prime`, `primeStr_eq`). -/
-private theorem rabin_prime_poly (H : ArithmeticFP) :
-    PolyTimeComputable fun w => [decide (listToNat w).Prime] := by
-  have h := H.prime
-  rw [primeStr_eq] at h
-  exact h
-
 /-- The residue `⟦w⟧ mod ⟦b⟧` as a numeral of the width of `b` is polynomial-time (`H.divMod`). -/
 private theorem rabin_mod_poly (H : ArithmeticFP) (b : List Bool) :
     PolyTimeComputable fun w => pairSndD (divModStr (pairEncode w b)) :=
-  rabin_comp polyTimeComputable_pairSndD
-    (rabin_comp H.divMod (polyTimeComputable_id.pairEncode (polyTimeComputable_const b)))
+  PolyTimeComputable.comp' polyTimeComputable_pairSndD
+    (PolyTimeComputable.comp' H.divMod (polyTimeComputable_id.pairEncode (polyTimeComputable_const b)))
 
 /-- The acceptance test of the odd generator: prime, and the residue modulo `2` reads `≥ 1`. -/
 private def rabin_oddAcc (w : List Bool) : Bool :=
@@ -846,20 +796,20 @@ private def rabin_blumAcc (w : List Bool) : Bool :=
 private theorem rabin_oddAcc_poly (H : ArithmeticFP) : PolyTimeComputable fun w => [rabin_oddAcc w] :=
   polyTimeComputable_and (p := fun w => decide (listToNat w).Prime)
     (q := fun w => decide (listToNat [true] ≤ listToNat (pairSndD (divModStr (pairEncode w [true, false])))))
-    (rabin_prime_poly H) (rabin_le_poly H (polyTimeComputable_const [true]) (rabin_mod_poly H _))
+    (H.prime_poly polyTimeComputable_id) (H.le_poly (polyTimeComputable_const [true]) (rabin_mod_poly H _))
 
 /-- The Blum test is polynomial-time (`H.prime`, `H.divMod`, `H.le`). -/
 private theorem rabin_blumAcc_poly (H : ArithmeticFP) : PolyTimeComputable fun w => [rabin_blumAcc w] :=
   polyTimeComputable_and (p := fun w => decide (listToNat w).Prime)
     (q := fun w => decide (listToNat [true, true] ≤
       listToNat (pairSndD (divModStr (pairEncode w [true, false, false])))))
-    (rabin_prime_poly H) (rabin_le_poly H (polyTimeComputable_const [true, true]) (rabin_mod_poly H _))
+    (H.prime_poly polyTimeComputable_id) (H.le_poly (polyTimeComputable_const [true, true]) (rabin_mod_poly H _))
 
 /-- The odd test decides "prime and `≠ 2`" on every word (a prime is `2` or odd, `Nat.Prime.eq_two_or_odd`; `divModStr_pairEncode`). -/
 private theorem rabin_oddAcc_spec (w : List Bool) :
     rabin_oddAcc w = decide ((listToNat w).Prime ∧ listToNat w ≠ 2) := by
   rw [rabin_oddAcc, divModStr_pairEncode, pairSndD_pairEncode, rabin_listToNat_two,
-    listToNat_natToList (by simp; omega), rabin_listToNat_one]
+    listToNat_natToList (by simp; omega), listToNat_singleton_true]
   by_cases hp : (listToNat w).Prime
   · have h := hp.eq_two_or_odd
     by_cases h2 : listToNat w = 2
@@ -920,12 +870,12 @@ private def rabin_genCore (acc0 : List Bool → Bool) (ds1 ds2 : List Bool) (z :
 
 /-- `1^{max n 3}` is polynomial-time (`polyTimeComputable_lenLe`, `_unaryPoly`, `_ite`). -/
 private theorem rabin_gU_poly : PolyTimeComputable rabin_gU := by
-  have hL' := rabin_comp polyTimeComputable_lenLe
+  have hL' := PolyTimeComputable.comp' polyTimeComputable_lenLe
     ((polyTimeComputable_const [true, true]).pairEncode NUPPT.polyTimeComputable_inParam)
   have hL : PolyTimeComputable fun z => [decide ((NUPPT.inParam z).length ≤ 2)] := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hL'
     simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons, List.length_nil]
-  have hR' := rabin_comp (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam
+  have hR' := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam
   have hR : PolyTimeComputable fun z => List.replicate (NUPPT.inParam z).length true := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hR'
     rw [PolyExpr.eval_var]
@@ -935,16 +885,16 @@ private theorem rabin_gU_poly : PolyTimeComputable rabin_gU := by
 
 /-- The first coin segment is polynomial-time (`polyTimeComputable_pairTakePoly rabinPrimeCoins`). -/
 private theorem rabin_gC1_poly : PolyTimeComputable rabin_gC1 := by
-  have h := rabin_comp (polyTimeComputable_pairTakePoly rabinPrimeCoins)
+  have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly rabinPrimeCoins)
     (rabin_gU_poly.pairEncode NUPPT.polyTimeComputable_inCoins)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   rw [pairFstD_pairEncode, pairSndD_pairEncode, rabin_gC1]
 
 /-- The second coin segment is polynomial-time (`_pairDropPoly`, `_pairTakePoly rabinPrimeCoins`). -/
 private theorem rabin_gC2_poly : PolyTimeComputable rabin_gC2 := by
-  have hD := rabin_comp (polyTimeComputable_pairDropPoly rabinPrimeCoins)
+  have hD := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly rabinPrimeCoins)
     (rabin_gU_poly.pairEncode NUPPT.polyTimeComputable_inCoins)
-  have h := rabin_comp (polyTimeComputable_pairTakePoly rabinPrimeCoins) (rabin_gU_poly.pairEncode hD)
+  have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly rabinPrimeCoins) (rabin_gU_poly.pairEncode hD)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   rw [pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, rabin_gC2]
 
@@ -962,7 +912,7 @@ private theorem rabin_genCore_poly (H : ArithmeticFP) {acc0 : List Bool → Bool
     rabin_spOut_poly H hacc0 rabin_gU_poly (polyTimeComputable_const ds1) rabin_gC1_poly
   have hQ : PolyTimeComputable (rabin_gQ acc0 ds2) :=
     rabin_spOut_poly H hacc0 rabin_gU_poly (polyTimeComputable_const ds2) rabin_gC2_poly
-  have hE' := rabin_comp polyTimeComputable_pairEq (hP.pairEncode hQ)
+  have hE' := PolyTimeComputable.comp' polyTimeComputable_pairEq (hP.pairEncode hQ)
   have hE : PolyTimeComputable fun z => [decide (rabin_gP acc0 ds1 z = rabin_gQ acc0 ds2 z)] := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hE'
     rw [pairFstD_pairEncode, pairSndD_pairEncode]
@@ -976,7 +926,7 @@ private theorem rabin_genCore_poly (H : ArithmeticFP) {acc0 : List Bool → Bool
     polyTimeComputable_ite (p := rabin_gValid acc0 ds1 ds2) (f := rabin_gQ acc0 ds2)
       (g := fun z => rabin_pad (rabin_gU z) ds2) hV hQ
       (rabin_pad_poly H rabin_gU_poly (polyTimeComputable_const ds2))
-  exact (rabin_comp H.mul (hA.pairEncode hB)).pairEncode (hA.pairEncode hB)
+  exact (PolyTimeComputable.comp' H.mul (hA.pairEncode hB)).pairEncode (hA.pairEncode hB)
 
 /-- `rabin_gU z` is `1^{max n 3}`. -/
 private theorem rabin_gU_eq (z : List Bool) :
@@ -1239,23 +1189,6 @@ noncomputable def rabinSampler (H : ArithmeticFP) : NUPPT :=
   NUPPT.ofPolyTimeUniform (polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg)
     rsaSampleCoins
 
-/-- The fallback `1 % N` of the unit sampler is a unit below `N` (for `N = 1` it is `0`, coprime
-to `1`). -/
-private theorem rabin_one_mod_spec {N : ℕ} (hN : 0 < N) : 1 % N < N ∧ Nat.Coprime (1 % N) N := by
-  refine ⟨Nat.mod_lt _ hN, ?_⟩
-  rcases Nat.lt_or_ge 1 N with h | h
-  · rw [Nat.mod_eq_of_lt h]; exact Nat.coprime_one_left _
-  · obtain rfl : N = 1 := by omega
-    simp
-
-/-- The total unit sampler's value is a unit below `N` (`sampleUnitL_spec`, or the fallback). -/
-private theorem rabin_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
-    (sampleUnitL N k B T r).getD (1 % N) < N ∧
-      Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N := by
-  rcases h : sampleUnitL N k B T r with _ | v
-  · exact rabin_one_mod_spec hN
-  · exact sampleUnitL_spec h
-
 /-- The activation of the Rabin sampler: `unitSampleStr` on the index numeral
 (`NUPPT.runAtL_ofPolyTimeUniform` and the layout equations). -/
 private theorem rabin_sampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool)
@@ -1299,7 +1232,7 @@ width, `v < N`, `gcd(v, N) = 1`). -/
 private theorem rabin_dec_unitSampleStr {P : ℕ → Prop} (m : ℕ) (R : RabinParams P m) (n : ℕ)
     (r : List Bool) :
     ∃ x, rabinDec (rabinIndexOf m R) (unitSampleStr (rabinIndexOf m R) n r) = some x := by
-  have hv := rabin_getD_spec (rabin_N_pos R) (Nat.size (R.z.p * R.z.q)) (rsaBlock.eval n)
+  have hv := sampleUnitL_getD_spec (rabin_N_pos R) (Nat.size (R.z.p * R.z.q)) (rsaBlock.eval n)
     (rsaTrials.eval n) r
   have hval := listToNat_natToList (hv.1.trans R.z.mul_lt)
   have hM := rabin_rabinMod_indexOf m R
@@ -1442,19 +1375,6 @@ private theorem rabin_coins_sampler (H : ArithmeticFP) : (rabinSampler H).coins
   unfold rabinSampler
   exact NUPPT.coins_ofPolyTimeUniform _ _
 
-/-- Any two samplers are `1`-close (`statClose_iff`; both probabilities lie in `[0, 1]`): the
-`δ n := 1` branch of the closeness targets. -/
-private theorem rabin_statClose_one {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) :
-    StatClose X Y 1 := by
-  rw [statClose_iff]
-  intro T
-  have h1 := uprob_nonneg (fun s => T (X s))
-  have h2 := uprob_le_one (fun s => T (X s))
-  have h3 := uprob_nonneg (fun t => T (Y t))
-  have h4 := uprob_le_one (fun t => T (Y t))
-  rw [abs_le]
-  constructor <;> linarith
-
 /-- A generated modulus fits the unit sampler's blocks for `n ≥ 1`:
 `Nat.size (pq) ≤ 2·max(n, 3) ≤ 2(n + 2) = B(n)` (`Nat.size_le`, `eval_rsaBlock`). -/
 private theorem rabin_size_le {P : ℕ → Prop} {n : ℕ} (hn : 1 ≤ n) (R : RabinParams P (max n 3)) :
@@ -1529,7 +1449,7 @@ theorem rabinCollection_sampleClose (H : ArithmeticFP) :
   intro n r
   by_cases hn : n < 3
   · rw [if_pos hn]
-    exact rabin_statClose_one _ _
+    exact statClose_one _ _
   rw [if_neg hn, rabinCollection_index, rabinCollection_sample]
   simp only [rabinCollection_decD, rabin_sampler_runAt]
   have h1 := ((rabin_statClose_dec _ (rabinGenParams (· ≠ 2) oddDefault n (List.ofFn r)) n
@@ -1564,47 +1484,6 @@ def rabinFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
           listToNat (NUPPT.inArg z))))
       (NUPPT.inAdvice z) ((NUPPT.inCoins z).drop (rsaSampleCoins.eval (NUPPT.inParam z).length))))
 
-/-- The number read from `a ++ b` is `⟦a⟧ · 2^{|b|} + ⟦b⟧` (the fold identity of `listToNat`; a re-proof of the private `foldl_bits_eq` of `Asymptotic/Sampling.lean`, also re-proved privately by the dl-a and rsa fills). -/
-private theorem rabin_listToNat_append (a b : List Bool) :
-    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
-  have key : ∀ (l : List Bool) (acc : ℕ),
-      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
-        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
-    intro l
-    induction l with
-    | nil => intro acc; simp
-    | cons c l ih =>
-      intro acc
-      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
-      ring
-  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]
-
-/-- Leading zeros do not change the number read: `⟦⟦0⟧_k ++ w⟧ = ⟦w⟧`. -/
-private theorem rabin_listToNat_zeros_append (k : ℕ) (w : List Bool) :
-    listToNat (natToList k 0 ++ w) = listToNat w := by
-  rw [rabin_listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]
-
-/-- **Width normalization by truncation**: `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`, the low `W` bits (copy of the rsa fill's private `rsa_drop_zeros_append`, itself dl-a's `dla_drop_natToList_zero_append`). -/
-private theorem rabin_drop_zeros_append (W : ℕ) (b : List Bool) :
-    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
-  set w := natToList W 0 ++ b with hw
-  have hlen : (w.drop b.length).length = W := by
-    rw [List.length_drop, hw, List.length_append, length_natToList]
-    omega
-  have hval : listToNat w = listToNat b := rabin_listToNat_zeros_append W b
-  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
-    conv_lhs => rw [← List.take_append_drop b.length w]
-    rw [rabin_listToNat_append, hlen]
-  have hlt := listToNat_lt_two_pow (w.drop b.length)
-  rw [hlen] at hlt
-  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
-    rw [← hval, hsplit, Nat.mul_add_mod_of_lt hlt]
-  have hnum : ∀ N : ℕ, natToList W N = natToList W (N % 2 ^ W) := fun N => by
-    have h := natToList_length_listToNat (natToList W N)
-    rw [length_natToList, listToNat_natToList_eq_mod] at h
-    exact h.symm
-  rw [hnum, hmod, ← hlen, natToList_length_listToNat]
-
 /-- The first `T(n)B(n)` coins (for the unit `x`). -/
 private def rabin_fC1 (z : List Bool) : List Bool :=
   (NUPPT.inCoins z).take (rsaSampleCoins.eval (NUPPT.inParam z).length)
@@ -1663,32 +1542,32 @@ private def rabin_fOut (A : NUPPT) (z : List Bool) : List Bool :=
 
 /-- The string computation of `A'` is polynomial-time.
 
-**Proof sketch.** Each word is a bundle field on pairs of earlier words, in applied form (`rabin_comp`), folded into its definition by `unfold`: the coin segments (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rsaSampleCoins`), `x` (`polyTimeComputable_unitSampleStr` on the re-laid-out input, `NUPPT.polyTimeComputable_layout`), `y` (`H.modExp`), `z` (`A.polyTimeComputable_output`), the padded modulus (`PolyTimeComputable.append`, `H.sub`), the test (`H.modExp`, two `H.le`), `d` and the gcd (`H.add`, `H.sub`, `H.divMod`, `H.xgcd`), and the truncation (`polyTimeComputable_unaryPoly`, `H.sub`, `polyTimeComputable_pairDropPoly var`); `polyTimeComputable_ite` selects the output. -/
+**Proof sketch.** Each word is a bundle field on pairs of earlier words, in applied form (`PolyTimeComputable.comp'`), folded into its definition by `unfold`: the coin segments (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rsaSampleCoins`), `x` (`polyTimeComputable_unitSampleStr` on the re-laid-out input, `NUPPT.polyTimeComputable_layout`), `y` (`H.modExp`), `z` (`A.polyTimeComputable_output`), the padded modulus (`PolyTimeComputable.append`, `H.sub`), the test (`H.modExp`, two `H.le`), `d` and the gcd (`H.add`, `H.sub`, `H.divMod`, `H.xgcd`), and the truncation (`polyTimeComputable_unaryPoly`, `H.sub`, `polyTimeComputable_pairDropPoly var`); `polyTimeComputable_ite` selects the output. -/
 private theorem rabin_fOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputable (rabin_fOut A) := by
   have hw := NUPPT.polyTimeComputable_inArg
   have hC1 : PolyTimeComputable rabin_fC1 := by
-    have h := rabin_comp (polyTimeComputable_pairTakePoly rsaSampleCoins)
+    have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly rsaSampleCoins)
       (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
     rw [pairFstD_pairEncode, pairSndD_pairEncode, rabin_fC1]
   have hC2 : PolyTimeComputable rabin_fC2 := by
-    have h := rabin_comp (polyTimeComputable_pairDropPoly rsaSampleCoins)
+    have h := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly rsaSampleCoins)
       (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
     rw [pairFstD_pairEncode, pairSndD_pairEncode, rabin_fC2]
   have hX : PolyTimeComputable rabin_fX := by
-    have h := rabin_comp (polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg)
+    have h := PolyTimeComputable.comp' (polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg)
       (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam hw
         NUPPT.polyTimeComputable_inAdvice hC1)
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
     simp only [rabin_fX, NUPPT.layout_eq, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.inCoins_eq,
       NUPPT.inAdvice_eq, pairFstD_pairEncode, pairSndD_pairEncode]
   have hY : PolyTimeComputable rabin_fY := by
-    have h := rabin_comp H.modExp (hX.pairEncode ((polyTimeComputable_const [true, false]).pairEncode hw))
+    have h := PolyTimeComputable.comp' H.modExp (hX.pairEncode ((polyTimeComputable_const [true, false]).pairEncode hw))
     unfold rabin_fY
     exact h
   have hZ : PolyTimeComputable (rabin_fZ A) := by
-    have h := rabin_comp A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
+    have h := PolyTimeComputable.comp' A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
       NUPPT.polyTimeComputable_inParam (hw.pairEncode hY) NUPPT.polyTimeComputable_inAdvice hC2)
     unfold rabin_fZ
     exact h
@@ -1697,35 +1576,35 @@ private theorem rabin_fOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputa
     unfold rabin_fK
     exact h
   have hW : PolyTimeComputable (rabin_fW A) := by
-    have h := (rabin_comp H.sub (hK.pairEncode hK)).append hw
+    have h := (PolyTimeComputable.comp' H.sub (hK.pairEncode hK)).append hw
     unfold rabin_fW
     exact h
   have hSq : ∀ {v : List Bool → List Bool}, PolyTimeComputable v →
       PolyTimeComputable fun z => rabin_fSq A z (v z) := by
     intro v hv
-    have h := rabin_comp H.modExp (hv.pairEncode ((polyTimeComputable_const [true, false]).pairEncode hW))
+    have h := PolyTimeComputable.comp' H.modExp (hv.pairEncode ((polyTimeComputable_const [true, false]).pairEncode hW))
     unfold rabin_fSq
     exact h
   have hT : PolyTimeComputable fun z => [rabin_fTest A z] := by
     have h := polyTimeComputable_and
       (p := fun z => decide (listToNat (rabin_fSq A z (rabin_fZ A z)) ≤ listToNat (rabin_fSq A z (rabin_fX z))))
       (q := fun z => decide (listToNat (rabin_fSq A z (rabin_fX z)) ≤ listToNat (rabin_fSq A z (rabin_fZ A z))))
-      (rabin_le_poly H (hSq hZ) (hSq hX)) (rabin_le_poly H (hSq hX) (hSq hZ))
+      (H.le_poly (hSq hZ) (hSq hX)) (H.le_poly (hSq hX) (hSq hZ))
     unfold rabin_fTest
     exact h
-  have hR := rabin_comp polyTimeComputable_pairSndD (rabin_comp H.divMod (hZ.pairEncode hW))
-  have hS := rabin_comp H.sub ((rabin_comp H.add (hX.pairEncode hw)).pairEncode hR)
+  have hR := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hZ.pairEncode hW))
+  have hS := PolyTimeComputable.comp' H.sub ((PolyTimeComputable.comp' H.add (hX.pairEncode hw)).pairEncode hR)
   have hD : PolyTimeComputable (rabin_fD A) := by
-    have h := rabin_comp polyTimeComputable_pairSndD (rabin_comp H.divMod (hS.pairEncode hW))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hS.pairEncode hW))
     unfold rabin_fD
     exact h
   have hG : PolyTimeComputable (rabin_fG A) := by
-    have h := rabin_comp polyTimeComputable_pairFstD (rabin_comp H.xgcd (hD.pairEncode hW))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' H.xgcd (hD.pairEncode hW))
     unfold rabin_fG
     exact h
-  have hO := rabin_comp (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam
-  have hZr := rabin_comp H.sub (hO.pairEncode hO)
-  have hTr' := rabin_comp (polyTimeComputable_pairDropPoly .var) (hG.pairEncode (hZr.append hG))
+  have hO := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam
+  have hZr := PolyTimeComputable.comp' H.sub (hO.pairEncode hO)
+  have hTr' := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var) (hG.pairEncode (hZr.append hG))
   have hTr : PolyTimeComputable fun z =>
       (subStr (pairEncode (List.replicate (NUPPT.inParam z).length true)
         (List.replicate (NUPPT.inParam z).length true)) ++ rabin_fG A z).drop (rabin_fG A z).length := by
@@ -1743,7 +1622,7 @@ private theorem rabin_mod_lt_two_pow {v N W : ℕ} (hv : v < 2 ^ W) (hN : N < 2
 
 /-- **The string computation is `A'`**: `rabin_fOut A = rabinFactorRaw A`.
 
-**Proof sketch.** The padded modulus word reads as `N` and is longer than `2|z|`, `2|x|`, `|x| + |N|` (`rabin_listToNat_zeros_append`), so `modExpStr`, `divModStr`, `addStr`, `subStr` and `xgcdStr` read back exactly (`listToNat_natToList`, also for `N = 0`, where `v mod 0 = v`). The test is `z² mod N = x² mod N`; the gcd word reads as `gcd(d, N)` with `d = ((x + N) ∸ (z mod N)) mod N`, which is `((x : Z_N) − z).val` (`Nat.cast_sub`, `ZMod.val_natCast`; for `N = 0` the test forces `z = x` and both are `0`); the truncation is the `n`-bit numeral (`rabin_drop_zeros_append`). -/
+**Proof sketch.** The padded modulus word reads as `N` and is longer than `2|z|`, `2|x|`, `|x| + |N|` (`listToNat_natToList_zero_append`), so `modExpStr`, `divModStr`, `addStr`, `subStr` and `xgcdStr` read back exactly (`listToNat_natToList`, also for `N = 0`, where `v mod 0 = v`). The test is `z² mod N = x² mod N`; the gcd word reads as `gcd(d, N)` with `d = ((x + N) ∸ (z mod N)) mod N`, which is `((x : Z_N) − z).val` (`Nat.cast_sub`, `ZMod.val_natCast`; for `N = 0` the test forces `z = x` and both are `0`); the truncation is the `n`-bit numeral (`natToList_zero_append_drop`). -/
 private theorem rabin_fOut_eq (A : NUPPT) (z : List Bool) : rabin_fOut A z = rabinFactorRaw A z := by
   have hYv : rabin_fY z = natToList (NUPPT.inArg z).length
       (listToNat (rabin_fX z) ^ 2 % listToNat (NUPPT.inArg z)) := by
@@ -1762,7 +1641,7 @@ private theorem rabin_fOut_eq (A : NUPPT) (z : List Bool) : rabin_fOut A z = rab
     simp only [hK, List.length_append, List.length_cons, List.length_nil]; omega
   set Wp := subStr (pairEncode K K) ++ w with hWp
   have hWv : listToNat Wp = listToNat w := by
-    rw [hWp, subStr_pairEncode, Nat.sub_self, rabin_listToNat_zeros_append]
+    rw [hWp, subStr_pairEncode, Nat.sub_self, listToNat_natToList_zero_append]
   have hWl : Wp.length = K.length + w.length := by
     rw [hWp, List.length_append, subStr_pairEncode, length_natToList]
   have hNW : listToNat w < 2 ^ Wp.length :=
@@ -1817,7 +1696,7 @@ private theorem rabin_fOut_eq (A : NUPPT) (z : List Bool) : rabin_fOut A z = rab
     · exact (Nat.gcd_le_left _ hpos).trans_lt hdlt
   have hz0 : subStr (pairEncode (List.replicate n true) (List.replicate n true)) = natToList n 0 := by
     rw [subStr_pairEncode, List.length_replicate, Nat.sub_self]
-  rw [hz0, rabin_drop_zeros_append, hG]
+  rw [hz0, natToList_zero_append_drop, hG]
   -- the residue of `x − z` is `d`
   have hval : ((listToNat xs : ZMod (listToNat w)) - (listToNat zs : ZMod (listToNat w))).val = d := by
     rcases Nat.eq_zero_or_pos (listToNat w) with h0 | hpos
@@ -2013,7 +1892,7 @@ private theorem rabin_core (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (z : Distinc
     have hmb : List.ofFn (modulusBits n z) = i := by rw [modulusBits_eq, ← natToList_eq]
     have hiN : listToNat i = z.p * z.q := listToNat_natToList hNlt
     have hil : i.length = 2 * n := length_natToList _ _
-    have hv := rabin_getD_spec hNpos (Nat.size (z.p * z.q)) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)
+    have hv := sampleUnitL_getD_spec hNpos (Nat.size (z.p * z.q)) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)
     simp only [NUPPT.inverter_eq_some_iff, hmb, rabinFactorer_runAt, rabin_fCoinsEquiv_ofFn,
       List.take_left' (List.length_ofFn (f := s)), List.drop_left' (List.length_ofFn (f := s)),
       ← NUPPT.runAt_eq, hiN, hil, unitSampleStr_eq, listToNat_natToList (hv.1.trans hNlt), Succ]
@@ -2697,26 +2576,12 @@ def blumInvRaw (z : List Bool) : List Bool :=
     (blumInvNat (listToNat (pairFstD (pairFstD (NUPPT.inArg z))))
       (listToNat (pairSndD (pairFstD (NUPPT.inArg z)))) (listToNat (pairSndD (NUPPT.inArg z))))
 
-/-- In `Z_0 = ℤ` the inverse of a natural number is its sign, so its value is at most `1` (copy of the rsa fill's private `rsa_val_inv_zero_le`). -/
-private theorem rabin_val_inv_zero_le (e : ℕ) : ((e : ZMod 0)⁻¹).val ≤ 1 := by
-  show (Int.sign (e : ℤ)).natAbs ≤ 1
-  rw [Int.natAbs_sign]
-  split_ifs <;> omega
-
-/-- `mulStr` reads back exactly: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧` (`mulStr_pairEncode`). -/
-private theorem rabin_listToNat_mulStr (a b : List Bool) :
-    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b := by
-  rw [mulStr_pairEncode]
-  exact listToNat_natToList (by
-    rw [pow_add]
-    exact Nat.mul_lt_mul'' (listToNat_lt_two_pow a) (listToNat_lt_two_pow b))
-
 /-- `|u|` leading zeros before `v` (`subStr ⟨u, u⟩ ++ v`). -/
 private def rabin_zpad (u v : List Bool) : List Bool := subStr (pairEncode u u) ++ v
 
 /-- Leading zeros do not change the value. -/
 private theorem rabin_listToNat_zpad (u v : List Bool) : listToNat (rabin_zpad u v) = listToNat v := by
-  rw [rabin_zpad, subStr_pairEncode, Nat.sub_self, rabin_listToNat_zeros_append]
+  rw [rabin_zpad, subStr_pairEncode, Nat.sub_self, listToNat_natToList_zero_append]
 
 /-- The padded word has length `|u| + |v|`. -/
 private theorem rabin_length_zpad (u v : List Bool) : (rabin_zpad u v).length = u.length + v.length := by
@@ -2726,7 +2591,7 @@ private theorem rabin_length_zpad (u v : List Bool) : (rabin_zpad u v).length =
 private theorem rabin_zpad_poly (H : ArithmeticFP) {fu fv : List Bool → List Bool}
     (hu : PolyTimeComputable fu) (hv : PolyTimeComputable fv) :
     PolyTimeComputable fun z => rabin_zpad (fu z) (fv z) := by
-  have h := (rabin_comp H.sub (hu.pairEncode hu)).append hv
+  have h := (PolyTimeComputable.comp' H.sub (hu.pairEncode hu)).append hv
   unfold rabin_zpad
   exact h
 
@@ -2758,7 +2623,7 @@ private def rabin_crtW (pw qw yw : List Bool) : List Bool :=
 /-- The exponent word reads as `p/4 + 1`. -/
 private theorem rabin_listToNat_cE (pw : List Bool) : listToNat (rabin_cE pw) = listToNat pw / 4 + 1 := by
   rw [rabin_cE, listToNat_addStr, divModStr_pairEncode, pairFstD_pairEncode, rabin_listToNat_four,
-    rabin_listToNat_one,
+    listToNat_singleton_true,
     listToNat_natToList ((Nat.div_le_self _ _).trans_lt (listToNat_lt_two_pow pw))]
 
 /-- The power word reads as `y^{p/4+1} mod p`. -/
@@ -2777,13 +2642,13 @@ private theorem rabin_listToNat_cPow (pw yw : List Bool) :
 private theorem rabin_listToNat_cInv (pw qw : List Bool) :
     listToNat (rabin_cInv pw qw) = ((listToNat qw : ZMod (listToNat pw))⁻¹).val := by
   have hz : listToNat ([false] ++ pw) = listToNat pw := by
-    rw [rabin_listToNat_append, show listToNat [false] = 0 by rw [listToNat_eq]; rfl, zero_mul, zero_add]
+    rw [listToNat_append, show listToNat [false] = 0 by rw [listToNat_eq]; rfl, zero_mul, zero_add]
   rw [rabin_cInv, xgcdStr_pairEncode, pairSndD_pairEncode, hz]
   apply listToNat_natToList
   rw [List.length_append, List.length_singleton]
   rcases Nat.eq_zero_or_pos (listToNat pw) with h0 | hpos
   · rw [h0]
-    exact (rabin_val_inv_zero_le _).trans_lt (Nat.one_lt_two_pow (by omega))
+    exact (val_inv_natCast_zmod_zero_le _).trans_lt (Nat.one_lt_two_pow (by omega))
   · haveI : NeZero (listToNat pw) := ⟨hpos.ne'⟩
     exact (ZMod.val_lt _).trans ((listToNat_lt_two_pow pw).trans_le
       (Nat.pow_le_pow_right (by norm_num) (by omega)))
@@ -2792,7 +2657,7 @@ private theorem rabin_listToNat_cInv (pw qw : List Bool) :
 private theorem rabin_listToNat_cTerm (pw qw yw : List Bool) :
     listToNat (rabin_cTerm pw qw yw) = listToNat yw ^ (listToNat pw / 4 + 1) % listToNat pw *
       (listToNat qw * ((listToNat qw : ZMod (listToNat pw))⁻¹).val) := by
-  rw [rabin_cTerm, rabin_listToNat_mulStr, rabin_listToNat_mulStr, rabin_listToNat_cPow,
+  rw [rabin_cTerm, listToNat_mulStr, listToNat_mulStr, rabin_listToNat_cPow,
     rabin_listToNat_cInv]
 
 /-- **The CRT word reads as `blumInvNat p q y`** (every intermediate word is exact: the padded widths cover the degenerate moduli `0`). -/
@@ -2804,19 +2669,19 @@ private theorem rabin_listToNat_crtW (pw qw yw : List Bool) :
       (listToNat pw * ((listToNat pw : ZMod (listToNat qw))⁻¹).val) := by
     rw [rabin_cSum, listToNat_addStr, rabin_listToNat_cTerm, rabin_listToNat_cTerm]
   rw [rabin_crtW, divModStr_pairEncode, pairSndD_pairEncode, rabin_listToNat_zpad,
-    rabin_listToNat_mulStr, listToNat_natToList, blumInvNat, hS]
+    listToNat_mulStr, listToNat_natToList, blumInvNat, hS]
   rw [rabin_length_zpad, hS]
   rcases Nat.eq_zero_or_pos (listToNat pw * listToNat qw) with h0 | hpos
   · rw [h0, Nat.mod_zero, ← hS]
     exact (listToNat_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
   · refine (Nat.mod_lt _ hpos).trans ?_
-    rw [← rabin_listToNat_mulStr]
+    rw [← listToNat_mulStr]
     exact (listToNat_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
 
 /-- The CRT word is polynomial-time.
 
 **Proof sketch.** Each word is one bundle field on pairs of earlier words, in applied form
-(`rabin_comp`) and folded into its definition by `unfold`: the exponent (`H.divMod`, `H.add`),
+(`PolyTimeComputable.comp'`) and folded into its definition by `unfold`: the exponent (`H.divMod`, `H.add`),
 the power (`H.modExp`, with the zero padding `rabin_zpad_poly`), the inverse (`H.xgcd` behind
 `polyTimeComputable_prepend [false]`), the summands and `N` (`H.mul`), the sum (`H.add`) and
 the final residue (`H.divMod`). -/
@@ -2826,52 +2691,52 @@ private theorem rabin_crtW_poly (H : ArithmeticFP) {fp fq fy : List Bool → Lis
   have hE : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
       PolyTimeComputable fun z => rabin_cE (f z) := by
     intro f hf
-    have h := rabin_comp H.add ((rabin_comp polyTimeComputable_pairFstD
-      (rabin_comp H.divMod (hf.pairEncode (polyTimeComputable_const [true, false, false])))).pairEncode
+    have h := PolyTimeComputable.comp' H.add ((PolyTimeComputable.comp' polyTimeComputable_pairFstD
+      (PolyTimeComputable.comp' H.divMod (hf.pairEncode (polyTimeComputable_const [true, false, false])))).pairEncode
       (polyTimeComputable_const [true]))
     unfold rabin_cE
     exact h
   have hPow : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
       PolyTimeComputable fun z => rabin_cPow (f z) (g z) := by
     intro f g hf hg
-    have h := rabin_comp H.modExp (hg.pairEncode ((hE hf).pairEncode (rabin_zpad_poly H hg hf)))
+    have h := PolyTimeComputable.comp' H.modExp (hg.pairEncode ((hE hf).pairEncode (rabin_zpad_poly H hg hf)))
     unfold rabin_cPow
     exact h
   have hInv : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
       PolyTimeComputable fun z => rabin_cInv (f z) (g z) := by
     intro f g hf hg
-    have h := rabin_comp polyTimeComputable_pairSndD
-      (rabin_comp H.xgcd (hg.pairEncode ((polyTimeComputable_prepend [false]).comp hf)))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD
+      (PolyTimeComputable.comp' H.xgcd (hg.pairEncode ((polyTimeComputable_prepend [false]).comp hf)))
     unfold rabin_cInv
     exact h
   have hTerm : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
       PolyTimeComputable fun z => rabin_cTerm (f z) (g z) (fy z) := by
     intro f g hf hg
-    have h := rabin_comp H.mul ((hPow hf hy).pairEncode (rabin_comp H.mul (hg.pairEncode (hInv hf hg))))
+    have h := PolyTimeComputable.comp' H.mul ((hPow hf hy).pairEncode (PolyTimeComputable.comp' H.mul (hg.pairEncode (hInv hf hg))))
     unfold rabin_cTerm
     exact h
   have hSum : PolyTimeComputable fun z => rabin_cSum (fp z) (fq z) (fy z) := by
-    have h := rabin_comp H.add ((hTerm hp hq).pairEncode (hTerm hq hp))
+    have h := PolyTimeComputable.comp' H.add ((hTerm hp hq).pairEncode (hTerm hq hp))
     unfold rabin_cSum
     exact h
-  have h := rabin_comp polyTimeComputable_pairSndD (rabin_comp H.divMod
-    (hSum.pairEncode (rabin_zpad_poly H hSum (rabin_comp H.mul (hp.pairEncode hq)))))
+  have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod
+    (hSum.pairEncode (rabin_zpad_poly H hSum (PolyTimeComputable.comp' H.mul (hp.pairEncode hq)))))
   unfold rabin_crtW
   exact h
 
 /-- The truncation of a word `v` to the width of `y`: `(⟦0⟧_{|y|} ++ v).drop |v|`. -/
 private def rabin_trunc (y v : List Bool) : List Bool := (subStr (pairEncode y y) ++ v).drop v.length
 
-/-- The truncation is the numeral of the word's value at the width of `y` (`rabin_drop_zeros_append`). -/
+/-- The truncation is the numeral of the word's value at the width of `y` (`natToList_zero_append_drop`). -/
 private theorem rabin_trunc_eq (y v : List Bool) : rabin_trunc y v = natToList y.length (listToNat v) := by
-  rw [rabin_trunc, subStr_pairEncode, Nat.sub_self, rabin_drop_zeros_append]
+  rw [rabin_trunc, subStr_pairEncode, Nat.sub_self, natToList_zero_append_drop]
 
 /-- The truncation is polynomial-time (`H.sub`, `PolyTimeComputable.append`, `polyTimeComputable_pairDropPoly var`). -/
 private theorem rabin_trunc_poly (H : ArithmeticFP) {fy fv : List Bool → List Bool}
     (hy : PolyTimeComputable fy) (hv : PolyTimeComputable fv) :
     PolyTimeComputable fun z => rabin_trunc (fy z) (fv z) := by
-  have h' := rabin_comp (polyTimeComputable_pairDropPoly .var)
-    (hv.pairEncode ((rabin_comp H.sub (hy.pairEncode hy)).append hv))
+  have h' := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var)
+    (hv.pairEncode ((PolyTimeComputable.comp' H.sub (hy.pairEncode hy)).append hv))
   have h : PolyTimeComputable fun z => (subStr (pairEncode (fy z) (fy z)) ++ fv z).drop (fv z).length := by
     refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h'
     simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
@@ -2892,9 +2757,9 @@ field in applied form (`rabin_crtW_poly`), and the truncation is `H.sub` on `⟨
 `PolyTimeComputable.append` and `polyTimeComputable_pairDropPoly var` (`rabin_trunc_poly`). -/
 theorem polyTimeComputable_blumInvRaw (H : ArithmeticFP) : PolyTimeComputable blumInvRaw := by
   have hw := NUPPT.polyTimeComputable_inArg
-  have hp := rabin_comp polyTimeComputable_pairFstD (rabin_comp polyTimeComputable_pairFstD hw)
-  have hq := rabin_comp polyTimeComputable_pairSndD (rabin_comp polyTimeComputable_pairFstD hw)
-  have hy := rabin_comp polyTimeComputable_pairSndD hw
+  have hp := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' polyTimeComputable_pairFstD hw)
+  have hq := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' polyTimeComputable_pairFstD hw)
+  have hy := PolyTimeComputable.comp' polyTimeComputable_pairSndD hw
   have h := rabin_trunc_poly H hy (rabin_crtW_poly H hp hq hy)
   refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
   rw [rabin_trunc_eq, rabin_listToNat_crtW, blumInvRaw]
@@ -3076,7 +2941,7 @@ theorem blumSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n)
   generalize rabinGenParams (· % 4 = 3) blumDefault n (List.ofFn r) = R
   have hV := rabin_blumValid_indexOf _ R
   have hM := rabin_blumMod_indexOf _ R
-  have hv := rabin_getD_spec (rabin_N_pos R) (Nat.size (R.z.p * R.z.q)) (rsaBlock.eval n)
+  have hv := sampleUnitL_getD_spec (rabin_N_pos R) (Nat.size (R.z.p * R.z.q)) (rsaBlock.eval n)
     (rsaTrials.eval n) (List.ofFn s)
   set v := (sampleUnitL (R.z.p * R.z.q) (Nat.size (R.z.p * R.z.q)) (rsaBlock.eval n)
     (rsaTrials.eval n) (List.ofFn s)).getD (1 % (R.z.p * R.z.q)) with hvdef
@@ -3245,7 +3110,7 @@ private theorem rabin_statClose_blumDec (m : ℕ) (R : RabinParams (· % 4 = 3)
           (listToNat (unitSampleStr (rabinIndexOf m R) n (List.ofFn s)) ^ 2 % listToNat (rabinIndexOf m R))) := by
     funext s
     rw [unitSampleStr_eq, listToNat_rabinIndexOf, hlen,
-      listToNat_natToList ((rabin_getD_spec (rabin_N_pos R) _ _ _ _).1.trans R.z.mul_lt)]
+      listToNat_natToList ((sampleUnitL_getD_spec (rabin_N_pos R) _ _ _ _).1.trans R.z.mul_lt)]
     congr 4
     rw [hM]
   have eY : (fun x : (ZMod (blumMod (rabinIndexOf m R)))ˣ => blumDec (rabinIndexOf m R)
@@ -3284,7 +3149,7 @@ theorem rabinBlumTrapdoor_sampleClose (H : ArithmeticFP) :
   intro n r
   by_cases hn : n < 3
   · rw [if_pos hn]
-    exact rabin_statClose_one _ _
+    exact statClose_one _ _
   rw [if_neg hn, rabinBlumTrapdoor_index, rabinBlumTrapdoor_sample]
   simp only [rabinBlumTrapdoor_decD, rabin_blumSampler_runAt]
   have h1 := ((rabin_statClose_blumDec _ (rabinGenParams (· % 4 = 3) blumDefault n (List.ofFn r)) n
@@ -3580,7 +3445,7 @@ private theorem rabin_rOut_eq (A : NUPPT) (z : List Bool) : rabin_rOut A z = rab
       listToNat_natToList ((Nat.div_le_self _ _).trans_lt (listToNat_lt_two_pow _))]
   have hT : rabin_rTest A z = decide (listToNat (rabin_rS A z) *
       (listToNat (pairFstD (NUPPT.inArg z)) / listToNat (rabin_rS A z)) = listToNat (pairFstD (NUPPT.inArg z))) := by
-    rw [rabin_rTest, rabin_listToNat_mulStr, hQ, Bool.eq_iff_iff]
+    rw [rabin_rTest, listToNat_mulStr, hQ, Bool.eq_iff_iff]
     simp only [Bool.and_eq_true, decide_eq_true_eq]
     omega
   rw [rabin_rOut, hT, rabinRootRaw, rabinRootStep, ← rabin_rS]
@@ -3597,25 +3462,25 @@ test (two `H.le`, `polyTimeComputable_and`), the truncated CRT word (`rabin_crtW
 `rabin_trunc_poly`), selected by `polyTimeComputable_ite`; each folded by `unfold`. -/
 private theorem rabin_rOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputable (rabin_rOut A) := by
   have hw := NUPPT.polyTimeComputable_inArg
-  have hN := rabin_comp polyTimeComputable_pairFstD hw
-  have hy := rabin_comp polyTimeComputable_pairSndD hw
+  have hN := PolyTimeComputable.comp' polyTimeComputable_pairFstD hw
+  have hy := PolyTimeComputable.comp' polyTimeComputable_pairSndD hw
   have hS : PolyTimeComputable (rabin_rS A) := by
-    have h := rabin_comp A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
+    have h := PolyTimeComputable.comp' A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
       NUPPT.polyTimeComputable_inParam hN NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
     unfold rabin_rS
     exact h
   have hQ : PolyTimeComputable (rabin_rQ A) := by
-    have h := rabin_comp polyTimeComputable_pairFstD (rabin_comp H.divMod (hN.pairEncode hS))
+    have h := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' H.divMod (hN.pairEncode hS))
     unfold rabin_rQ
     exact h
-  have hM := rabin_comp H.mul (hS.pairEncode hQ)
+  have hM := PolyTimeComputable.comp' H.mul (hS.pairEncode hQ)
   have hT : PolyTimeComputable fun z => [rabin_rTest A z] := by
     have h := polyTimeComputable_and
       (p := fun z => decide (listToNat (mulStr (pairEncode (rabin_rS A z) (rabin_rQ A z))) ≤
         listToNat (pairFstD (NUPPT.inArg z))))
       (q := fun z => decide (listToNat (pairFstD (NUPPT.inArg z)) ≤
         listToNat (mulStr (pairEncode (rabin_rS A z) (rabin_rQ A z)))))
-      (rabin_le_poly H hM hN) (rabin_le_poly H hN hM)
+      (H.le_poly hM hN) (H.le_poly hN hM)
     unfold rabin_rTest
     exact h
   have h := polyTimeComputable_ite (p := rabin_rTest A) hT
diff --git a/TCSlib/Cryptography/HardcoreBit/Basic.lean b/TCSlib/Cryptography/HardcoreBit/Basic.lean
index a039599a..39ff2cfa 100644
--- a/TCSlib/Cryptography/HardcoreBit/Basic.lean
+++ b/TCSlib/Cryptography/HardcoreBit/Basic.lean
@@ -37,6 +37,8 @@ independent and uniform, a subset XOR of uniform strings is uniform) are express
 * `pushesUniform_eval`, `pushesUniform_eval_pair`, `PushesUniform.prodMap`,
   `pushesUniform_of_surjective`: coordinates and pairs of coordinates of a uniform
   tuple, products, and surjective additive homomorphisms push uniform to uniform.
+* `pushesUniform_restrict`: restricting a uniform table along an injection gives a uniform
+  table.
 
 ## References
 
@@ -207,6 +209,30 @@ theorem pushesUniform_fst [Nonempty β] : PushesUniform (Prod.fst : α × β →
 theorem pushesUniform_snd [Nonempty α] : PushesUniform (Prod.snd : α × β → β) :=
   (pushesUniform_equiv (Equiv.prodComm α β)).comp pushesUniform_fst
 
+/-- **Restricting a uniform table along an injection gives a uniform table**: for an injective
+`r : J → I`, the map `R ↦ R ∘ r` pushes the uniform distribution on `I → O` to the uniform
+distribution on `J → O`.
+
+**Proof sketch.** Split `I` into the image of `r` and its complement (`Equiv.ofInjective`,
+`Equiv.Set.sumCompl`). A table is the pair of its two restrictions (`Equiv.sumArrowEquivProdArrow`),
+and `R ∘ r` is the first one (`pushesUniform_equiv`, `pushesUniform_fst`). -/
+theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J]
+    [DecidableEq J] [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) :
+    PushesUniform (fun R : I → O => fun j => R (r j)) := by
+  classical
+  let e₁ : J ⊕ ((Set.range r)ᶜ : Set I) ≃ I :=
+    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
+      (Equiv.Set.sumCompl (Set.range r))
+  let e : (I → O) ≃ (J → O) × (((Set.range r)ᶜ : Set I) → O) :=
+    (Equiv.arrowCongr e₁.symm (Equiv.refl O)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
+  have he : (fun R : I → O => fun j => R (r j)) = fun R => (e R).1 := by
+    funext R j
+    have h1 : e₁ (Sum.inl j) = r j := rfl
+    show R (r j) = R (e₁ (Sum.inl j))
+    rw [h1]
+  rw [he]
+  exact (pushesUniform_equiv e).comp pushesUniform_fst
+
 /-- A product of maps pushing uniform to uniform pushes uniform to uniform: the
 coordinates of a uniform pair are independent.
 
diff --git a/TCSlib/Cryptography/NumberTheory/Primality.lean b/TCSlib/Cryptography/NumberTheory/Primality.lean
index 0897aded..4e32f7d0 100644
--- a/TCSlib/Cryptography/NumberTheory/Primality.lean
+++ b/TCSlib/Cryptography/NumberTheory/Primality.lean
@@ -75,6 +75,8 @@ density as `1/n` (it is `1/(2n)`, Claim-33.1).
   `TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp`,
   `TCSlib.Cryptography.NumberTheory.statClose_samplePrime`,
   `TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt` — [PS10, Lemma 51.17].
+* `TCSlib.Cryptography.NumberTheory.listToNat_nil`, `listToNat_cons`, `listToNat_append`,
+  `listToNat_singleton_true` — the equations of the binary reading `listToNat`.
 
 ## References
 
@@ -671,6 +673,26 @@ theorem listToNat_eq (w : List Bool) :
 theorem bitsToNat_eq_listToNat {n : ℕ} (b : Fin n → Bool) : bitsToNat b = listToNat (List.ofFn b) :=
   rfl
 
+/-- The empty word reads as `0`: `listToNat [] = 0`. -/
+theorem listToNat_nil : listToNat [] = 0 := by
+  rw [listToNat_eq, List.foldl_nil]
+
+/-- **Prepending a bit** (most significant first): `⟦b :: l⟧ = [b] · 2^{|l|} + ⟦l⟧`, with
+`[b] = 1` if `b` and `0` otherwise. -/
+theorem listToNat_cons (b : Bool) (l : List Bool) :
+    listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l := by
+  rw [listToNat_eq, listToNat_eq, List.foldl_cons, foldl_bits_eq, Nat.mul_zero, Nat.zero_add]
+
+/-- **Concatenation** (most significant first): `⟦a ++ b⟧ = ⟦a⟧ · 2^{|b|} + ⟦b⟧`. -/
+theorem listToNat_append (a b : List Bool) :
+    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
+  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, foldl_bits_eq]
+
+/-- The one-bit word `[true]` reads as `1`: `listToNat [true] = 1`. -/
+theorem listToNat_singleton_true : listToNat [true] = 1 := by
+  rw [listToNat_eq, List.foldl_cons, List.foldl_nil]
+  rfl
+
 /-- The coin polynomial of `SamplePrime` at `T = 2n²` trials of `n` bits: `2n² · n`. -/
 def samplePrimeCoins : PolyExpr :=
   PolyExpr.mul (PolyExpr.mul (PolyExpr.const 2) (PolyExpr.pow PolyExpr.var 2)) PolyExpr.var
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean
index 45d6fef9..c1fbe98d 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean
@@ -16,8 +16,8 @@ set_option autoImplicit false
 
 Generic facts used by the fill ladder of `col_zk` (`ThreeColoring/Simulator.lean`, the proof of
 [PS10, Proposition 128.8]): reading disjoint fields of a uniform tape gives independent uniform
-fields (`pushesUniform_restrict`, `pushesUniform_offsetTable`), and the bookkeeping of the error
-function (`negligible_colZKErr`).
+fields (`pushesUniform_offsetTable`, through `HardcoreBit.pushesUniform_restrict` of
+`HardcoreBit/Basic.lean`), and the bookkeeping of the error function (`negligible_colZKErr`).
 
 ## Main definitions
 
@@ -25,8 +25,6 @@ function (`negligible_colZKErr`).
 
 ## Main results
 
-* `TCSlib.Cryptography.ColZK.pushesUniform_restrict` — restricting a uniform table along an
-  injective map gives a uniform table.
 * `TCSlib.Cryptography.ColZK.pushesUniform_offsetTable`, `pushesUniform_blockFields` — disjoint
   fields of a uniform tape are independent and uniform.
 * `TCSlib.Cryptography.ColZK.exists_fixSeed`, `distAdv_seed_to_coins`,
@@ -47,30 +45,6 @@ open Complexity Turing
 
 /-! ### Uniform fields of a uniform tape -/
 
-/-- **Restricting a uniform table along an injective map gives a uniform table**: for an
-injective `r : J → I`, `R ↦ R ∘ r` pushes the uniform distribution on `I → O` to the uniform
-distribution on `J → O`. Generic form (any finite `J`) of `pushesUniform_comp_injective` of
-`Asymptotic/MultiMessage.lean` (stated there for `J = Fin (q + 1)`; that file is not upstream of
-this one), with the same proof.
-
-**Proof sketch.** Split `I` into the image of `r` and its complement (`Equiv.ofInjective`,
-`Equiv.Set.sumCompl`): the table is the pair of its restrictions
-(`Equiv.sumArrowEquivProdArrow`), and `R ∘ r` is the first one (`pushesUniform_fst`). -/
-theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
-    [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) :
-    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
-  classical
-  let e₁ : J ⊕ ((Set.range r)ᶜ : Set I) ≃ I :=
-    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
-      (Equiv.Set.sumCompl (Set.range r))
-  let e : (I → O) ≃ (J → O) × (((Set.range r)ᶜ : Set I) → O) :=
-    (Equiv.arrowCongr e₁.symm (Equiv.refl O)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
-  have he : (fun R : I → O => fun j => R (r j)) = fun R => (e R).1 := by
-    funext R j
-    simp [e, e₁]
-  rw [he]
-  exact (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
-
 /-- Entry `(i, j)` of an `n × k` table sits at position `i k + j < n k`. -/
 theorem table_index_lt {n k : ℕ} (i : Fin n) (j : Fin k) : (i : ℕ) * k + j < n * k := by
   have h1 := i.isLt
@@ -96,8 +70,8 @@ theorem table_index_inj {n k : ℕ} {i i' : Fin n} {j j' : Fin k}
 
 **Proof sketch.** The two fields read the tape along the injective map
 `Fin a ⊕ (Fin n × Fin k) → Fin L`, `inl i ↦ i`, `inr (i, j) ↦ a + i k + j` (`table_index_inj`),
-so `pushesUniform_restrict` applies; the pair of fields is that restriction followed by the
-bijection `Equiv.sumArrowEquivProdArrow` and `Equiv.curry`. -/
+so `HardcoreBit.pushesUniform_restrict` applies; the pair of fields is that restriction followed
+by the bijection `Equiv.sumArrowEquivProdArrow` and `Equiv.curry`. -/
 theorem pushesUniform_offsetTable {L a n k : ℕ} (h : a + n * k ≤ L) :
     HardcoreBit.PushesUniform (fun t : Fin L → Bool =>
       ((fun i : Fin a => t (Fin.castLE (by omega) i)),
@@ -119,7 +93,7 @@ theorem pushesUniform_offsetTable {L a n k : ℕ} (h : a + n * k ≤ L) :
   let e : (Fin a ⊕ (Fin n × Fin k) → Bool) ≃ (Fin a → Bool) × (Fin n → Fin k → Bool) :=
     (Equiv.sumArrowEquivProdArrow _ _ _).trans
       (Equiv.prodCongr (Equiv.refl _) (Equiv.curry _ _ _))
-  exact (pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)
+  exact (HardcoreBit.pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)
 
 /-- **Four disjoint fields of a uniform tape are independent and uniform**: for offsets
 `a₁ ≤ o₂`, `o₂ + a₂ ≤ o₃`, `o₃ + n k ≤ o₄`, `o₄ + a₄ ≤ L`, the map sending a tape `t` of `L`
@@ -129,8 +103,8 @@ simulator, `colSimBlock`).
 
 **Proof sketch.** The fields read the tape along an injective map
 `((Fin a₁ ⊕ Fin a₂) ⊕ (Fin n × Fin k)) ⊕ Fin a₄ → Fin L` (disjoint ranges, `table_index_inj`), so
-`pushesUniform_restrict` applies, followed by the bijection `Equiv.sumArrowEquivProdArrow` (three
-times) and `Equiv.curry`. -/
+`HardcoreBit.pushesUniform_restrict` applies, followed by the bijection
+`Equiv.sumArrowEquivProdArrow` (three times) and `Equiv.curry`. -/
 theorem pushesUniform_blockFields {L a₁ o₂ a₂ o₃ n k o₄ a₄ : ℕ} (h₁ : a₁ ≤ o₂)
     (h₂ : o₂ + a₂ ≤ o₃) (h₃ : o₃ + n * k ≤ o₄) (h₄ : o₄ + a₄ ≤ L) :
     HardcoreBit.PushesUniform (fun t : Fin L → Bool =>
@@ -161,7 +135,7 @@ theorem pushesUniform_blockFields {L a₁ o₂ a₂ o₃ n k o₄ a₄ : ℕ} (h
     (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
       ((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
         (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.curry _ _ _))) (Equiv.refl _))
-  exact (pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)
+  exact (HardcoreBit.pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)
 
 /-! ### Averaging over seeds -/
 

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/replay.log =====

TCSlib/Complexity/Randomized/Build/IterateFind rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/SamplingFinDist rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Permutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 65s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 7s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/InnerProduct rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/GoldreichLevin rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/ThreeQuarters rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 42s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 76s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 23s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/RSA rc=0 25s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/QuadraticResidues rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Rabin rc=0 16s errors=0 sorry=0
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 28s errors=0 sorry=0
TCSlib/Cryptography/Candidates/ElGamal rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/NoFixedBit rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColRepWitness rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColRepSound rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 178s errors=0 sorry=0
# done 2026-11-07T02:27:02Z

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/sorry-census-base.txt =====

   2 TCSlib/BooleanAnalysis/BLR/LowDegree.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/Anticoncentration.lean
   1 TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Walk.lean
   1 TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/Condorcet.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/MajorityIsStablest.lean
   9 TCSlib/BooleanAnalysis/GaussianSpace/MaxCut.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/MaxCutAlgorithm.lean
   9 TCSlib/BooleanAnalysis/GaussianSpace/OrnsteinUhlenbeck.lean
   6 TCSlib/BooleanAnalysis/GaussianSpace/SumInvariance.lean
  10 TCSlib/BooleanAnalysis/GaussianSpace/SurfaceExamples.lean
   4 TCSlib/BooleanAnalysis/GaussianSpace/SurfaceRelaxation.lean
   8 TCSlib/BooleanAnalysis/GaussianSpace/UniqueGames.lean
   7 TCSlib/BooleanAnalysis/Hypercontractivity/SharpThresholds/General.lean
   1 TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean
   1 TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean
   2 TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean
   1 TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean
   2 TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean
   5 TCSlib/BooleanAnalysis/ThresholdFunctions/Gaussian.lean
   3 TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean
   1 TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean
   1 TCSlib/Complexity/ClassNP/NDNormalForm.lean
   2 TCSlib/Complexity/ClassP/TimeConstructible.lean
  21 TCSlib/Complexity/ClassPSPACE/TQBF.lean
   2 TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
   1 TCSlib/Complexity/Expanders/Chernoff.lean
  10 TCSlib/Complexity/FormulaKit/Emit.lean
  10 TCSlib/Complexity/FormulaKit/Gate.lean
   9 TCSlib/Complexity/RAMSimulation/Classes.lean
   2 TCSlib/Complexity/RAMSimulation/Simulation.lean
   3 TCSlib/Complexity/RAMSimulation/WordSize.lean
   1 TCSlib/Complexity/Randomized/NonUniform.lean
   4 TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
   1 TCSlib/Complexity/SpaceComplexity/Savitch.lean
   5 TCSlib/Complexity/TuringMachine/Build/Loop.lean
   3 TCSlib/Complexity/TuringMachine/Build/Primitives.lean
   4 TCSlib/Complexity/TuringMachine/Build/RecordTable.lean
   2 TCSlib/Complexity/TuringMachine/Build/Wrappers.lean
   3 TCSlib/Complexity/TuringMachine/Composition.lean
   1 TCSlib/Complexity/TuringMachine/Encoding.lean
   1 TCSlib/Complexity/TuringMachine/Simulation.lean
   1 TCSlib/Cryptography/Asymptotic/Universal.lean
   1 TCSlib/Cryptography/Asymptotic/UniversalPadding.lean
   7 TCSlib/ErrorCorrectingCodes/MRRW.lean
   8 TCSlib/GraphTheory/Core/Connectivity.lean
  17 TCSlib/GraphTheory/Core/CycleSpaceBondSpace.lean
  39 TCSlib/GraphTheory/Core/DirectedGraphs.lean
  17 TCSlib/GraphTheory/Core/EdgeColourings.lean
  18 TCSlib/GraphTheory/Core/EulerHamilton.lean
  22 TCSlib/GraphTheory/Core/GraphsAndSubgraphs.lean
  60 TCSlib/GraphTheory/Core/IndependentSetsCliques.lean
  19 TCSlib/GraphTheory/Core/Matchings.lean
  41 TCSlib/GraphTheory/Core/Networks.lean
  12 TCSlib/GraphTheory/Core/PlanarGraphs.lean
   8 TCSlib/GraphTheory/Core/Trees.lean
  51 TCSlib/GraphTheory/Core/VertexColourings.lean
  18 TCSlib/Programs/WordRAM/Extended.lean
   1 TCSlib/Tactics/Haves.lean
TOTAL 507

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/sorry-census-head.txt =====

   2 TCSlib/BooleanAnalysis/BLR/LowDegree.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/Anticoncentration.lean
   1 TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Walk.lean
   1 TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/Condorcet.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/MajorityIsStablest.lean
   9 TCSlib/BooleanAnalysis/GaussianSpace/MaxCut.lean
   2 TCSlib/BooleanAnalysis/GaussianSpace/MaxCutAlgorithm.lean
   9 TCSlib/BooleanAnalysis/GaussianSpace/OrnsteinUhlenbeck.lean
   6 TCSlib/BooleanAnalysis/GaussianSpace/SumInvariance.lean
  10 TCSlib/BooleanAnalysis/GaussianSpace/SurfaceExamples.lean
   4 TCSlib/BooleanAnalysis/GaussianSpace/SurfaceRelaxation.lean
   8 TCSlib/BooleanAnalysis/GaussianSpace/UniqueGames.lean
   7 TCSlib/BooleanAnalysis/Hypercontractivity/SharpThresholds/General.lean
   1 TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean
   1 TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean
   2 TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean
   1 TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean
   2 TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean
   5 TCSlib/BooleanAnalysis/ThresholdFunctions/Gaussian.lean
   3 TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean
   1 TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean
   1 TCSlib/Complexity/ClassNP/NDNormalForm.lean
   2 TCSlib/Complexity/ClassP/TimeConstructible.lean
  21 TCSlib/Complexity/ClassPSPACE/TQBF.lean
   2 TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
   1 TCSlib/Complexity/Expanders/Chernoff.lean
  10 TCSlib/Complexity/FormulaKit/Emit.lean
  10 TCSlib/Complexity/FormulaKit/Gate.lean
   9 TCSlib/Complexity/RAMSimulation/Classes.lean
   2 TCSlib/Complexity/RAMSimulation/Simulation.lean
   3 TCSlib/Complexity/RAMSimulation/WordSize.lean
   1 TCSlib/Complexity/Randomized/NonUniform.lean
   4 TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
   1 TCSlib/Complexity/SpaceComplexity/Savitch.lean
   5 TCSlib/Complexity/TuringMachine/Build/Loop.lean
   3 TCSlib/Complexity/TuringMachine/Build/Primitives.lean
   4 TCSlib/Complexity/TuringMachine/Build/RecordTable.lean
   2 TCSlib/Complexity/TuringMachine/Build/Wrappers.lean
   3 TCSlib/Complexity/TuringMachine/Composition.lean
   1 TCSlib/Complexity/TuringMachine/Encoding.lean
   1 TCSlib/Complexity/TuringMachine/Simulation.lean
   1 TCSlib/Cryptography/Asymptotic/Universal.lean
   1 TCSlib/Cryptography/Asymptotic/UniversalPadding.lean
   1 TCSlib/Cryptography/Candidates/Concrete.lean
   7 TCSlib/ErrorCorrectingCodes/MRRW.lean
   8 TCSlib/GraphTheory/Core/Connectivity.lean
  17 TCSlib/GraphTheory/Core/CycleSpaceBondSpace.lean
  39 TCSlib/GraphTheory/Core/DirectedGraphs.lean
  17 TCSlib/GraphTheory/Core/EdgeColourings.lean
  18 TCSlib/GraphTheory/Core/EulerHamilton.lean
  22 TCSlib/GraphTheory/Core/GraphsAndSubgraphs.lean
  60 TCSlib/GraphTheory/Core/IndependentSetsCliques.lean
  19 TCSlib/GraphTheory/Core/Matchings.lean
  41 TCSlib/GraphTheory/Core/Networks.lean
  12 TCSlib/GraphTheory/Core/PlanarGraphs.lean
   8 TCSlib/GraphTheory/Core/Trees.lean
  51 TCSlib/GraphTheory/Core/VertexColourings.lean
  18 TCSlib/Programs/WordRAM/Extended.lean
   1 TCSlib/Tactics/Haves.lean
TOTAL 508

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/axioms-new.log =====

'Complexity.IterateFind.find?_range_and_lt' depends on axioms: [propext, Quot.sound]
'Complexity.PolyTimeComputable.comp'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PolyTimeComputable.congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.abs_uexp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.foldl_bits_eq' depends on axioms: [propext]
'TCSlib.Cryptography.statClose_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.two_pow_size_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ArithmeticFP.le_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ArithmeticFP.prime_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_mulStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_natToList_zero_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_replicate_false' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.listToNat_replicate_true' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.natToList_mod_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.natToList_zero_append_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.subStr_self' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.val_inv_natCast_zmod_zero_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find?' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleUnitL_getD_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.listToNat_append' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.NumberTheory.listToNat_cons' depends on axioms: [propext]
'TCSlib.Cryptography.NumberTheory.listToNat_nil' does not depend on any axioms
'TCSlib.Cryptography.NumberTheory.listToNat_singleton_true' does not depend on any axioms
[rc=0 time=4s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/axioms-touched.tsv =====

module	declaration	axioms
TCSlib.Complexity.Randomized.Build.IterateFind	Complexity.IterateFind.find?_range_and_lt	[Quot.sound, propext]
TCSlib.Complexity.Randomized.Closure	Complexity.PolyTimeComputable.comp'	[Classical.choice, Quot.sound, propext]
TCSlib.Complexity.Randomized.Closure	Complexity.PolyTimeComputable.congr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Asymptotic.PublicKeyLemmas	TCSlib.Cryptography.uexp_half_sub	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Asymptotic.Sampling	TCSlib.Cryptography.abs_uexp_sub_le	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Asymptotic.Sampling	TCSlib.Cryptography.statClose_one	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Asymptotic.Sampling	TCSlib.Cryptography.foldl_bits_eq	[propext]
TCSlib.Cryptography.Asymptotic.Sampling	TCSlib.Cryptography.two_pow_size_le_two_mul	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.natToList_mod_two_pow	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.listToNat_natToList_zero_append	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.natToList_zero_append_drop	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.listToNat_replicate_true	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.listToNat_replicate_false	[propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.listToNat_mulStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.subStr_self	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.val_inv_natCast_zmod_zero_le	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.ArithmeticFP.le_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Arithmetic	TCSlib.Cryptography.Candidates.ArithmeticFP.prime_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Concrete	TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find?	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Concrete	TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL	[Classical.choice, Quot.sound, propext, sorryAx]
TCSlib.Cryptography.Candidates.Concrete	TCSlib.Cryptography.Candidates.statClose_rejectBlocksL	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.statClose_sampleBelowL	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.expSampleRaw	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.dla_ssFind_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.expCollection_D	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLog	TCSlib.Cryptography.Candidates.expCollection_sampleClose	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_mulMod_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_powMod_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_invMod_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_quot_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_rem_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_take_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_drop_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_eq_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_stateIterate_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_vote_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_iStep_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_iStart_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_oQr_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_oRoot_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_oFin_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_oNext_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_oStep_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_zfix_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_zacc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_raw_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_rootF_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_loop_sem	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_instance	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.DiscreteLogHardcore	TCSlib.Cryptography.Candidates.dlb_reduction	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.egGenRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_numPoly_mul	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_numPoly_mod	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_numPoly_two_pow	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_poly_natToList	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_natToList_mod_safeMod	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_ssLoop_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_ssLoop_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.egDecStr	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.egGroupGen	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_splitEquiv	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_uprob_shift	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_encEquiv	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_encEquiv_ofFn	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.ElGamal	TCSlib.Cryptography.Candidates.dlc_hyb3	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.fmult_inv_factor	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.fac_natToList_lead	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.fac_polyTimeComputable_isOne	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.fac_bitsToNat_false	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.samplePrimeL	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.fac_natToList_two	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.factoringCollection_index	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Factoring	TCSlib.Cryptography.Candidates.factoringCollection_sampleClose	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.sampleUnitL_getD_spec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsaGenRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_unitTest_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_usOut	[]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_usBlock_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_usAcc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_usFind_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_ptc_unitSampleStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_listToNat_three	[]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_norm	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gP_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gQ_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gValid_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gPhi_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gE_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_gNorm_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_genCore_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_genCore_spec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_dec_unitSampleStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsaSampler_spec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsaFromFactorRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_fOut_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.rsa_fOut_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.RSA	TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabinGenRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_rbAcc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_rbFind_eq	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_pad_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_spOut_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_four	[]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_mod_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_oddAcc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_blumAcc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_oddAcc_spec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_gU_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_gC1_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_gC2_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_genCore_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabinSampler	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_dec_unitSampleStr	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_coins_sampler	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabinCollection_sampleClose	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabinFactorRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_fOut_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_fOut_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_core	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.blumInvRaw	[Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_zpad	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_zpad_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_cE	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_cInv	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_cTerm	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_listToNat_crtW	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_crtW_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_trunc_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_trunc_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.blumSampler_spec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_statClose_blumDec	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_rOut_eq	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.Candidates.Rabin	TCSlib.Cryptography.Candidates.rabin_rOut_poly	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.HardcoreBit.Basic	TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.NumberTheory.Primality	TCSlib.Cryptography.NumberTheory.listToNat_nil	[]
TCSlib.Cryptography.NumberTheory.Primality	TCSlib.Cryptography.NumberTheory.listToNat_cons	[propext]
TCSlib.Cryptography.NumberTheory.Primality	TCSlib.Cryptography.NumberTheory.listToNat_append	[Quot.sound, propext]
TCSlib.Cryptography.NumberTheory.Primality	TCSlib.Cryptography.NumberTheory.listToNat_singleton_true	[]
TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas	TCSlib.Cryptography.ColZK.pushesUniform_offsetTable	[Classical.choice, Quot.sound, propext]
TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas	TCSlib.Cryptography.ColZK.pushesUniform_blockFields	[Classical.choice, Quot.sound, propext]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/checks-axioms-head.log =====

'Complexity.NUPPT.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.PPT.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_strongOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OracleEnsemble.Indist.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hybrid_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_unaryPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.decides_of_decidesWithAdviceInTime' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'Turing.FinTM.computesFunInTime_pairSplitAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_unaryMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_pairTakePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_pairDropPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_reparam' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_reparam_advice' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_withAdvice' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_iterateFind' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_iterateEmit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_majority' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_pairXor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_pairEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.polyTimeComputable_blockMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_le_of_statClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatClose.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatClose.map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.rejectionSample_uniform_of_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_rejectionSample_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_rejectionSample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.permFromCoins_uniform_of_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permFromCoins_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.Easy.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_38_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.weak_to_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.strong_prod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.exists_collection_oneWay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Collection.OneWay.owfFamily_strongOneWay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.fUniversal_easy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.lemma_64_3' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_65_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_65_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_65_2_cond' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.fUniversal_hard' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.fUniversal_weakOneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.theorem_63_1' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.extEuclid_spec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.NumberTheory.extEuclid_inv' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.NumberTheory.extEuclidCalls_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.NumberTheory.modExpMults_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.totient_prime_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_units_zmod_prime_mul_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.units_pow_mod_totient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.pow_mod_totient_modEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.rsa_pow_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.rsa_pow_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.exists_rsa_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.le_totient_mul_log_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.millerRabin_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.statClose_samplePrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_QR_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_sqrt_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.sqrtMod3_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.pow_div_four_succ_mem_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mem_QR_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_sqrt_mul_eq_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_QR_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.pushesUniform_sqTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.blumSqrt_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.sqTo_bijective_of_blum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inv_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_easy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_weakOneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_sampleClose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_sampleClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_rsaProb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsa_imp_factoring' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabin_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_sampleClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumInv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expF_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sq_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_secure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_negligible_iff_exists_polyExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.IndistLit.toIndist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.push' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.Indist.copies' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.predict_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prediction_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.uniform_pseudorandom' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.stretch_pos' depends on axioms: [propext]
'TCSlib.Cryptography.acceptProb_nextBitHybrid_mix' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.nextBitProb_nextBitPred_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_nextBitPred' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.exists_owpPredictorSnoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.owp_hardcore_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_expandRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prg_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.cor_81_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.glPad_f_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.glPad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.goldreich_levin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Collection.OneWay.glPad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Collection.OneWay.glPad_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.goldreich_levin_coll' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermCollection.OneWay.glPad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.distAdv_padXor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prgScheme_singleMessageSecure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PrivateKeyScheme.not_multiMessageSecure_of_deterministic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.PrivateKeyScheme.ZeroKnowledge.singleMessageSecure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure.zeroKnowledge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Complexity.NUPPT.toOracleAdversary_boundedBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.oracle_hybrid_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.two_mul_add_one_expands' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PRG.Secure.doubling' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_97_3_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_97_3_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_ggmBitsDist_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ggmPRF_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_prf_of_exists_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_not_injective_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_otpEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfScheme_multiMessageSecure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_multi_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.predProb_pkPredictor_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_pkPredictor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_witnessRelation_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.pushesUniform_coinTable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_encPermGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_encPermMulInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_encPermFromCoins' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Riso_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_cheat_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_rep_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gni_rep_cheat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_sim_H_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_sim_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_giSimTrunc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_giSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_pairRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.owpComStr_binding' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bitComPredictor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.HardCore.bitHiding' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitHiding.owpComStr_hides' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.owpComStr_polyTimeComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.owp_commitment' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_of_owp_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bad_edge' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_col_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.R3COL_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_colSimTruncH' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zeroKnowledgeProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_levinReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_owp_levinReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_getD_of_uniform_of_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatClose.comp_pushesUniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_permFromCoins' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permFromCoins_none_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_permFromCoins_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_samplePerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_mul_permFailBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Collection.evalSampled' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_canonizerExp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.PermFamily.glHalf_f_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermFamily.glHalf_f_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.glHalfBit_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.glHalfBit_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.predProb_glHalf_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.predProb_glHalf_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.invProb_glHalf_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.invProb_glHalf_odd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_div_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWayPermutation.glHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_owp_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_securePRG_of_owp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_addStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_subStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rabinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NP_subset_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ddhExpo_statClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_readsPrefix' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Collection.sample_eq_encD' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Collection.HardCore.evaluator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.inv_eq_encD' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.eval_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Collection.HardCore.nonempty_predEvaluator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.not_weakOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_worstCaseOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.not_toCollection_oneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.pullback_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Commitment.multiHiding' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.mono' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.proverBounded_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.ProverBounded.exists_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_proverBounded' depends on axioms: [propext]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocolRep_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.statClose_retry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.exists_retrySimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_attempt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perfectZK_zeroRounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_of_owp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_iff_epsClose_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.computes_iff_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.Computes.polyTimeComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_uniform_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.uniform_samplable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.invProbOpt_le_invProb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.invProbOpt_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_firstHit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.pushesUniform_of_card_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.pairwise_sampling_ineq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.exists_compParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'PassShelatChecks.not_indist_uniform_zeros' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prgAdv_eq_zero_of_length_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.fact_88_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.thm_87_3_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_hardCore_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Ensemble.uniform_nextBitUnpredictable' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.easy_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.hardCore_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PRG.oneBit_stretch' depends on axioms: [propext]
'TCSlib.Cryptography.PRG.oneBit_G' depends on axioms: [propext]
'TCSlib.Cryptography.owpPredictorSnoc_eq' does not depend on any axioms
'TCSlib.Cryptography.oneBitStep_eq' does not depend on any axioms
'TCSlib.Cryptography.expandRed_eq' does not depend on any axioms
'TCSlib.Cryptography.Collection.glBit_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
[rc=0 time=138s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/line-counts.tsv =====

file	added	removed	base_lines	head_lines
TCSlib/Complexity/Randomized/Build/IterateFind.lean	+23	-0	531	554
TCSlib/Complexity/Randomized/Closure.lean	+18	-0	456	474
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas.lean	+5	-20	856	841
TCSlib/Cryptography/Asymptotic/Sampling.lean	+30	-6	856	880
TCSlib/Cryptography/Candidates/Arithmetic.lean	+97	-0	385	482
TCSlib/Cryptography/Candidates/Concrete.lean	+81	-21	691	751
TCSlib/Cryptography/Candidates/DiscreteLog.lean	+11	-109	1446	1348
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean	+50	-83	3091	3058
TCSlib/Cryptography/Candidates/ElGamal.lean	+21	-143	2391	2269
TCSlib/Cryptography/Candidates/Factoring.lean	+12	-35	1851	1828
TCSlib/Cryptography/Candidates/RSA.lean	+88	-240	2762	2610
TCSlib/Cryptography/Candidates/Rabin.lean	+80	-215	3813	3678
TCSlib/Cryptography/HardcoreBit/Basic.lean	+26	-0	266	292
TCSlib/Cryptography/NumberTheory/Primality.lean	+22	-0	922	944
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas.lean	+8	-34	328	302
 15 files changed, 572 insertions(+), 906 deletions(-)

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/style-lint-head.log =====


6 findings in 15 files






TCSlib/Cryptography/Candidates/DiscreteLog.lean: 1349 lines (> 1000, must split)
TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean: 3059 lines (> 1000, must split)
TCSlib/Cryptography/Candidates/ElGamal.lean: 2270 lines (> 1000, must split)
TCSlib/Cryptography/Candidates/Factoring.lean: 1829 lines (> 1000, must split)
TCSlib/Cryptography/Candidates/RSA.lean: 2611 lines (> 1000, must split)
TCSlib/Cryptography/Candidates/Rabin.lean: 3679 lines (> 1000, must split)




## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/Collect.lean =====

import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.DiscreteLogHardcore
import TCSlib.Cryptography.Candidates.ElGamal
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas
import TCSlib.Cryptography.Asymptotic.PublicKeyLemmas
open Lean Meta Elab Command

/-- user-facing name of a constant (private prefix removed) -/
def userStr (n : Name) : String := ((privateToUserName? n).getD n).toString

def matchesTouched (ts : List String) (n : Name) : Bool :=
  let s := userStr n
  ts.any fun t => s == t || s.endsWith ("." ++ t) ||
    (s.splitOn (t ++ ".")).length > 1 && (s.startsWith (t ++ ".") || (s.splitOn ("." ++ t ++ ".")).length > 1)

def isTCS (env : Environment) (c : Name) : Option Name :=
  match env.getModuleIdxFor? c with
  | some mi => let m := env.header.moduleNames[mi.toNat]!; if (`TCSlib).isPrefixOf m then some m else none
  | none => none

syntax (name := collectCmd) "#collect " ident "[" str,* "]" : command

@[command_elab collectCmd] def elabCollect : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  let mut ours : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some modIdx && matchesTouched ts n then ours := ours.push n
  -- every touched name must be found
  for t in ts do
    unless ours.any (fun n => userStr n == t || (userStr n).endsWith ("." ++ t)) do
      logWarning m!"TOUCHED-NOT-FOUND {t}"
  -- wide pass: types of all constants reached; values of own-module definitions, transitively
  let mut cs : NameSet := {}
  let mut seen : NameSet := {}
  let mut stack : List Name := []
  for n in ours do
    let some ci := env.find? n | continue
    stack := stack ++ ci.type.getUsedConstants.toList ++ (ci.value?.map (·.getUsedConstants.toList) |>.getD [])
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    cs := cs.insert c
    let some cc := env.find? c | continue
    if env.getModuleIdxFor? c == some modIdx then
      stack := stack ++ cc.type.getUsedConstants.toList
      if cc.isDefinition then
        stack := stack ++ (cc.value?.map (·.getUsedConstants.toList) |>.getD [])
  let mut rows : Array String := #[]
  let mut reds : Array String := #[]
  for c in cs.toList do
    let some m := isTCS env c | continue
    if m == modN then continue
    let some cinfo := env.find? c | continue
    unless cinfo.isDefinition do continue
    if isInstanceCore env c then continue
    let isM := (Match.Extension.getMatcherInfo? env c).isSome
    let st ← liftCoreM <| getReducibilityStatus c
    if !isM && st == .reducible then
      reds := reds.push s!"REDUCIBLE {c} | {m}"
      continue
    rows := rows.push s!"SEALROW {modN} | {c} | {m} | matcher={isM} | {repr st}"
  logInfo m!"MODULE {modN}: touched {ts.length}, constants {ours.size}, reached {cs.size}"
  for r in rows.qsort (· < ·) do logInfo m!"{r}"
  for r in reds.qsort (· < ·) do logInfo m!"{r}"

syntax (name := axsCmd) "#axs " ident "[" str,* "]" : command

/-- axioms of every touched top-level declaration of a module (private ones included) -/
@[command_elab axsCmd] def elabAxs : CommandElab := fun stx => do
  let modN := stx[1].getId
  let ts : List String := (stx[3].getSepArgs.map fun s => s.isStrLit?.getD "").toList
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modN | throwError "no module {modN}"
  for t in ts do
    let mut found := false
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some modIdx then
        let s := userStr n
        if s == t || s.endsWith ("." ++ t) then
          found := true
          let axs ← liftCoreM <| collectAxioms n
          let axs := axs.qsort (fun a b => a.toString < b.toString)
          logInfo m!"AXIOMS {modN} | {s} | {axs.toList}"
    unless found do logWarning m!"AXIOMS-NOT-FOUND {t}"

#collect TCSlib.Complexity.Randomized.Build.IterateFind ["find?_range_and_lt"]
#axs TCSlib.Complexity.Randomized.Build.IterateFind ["find?_range_and_lt"]
#collect TCSlib.Complexity.Randomized.Closure ["PolyTimeComputable.comp'", "PolyTimeComputable.congr"]
#axs TCSlib.Complexity.Randomized.Closure ["PolyTimeComputable.comp'", "PolyTimeComputable.congr"]
#collect TCSlib.Cryptography.Asymptotic.PublicKeyLemmas ["uexp_half_sub"]
#axs TCSlib.Cryptography.Asymptotic.PublicKeyLemmas ["uexp_half_sub"]
#collect TCSlib.Cryptography.Asymptotic.Sampling ["abs_uexp_sub_le", "statClose_one", "foldl_bits_eq", "two_pow_size_le_two_mul"]
#axs TCSlib.Cryptography.Asymptotic.Sampling ["abs_uexp_sub_le", "statClose_one", "foldl_bits_eq", "two_pow_size_le_two_mul"]
#collect TCSlib.Cryptography.Candidates.Arithmetic ["natToList_mod_two_pow", "listToNat_natToList_zero_append", "natToList_zero_append_drop", "listToNat_replicate_true", "listToNat_replicate_false", "listToNat_mulStr", "subStr_self", "val_inv_natCast_zmod_zero_le", "ArithmeticFP.le_poly", "ArithmeticFP.prime_poly"]
#axs TCSlib.Cryptography.Candidates.Arithmetic ["natToList_mod_two_pow", "listToNat_natToList_zero_append", "natToList_zero_append_drop", "listToNat_replicate_true", "listToNat_replicate_false", "listToNat_mulStr", "subStr_self", "val_inv_natCast_zmod_zero_le", "ArithmeticFP.le_poly", "ArithmeticFP.prime_poly"]
#collect TCSlib.Cryptography.Candidates.Concrete ["rejectBlocksL_eq_find?", "polyTimeComputable_rejectBlocksL", "statClose_rejectBlocksL"]
#axs TCSlib.Cryptography.Candidates.Concrete ["rejectBlocksL_eq_find?", "polyTimeComputable_rejectBlocksL", "statClose_rejectBlocksL"]
#collect TCSlib.Cryptography.Candidates.DiscreteLog ["statClose_sampleBelowL", "expSampleRaw", "dla_ssFind_eq", "polyTimeComputable_expSampleRaw", "expCollection_D", "expCollection_sampleClose"]
#axs TCSlib.Cryptography.Candidates.DiscreteLog ["statClose_sampleBelowL", "expSampleRaw", "dla_ssFind_eq", "polyTimeComputable_expSampleRaw", "expCollection_D", "expCollection_sampleClose"]
#collect TCSlib.Cryptography.Candidates.DiscreteLogHardcore ["polyTimeComputable_halfStr", "dlb_mulMod_poly", "dlb_powMod_poly", "dlb_invMod_poly", "dlb_quot_poly", "dlb_rem_poly", "dlb_take_poly", "dlb_drop_poly", "dlb_eq_poly", "dlb_stateIterate_poly", "dlb_vote_poly", "dlb_iStep_poly", "dlb_iStart_poly", "dlb_oQr_poly", "dlb_oRoot_poly", "dlb_oFin_poly", "dlb_oNext_poly", "dlb_oStep_poly", "dlb_zfix_poly", "dlb_zacc_poly", "dlb_raw_poly", "dlb_rootF_eq", "dlb_loop_sem", "dlb_instance", "dlb_reduction"]
#axs TCSlib.Cryptography.Candidates.DiscreteLogHardcore ["polyTimeComputable_halfStr", "dlb_mulMod_poly", "dlb_powMod_poly", "dlb_invMod_poly", "dlb_quot_poly", "dlb_rem_poly", "dlb_take_poly", "dlb_drop_poly", "dlb_eq_poly", "dlb_stateIterate_poly", "dlb_vote_poly", "dlb_iStep_poly", "dlb_iStart_poly", "dlb_oQr_poly", "dlb_oRoot_poly", "dlb_oFin_poly", "dlb_oNext_poly", "dlb_oStep_poly", "dlb_zfix_poly", "dlb_zacc_poly", "dlb_raw_poly", "dlb_rootF_eq", "dlb_loop_sem", "dlb_instance", "dlb_reduction"]
#collect TCSlib.Cryptography.Candidates.ElGamal ["egGenRaw", "dlc_numPoly_mul", "dlc_numPoly_mod", "dlc_numPoly_two_pow", "dlc_poly_natToList", "dlc_natToList_mod_safeMod", "dlc_ssLoop_poly", "dlc_ssLoop_eq", "egDecStr", "polyTimeComputable_egDecStr", "egGroupGen", "dlc_splitEquiv", "dlc_uprob_shift", "dlc_encEquiv", "dlc_encEquiv_ofFn", "dlc_hyb3"]
#axs TCSlib.Cryptography.Candidates.ElGamal ["egGenRaw", "dlc_numPoly_mul", "dlc_numPoly_mod", "dlc_numPoly_two_pow", "dlc_poly_natToList", "dlc_natToList_mod_safeMod", "dlc_ssLoop_poly", "dlc_ssLoop_eq", "egDecStr", "polyTimeComputable_egDecStr", "egGroupGen", "dlc_splitEquiv", "dlc_uprob_shift", "dlc_encEquiv", "dlc_encEquiv_ofFn", "dlc_hyb3"]
#collect TCSlib.Cryptography.Candidates.Factoring ["fmult_inv_factor", "fac_natToList_lead", "fac_polyTimeComputable_isOne", "fac_bitsToNat_false", "samplePrimeL", "fac_natToList_two", "factoringCollection_index", "factoringCollection_sampleClose"]
#axs TCSlib.Cryptography.Candidates.Factoring ["fmult_inv_factor", "fac_natToList_lead", "fac_polyTimeComputable_isOne", "fac_bitsToNat_false", "samplePrimeL", "fac_natToList_two", "factoringCollection_index", "factoringCollection_sampleClose"]
#collect TCSlib.Cryptography.Candidates.RSA ["sampleUnitL_getD_spec", "rsaGenRaw", "rsa_unitTest_eq", "rsa_usOut", "rsa_usBlock_poly", "rsa_usAcc_poly", "rsa_usFind_eq", "rsa_ptc_unitSampleStr", "rsa_listToNat_three", "rsa_norm", "rsa_gP_poly", "rsa_gQ_poly", "rsa_gValid_poly", "rsa_gPhi_poly", "rsa_gE_poly", "rsa_gNorm_poly", "rsa_genCore_poly", "rsa_genCore_spec", "polyTimeComputable_rsaGenRaw", "rsa_dec_unitSampleStr", "rsaSampler_spec", "rsaFromFactorRaw", "rsa_fOut_poly", "rsa_fOut_eq", "polyTimeComputable_rsaFromFactorRaw"]
#axs TCSlib.Cryptography.Candidates.RSA ["sampleUnitL_getD_spec", "rsaGenRaw", "rsa_unitTest_eq", "rsa_usOut", "rsa_usBlock_poly", "rsa_usAcc_poly", "rsa_usFind_eq", "rsa_ptc_unitSampleStr", "rsa_listToNat_three", "rsa_norm", "rsa_gP_poly", "rsa_gQ_poly", "rsa_gValid_poly", "rsa_gPhi_poly", "rsa_gE_poly", "rsa_gNorm_poly", "rsa_genCore_poly", "rsa_genCore_spec", "polyTimeComputable_rsaGenRaw", "rsa_dec_unitSampleStr", "rsaSampler_spec", "rsaFromFactorRaw", "rsa_fOut_poly", "rsa_fOut_eq", "polyTimeComputable_rsaFromFactorRaw"]
#collect TCSlib.Cryptography.Candidates.Rabin ["rabinGenRaw", "rabin_rbAcc_poly", "rabin_rbFind_eq", "rabin_pad_poly", "rabin_spOut_poly", "rabin_listToNat_four", "rabin_mod_poly", "rabin_oddAcc_poly", "rabin_blumAcc_poly", "rabin_oddAcc_spec", "rabin_gU_poly", "rabin_gC1_poly", "rabin_gC2_poly", "rabin_genCore_poly", "rabinSampler", "rabin_dec_unitSampleStr", "rabin_coins_sampler", "rabinCollection_sampleClose", "rabinFactorRaw", "rabin_fOut_poly", "rabin_fOut_eq", "rabin_core", "blumInvRaw", "rabin_listToNat_zpad", "rabin_zpad_poly", "rabin_listToNat_cE", "rabin_listToNat_cInv", "rabin_listToNat_cTerm", "rabin_listToNat_crtW", "rabin_crtW_poly", "rabin_trunc_eq", "rabin_trunc_poly", "polyTimeComputable_blumInvRaw", "blumSampler_spec", "rabin_statClose_blumDec", "rabinBlumTrapdoor_sampleClose", "rabin_rOut_eq", "rabin_rOut_poly"]
#axs TCSlib.Cryptography.Candidates.Rabin ["rabinGenRaw", "rabin_rbAcc_poly", "rabin_rbFind_eq", "rabin_pad_poly", "rabin_spOut_poly", "rabin_listToNat_four", "rabin_mod_poly", "rabin_oddAcc_poly", "rabin_blumAcc_poly", "rabin_oddAcc_spec", "rabin_gU_poly", "rabin_gC1_poly", "rabin_gC2_poly", "rabin_genCore_poly", "rabinSampler", "rabin_dec_unitSampleStr", "rabin_coins_sampler", "rabinCollection_sampleClose", "rabinFactorRaw", "rabin_fOut_poly", "rabin_fOut_eq", "rabin_core", "blumInvRaw", "rabin_listToNat_zpad", "rabin_zpad_poly", "rabin_listToNat_cE", "rabin_listToNat_cInv", "rabin_listToNat_cTerm", "rabin_listToNat_crtW", "rabin_crtW_poly", "rabin_trunc_eq", "rabin_trunc_poly", "polyTimeComputable_blumInvRaw", "blumSampler_spec", "rabin_statClose_blumDec", "rabinBlumTrapdoor_sampleClose", "rabin_rOut_eq", "rabin_rOut_poly"]
#collect TCSlib.Cryptography.HardcoreBit.Basic ["pushesUniform_restrict"]
#axs TCSlib.Cryptography.HardcoreBit.Basic ["pushesUniform_restrict"]
#collect TCSlib.Cryptography.NumberTheory.Primality ["listToNat_nil", "listToNat_cons", "listToNat_append", "listToNat_singleton_true"]
#axs TCSlib.Cryptography.NumberTheory.Primality ["listToNat_nil", "listToNat_cons", "listToNat_append", "listToNat_singleton_true"]
#collect TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas ["pushesUniform_offsetTable", "pushesUniform_blockFields"]
#axs TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas ["pushesUniform_offsetTable", "pushesUniform_blockFields"]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/Controls.lean =====

import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.ElGamal
import TCSlib.Cryptography.Candidates.DiscreteLogHardcore
/-! S1 seal controls: thirteen readings of foreign definitions by their bodies (C1–C13), each
closing unsealed (namespace `S1Unsealed`) and failing under the union of the S1 seals (namespace
`S1Sealed`, 89 names; `PolyExpr.eval` and `glNeed` left unsealed). -/
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates NumberTheory

namespace S1Unsealed
-- C1 natToList by its body
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
-- C2 listToNat by its body
example (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := rfl
-- C3 rejectBlocksL by its body
example (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none := rfl
-- C4 StatClose by its body
example (X Y : Fin 2 → ℕ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : ℕ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl
-- C5 uexp by its body
example (f : Fin 3 → ℝ) : uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
-- C6 PushesUniform by its body
example (π : Fin 2 → Fin 2) :
    HardcoreBit.PushesUniform π ↔ ∀ F : Fin 2 → ℝ, uexp (fun ω => F (π ω)) = uexp F := Iff.rfl
-- C7 PolyTimeComputable by its body
example (f : List Bool → List Bool) : PolyTimeComputable f ↔
    ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c := Iff.rfl
-- C8 sampleUnitL by its body
example (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl
-- C9 subStr by its body
example (z : List Bool) : subStr z =
    natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) := rfl
-- C10 the repetition host's matcher against a local match on the same discriminant
example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :
    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =
      (match o with | some i => a i | none => b) := rfl
-- C11 sampleBelowL by its body
example (m k B T : ℕ) (r : List Bool) : sampleBelowL m k B T r = (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none := rfl
-- C12 bitsToNat by its body
example (b : Fin 3 → Bool) :
    bitsToNat b = (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := rfl
-- C13 mulStr by its body
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl
end S1Unsealed

namespace S1Sealed
attribute [local irreducible] _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.PolyTimeComputable _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.default _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.p _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.q _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.DLHard _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb _root_.TCSlib.Cryptography.Candidates.ExpValid _root_.TCSlib.Cryptography.Candidates.SafePrimeValid _root_.TCSlib.Cryptography.Candidates.WellFormedIndex _root_.TCSlib.Cryptography.Candidates.addStr _root_.TCSlib.Cryptography.Candidates.decodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.divModStr _root_.TCSlib.Cryptography.Candidates.dlG _root_.TCSlib.Cryptography.Candidates.dlM _root_.TCSlib.Cryptography.Candidates.dlP _root_.TCSlib.Cryptography.Candidates.dlW _root_.TCSlib.Cryptography.Candidates.encodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.expCollection _root_.TCSlib.Cryptography.Candidates.expCollection_coinsEquiv _root_.TCSlib.Cryptography.Candidates.expCollection_domEquiv _root_.TCSlib.Cryptography.Candidates.expF _root_.TCSlib.Cryptography.Candidates.expOrd _root_.TCSlib.Cryptography.Candidates.expUnit _root_.TCSlib.Cryptography.Candidates.leStr _root_.TCSlib.Cryptography.Candidates.modExpStr _root_.TCSlib.Cryptography.Candidates.modulusBits _root_.TCSlib.Cryptography.Candidates.mulStr _root_.TCSlib.Cryptography.Candidates.natToBits _root_.TCSlib.Cryptography.Candidates.natToList _root_.TCSlib.Cryptography.Candidates.rejectBlocksL _root_.TCSlib.Cryptography.Candidates.rsaBlock _root_.TCSlib.Cryptography.Candidates.rsaSampleCoins _root_.TCSlib.Cryptography.Candidates.rsaTrials _root_.TCSlib.Cryptography.Candidates.sampleBelowL _root_.TCSlib.Cryptography.Candidates.samplePrimeL _root_.TCSlib.Cryptography.Candidates.sampleUnitL _root_.TCSlib.Cryptography.Candidates.sizeStr _root_.TCSlib.Cryptography.Candidates.subStr _root_.TCSlib.Cryptography.Candidates.unitSampleStr _root_.TCSlib.Cryptography.Candidates.xgcdStr _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.NumberTheory.QR _root_.TCSlib.Cryptography.NumberTheory.chunk _root_.TCSlib.Cryptography.NumberTheory.listToNat _root_.TCSlib.Cryptography.NumberTheory.samplePrime _root_.TCSlib.Cryptography.NumberTheory.samplePrimeCoins _root_.TCSlib.Cryptography.NumberTheory.sqTo _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode
-- C1 natToList by its body
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
-- C2 listToNat by its body
example (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := rfl
-- C3 rejectBlocksL by its body
example (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none := rfl
-- C4 StatClose by its body
example (X Y : Fin 2 → ℕ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : ℕ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl
-- C5 uexp by its body
example (f : Fin 3 → ℝ) : uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
-- C6 PushesUniform by its body
example (π : Fin 2 → Fin 2) :
    HardcoreBit.PushesUniform π ↔ ∀ F : Fin 2 → ℝ, uexp (fun ω => F (π ω)) = uexp F := Iff.rfl
-- C7 PolyTimeComputable by its body
example (f : List Bool → List Bool) : PolyTimeComputable f ↔
    ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c := Iff.rfl
-- C8 sampleUnitL by its body
example (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl
-- C9 subStr by its body
example (z : List Bool) : subStr z =
    natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) := rfl
-- C10 the repetition host's matcher against a local match on the same discriminant
example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :
    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =
      (match o with | some i => a i | none => b) := rfl
-- C11 sampleBelowL by its body
example (m k B T : ℕ) (r : List Bool) : sampleBelowL m k B T r = (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none := rfl
-- C12 bitsToNat by its body
example (b : Fin 3 → Bool) :
    bitsToNat b = (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := rfl
-- C13 mulStr by its body
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl
end S1Sealed

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/Controls.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:56:65: error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  natToList k N = List.ofFn (natToBits k N)
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:58:93: error: Type mismatch
  rfl
has type
  ?m.45 = ?m.45
but is expected to have type
  listToNat w = List.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 w
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:63:19: error: Type mismatch
  rfl
has type
  ?m.26 = ?m.26
but is expected to have type
  rejectBlocksL E k B T r =
    List.findSome?
      (fun t =>
        if E (listToNat (List.take k (List.drop (t * B) r))) then some (listToNat (List.take k (List.drop (t * B) r)))
        else none)
      (List.range T)
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:67:2: error: Type mismatch
  Iff.rfl
has type
  ?m.25 ↔ ?m.25
but is expected to have type
  StatClose X Y δ ↔ ∀ (T : ℕ → Prop), |(uprob fun s => T (X s)) - uprob fun t => T (Y t)| ≤ δ
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:69:72: error: Type mismatch
  rfl
has type
  ?m.20 = ?m.20
but is expected to have type
  uexp f = (∑ a, f a) / ↑(Fintype.card (Fin 3))
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:72:87: error: Type mismatch
  Iff.rfl
has type
  ?m.17 ↔ ?m.17
but is expected to have type
  HardcoreBit.PushesUniform π ↔ ∀ (F : Fin 2 → ℝ), (uexp fun ω => F (π ω)) = uexp F
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:75:84: error: Type mismatch
  Iff.rfl
has type
  ?m.24 ↔ ?m.24
but is expected to have type
  PolyTimeComputable f ↔ ∃ M C c, M.ComputesFunInTime f fun n => C * (n + 1) ^ c
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:78:88: error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ v.Coprime N) k B T r
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:81:87: error: Type mismatch
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  subStr z = natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z))
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:85:52: error: Type mismatch
  rfl
has type
  ?m.22 = ?m.22
but is expected to have type
  (match o with
    | some i => a i
    | none => b) =
    match o with
    | some i => a i
    | none => b
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:89:17: error: Type mismatch
  rfl
has type
  ?m.26 = ?m.26
but is expected to have type
  sampleBelowL m k B T r =
    List.findSome?
      (fun t =>
        if listToNat (List.take k (List.drop (t * B) r)) < m then some (listToNat (List.take k (List.drop (t * B) r)))
        else none)
      (List.range T)
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:92:85: error: Type mismatch
  rfl
has type
  ?m.50 = ?m.50
but is expected to have type
  bitsToNat b = List.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 (List.ofFn b)
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/Controls.lean:95:57: error: Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  mulStr z = natToList ((pairFstD z).length + (pairSndD z).length) (listToNat (pairFstD z) * listToNat (pairSndD z))
[rc=1 time=2s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedArithmetic.out =====

[rc=0 time=3s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedBasic.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedBasic.lean:86:2: error: Type mismatch
  div_le_div_of_nonneg_right (sum_le_sum fun ω x => h ω) (Nat.cast_nonneg ?m.31)
has type
  (∑ i ∈ ?m.23, f i) / ↑?m.31 ≤ (∑ i ∈ ?m.23, g i) / ↑?m.31
but is expected to have type
  uexp f ≤ uexp g
[rc=1 time=2s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedClosure.out =====

[rc=0 time=1s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedColZKLemmas.out =====

[rc=0 time=3s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedConcrete.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedConcrete.lean:345:59: error: unsolved goals
n : ℕ
z : { z // Nat.Prime (bitsToNat z.1) ∧ Nat.Prime (bitsToNat z.2) }
⊢ ↑(↑((((bitsEquiv n).prodCongr (bitsEquiv n)).subtypeEquiv ⋯) z)).1 = bitsToNat (↑z).1 ∧
    ↑(↑((((bitsEquiv n).prodCongr (bitsEquiv n)).subtypeEquiv ⋯) z)).2 = bitsToNat (↑z).2
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedConcrete.lean:635:8: warning: declaration uses 'sorry'
[rc=1 time=4s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedDiscreteLog.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedDiscreteLog.lean:444:22: error: Application type mismatch: The argument
  fun c => ?m.14
has type
  (c : ?m.12) → ?m.15 c
but is expected to have type
  Negligible fun x => 0
in the application
  And.intro fun c => ?m.14
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedDiscreteLog.lean:444:31: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedDiscreteLog.lean:445:2: error: No goals to be solved
[rc=1 time=4s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedDiscreteLogHardcore.out =====

[rc=0 time=23s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedElGamal.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedElGamal.lean:117:0: warning: automatically included section variable(s) unused in theorem `TCSlib.Cryptography.Candidates.safe_ne_two`:
  hp
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit hp in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedElGamal.lean:122:0: warning: automatically included section variable(s) unused in theorem `TCSlib.Cryptography.Candidates.five_le_safe`:
  hp
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit hp in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedElGamal.lean:127:0: warning: automatically included section variable(s) unused in theorem `TCSlib.Cryptography.Candidates.safe_half`:
  hp
  hq
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit hp hq in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
[rc=0 time=10s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedFactoring.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedFactoring.lean:795:4: error: Type mismatch
  Eq.symm (List.ofFn_congr (OneWay.YaoMachine.ρP_eval D n) ?m.232)
has type
  (@List.ofFn ?m.229 (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n)) fun i => ?m.232 (Fin.cast ⋯ i)) =
    List.ofFn ?m.232
but is expected to have type
  @List.ofFn Bool (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n))
      (((finCongr ⋯).arrowCongr (Equiv.refl Bool))
        ((NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
            (OneWay.YaoMachine.adv D) ⋯ n)
          r)) =
    List.ofFn
      ((NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D) (OneWay.YaoMachine.adv D)
          ⋯ n)
        r)
[rc=1 time=6s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedIterateFind.out =====

[rc=0 time=5s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedPrimality.out =====

[rc=0 time=6s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedPublicKeyLemmas.out =====

[rc=0 time=67s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedRSA-review50.out =====

[rc=0 time=7s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedRSA.out =====

[rc=0 time=7s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedRabin.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedRabin.lean:1345:2: error: 'show' tactic failed, pattern
  pairFstD ((oddGen H).runAt n [] r) = ?m.14
is not definitionally equal to target
  (rabinCollection H).index n r = rabinIndexOf (max n 3) (rabinGenParams (fun x => x ≠ 2) oddDefault n (List.ofFn r))
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/SealedRabin.lean:3072:2: error: 'show' tactic failed, pattern
  pairFstD ((blumGen H).runAt n [] r) = ?m.20
is not definitionally equal to target
  (rabinBlumTrapdoor H).index n r =
    rabinIndexOf (max n 3) (rabinGenParams (fun x => x % 4 = 3) blumDefault n (List.ofFn r))
[rc=1 time=12s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/SealedSampling.out =====

[rc=0 time=6s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/base-control/BaseSealedBasic.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedBasic.lean:84:2: error: Type mismatch
  div_le_div_of_nonneg_right (sum_le_sum fun ω x => h ω) (Nat.cast_nonneg ?m.31)
has type
  (∑ i ∈ ?m.23, f i) / ↑?m.31 ≤ (∑ i ∈ ?m.23, g i) / ↑?m.31
but is expected to have type
  uexp f ≤ uexp g
[rc=1 time=2s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/base-control/BaseSealedConcrete.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedConcrete.lean:340:59: error: unsolved goals
n : ℕ
z : { z // Nat.Prime (bitsToNat z.1) ∧ Nat.Prime (bitsToNat z.2) }
⊢ ↑(↑((((bitsEquiv n).prodCongr (bitsEquiv n)).subtypeEquiv ⋯) z)).1 = bitsToNat (↑z).1 ∧
    ↑(↑((((bitsEquiv n).prodCongr (bitsEquiv n)).subtypeEquiv ⋯) z)).2 = bitsToNat (↑z).2
[rc=1 time=4s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/base-control/BaseSealedDiscreteLog.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedDiscreteLog.lean:444:22: error: Application type mismatch: The argument
  fun c => ?m.14
has type
  (c : ?m.12) → ?m.15 c
but is expected to have type
  Negligible fun x => 0
in the application
  And.intro fun c => ?m.14
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedDiscreteLog.lean:444:31: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedDiscreteLog.lean:445:2: error: No goals to be solved
[rc=1 time=3s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/base-control/BaseSealedFactoring.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedFactoring.lean:803:4: error: Type mismatch
  Eq.symm (List.ofFn_congr (OneWay.YaoMachine.ρP_eval D n) ?m.232)
has type
  (@List.ofFn ?m.229 (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n)) fun i => ?m.232 (Fin.cast ⋯ i)) =
    List.ofFn ?m.232
but is expected to have type
  @List.ofFn Bool (n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n))
      (((finCongr ⋯).arrowCongr (Equiv.refl Bool))
        ((NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
            (OneWay.YaoMachine.adv D) ⋯ n)
          r)) =
    List.ofFn
      ((NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D) (OneWay.YaoMachine.adv D)
          ⋯ n)
        r)
[rc=1 time=6s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/base-control/BaseSealedRabin.out =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedRabin.lean:1412:2: error: 'show' tactic failed, pattern
  pairFstD ((oddGen H).runAt n [] r) = ?m.14
is not definitionally equal to target
  (rabinCollection H).index n r = rabinIndexOf (max n 3) (rabinGenParams (fun x => x ≠ 2) oddDefault n (List.ofFn r))
/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/shared-s1/seal/base-control/BaseSealedRabin.lean:3207:2: error: 'show' tactic failed, pattern
  pairFstD ((blumGen H).runAt n [] r) = ?m.20
is not definitionally equal to target
  (rabinBlumTrapdoor H).index n r =
    rabinIndexOf (max n 3) (rabinGenParams (fun x => x % 4 = 3) blumDefault n (List.ofFn r))
[rc=1 time=13s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/collect.log =====

MODULE TCSlib.Complexity.Randomized.Build.IterateFind: touched 1, constants 2, reached 99
AXIOMS TCSlib.Complexity.Randomized.Build.IterateFind | Complexity.IterateFind.find?_range_and_lt | [Quot.sound,
 propext]
MODULE TCSlib.Complexity.Randomized.Closure: touched 2, constants 2, reached 7
SEALROW TCSlib.Complexity.Randomized.Closure | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Complexity.Randomized.Closure | Complexity.PolyTimeComputable.comp' | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Complexity.Randomized.Closure | Complexity.PolyTimeComputable.congr | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Asymptotic.PublicKeyLemmas: touched 1, constants 1, reached 123
SEALROW TCSlib.Cryptography.Asymptotic.PublicKeyLemmas | TCSlib.Cryptography.uexp | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.Asymptotic.PublicKeyLemmas | TCSlib.Cryptography.uexp_half_sub | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Asymptotic.Sampling: touched 4, constants 4, reached 278
SEALROW TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.uexp | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.abs_uexp_sub_le | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.statClose_one | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.foldl_bits_eq | [propext]
AXIOMS TCSlib.Cryptography.Asymptotic.Sampling | TCSlib.Cryptography.two_pow_size_le_two_mul | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.Arithmetic: touched 10, constants 14, reached 212
SEALROW TCSlib.Cryptography.Candidates.Arithmetic | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Arithmetic | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Arithmetic | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Arithmetic | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.natToList_mod_two_pow | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.listToNat_natToList_zero_append | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.natToList_zero_append_drop | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.listToNat_replicate_true | [Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.listToNat_replicate_false | [propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.listToNat_mulStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.subStr_self | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.val_inv_natCast_zmod_zero_le | [Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.ArithmeticFP.le_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Arithmetic | TCSlib.Cryptography.Candidates.ArithmeticFP.prime_poly | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.Concrete: touched 3, constants 3, reached 137
SEALROW TCSlib.Cryptography.Candidates.Concrete | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.HardcoreBit.PushesUniform | TCSlib.Cryptography.HardcoreBit.Basic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.StatClose | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.bitsEquiv | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.bitsToNat | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.firstHit | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Concrete | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.Candidates.rejectBlocksL_eq_find? | [Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL | [Classical.choice,
 Quot.sound,
 propext,
 sorryAx]
AXIOMS TCSlib.Cryptography.Candidates.Concrete | TCSlib.Cryptography.Candidates.statClose_rejectBlocksL | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.DiscreteLog: touched 6, constants 10, reached 396
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.Uniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.coinsCongr | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.inArg | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.layout | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.ofPolyTimeUniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.output | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Complexity.polyTimeComputable_iterateFind.match_1 | TCSlib.Complexity.Randomized.Repetition | matcher=true | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.modExpStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.rejectBlocksL | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.sizeStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.subStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Collection.SampleClose | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Collection.index | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Negligible | TCSlib.Cryptography.Foundations.Negligible | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.StatClose | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.bitsEquiv | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.rejectionSample | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLog | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Collection.D | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.decD | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.gen | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.sample | TCSlib.Cryptography.Asymptotic.Collections
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.statClose_sampleBelowL | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.expSampleRaw | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.dla_ssFind_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.expCollection_D | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLog | TCSlib.Cryptography.Candidates.expCollection_sampleClose | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.DiscreteLogHardcore: touched 25, constants 45, reached 1046
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.distinguisherL | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.inAdvice | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.inArg | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.layout | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.ofPolyTime | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.output | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.StateLoop.gstep | TCSlib.Complexity.Randomized.Build.StateLoop | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.StateLoop.gstepBound | TCSlib.Complexity.Randomized.Build.StateLoop | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.ExpGroupGen.DLHard | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.ExpValid | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.WellFormedIndex | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.addStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.divModStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlG | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlM | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlP | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlW | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expCollection | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expCollection_coinsEquiv | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expCollection_domEquiv | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expF | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expOrd | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.expUnit | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.leStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.modExpStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.mulStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.natToBits | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.subStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.xgcdStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Collection.SampleClose | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Collection.index | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.HardcoreBit.PushesUniform | TCSlib.Cryptography.HardcoreBit.Basic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.HardcoreBit.majority | TCSlib.Cryptography.HardcoreBit.PairwiseIndependence | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Negligible | TCSlib.Cryptography.Foundations.Negligible | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.NumberTheory.QR | TCSlib.Cryptography.NumberTheory.QuadraticResidues | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.StatClose | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.bitsToNat | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.decodeFin | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.invProb | TCSlib.Cryptography.Foundations.Experiments | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.predProb | TCSlib.Cryptography.Foundations.Experiments | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.uexp | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.DiscreteLogHardcore | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.adv | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.advice | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Candidates.ExpGroupGen.gen | TCSlib.Cryptography.Candidates.DiscreteLog
REDUCIBLE TCSlib.Cryptography.Candidates.ExpGroupGen.n₀ | TCSlib.Cryptography.Candidates.DiscreteLog
REDUCIBLE TCSlib.Cryptography.Collection.D | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.decD | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.f | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.gen | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.sample | TCSlib.Cryptography.Asymptotic.Collections
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_mulMod_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_powMod_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_invMod_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_quot_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_rem_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_take_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_drop_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_eq_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_stateIterate_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_vote_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_iStep_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_iStart_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_oQr_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_oRoot_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_oFin_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_oNext_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_oStep_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_zfix_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_zacc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_raw_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_rootF_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_loop_sem | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_instance | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.DiscreteLogHardcore | TCSlib.Cryptography.Candidates.dlb_reduction | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.ElGamal: touched 16, constants 22, reached 453
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.Uniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.distinguisher | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.inArg | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.layout | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.ofPolyTimeUniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.output | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Complexity.polyTimeComputable_iterateFind.match_1 | TCSlib.Complexity.Randomized.Repetition | matcher=true | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.SafePrimeValid | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.WellFormedIndex | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.divModStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlG | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlM | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlP | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.expF | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.expOrd | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.modExpStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.mulStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.rejectBlocksL | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.sampleBelowL | TCSlib.Cryptography.Candidates.DiscreteLog | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.subStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.xgcdStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.acceptProb | TCSlib.Cryptography.Foundations.Experiments | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.padFin | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.splitCoins | TCSlib.Cryptography.Asymptotic.CollectionsHelpers | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.uexp | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.ElGamal | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Candidates.ExpGroupGen.gen | TCSlib.Cryptography.Candidates.DiscreteLog
REDUCIBLE TCSlib.Cryptography.Candidates.ExpGroupGen.n₀ | TCSlib.Cryptography.Candidates.DiscreteLog
REDUCIBLE TCSlib.Cryptography.Candidates.SafePrimeGen | TCSlib.Cryptography.Candidates.DiscreteLog
REDUCIBLE TCSlib.Cryptography.Ensemble.X | TCSlib.Cryptography.Asymptotic.Ensembles
REDUCIBLE TCSlib.Cryptography.Ensemble.σ | TCSlib.Cryptography.Asymptotic.Ensembles
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.egGenRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_numPoly_mul | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_numPoly_mod | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_numPoly_two_pow | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_poly_natToList | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_natToList_mod_safeMod | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_ssLoop_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_ssLoop_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.egDecStr | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.egGroupGen | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_splitEquiv | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_uprob_shift | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_encEquiv | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_encEquiv_ofFn | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.ElGamal | TCSlib.Cryptography.Candidates.dlc_hyb3 | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.Factoring: touched 8, constants 8, reached 354
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.Uniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.ofPolyTimeUniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.DistinctPrimes.default | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.DistinctPrimes.p | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.DistinctPrimes.q | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.decodeDistinctPrimes | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.encodeDistinctPrimes | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.leStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.mulStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.natToBits | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Collection.SampleClose | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Collection.index | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.FunFamily.blocks | TCSlib.Cryptography.Asymptotic.OneWay | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Negligible | TCSlib.Cryptography.Foundations.Negligible | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.NumberTheory.chunk | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.NumberTheory.samplePrime | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.NumberTheory.samplePrimeCoins | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.StatClose | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.bitsToNat | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.padFin | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Factoring | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Candidates.DistinctPrimes | TCSlib.Cryptography.Candidates.Concrete
REDUCIBLE TCSlib.Cryptography.Collection.D | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.decD | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.gen | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.sample | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.FunFamily.f | TCSlib.Cryptography.Asymptotic.OneWay
REDUCIBLE TCSlib.Cryptography.FunFamily.outLen | TCSlib.Cryptography.Asymptotic.OneWay
REDUCIBLE TCSlib.Cryptography.NumberTheory.Primes | TCSlib.Cryptography.NumberTheory.Chebyshev
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.fmult_inv_factor | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.fac_natToList_lead | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.fac_polyTimeComputable_isOne | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.fac_bitsToNat_false | [Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.samplePrimeL | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.fac_natToList_two | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.factoringCollection_index | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Factoring | TCSlib.Cryptography.Candidates.factoringCollection_sampleClose | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.RSA: touched 25, constants 51, reached 634
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.inAdvice | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.inArg | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.layout | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.ofPolyTimeUniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.output | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.DistinctPrimes.default | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.DistinctPrimes.p | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.DistinctPrimes.q | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.divModStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.modExpStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.mulStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rejectBlocksL | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.samplePrimeL | TCSlib.Cryptography.Candidates.Factoring | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.sizeStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.subStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.xgcdStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.NumberTheory.samplePrimeCoins | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.RSA | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Candidates.DistinctPrimes | TCSlib.Cryptography.Candidates.Concrete
REDUCIBLE TCSlib.Cryptography.NumberTheory.Primes | TCSlib.Cryptography.NumberTheory.Chebyshev
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.sampleUnitL_getD_spec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsaGenRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_unitTest_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_usOut | []
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_usBlock_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_usAcc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_usFind_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_ptc_unitSampleStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_listToNat_three | []
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_norm | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gP_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gQ_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gValid_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gPhi_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gE_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_gNorm_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_genCore_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_genCore_spec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_dec_unitSampleStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsaSampler_spec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsaFromFactorRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_fOut_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.rsa_fOut_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.RSA | TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.Candidates.Rabin: touched 38, constants 65, reached 913
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.Uniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.coinLen | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.coinsEquivPoly | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.inAdvice | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.inArg | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.inCoins | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.inParam | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.inverter | TCSlib.Cryptography.Asymptotic.Adversary | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.layout | TCSlib.Complexity.Randomized.Closure | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.ofPolyTime | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.ofPolyTimeUniform | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.output | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.runAt | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.NUPPT.runAtL | TCSlib.Complexity.Randomized.PPT | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.PolyExpr.eval | TCSlib.Complexity.Randomized.PolyExpr | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.PolyTimeComputable | TCSlib.Complexity.ClassNP.PolyTime | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.pairFstD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Complexity.pairSndD | TCSlib.Complexity.ClassNP.PolyTimePairing | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.DistinctPrimes.p | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.DistinctPrimes.q | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.addStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.divModStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.encodeDistinctPrimes | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.modExpStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.modulusBits | TCSlib.Cryptography.Candidates.Factoring | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.mulStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.natToBits | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.natToList | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rejectBlocksL | TCSlib.Cryptography.Candidates.Concrete | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rsaBlock | TCSlib.Cryptography.Candidates.RSA | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rsaSampleCoins | TCSlib.Cryptography.Candidates.RSA | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rsaTrials | TCSlib.Cryptography.Candidates.RSA | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.sampleUnitL | TCSlib.Cryptography.Candidates.RSA | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.subStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.unitSampleStr | TCSlib.Cryptography.Candidates.RSA | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.xgcdStr | TCSlib.Cryptography.Candidates.Arithmetic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Collection.SampleClose | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Collection.index | TCSlib.Cryptography.Asymptotic.Collections | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.HardcoreBit.PushesUniform | TCSlib.Cryptography.HardcoreBit.Basic | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Negligible | TCSlib.Cryptography.Foundations.Negligible | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.NumberTheory.QR | TCSlib.Cryptography.NumberTheory.QuadraticResidues | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.NumberTheory.listToNat | TCSlib.Cryptography.NumberTheory.Primality | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.NumberTheory.sqTo | TCSlib.Cryptography.NumberTheory.QuadraticResidues | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.StatClose | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.bitsToNat | TCSlib.Cryptography.Asymptotic.Sampling | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.uprob | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
SEALROW TCSlib.Cryptography.Candidates.Rabin | Turing.pairEncode | TCSlib.Complexity.TuringMachine.Encoding | matcher=false | Lean.ReducibilityStatus.semireducible
REDUCIBLE Complexity.NUPPT.Coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.adv | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.advice | TCSlib.Complexity.Randomized.PPT
REDUCIBLE Complexity.NUPPT.coins | TCSlib.Complexity.Randomized.PPT
REDUCIBLE TCSlib.Cryptography.Candidates.DistinctPrimes | TCSlib.Cryptography.Candidates.Concrete
REDUCIBLE TCSlib.Cryptography.Collection.D | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.decD | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.gen | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.Collection.sample | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.NumberTheory.Primes | TCSlib.Cryptography.NumberTheory.Chebyshev
REDUCIBLE TCSlib.Cryptography.PermCollection.toCollection | TCSlib.Cryptography.Asymptotic.Collections
REDUCIBLE TCSlib.Cryptography.TrapdoorCollection.toPermCollection | TCSlib.Cryptography.Asymptotic.Collections
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabinGenRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_rbAcc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_rbFind_eq | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_pad_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_spOut_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_four | []
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_mod_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_oddAcc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_blumAcc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_oddAcc_spec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_gU_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_gC1_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_gC2_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_genCore_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabinSampler | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_dec_unitSampleStr | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_coins_sampler | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabinCollection_sampleClose | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabinFactorRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_fOut_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_fOut_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_core | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.blumInvRaw | [Quot.sound, propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_zpad | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_zpad_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_cE | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_cInv | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_cTerm | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_listToNat_crtW | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_crtW_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_trunc_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_trunc_poly | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.blumSampler_spec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_statClose_blumDec | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_rOut_eq | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.Candidates.Rabin | TCSlib.Cryptography.Candidates.rabin_rOut_poly | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.HardcoreBit.Basic: touched 1, constants 1, reached 47
SEALROW TCSlib.Cryptography.HardcoreBit.Basic | TCSlib.Cryptography.uexp | TCSlib.Cryptography.Foundations.Probability | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.HardcoreBit.Basic | TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict | [Classical.choice,
 Quot.sound,
 propext]
MODULE TCSlib.Cryptography.NumberTheory.Primality: touched 4, constants 4, reached 38
AXIOMS TCSlib.Cryptography.NumberTheory.Primality | TCSlib.Cryptography.NumberTheory.listToNat_nil | []
AXIOMS TCSlib.Cryptography.NumberTheory.Primality | TCSlib.Cryptography.NumberTheory.listToNat_cons | [propext]
AXIOMS TCSlib.Cryptography.NumberTheory.Primality | TCSlib.Cryptography.NumberTheory.listToNat_append | [Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.NumberTheory.Primality | TCSlib.Cryptography.NumberTheory.listToNat_singleton_true | []
MODULE TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas: touched 2, constants 30, reached 170
SEALROW TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas | TCSlib.Cryptography.HardcoreBit.PushesUniform | TCSlib.Cryptography.HardcoreBit.Basic | matcher=false | Lean.ReducibilityStatus.semireducible
AXIOMS TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas | TCSlib.Cryptography.ColZK.pushesUniform_offsetTable | [Classical.choice,
 Quot.sound,
 propext]
AXIOMS TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas | TCSlib.Cryptography.ColZK.pushesUniform_blockFields | [Classical.choice,
 Quot.sound,
 propext]
[rc=0 time=105s]

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-ALL.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.coinLen
Complexity.NUPPT.coinsCongr
Complexity.NUPPT.coinsEquivPoly
Complexity.NUPPT.distinguisher
Complexity.NUPPT.distinguisherL
Complexity.NUPPT.inAdvice
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.inverter
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTime
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.NUPPT.runAtL
Complexity.PolyTimeComputable
Complexity.StateLoop.gstep
Complexity.StateLoop.gstepBound
Complexity.pairFstD
Complexity.pairSndD
Complexity.polyTimeComputable_iterateFind.match_1
TCSlib.Cryptography.Candidates.DistinctPrimes.default
TCSlib.Cryptography.Candidates.DistinctPrimes.p
TCSlib.Cryptography.Candidates.DistinctPrimes.q
TCSlib.Cryptography.Candidates.ExpGroupGen.DLHard
TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept
TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb
TCSlib.Cryptography.Candidates.ExpValid
TCSlib.Cryptography.Candidates.SafePrimeValid
TCSlib.Cryptography.Candidates.WellFormedIndex
TCSlib.Cryptography.Candidates.addStr
TCSlib.Cryptography.Candidates.decodeDistinctPrimes
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.dlG
TCSlib.Cryptography.Candidates.dlM
TCSlib.Cryptography.Candidates.dlP
TCSlib.Cryptography.Candidates.dlW
TCSlib.Cryptography.Candidates.encodeDistinctPrimes
TCSlib.Cryptography.Candidates.expCollection
TCSlib.Cryptography.Candidates.expCollection_coinsEquiv
TCSlib.Cryptography.Candidates.expCollection_domEquiv
TCSlib.Cryptography.Candidates.expF
TCSlib.Cryptography.Candidates.expOrd
TCSlib.Cryptography.Candidates.expUnit
TCSlib.Cryptography.Candidates.leStr
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.modulusBits
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToBits
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.rsaBlock
TCSlib.Cryptography.Candidates.rsaSampleCoins
TCSlib.Cryptography.Candidates.rsaTrials
TCSlib.Cryptography.Candidates.sampleBelowL
TCSlib.Cryptography.Candidates.samplePrimeL
TCSlib.Cryptography.Candidates.sampleUnitL
TCSlib.Cryptography.Candidates.sizeStr
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.unitSampleStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.FunFamily.blocks
TCSlib.Cryptography.HardcoreBit.PushesUniform
TCSlib.Cryptography.HardcoreBit.majority
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.QR
TCSlib.Cryptography.NumberTheory.chunk
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.NumberTheory.samplePrime
TCSlib.Cryptography.NumberTheory.samplePrimeCoins
TCSlib.Cryptography.NumberTheory.sqTo
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.acceptProb
TCSlib.Cryptography.bitsEquiv
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.decodeFin
TCSlib.Cryptography.firstHit
TCSlib.Cryptography.invProb
TCSlib.Cryptography.padFin
TCSlib.Cryptography.predProb
TCSlib.Cryptography.rejectionSample
TCSlib.Cryptography.splitCoins
TCSlib.Cryptography.uexp
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Arithmetic.txt =====

Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
TCSlib.Cryptography.NumberTheory.listToNat
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Basic.txt =====

TCSlib.Cryptography.uexp

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Closure.txt =====

Complexity.PolyTimeComputable

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-ColZKLemmas.txt =====

TCSlib.Cryptography.HardcoreBit.PushesUniform

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Concrete.txt =====

Complexity.PolyTimeComputable
TCSlib.Cryptography.HardcoreBit.PushesUniform
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsEquiv
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.firstHit
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-DiscreteLog.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.coinLen
Complexity.NUPPT.coinsCongr
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
Complexity.polyTimeComputable_iterateFind.match_1
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.sizeStr
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsEquiv
TCSlib.Cryptography.rejectionSample
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-DiscreteLogHardcore.txt =====

Complexity.NUPPT.coinLen
Complexity.NUPPT.distinguisherL
Complexity.NUPPT.inAdvice
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTime
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.PolyTimeComputable
Complexity.StateLoop.gstep
Complexity.StateLoop.gstepBound
Complexity.pairFstD
Complexity.pairSndD
TCSlib.Cryptography.Candidates.ExpGroupGen.DLHard
TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept
TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb
TCSlib.Cryptography.Candidates.ExpValid
TCSlib.Cryptography.Candidates.WellFormedIndex
TCSlib.Cryptography.Candidates.addStr
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.dlG
TCSlib.Cryptography.Candidates.dlM
TCSlib.Cryptography.Candidates.dlP
TCSlib.Cryptography.Candidates.dlW
TCSlib.Cryptography.Candidates.expCollection
TCSlib.Cryptography.Candidates.expCollection_coinsEquiv
TCSlib.Cryptography.Candidates.expCollection_domEquiv
TCSlib.Cryptography.Candidates.expF
TCSlib.Cryptography.Candidates.expOrd
TCSlib.Cryptography.Candidates.expUnit
TCSlib.Cryptography.Candidates.leStr
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToBits
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.HardcoreBit.PushesUniform
TCSlib.Cryptography.HardcoreBit.majority
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.QR
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.decodeFin
TCSlib.Cryptography.invProb
TCSlib.Cryptography.predProb
TCSlib.Cryptography.uexp
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-ElGamal.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.coinLen
Complexity.NUPPT.distinguisher
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
Complexity.polyTimeComputable_iterateFind.match_1
TCSlib.Cryptography.Candidates.SafePrimeValid
TCSlib.Cryptography.Candidates.WellFormedIndex
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.dlG
TCSlib.Cryptography.Candidates.dlM
TCSlib.Cryptography.Candidates.dlP
TCSlib.Cryptography.Candidates.expF
TCSlib.Cryptography.Candidates.expOrd
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.sampleBelowL
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.acceptProb
TCSlib.Cryptography.padFin
TCSlib.Cryptography.splitCoins
TCSlib.Cryptography.uexp
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Factoring.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.coinLen
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.runAt
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
TCSlib.Cryptography.Candidates.DistinctPrimes.default
TCSlib.Cryptography.Candidates.DistinctPrimes.p
TCSlib.Cryptography.Candidates.DistinctPrimes.q
TCSlib.Cryptography.Candidates.decodeDistinctPrimes
TCSlib.Cryptography.Candidates.encodeDistinctPrimes
TCSlib.Cryptography.Candidates.leStr
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToBits
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.FunFamily.blocks
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.chunk
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.NumberTheory.samplePrime
TCSlib.Cryptography.NumberTheory.samplePrimeCoins
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.padFin
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-IterateFind.txt =====



## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Primality.txt =====



## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-PublicKeyLemmas.txt =====

TCSlib.Cryptography.uexp

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-RSA-review50.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.advInput
Complexity.NUPPT.coinLen
Complexity.NUPPT.coinsCongr
Complexity.NUPPT.coinsEquivPoly
Complexity.NUPPT.inAdvice
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.inverter
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTime
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.NUPPT.runAtL
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
Complexity.polyTimeComputable_iterateFind.match_1
TCSlib.Cryptography.Candidates.DistinctPrimes.default
TCSlib.Cryptography.Candidates.DistinctPrimes.p
TCSlib.Cryptography.Candidates.DistinctPrimes.q
TCSlib.Cryptography.Candidates.FactoringAssumption
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.factorProb
TCSlib.Cryptography.Candidates.leStr
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.modulusBits
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToBits
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.primeStr
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.samplePrimeL
TCSlib.Cryptography.Candidates.sizeStr
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.Collection.invProbAt
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.NumberTheory.samplePrimeCoins
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.decodeFin
TCSlib.Cryptography.uexp
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-RSA.txt =====

Complexity.NUPPT.coinLen
Complexity.NUPPT.inAdvice
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
TCSlib.Cryptography.Candidates.DistinctPrimes.default
TCSlib.Cryptography.Candidates.DistinctPrimes.p
TCSlib.Cryptography.Candidates.DistinctPrimes.q
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.samplePrimeL
TCSlib.Cryptography.Candidates.sizeStr
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.NumberTheory.samplePrimeCoins
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Rabin.txt =====

Complexity.NUPPT.Uniform
Complexity.NUPPT.coinLen
Complexity.NUPPT.coinsEquivPoly
Complexity.NUPPT.inAdvice
Complexity.NUPPT.inArg
Complexity.NUPPT.inCoins
Complexity.NUPPT.inParam
Complexity.NUPPT.inverter
Complexity.NUPPT.layout
Complexity.NUPPT.ofPolyTime
Complexity.NUPPT.ofPolyTimeUniform
Complexity.NUPPT.output
Complexity.NUPPT.runAt
Complexity.NUPPT.runAtL
Complexity.PolyTimeComputable
Complexity.pairFstD
Complexity.pairSndD
TCSlib.Cryptography.Candidates.DistinctPrimes.p
TCSlib.Cryptography.Candidates.DistinctPrimes.q
TCSlib.Cryptography.Candidates.addStr
TCSlib.Cryptography.Candidates.divModStr
TCSlib.Cryptography.Candidates.encodeDistinctPrimes
TCSlib.Cryptography.Candidates.modExpStr
TCSlib.Cryptography.Candidates.modulusBits
TCSlib.Cryptography.Candidates.mulStr
TCSlib.Cryptography.Candidates.natToBits
TCSlib.Cryptography.Candidates.natToList
TCSlib.Cryptography.Candidates.rejectBlocksL
TCSlib.Cryptography.Candidates.rsaBlock
TCSlib.Cryptography.Candidates.rsaSampleCoins
TCSlib.Cryptography.Candidates.rsaTrials
TCSlib.Cryptography.Candidates.sampleUnitL
TCSlib.Cryptography.Candidates.subStr
TCSlib.Cryptography.Candidates.unitSampleStr
TCSlib.Cryptography.Candidates.xgcdStr
TCSlib.Cryptography.Collection.SampleClose
TCSlib.Cryptography.Collection.index
TCSlib.Cryptography.HardcoreBit.PushesUniform
TCSlib.Cryptography.Negligible
TCSlib.Cryptography.NumberTheory.QR
TCSlib.Cryptography.NumberTheory.listToNat
TCSlib.Cryptography.NumberTheory.sqTo
TCSlib.Cryptography.StatClose
TCSlib.Cryptography.bitsToNat
TCSlib.Cryptography.uprob
Turing.pairEncode

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/names-Sampling.txt =====

TCSlib.Cryptography.uexp
TCSlib.Cryptography.uprob

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/seal-summary.tsv =====

file	touched	sealed_names	head_sealed_errors	failing_decls(head)	base_control
TCSlib/Complexity/Randomized/Build/IterateFind	1	0	0	-	-
TCSlib/Complexity/Randomized/Closure	2	1	0	-	-
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas	1	1	0	-	-
TCSlib/Cryptography/Asymptotic/Sampling	4	2	0	-	-
TCSlib/Cryptography/Candidates/Arithmetic	10	5	0	-	-
TCSlib/Cryptography/Candidates/Concrete	3	9	1	primesPairEquiv_apply_val(touched=False) 	primesPairEquiv_apply_val 
TCSlib/Cryptography/Candidates/DiscreteLog	6	28	3	ExpGroupGen.FullLength.exists_fullLengthExcept(touched=False) 	ExpGroupGen.FullLength.exists_fullLengthExcept 
TCSlib/Cryptography/Candidates/DiscreteLogHardcore	25	54	0	-	-
TCSlib/Cryptography/Candidates/ElGamal	16	36	0	-	-
TCSlib/Cryptography/Candidates/Factoring	8	31	1	exists_plantFactorer(touched=False) 	exists_plantFactorer 
TCSlib/Cryptography/Candidates/RSA	25	27	0	-	-
TCSlib/Cryptography/Candidates/Rabin	38	46	2	rabinCollection_index(touched=False) rabinBlumTrapdoor_index(touched=False) 	rabinCollection_index rabinBlumTrapdoor_index 
TCSlib/Cryptography/HardcoreBit/Basic	1	1	1	uexp_mono(touched=False) 	uexp_mono 
TCSlib/Cryptography/NumberTheory/Primality	4	0	0	-	-
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas	2	1	0	-	-

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Arithmetic.txt =====

natToList_mod_two_pow
listToNat_natToList_zero_append
natToList_zero_append_drop
listToNat_replicate_true
listToNat_replicate_false
listToNat_mulStr
subStr_self
val_inv_natCast_zmod_zero_le
ArithmeticFP.le_poly
ArithmeticFP.prime_poly

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Basic.txt =====

pushesUniform_restrict

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Closure.txt =====

PolyTimeComputable.comp'
PolyTimeComputable.congr

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-ColZKLemmas.txt =====

pushesUniform_offsetTable
pushesUniform_blockFields

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Concrete.txt =====

rejectBlocksL_eq_find?
polyTimeComputable_rejectBlocksL
statClose_rejectBlocksL

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-DiscreteLog.txt =====

statClose_sampleBelowL
expSampleRaw
dla_ssFind_eq
polyTimeComputable_expSampleRaw
expCollection_D
expCollection_sampleClose

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-DiscreteLogHardcore.txt =====

polyTimeComputable_halfStr
dlb_mulMod_poly
dlb_powMod_poly
dlb_invMod_poly
dlb_quot_poly
dlb_rem_poly
dlb_take_poly
dlb_drop_poly
dlb_eq_poly
dlb_stateIterate_poly
dlb_vote_poly
dlb_iStep_poly
dlb_iStart_poly
dlb_oQr_poly
dlb_oRoot_poly
dlb_oFin_poly
dlb_oNext_poly
dlb_oStep_poly
dlb_zfix_poly
dlb_zacc_poly
dlb_raw_poly
dlb_rootF_eq
dlb_loop_sem
dlb_instance
dlb_reduction

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-ElGamal.txt =====

egGenRaw
dlc_numPoly_mul
dlc_numPoly_mod
dlc_numPoly_two_pow
dlc_poly_natToList
dlc_natToList_mod_safeMod
dlc_ssLoop_poly
dlc_ssLoop_eq
egDecStr
polyTimeComputable_egDecStr
egGroupGen
dlc_splitEquiv
dlc_uprob_shift
dlc_encEquiv
dlc_encEquiv_ofFn
dlc_hyb3

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Factoring.txt =====

fmult_inv_factor
fac_natToList_lead
fac_polyTimeComputable_isOne
fac_bitsToNat_false
samplePrimeL
fac_natToList_two
factoringCollection_index
factoringCollection_sampleClose

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-IterateFind.txt =====

find?_range_and_lt

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Primality.txt =====

listToNat_nil
listToNat_cons
listToNat_append
listToNat_singleton_true

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-PublicKeyLemmas.txt =====

uexp_half_sub

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-RSA.txt =====

sampleUnitL_getD_spec
rsaGenRaw
rsa_unitTest_eq
rsa_usOut
rsa_usBlock_poly
rsa_usAcc_poly
rsa_usFind_eq
rsa_ptc_unitSampleStr
rsa_listToNat_three
rsa_norm
rsa_gP_poly
rsa_gQ_poly
rsa_gValid_poly
rsa_gPhi_poly
rsa_gE_poly
rsa_gNorm_poly
rsa_genCore_poly
rsa_genCore_spec
polyTimeComputable_rsaGenRaw
rsa_dec_unitSampleStr
rsaSampler_spec
rsaFromFactorRaw
rsa_fOut_poly
rsa_fOut_eq
polyTimeComputable_rsaFromFactorRaw

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Rabin.txt =====

rabinGenRaw
rabin_rbAcc_poly
rabin_rbFind_eq
rabin_pad_poly
rabin_spOut_poly
rabin_listToNat_four
rabin_mod_poly
rabin_oddAcc_poly
rabin_blumAcc_poly
rabin_oddAcc_spec
rabin_gU_poly
rabin_gC1_poly
rabin_gC2_poly
rabin_genCore_poly
rabinSampler
rabin_dec_unitSampleStr
rabin_coins_sampler
rabinCollection_sampleClose
rabinFactorRaw
rabin_fOut_poly
rabin_fOut_eq
rabin_core
blumInvRaw
rabin_listToNat_zpad
rabin_zpad_poly
rabin_listToNat_cE
rabin_listToNat_cInv
rabin_listToNat_cTerm
rabin_listToNat_crtW
rabin_crtW_poly
rabin_trunc_eq
rabin_trunc_poly
polyTimeComputable_blumInvRaw
blumSampler_spec
rabin_statClose_blumDec
rabinBlumTrapdoor_sampleClose
rabin_rOut_eq
rabin_rOut_poly

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/touched-Sampling.txt =====

abs_uexp_sub_le
statClose_one
foldl_bits_eq
two_pow_size_le_two_mul

## ===== briefs/pass-shelat-ch5-8/gates/08-shared/evidence/seal/unfold-scan.txt =====

== TCSlib/Complexity/Randomized/Build/IterateFind
rewrite/simp lists in added code: 5 ; unfold/delta: 0
hits: 0
== TCSlib/Complexity/Randomized/Closure
UNFOLD 93 a
UNFOLD 93 composite
UNFOLD 93 against
UNFOLD 93 a
UNFOLD 93 lambda
UNFOLD 93 (such
UNFOLD 93 matches
UNFOLD 93 can
UNFOLD 93 unfold
UNFOLD 93 bundle
UNFOLD 93 string
UNFOLD 93 functions).
UNFOLD 93 -/
rewrite/simp lists in added code: 0 ; unfold/delta: 1
hits: 0
  EXPLICIT 13:+to unfold a composite against a lambda (such matches can unfold bundle string functions). -/
== TCSlib/Cryptography/Asymptotic/PublicKeyLemmas
rewrite/simp lists in added code: 0 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Asymptotic/Sampling
rewrite/simp lists in added code: 3 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/Arithmetic
rewrite/simp lists in added code: 16 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/Concrete
rewrite/simp lists in added code: 4 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/DiscreteLog
rewrite/simp lists in added code: 2 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/DiscreteLogHardcore
rewrite/simp lists in added code: 1 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/ElGamal
rewrite/simp lists in added code: 6 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/Factoring
rewrite/simp lists in added code: 6 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/RSA
rewrite/simp lists in added code: 12 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/Candidates/Rabin
rewrite/simp lists in added code: 9 ; unfold/delta: 0
HIT 2645 rw listToNat
hits: 1
  EXPLICIT 207:+**Proof sketch.** Each word is a bundle field on pairs of earlier words, in applied form (`PolyTimeComputable.comp'`), folded into its definition by `unfold`: the coin segments (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rsaSampleCoins`), `x` (`polyTimeComputable_unitSampleStr` on the re-laid-out input, `NUPPT.polyTimeComputable_layout`), `y` (`H.modExp`), `z` (`A.polyTimeComputable_output`), the padded modulus (`PolyTimeComputable.append`, `H.sub`), the test (`H.modExp`, two `H.le`), `d` and the gcd (`H.add`, `H.sub`, `H.divMod`, `H.xgcd`), and the truncation (`polyTimeComputable_unaryPoly`, `H.sub`, `polyTimeComputable_pairDropPoly var`); `polyTimeComputable_ite` selects the output. -/
  EXPLICIT 303:+(`PolyTimeComputable.comp'`) and folded into its definition by `unfold`: the exponent (`H.divMod`, `H.add`),
== TCSlib/Cryptography/HardcoreBit/Basic
rewrite/simp lists in added code: 2 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/NumberTheory/Primality
rewrite/simp lists in added code: 4 ; unfold/delta: 0
hits: 0
== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ColZKLemmas
rewrite/simp lists in added code: 0 ; unfold/delta: 0
hits: 0
